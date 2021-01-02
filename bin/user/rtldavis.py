#!/usr/bin/env python
# coding: latin-1
#
# This driver is a merge of modified versions of both
# the weewx-sdr driver and the weewx_meteostick driver.
# This program also use a modified version of the rtldavis package.
# See: https://github.com/matthewwall/weewx-sdr
#      https://github.com/matthewwall/weewx-meteostick
#      https://github.com/bemasher/rtldavis
#
# Copyright 2019 Matthew Wall, Luc Heijst
# Thanks to kobuki for the calc_wind_speed_ec logic.
#
# Distributed under the terms of the GNU Public License (GPLv3)
#
# This program is free software: you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation, either version 3 of the License, or any later version.
#
# This program is distributed in the hope that it will be useful, but WITHOUT
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE.
#
# See http://www.gnu.org/licenses/
#
# 27-04-2020 release note:
# This version of rtldavis.py works best with version 0.13 of main.go or higher.
# For EU frequencies the freqError values are stored in the database in 
# time slots of two days per transmitter (when activated).

"""
Collect data from rtldavis  
see: https://github.com/bemasher/rtldavis

Run rtld on a thread and push the output onto a queue.

....

[Rtldavis]
    # This section is for the rtldavis sdr-rtl USB receiver.
    cmd = /home/pi/work/bin/rtldavis 

    # Radio frequency to use between USB transceiver and console: US, NZ or EU
    # US uses 915 MHz, NZ uses 921 MHz and EU uses 868.3 MHz.  Default is EU.
    transceiver_frequency = EU
    
    # Used channels: 0=not present, 1-8)
    # The channel of the Vantage Vue ISS or Vantage Pro or Pro2 ISS
    iss_channel = 1
    # The values below only apply for Vantage Pro or Pro2
    anemometer_channel = 0
    leaf_soil_channel  = 0
    temp_hum_1_channel = 0
    temp_hum_2_channel = 0
    # rain bucket type (0: 0.01 inch, 1: 0.2 mm)
    rain_bucket_type = 1
    
    # Print debug messages
    # 0=no logging; 1=minimum logging; 2=normal logging; 3=detailed logging
    debug_parse = 0
    debug_rain  = 0
    debug_rtld  = 2    # rtldavis logging: 1=inf; 2=(1)+data+chan; 3=(2)+pkt

    # The pct_good per transmitter can be saved to the database
    # This has only effect with 2 transmitters or more
    save_pct_good_per_transmitter = False

    # The driver to use:
    driver = user.rtldavis

"""
from __future__ import print_function  # Python 2/3 compatiblity
from __future__ import with_statement

from subprocess import check_output
import signal
from calendar import timegm
import fnmatch
import os
import re
import subprocess
import math
import string
import threading
import time

# Python 2/3 compatiblity
try:
    import Queue as queue   # python 2
except ImportError:
    import queue            # python 3

import weewx.drivers
import weewx.engine
import weewx.units
from weewx.crc16 import crc16
from weewx.units import obs_group_dict
from weeutil.weeutil import tobool

# Use new-style weewx logging
import weeutil.logger
import logging
log = logging.getLogger(__name__)

def logdbg(msg):
	log.debug(msg)

def loginf(msg):
	log.info(msg)

def logerr(msg):
	log.error(msg)

DRIVER_NAME = 'Rtldavis'
DRIVER_VERSION = '0.20'

weewx.units.obs_group_dict['frequency'] = 'group_frequency'
weewx.units.USUnits['group_frequency'] = 'hertz'
weewx.units.MetricUnits['group_frequency'] = 'hertz'
weewx.units.MetricWXUnits['group_frequency'] = 'hertz'
weewx.units.default_unit_format_dict['hertz'] = '%.0f'
weewx.units.default_unit_label_dict['hertz'] = ' Hz'

if weewx.__version__ < "3":
    raise weewx.UnsupportedFeature("weewx 3 is required, found %s" %
                                   weewx.__version__)

# Rtldavis Usage
#
# For 868MHz the usually supplied 10cm DVB-T antenna stick is well suited. Make 
# sure that it is placed on a small metallic ground plane. Avoid near WLAN, DECT 
# or other RF stuff that may disturb the SDR stick.
# 
# To reduce other disturbances, place a sensor in about 2m distance for the first 
# test.
# 
# Call with:  /home/pi/work/bin/rtldavis -tf [transceiver-frequency: US, NZ or EU] -tr [transmitters]} 
#
DEFAULT_CMD = '/home/pi/work/bin/rtldavis -tf EU' 
DEBUG_RAIN = 0
DEBUG_PARSE = 0
DEBUG_RTLD = 0
MPH_TO_MPS = 1609.34 / 3600.0 # meter/mile * hour/second

def loader(config_dict, engine):
    return RtldavisDriver(engine, config_dict)

def confeditor_loader():
    return RtldavisConfigurationEditor()

def dbg_parse(verbosity, msg):
    if DEBUG_PARSE >= verbosity:
        logdbg(msg)

def dbg_rtld(verbosity, msg):
    if DEBUG_RTLD >= verbosity:
        logdbg(msg)

def _fmt(data):
    if not data:
        return ''
    return ' '.join(['%02x' % ord(x) for x in data])

# default temperature for soil moisture and leaf wetness sensors that
# do not have a temperature sensor.
# Also used to normalize raw values for a standard temperature.
DEFAULT_SOIL_TEMP = 24 # C

RAW = 0  # indices of table with raw values
POT = 1  # indices of table with potentials

# Lookup table for soil_moisture_raw values to get a soil_moisture value based
# upon a linear formula.  Correction factor = 0.009
SM_MAP = {RAW: ( 99.2, 140.1, 218.7, 226.9, 266.8, 391.7, 475.6, 538.2, 596.1, 673.7, 720.1),
          POT: (  0.0,   1.0,   9.0,  10.0,  15.0,  35.0,  55.0,  75.0, 100.0, 150.0, 200.0)}

# Lookup table for leaf_wetness_raw values to get a leaf_wetness value based
# upon a linear formula.  Correction factor = 0.0
LW_MAP = {RAW: (857.0, 864.0, 895.0, 911.0, 940.0, 952.0, 991.0, 1013.0),
          POT: ( 15.0,  14.0,   5.0,   4.0,   3.0,   2.0,   1.0,    0.0)}


def calculate_thermistor_temp(temp_raw):
    """ Decode the raw thermistor temperature, then calculate the actual
    thermistor temperature and the leaf_soil potential, using Davis' formulas.
    see: https://github.com/cmatteri/CC1101-Weather-Receiver/wiki/Soil-Moisture-Station-Protocol
    :param temp_raw: raw value from sensor for leaf wetness and soil moisture
    """

    # Convert temp_raw to a resistance (R) in kiloOhms
    a = 18.81099
    b = 0.0009988027
    r = a / (1.0 / temp_raw - b) / 1000 # k ohms

    # Steinhart-Hart parameters
    s1 = 0.002783573
    s2 = 0.0002509406
    try:
        thermistor_temp = 1 / (s1 + s2 * math.log(r)) - 273
        dbg_parse(3, 'r (k ohm) %s temp_raw %s thermistor_temp %s' %
                  (r, temp_raw, thermistor_temp))
        return thermistor_temp
    except ValueError as e:
        logerr('thermistor_temp failed for temp_raw %s r (k ohm) %s'
               'error: %s' % (temp_raw, r, e))
    return DEFAULT_SOIL_TEMP


def lookup_potential(sensor_name, norm_fact, sensor_raw, sensor_temp, lookup):
    """Look up potential based upon a normalized raw value (i.e. temp corrected
    for DEFAULT_SOIL_TEMP) and a linear function between two points in the
    lookup table.
    :param lookup: a table with both sensor_raw_norm values and corresponding
                   potential values. the table is composed for a specific
                   norm-factor.
    :param sensor_temp: sensor temp in C
    :param sensor_raw: sensor raw potential value
    :param norm_fact: temp correction factor for normalizing sensor-raw values
    :param sensor_name: string used in debug messages
    """

    # normalize raw value for standard temperature (DEFAULT_SOIL_TEMP)
    sensor_raw_norm = sensor_raw * (1 + norm_fact * (sensor_temp - DEFAULT_SOIL_TEMP))

    numcols = len(lookup[RAW])
    if sensor_raw_norm >= lookup[RAW][numcols - 1]:
        potential = lookup[POT][numcols - 1] # preset potential to last value
        dbg_parse(2, "%s: temp=%s fact=%s raw=%s norm=%s potential=%s >= RAW=%s" %
                  (sensor_name, sensor_temp, norm_fact, sensor_raw,
                   sensor_raw_norm, potential, lookup[RAW][numcols - 1]))
    else:
        potential = lookup[POT][0] # preset potential to first value
        # lookup sensor_raw_norm value in table
        for x in range(0, numcols):
            if sensor_raw_norm < lookup[RAW][x]:
                if x == 0:
                    # 'pre zero' phase; potential = first value
                    dbg_parse(2, "%s: temp=%s fact=%s raw=%s norm=%s potential=%s < RAW=%s" %
                              (sensor_name, sensor_temp, norm_fact, sensor_raw,
                               sensor_raw_norm, potential, lookup[RAW][0]))
                    break
                else:
                    # determine the potential value
                    potential_per_raw = (lookup[POT][x] - lookup[POT][x - 1]) / (lookup[RAW][x] - lookup[RAW][x - 1])
                    potential_offset = (sensor_raw_norm - lookup[RAW][x - 1]) * potential_per_raw
                    potential = lookup[POT][x - 1] + potential_offset
                    dbg_parse(2, "%s: temp=%s fact=%s raw=%s norm=%s potential=%s RAW=%s to %s POT=%s to %s " %
                              (sensor_name, sensor_temp, norm_fact, sensor_raw,
                               sensor_raw_norm, potential,
                               lookup[RAW][x - 1], lookup[RAW][x],
                               lookup[POT][x - 1], lookup[POT][x]))
                    break
    return potential

# Normalize and interpolate raw wind values at raw angles
def calc_wind_speed_ec(raw_mph, raw_angle):

    # some sanitization: no corrections needed under 3 and no values exist
    # above 150 mph
    if raw_mph < 3 or raw_mph > 150:
        return raw_mph

    # Error correction values for
    #  [ 1..29 by 1, 30..150 by 5 raw mph ]
    #   x
    #  [ 1, 4, 8..124 by 4, 127, 128 raw degrees ]
    #
    # Extracted from a Davis Weather Envoy using a DIY transmitter to
    # transmit raw values and logging LOOP packets.
    # first row: raw angles;
    # first column: raw speed;
    # cells: values provided in response to raw data by the Envoy;
    # [0][0] is filler
    windtab = [
        [0, 1, 4, 8, 12, 16, 20, 24, 28, 32, 36, 40, 44, 48, 52, 56, 60, 64, 68, 72, 76, 80, 84, 88, 92, 96, 100, 104, 108, 112, 116, 120, 124, 127, 128],
        [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
        [3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
        [4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0],
        [5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 0, 0],
        [6, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0],
        [7, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0],
        [8, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0],
        [9, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 0, 0],
        [10, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 0],
        [11, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 0],
        [12, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 0, 0],
        [13, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [14, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [15, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [16, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [17, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [18, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 1, 0, 0],
        [19, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 1, 0, 0],
        [20, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 0, 0],
        [21, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 0, 0],
        [22, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 0, 0],
        [23, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 4, 2, 0, 0],
        [24, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 0, 0],
        [25, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 0, 0],
        [26, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 4, 2, 0, 0],
        [27, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5, 2, 0, 0],
        [28, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 5, 2, 0, 0],
        [29, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5, 5, 2, 0, 0],
        [30, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5, 5, 2, 0, 0],
        [35, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6, 5, 2, 0, -1],
        [40, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 6, 6, 2, 0, -1],
        [45, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 4, 7, 6, 2, -1, -1],
        [50, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 7, 7, 2, -1, -2],
        [55, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 8, 7, 2, -1, -2],
        [60, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 8, 8, 2, -1, -2],
        [65, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 5, 9, 8, 2, -2, -3],
        [70, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 0, 2, 5, 9, 9, 2, -2, -3],
        [75, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 0, 2, 6, 10, 9, 2, -2, -3],
        [80, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 0, 2, 6, 10, 10, 2, -2, -3],
        [85, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 0, 2, 7, 11, 11, 2, -3, -4],
        [90, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2, 7, 12, 11, 2, -3, -4],
        [95, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 2, 3, 2, 2, 2, 1, 1, 1, 1, 2, 7, 12, 12, 3, -3, -4],
        [100, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 2, 2, 1, 1, 1, 1, 2, 8, 13, 12, 3, -3, -4],
        [105, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 2, 8, 13, 13, 3, -3, -4],
        [110, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 2, 8, 14, 14, 3, -3, -5],
        [115, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 2, 9, 15, 14, 3, -3, -5],
        [120, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 2, 3, 3, 3, 3, 3, 2, 2, 2, 1, 1, 1, 3, 9, 15, 15, 3, -4, -5],
        [125, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 2, 2, 1, 1, 1, 3, 10, 16, 16, 3, -4, -5],
        [130, 1, 1, 2, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 3, 3, 3, 2, 2, 2, 1, 1, 3, 10, 17, 16, 3, -4, -6],
        [135, 1, 2, 2, 1, 1, 0, 0, 0, -1, 0, 0, 1, 1, 2, 2, 3, 3, 3, 3, 4, 3, 3, 2, 2, 2, 1, 1, 3, 10, 17, 17, 4, -4, -6],
        [140, 1, 2, 2, 1, 1, 0, 0, 0, -1, 0, 0, 1, 1, 2, 2, 3, 3, 3, 4, 4, 3, 3, 2, 2, 2, 1, 1, 3, 11, 18, 17, 4, -4, -6],
        [145, 2, 2, 2, 1, 1, 0, 0, 0, -1, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 4, 3, 3, 3, 2, 2, 1, 1, 3, 11, 19, 18, 4, -4, -6],
        [150, 2, 2, 2, 1, 1, 0, 0, -1, -1, 0, 0, 1, 1, 2, 3, 3, 4, 4, 4, 4, 4, 3, 3, 2, 2, 1, 1, 3, 12, 19, 19, 4, -4, -6]
    ]

    # EC is symmetric between W/E (90/270°) - probably a wrong assumption,
    # table needs to be redone for 0-360°
    if raw_angle > 128:
        raw_angle = 256 - raw_angle

    s0 = a0 = 1

    while windtab[s0][0] < raw_mph:
        s0 += 1
    while windtab[0][a0] < raw_angle:
        a0 += 1

    if windtab[s0][0] == raw_mph:
        s1 = s0
    else:
        if s0 > 1:
            s0 -= 1
        s1 = len(windtab) - 1 if s0 == len(windtab) - 1 else s0 + 1

    if windtab[0][a0] == raw_angle:
        a1 = a0
    else:
        if a0 > 1:
            a0 -= 1
        a1 = len(windtab[0]) - 2 if a0 == len(windtab) - 1 else a0 + 1

    if s0 == s1 and a0 == a1:
        return raw_mph + windtab[s0][a0]
    else:
        return interpolate(windtab[0][a0], windtab[0][a1],
                                      windtab[s0][0], windtab[s1][0],
                                      windtab[s0][a0], windtab[s0][a1],
                                      windtab[s1][a0], windtab[s1][a1],
                                      raw_angle, raw_mph)

# Simple bilinear interpolation
#
#  a0         a1 <-- fixed raw angles
#  x0---------x1 s0
#  |          |
#  |          |
#  |      * <-|-- raw input angle, raw speed value (x, y)
#  |          |
#  y0---------y1 s1
#                ^
#                \__ speed: measured raw / correction values
#
def interpolate(rx0, rx1,
                ry0, ry1,
                x0, x1,
                y0, y1,
                x, y):

    dbg_parse(2, "rx0=%s, rx1=%s, ry0=%s, ry1=%s, x0=%s, x1=%s, y0=%s, y1=%s, x=%s, y=%s" %
              (rx0, rx1, ry0, ry1, x0, x1, y0, y1, x, y))

    if rx0 == rx1:
        return y + x0 + (y - ry0) / float(ry1 - ry0) * (y1 - y0)

    if ry0 == ry1:
        return y + y0 + (x - rx0) / float(rx1 - rx0) * (x1 - x0)

    dy0 = x0 + (y - ry0) / float(ry1 - ry0) * (y0 - x0)
    dy1 = x1 + (y - ry0) / float(ry1 - ry0) * (y1 - x1)

    return y + dy0 + (x - rx0) / float(rx1 - rx0) * (dy1 - dy0)

class AsyncReader(threading.Thread):

    def __init__(self, fd, queue, label):
        threading.Thread.__init__(self)
        self._fd = fd
        self._queue = queue
        self._running = False
        self.setDaemon(True)
        self.setName(label)

    def run(self):
        logdbg("start async reader for %s" % self.getName())
        self._running = True
        for line in iter(self._fd.readline, ''):
            self._queue.put(line)
            if not self._running:
                break

    def stop_running(self):
        self._running = False


class ProcManager():

    def __init__(self):
        self._cmd = None
        self._process = None
        self.stderr_queue = queue.Queue()
        self.stderr_reader = None
        self.stdout_queue = queue.Queue()
        self.stdout_reader = None

    def get_pid(self, name):
        return map(int,check_output(["pidof",name]).split())

    def startup(self, cmd, path=None, ld_library_path=None):
        # kill existiing rtld processes
        try:
            pid_list = self.get_pid("rtldavis")
            for pid in pid_list:
                os.kill(int(pid), signal.SIGKILL)
                loginf("rtldavis with pid %s killed" % pid)
        except:
            pass

        self._cmd = cmd
        loginf("startup process '%s'" % self._cmd)
        env = os.environ.copy()
        if path:
            env['PATH'] = path + ':' + env['PATH']
        if ld_library_path:
            env['LD_LIBRARY_PATH'] = ld_library_path
        try:
            self._process = subprocess.Popen(cmd.split(' '),
                                             env=env,
                                             stderr=subprocess.PIPE,
                                             stdout=subprocess.PIPE)
            self.stderr_reader = AsyncReader(
                self._process.stderr, self.stderr_queue, 'stderr-thread')
            self.stderr_reader.start()
            self.stdout_reader = AsyncReader(
                self._process.stdout, self.stdout_queue, 'stdout-thread')
            self.stdout_reader.start()
        except (OSError, ValueError) as e:
            raise weewx.WeeWxIOError("failed to start process: %s" % e)

    def shutdown(self):
        loginf('shutdown process %s' % self._cmd)
        self.stderr_reader.stop_running()
        self.stdout_reader.stop_running()
        # kill existiing rtldavis processes
        pid_list = self.get_pid("rtldavis")
        for pid in pid_list:
            os.kill(int(pid), signal.SIGKILL)
            loginf("rtldavis with pid %s killed" % pid)

    def running(self):
        return self._process.poll() is None

    def get_stdout(self):
        lines = []
        while not self.stdout_queue.empty():
            lines.append(self.stdout_queue.get().decode('utf-8'))
        return lines

    def get_stderr(self):
        lines = [] 
        # When a lot rtldavis packets are read, a hangup
        # will occur regularly, sometimes of more than a minute.
        # Therefor a maximum run-time of get_stderr of 10 seconds 
        # is invoked to let genLoopPackets process the yielded lines. 
        start_time = int(time.time())
        while self.running() and int(time.time()) - start_time < 10:
            try:             
                line = self.stderr_queue.get(True, 10).decode('utf-8')
                lines.append(line) 
                yield lines
                lines = []
            except queue.Empty:
                yield lines
                lines = []


class Packet:

    def __init__(self):
        pass

    @staticmethod
    def parse_text(ts, payload, lines):
        return None


class DATAPacket(Packet):
    IDENTIFIER = re.compile("^\d\d:\d\d:\d\d.[\d]{6} [0-9A-F][0-7][0-9A-F]{14}")
    PATTERN = re.compile('([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2})([0-9A-F]{2}) ([\d]+) ([\d]+) ([\d]+) ([\d]+)')

    @staticmethod
    def parse_text(self, payload, lines):
        pkt = dict()
        m = DATAPacket.PATTERN.search(lines[0])
        if m:
            dbg_rtld(2, "data: %s" % lines[0])
            raw_msg = [0] * 8
            for i in range(0, 8):
                raw_msg[i] = chr(int(m.group(i + 1), 16))
            PacketFactory._check_crc(raw_msg)
            for i in range(0, 8):
                raw_msg[i] = m.group(i + 1)
            raw_pkt = bytearray([int(i, base=16) for i in raw_msg])
            pkt = self.parse_raw(self, raw_pkt)
            for i in range(0, 4):
                pkt['curr_cnt%d' % i] = int(m.group(i + 9))
            dbg_rtld(3, "data_pkt: %s" % pkt)
            lines.pop(0)
            return pkt
        else:
            dbg_rtld(1, "DATAPacket: unrecognized data: '%s'" % lines[0])
            lines.pop(0)


class CHANNELPacket(Packet):
    IDENTIFIER = re.compile("ChannelIdx:")
    # chan: 13:44:13.116046 Hop: {ChannelIdx:3 ChannelFreq:868437250 FreqError:431 Transmitter:1}
    PATTERNv13 = re.compile('ChannelIdx:([\d]+) ChannelFreq:([\d]+) FreqError:([\d-]+) Transmitter:([\d]+)')
    PATTERNv12 = re.compile('ChannelIdx:([\d]+) ChannelFreq:([\d]+) FreqError:([\d-]+)')

    @staticmethod
    def parse_text(self, payload, lines):
        pkt = dict()
        # check for channelpacket of rtldavis version 13 and higher
        m = CHANNELPacket.PATTERNv13.search(lines[0])
        if m:
            dbg_rtld(2, "chan: %s" % lines[0])

            if abs(int(m.group(3))) > 20000:
                raise weewx.WeeWxIOError("RESTART RTLDAVIS PROGRAM: abs freqOffset channel %s too big (> 20000): %s" % (m.group(1), m.group(3)))
            # save frequency errors only for EU band
            if self.frequency == 'EU':
                # Store the FreqErrors only for one transmitter
                # The data for each transmitter is stored during 2 full days
                if int(m.group(4)) == self.transm_to_store:
                    pkt['dateTime'] = int(time.time() + 0.5)
                    pkt['usUnits'] = weewx.METRICWX
                    for y in range(0, 5):
                        if int(m.group(1)) == y:
                            pkt['freqError%d' % y] = int(m.group(3))
                            dbg_rtld(3, "Store freqError%d: %s for transmitter: %s" % (y, int(m.group(3)), int(m.group(4))))
                    dbg_rtld(3, "chan_pkt: %s" % pkt)
                else:
                    dbg_rtld(3, "Don't store freqErr: %s for transm: %s" % (int(m.group(3)), int(m.group(4))))
            else:
                dbg_rtld(3, "Don't store freqErrors for frequency band %s" % self.frequency)
            lines.pop(0)
            return pkt
        else:
            # check for channelpacket of rtldavis version 12 and lower
            m = CHANNELPacket.PATTERNv12.search(lines[0])
            if m:
                dbg_rtld(2, "chan: %s" % lines[0])

                if abs(int(m.group(3))) > 20000:
                    raise weewx.WeeWxIOError("RESTART RTLDAVIS PROGRAM: abs freqOffset channel %s too big (> 20000): %s" % (m.group(1), m.group(3)))
                # save frequency errors only for EU band
                if self.frequency == 'EU':
                    pkt['dateTime'] = int(time.time() + 0.5)
                    pkt['usUnits'] = weewx.METRICWX
                    for y in range(0, 5):
                        if int(m.group(1)) == y:
                            pkt['freqError%d' % y] = int(m.group(3))
                    dbg_rtld(3, "chan_pkt: %s" % pkt)
                else:
                    dbg_rtld(3, "Don't store freqErrors for frequency band %s" % self.frequency)
                lines.pop(0)
                return pkt
            else:
                dbg_rtld(1, "CHANNELPacket: unrecognized data: '%s'" % lines[0])
                lines.pop(0)


class PacketFactory(object):

    # FIXME: do this with class introspection
    KNOWN_PACKETS = [
        DATAPacket,
        CHANNELPacket
    ]

    @staticmethod
    def _check_crc(msg):
        if crc16(msg) != 0:
            raise ValueError("CRC error")

    @staticmethod
    def create(self, lines):
        # return a list of packets from the specified lines
        while lines:
            pkt = PacketFactory.parse_text(self, lines)
            if pkt is not None:
                yield pkt

    @staticmethod
    def parse_text(self, lines):
        pkt = dict()
        payload = lines[0].strip()
        if payload:
            for parser in PacketFactory.KNOWN_PACKETS:
                m = parser.IDENTIFIER.search(payload)
                if m:
                    pkt = parser.parse_text(self, payload, lines)
                    return pkt
            dbg_rtld(1, "info: %s" % payload)
        else:
            dbg_rtld(2, "blank line")
        lines.pop(0)
        return None



class RtldavisConfigurationEditor(weewx.drivers.AbstractConfEditor):
    @property
    def default_stanza(self):
        return """
[Rtldavis]
    # This section is for the rtldavis sdr-rtl USB receiver.

    cmd = /home/pi/work/bin/rtldavis [options]
    # Options:
    # -ppm = frequency correction of rtl dongle in ppm; default = 0
    # -gain = tuner gain in tenths of Db; default = 0 means "auto gain"
    # -ex = extra loopTime in ms; default = 0
    # -fc = frequency correction for all channels; default = 0
    # -u  = log undefined signals
    #
    # The options below will autoamically be set
    # -tf = transmitter frequencies, US, NZ or EU
    # -tr = transmitters: tr1=1,  tr2=2,  tr3=4,  tr4=8, 
    #                     tr5=16, tr6=32, tr7=64, tr8=128

    # Radio frequency to use between USB transceiver and console: US, NZ or EU
    # US uses 915 MHz, NZ uses 921 MHz and EU uses 868.3 MHz.  Default is EU.
    transceiver_frequency = EU
    
    # Used channels: 0=not present, 1-8)
    # The channel of the Vantage Vue ISS or Vantage Pro or Pro2 ISS
    iss_channel = 1
    # The values below only apply for Vantage Pro or Pro2
    anemometer_channel = 0
    leaf_soil_channel  = 0
    temp_hum_1_channel = 0
    temp_hum_2_channel = 0
    # rain bucket type (0: 0.01 inch, 1: 0.2 mm)
    rain_bucket_type = 1
    
    # Print debug messages
    # 0=no logging; 1=minimum logging; 2=normal logging; 3=detailed logging
    debug_parse = 0
    debug_rain  = 0
    debug_rtld  = 2     # rtldavis logging: 1=inf; 2=(1)+data+chan; 3=(2)+pkt

    # The pct_good per transmitter can be saved to the database
    # This has only effect with 2 transmitters or more
    save_pct_good_per_transmitter = False

    # The driver to use:
    driver = user.rtldavis

"""

class RtldavisDriver(weewx.drivers.AbstractDevice, weewx.engine.StdService):

    NUM_CHAN = 10 # 8 channels, one fake channel (9), one unused channel (0)
    DEFAULT_FREQUENCY = 'EU'
    DEFAULT_RAIN_BUCKET_TYPE = 1
    DEFAULT_SENSOR_MAP = {
        'pressure': 'pressure',
        'inTemp': 'temp_in',  # temperature of optional BMP280 module
        'windSpeed': 'wind_speed',
        'windDir': 'wind_dir',
        'outTemp': 'temperature',
        'outHumidity': 'humidity',
        'inHumidity': 'humidity_in',
        # To use a rainRate calculation from this driver that closely matches
        # that of a Davis station, uncomment the rainRate field then specify
        # rainRate = hardware in section [StdWXCalculate] of weewx.conf
        'rainRate': 'rain_rate',
        'radiation': 'solar_radiation',
        'UV': 'uv',
        #'extraTemp1': 'temp_1',
        #'extraTemp2': 'temp_2',
        #'extraTemp3': 'temp_3',
        'soilTemp1': 'soil_temp_1',
        'soilTemp2': 'soil_temp_2',
        'soilTemp3': 'soil_temp_3',
        'soilTemp4': 'soil_temp_4',
        'leafTemp1': 'leaf_temp_1',
        #'leafTemp2': 'leaf_temp_2',
        'extraHumid1': 'humid_1',
        'extraHumid2': 'humid_2',
        'soilMoist1': 'soil_moisture_1',
        'soilMoist2': 'soil_moisture_2',
        'soilMoist3': 'soil_moisture_3',
        'soilMoist4': 'soil_moisture_4',
        'leafWet1': 'leaf_wetness_1',
        'leafWet2': 'leaf_wetness_2',
        'rxCheckPercent': 'pct_good_all', # updated in 
        'txBatteryStatus': 'bat_iss',
        'supplyVoltage': 'supercap_volt',
        'referenceVoltage': 'solar_power',
        'windBatteryStatus': 'bat_anemometer',
        'rainBatteryStatus': 'bat_leaf_soil',
        'outTempBatteryStatus': 'bat_th_1',
        'inTempBatteryStatus': 'bat_th_2',
        'extraTemp1': 'pct_good_0',  # renamed
        'extraTemp2': 'pct_good_1',  # renamed
        'extraTemp3': 'pct_good_2',  # renamed
        'leafTemp2': 'pct_good_3',   # renamed
        'consBatteryVoltage': 'freqError0',
        'hail': 'freqError1',
        'hailRate': 'freqError2',
        'heatingTemp': 'freqError3',
        'heatingVoltage': 'freqError4'}


    def __init__(self, engine, config_dict):
        loginf('driver version is %s' % DRIVER_VERSION)
        self.setup_units_rtld_schema()

        if engine:
            weewx.engine.StdService.__init__(self, engine, config_dict)
        stn_dict = config_dict.get(DRIVER_NAME, {})

        global DEBUG_PARSE
        DEBUG_PARSE = int(stn_dict.get('debug_parse', DEBUG_PARSE))
        global DEBUG_RAIN
        DEBUG_RAIN = int(stn_dict.get('debug_rain', DEBUG_RAIN))
        global DEBUG_RTLD
        DEBUG_RTLD = int(stn_dict.get('debug_rtld', DEBUG_RTLD))

        # modification by Luc Heijst
        self.last_hum = None
        # end modification by Luc

        bucket_type = int(stn_dict.get('rain_bucket_type',
                                       self.DEFAULT_RAIN_BUCKET_TYPE))
        if bucket_type not in [0, 1]:
            raise ValueError("unsupported rain bucket type %s" % bucket_type)
        self.rain_per_tip = 0.254 if bucket_type == 0 else 0.2 # mm
        loginf('using rain_bucket_type %s' % bucket_type)
        self.sensor_map = dict(self.DEFAULT_SENSOR_MAP)
        if 'sensor_map' in stn_dict:
            self.sensor_map.update(stn_dict['sensor_map'])
        loginf('sensor map is: %s' % self.sensor_map)
        self._init_stats()
        self.last_rain_count = None
        self._log_humidity_raw = tobool(stn_dict.get('log_humidity_raw', False))
        self._save_pct_good_per_transmitter = tobool(stn_dict.get('save_pct_good_per_transmitter', False))
        self._sensor_map = stn_dict.get('sensor_map', {})
        loginf('sensor map is %s' % self._sensor_map)
        self.cmd = stn_dict.get('cmd', DEFAULT_CMD)
        self.path = stn_dict.get('path', None)
        self.ld_library_path = stn_dict.get('ld_library_path', None)

        freq = stn_dict.get('transceiver_frequency', self.DEFAULT_FREQUENCY)
        if freq not in ['US', 'NZ', 'EU']:
            raise ValueError("invalid frequency %s" % freq)
        self.frequency = freq
        loginf('using frequency %s' % self.frequency)
        channels = dict()
        channels['iss'] = int(stn_dict.get('iss_channel', 1))
        channels['anemometer'] = int(stn_dict.get('anemometer_channel', 0))
        channels['leaf_soil'] = int(stn_dict.get('leaf_soil_channel', 0))
        channels['temp_hum_1'] = int(stn_dict.get('temp_hum_1_channel', 0))
        channels['temp_hum_2'] = int(stn_dict.get('temp_hum_2_channel', 0))
        if channels['anemometer'] == 0:
            channels['wind_channel'] = channels['iss']
        else:
            channels['wind_channel'] = channels['anemometer']
        self.channels = channels
        loginf('using iss_channel %s' % channels['iss'])
        loginf('using anemometer_channel %s' % channels['anemometer'])
        loginf('using leaf_soil_channel %s' % channels['leaf_soil'])
        loginf('using temp_hum_1_channel %s' % channels['temp_hum_1'])
        loginf('using temp_hum_2_channel %s' % channels['temp_hum_2'])

        self.transmitters, self.tr_count = RtldavisDriver.ch_to_xmit(self, 
            channels['iss'], channels['anemometer'], channels['leaf_soil'],
            channels['temp_hum_1'], channels['temp_hum_2'])
        loginf('using transmitters %d' % self.transmitters)
        loginf('log_humidity_raw %s' % self._log_humidity_raw)

        self.cmd = self.cmd + " -tf " + str(self.frequency) + " -tr " + str(self.transmitters)

        self._last_pkt = None # avoid duplicate sequential packets
        self._mgr = ProcManager()
        self._mgr.startup(self.cmd, self.path, self.ld_library_path)

        # bind to new archive record events so that we can update the rf
        # stats on each archive record.
        if engine:
            self.bind(weewx.NEW_ARCHIVE_RECORD, self.new_archive_record)

    @staticmethod
    def ch_to_xmit(self, iss_channel, anemometer_channel, leaf_soil_channel,
                   temp_hum_1_channel, temp_hum_2_channel):
        transmitters = 0
        transmitters += 1 << (iss_channel - 1)
        if anemometer_channel != 0:
            transmitters += 1 << (anemometer_channel - 1)
        if leaf_soil_channel != 0:
            transmitters += 1 << (leaf_soil_channel - 1)
        if temp_hum_1_channel != 0:
            transmitters += 1 << (temp_hum_1_channel - 1)
        if temp_hum_2_channel != 0:
            transmitters += 1 << (temp_hum_2_channel - 1)
        # program main.go reports the current msg count for the first 4 active transmitters
        # table self.stats['activeTrIds'] contain the transmitter ID's (range 0-7) of
        # the active transmitters.
        # This is used as a pointer to self.stats['loop_times'] in _update_summaries.
        mask = 1
        trIdCount = 0
        for i in range(0, 8):
            if transmitters & mask != 0:
                self.stats['activeTrIds'][trIdCount] = i
                self.stats['activeTrIdPtrs'][i] = trIdCount
                trIdCount = trIdCount + 1
            mask = mask << 1
        return transmitters, trIdCount

    def _data_to_packet(self, data):
        packet = dict()
        # map sensor observations to database field names
        for k in self.sensor_map:
            if self.sensor_map[k] in data:
                packet[k] = data[self.sensor_map[k]]
        # convert the rain count to a rain delta measure
        if 'rain_count' in data:
            if self.last_rain_count is not None:
                rain_count = data['rain_count'] - self.last_rain_count
            else:
                rain_count = 0
            # handle rain counter wrap around from 127 to 0
            if rain_count < 0:
                loginf("rain counter wraparound detected rain_count=%s" %
                       rain_count)
                rain_count += 128
            self.last_rain_count = data['rain_count']
            packet['rain'] = float(rain_count) * self.rain_per_tip
            if DEBUG_RAIN:
                logdbg("rain=%s rain_count=%s last_rain_count=%s" %
                       (packet['rain'], rain_count, self.last_rain_count))
        packet['dateTime'] = int(time.time() + 0.5)
        packet['usUnits'] = weewx.METRICWX
        return packet

    def _init_stats(self):
        self.stats = {
            # theoretical loop times for 8 transmitter channels (plus 100.0 as dummy)
            'loop_times': [2.5625, 2.625, 2.6875, 2.75, 2.8125, 2.875, 2.9375, 3, 100.0],
            'activeTrIds': [9] * 8,    # 9 means: sensor not active
            'activeTrIdPtrs': [0] * 8, # pointer to active transmitter
            'curr_ts': 0,              # time stamp of current archive  
            'last_ts': 0,              # time stamp of previous archive
            'curr_cnt': [0] * 4,       # received messages since startup at current archive
            'last_cnt': [0] * 4,       # received messages since startup at previous archive
            'max_count': [0] * 4,      # max to receive messages per transmitter current archive period
            'count': [0] * 4,          # received messages per transmitter current archive period 
            'missed': [0] * 4,         # missed messages per transmitter current archive period
            'pct_good': [None] * 4,    # percentage of good messages per transmitter
            'pct_good_all': None}      # percentage of good messages for all transmitters

    def _reset_stats(self):
        self.stats['last_ts'] = self.stats['curr_ts']
        for i in range(0, 4):
            self.stats['last_cnt'][i] = self.stats['curr_cnt'][i]
            self.stats['pct_good'][i] = None
        self.stats['pct_good_all'] = None

    def _update_stats(self, curr_cnt0, curr_cnt1, curr_cnt2, curr_cnt3):
        # update the statistics
        # save the message counts since startup
        self.stats['curr_cnt'][0] = int(curr_cnt0)
        self.stats['curr_cnt'][1] = int(curr_cnt1)
        self.stats['curr_cnt'][2] = int(curr_cnt2)
        self.stats['curr_cnt'][3] = int(curr_cnt3)

    def _update_summaries(self):
        self.stats['curr_ts'] = int(time.time())
        logdbg("ARCHIVE_STATS: last time: last_cnt[0-3]: %12d %8d %8d %8d %8d" % (self.stats['last_ts'], self.stats['last_cnt'][0], self.stats['last_cnt'][1], self.stats['last_cnt'][2], self.stats['last_cnt'][3]))
        logdbg("ARCHIVE_STATS: curr time: curr_cnt[0-3]: %12d %8d %8d %8d %8d" % (self.stats['curr_ts'], self.stats['curr_cnt'][0], self.stats['curr_cnt'][1], self.stats['curr_cnt'][2], self.stats['curr_cnt'][3]))
        # if not the first time since startup
        if self.stats['last_ts'] > 0:
            total_count = 0
            total_missed = 0
            total_max_count = 0
            period = self.stats['curr_ts'] - self.stats['last_ts']
            # do for the first 4 active transmitters
            # Note: the stats of the 5th and more active transmitters are not calculated.
            for i in range(0, 4):
                # if this transmitter is active
                if self.stats['curr_cnt'][i] > 0:
                    # y is a pointer to the channel number of the active transmitters (9 means: not-active)
                    # the loop_time is different for each transmitter
                    x = self.stats['activeTrIds'][i]
                    # calculate per transmitter the theoretical maximum number of received message this archive period
                    self.stats['max_count'][i] = period // self.stats['loop_times'][x]
                    self.stats['count'][i] = self.stats['curr_cnt'][i] - self.stats['last_cnt'][i]
                    # test if not init (counters reset to zero)
                    if self.stats['count'][i] > 0:
                        self.stats['missed'][i] = self.stats['max_count'][i] - self.stats['count'][i]
                        self.stats['pct_good'][i] = 100.0 * self.stats['count'][i] / self.stats['max_count'][i]
                        # calculate the totals for all active transmitters
                        total_count = total_count + self.stats['count'][i]
                        total_missed = total_missed + self.stats['missed'][i]
                        total_max_count = total_max_count + self.stats['max_count'][i]
            # if there is a total
            if total_max_count > 0 and self.stats['pct_good_all'] is not None:
                self.stats['pct_good_all'] = 100.0 * total_count / total_max_count
				logdbg("ARCHIVE_STATS: total_max_count=%d total_count=%d total_missed=%d  pctGood=%6.2f" % 
					(total_max_count, total_count, total_missed, self.stats['pct_good_all']))
            # log the stats for each active transmitter and no-init-counters
            for i in range(0, 4):
                if self.stats['curr_cnt'][i] > 0 and self.stats['count'][i] > 0 and self.stats['pct_good'] is not None:
                    x = self.stats['activeTrIds'][i]
                    logdbg("ARCHIVE_STATS: station %d: max_count= %4d count=%4d missed=%4d pct_good=%6.2f" % 
                        (i+1, self.stats['max_count'][i], self.stats['count'][i], self.stats['missed'][i], self.stats['pct_good'][i]))

    def new_archive_record(self, event):
        logdbg("new_archive_record")
        # calculations per archive period
        self._update_summaries()  # calculate summaries
        # Store the summaries in the database
        # for the pct_good values in the DEFAULT_SENSOR_MAP
        if self.stats['pct_good_all'] is not None:
            # Store overal pct_good if value not None
            event.record['rxCheckPercent'] = self.stats['pct_good_all']
            # test if individual pct_good values have to be saved
            if self._save_pct_good_per_transmitter:
                for tr in range(0, 4):
                    data = 'pct_good_%s' % tr
                    for k in self.sensor_map:
                        # Test if sensor is in the sensor map.
                        if self.sensor_map[k] in data:
                            if tr == 0 and self.tr_count > 1:
                                # When tr_count = 1 we don't store the pct_good of transmitter 1
                                # because the value is the same as in rxCheckPercent
                                event.record[k] = self.stats['pct_good'][tr]
                            if tr > 0 and tr <= self.tr_count:
                                # save pct_good for active transmitters (max=4)
                                event.record[k] = self.stats['pct_good'][tr]
        self._reset_stats()  # save current stats in last stats

    def closePort(self):
        self._mgr.shutdown()

    @property
    def hardware_name(self):
        return 'Rtldavis'

    def genLoopPackets(self):
        packet = dict()
        time_last_received = int(time.time())
        # change the presentation of the FrequencyErrors of the transmitters 
        #  each period
        periodShowOneTransm = 2*24*3600  # 2 days
        rel_transm_to_store = int(((time_last_received-(3*3600)) % (periodShowOneTransm * self.tr_count)) / periodShowOneTransm)
        self.transm_to_store = self.stats['activeTrIds'][rel_transm_to_store]
        dbg_parse(1, "Number of transmitters: %s, store freqError data for transmitter with ID=%s" % (self.tr_count, self.transm_to_store))
        
        while self._mgr.running():
            # the stalled timeout must be greater than the init period
            # init period is EU: 16 s, US, AU and NZ: 133 s
            if int(time.time()) - time_last_received > 150:
                raise weewx.WeeWxIOError("rtldavis process stalled")
            # program main.go writes its data to stderr
            for lines in self._mgr.get_stderr():
                for data in PacketFactory.create(self, lines):
                    if data:
                        time_last_received = int(time.time())
                        if 'curr_cnt0' in data:
                            self._update_stats(data['curr_cnt0'], data['curr_cnt1'], data['curr_cnt2'], data['curr_cnt3'])
                        if data != self._last_pkt:
                            self._last_pkt = data
                            packet = self._data_to_packet(data)
                            if packet is not None:
                                dbg_parse(3, "pkt= %s" % packet)
                                yield packet
                        else:
                            if packet:
                                dbg_parse(3, "ignoring duplicate packet %s" % packet)
                    elif lines:
                        loginf("missed (unparsed): %s" % lines)
        else:
            logerr("err: %s" % self._mgr.get_stderr())
            raise weewx.WeeWxIOError("rtldavis process is not running")

    def parse_readings(self, pkt):
        data = dict()
        if not pkt:
            return data
        try:
            data = self.parse_raw(self, pkt)
        except ValueError as e:
            logerr("parse failed for '%s': %s" % (pkt, e))
        return data

    @staticmethod
    def parse_raw(self, pkt):
        data = dict()
        data['channel'] = (pkt[0] & 0x7) + 1
        battery_low = (pkt[0] >> 3) & 0x1
        if data['channel'] == self.channels['iss']or data['channel'] == self.channels['anemometer'] \
                or data['channel'] == self.channels['temp_hum_1']or data['channel'] == self.channels['temp_hum_2']:
            if data['channel'] == self.channels['iss']:
                data['bat_iss'] = battery_low
            elif data['channel'] == self.channels['anemometer']:
                data['bat_anemometer'] = battery_low
            elif data['channel'] == self.channels['temp_hum_1']:
                data['bat_th_1'] = battery_low
            else:
                data['bat_th_2'] = battery_low
            # Each data packet of iss or anemometer contains wind info,
            # but it is only valid when received from the channel with
            # the anemometer connected
            # message examples:
            # 51 06 B2 FF 73 00 76 61
            # E0 00 00 4E 05 00 72 61 (no sensor)
            wind_speed_raw = pkt[1]
            wind_dir_raw = pkt[2]
            if not(wind_speed_raw == 0 and wind_dir_raw == 0):
                """ The elder Vantage Pro and Pro2 stations measured
                the wind direction with a potentiometer. This type has
                a fairly big dead band around the North. The Vantage
                Vue station uses a hall effect device to measure the
                wind direction. This type has a much smaller dead band,
                so there are two different formulas for calculating
                the wind direction. To be able to select the right
                formula the Vantage type must be known.
                For now we use the traditional 'pro' formula for all
                wind directions.
                """
                dbg_parse(2, "wind_speed_raw=%03x wind_dir_raw=0x%03x" %
                          (wind_speed_raw, wind_dir_raw))

                # Vantage Pro and Pro2
                if wind_dir_raw == 0:
                    wind_dir_pro = 5.0
                elif wind_dir_raw == 255:
                    wind_dir_pro = 355.0
                else:
                    wind_dir_pro = 9.0 + (wind_dir_raw - 1) * 342.0 / 253.0

                    # Vantage Vue
                    wind_dir_vue = wind_dir_raw * 1.40625 + 0.3

                    # wind error correction is by raw byte values
                    wind_speed_ec = round(calc_wind_speed_ec(wind_speed_raw, wind_dir_raw))

                    data['wind_speed_ec'] = wind_speed_ec
                    data['wind_speed_raw'] = wind_speed_raw
                    data['wind_dir'] = wind_dir_pro
                    data['wind_speed'] = wind_speed_ec * MPH_TO_MPS
                    dbg_parse(2, "WS=%s WD=%s WS_raw=%s WS_ec=%s WD_raw=%s WD_pro=%s WD_vue=%s" %
                              (data['wind_speed'], data['wind_dir'],
                               wind_speed_raw, wind_speed_ec,
                               wind_dir_raw if wind_dir_raw <= 180 else 360 - wind_dir_raw,
                               wind_dir_pro, wind_dir_vue))

            # data from both iss sensors and extra sensors on
            # Anemometer Transport Kit
            message_type = (pkt[0] >> 4 & 0xF)
            if message_type == 2:
                # supercap voltage (Vue only) max: 0x3FF (1023)
                # message example:
                # 20 04 C3 D4 C1 81 89 EE
                """When the raw values are divided by 300 the maximum
                voltage of the super capacitor will be about 2.8 V. This
                is close to its maximum operating voltage of 2.7 V
                """
                supercap_volt_raw = ((pkt[3] << 2) + (pkt[4] >> 6)) & 0x3FF
                if supercap_volt_raw != 0x3FF:
                    data['supercap_volt'] = supercap_volt_raw / 300.0
                    dbg_parse(2, "supercap_volt_raw=0x%03x value=%s" %
                              (supercap_volt_raw, data['supercap_volt']))
            elif message_type == 3:
                # unknown message type
                # message examples:
                # TODO
                # TODO (no sensor)
                dbg_parse(1, "unknown message with type=0x03; "
                          "pkt[3]=0x%02x pkt[4]=0x%02x pkt[5]=0x%02x"
                          % (pkt[3], pkt[4], pkt[5]))
            elif message_type == 4:
                # uv
                # message examples:
                # 40 00 00 12 45 00 B5 2A
                # 41 00 DE FF C3 00 A9 8D (no sensor)
                uv_raw = ((pkt[3] << 2) + (pkt[4] >> 6)) & 0x3FF
                if uv_raw != 0x3FF:
                    data['uv'] = uv_raw / 50.0
                    dbg_parse(2, "uv_raw=%04x value=%s" %
                              (uv_raw, data['uv']))
            elif message_type == 5:
                # rain rate
                # message examples:
                # 50 00 00 FF 75 00 48 5B (no rain)
                # 50 00 00 FE 75 00 7F 6B (light_rain)
                # 50 00 00 1B 15 00 3F 80 (heavy_rain)
                # 51 00 DB FF 73 00 11 41 (no sensor)
                """ The published rain_rate formulas differ from each
                other. For both light and heavy rain we like to know a
                'time between tips' in s. The rain_rate then would be:
                3600 [s/h] / time_between_tips [s] * 0.2 [mm] = xxx [mm/h]
                """
                time_between_tips_raw = ((pkt[4] & 0x30) << 4) + pkt[3]  # typical: 64-1022
                dbg_parse(2, "time_between_tips_raw=%03x (%s)" %
                          (time_between_tips_raw, time_between_tips_raw))
                if data['channel'] == self.channels['iss']: # rain sensor is present
                    rain_rate = None
                    if time_between_tips_raw == 0x3FF:
                        # no rain
                        rain_rate = 0
                        dbg_parse(3, "no_rain=%s mm/h" % rain_rate)
                    elif pkt[4] & 0x40 == 0:
                        # heavy rain. typical value:
                        # 64/16 - 1020/16 = 4 - 63.8 (180.0 - 11.1 mm/h)
                        time_between_tips = time_between_tips_raw / 16.0
                        rain_rate = 3600.0 / time_between_tips * self.rain_per_tip
                        dbg_parse(2, "heavy_rain=%s mm/h, time_between_tips=%s s" %
                                  (rain_rate, time_between_tips))
                    else:
                        # light rain. typical value:
                        # 64 - 1022 (11.1 - 0.8 mm/h)
                        time_between_tips = time_between_tips_raw
                        rain_rate = 3600.0 / time_between_tips * self.rain_per_tip
                        dbg_parse(2, "light_rain=%s mm/h, time_between_tips=%s s" %
                                  (rain_rate, time_between_tips))
                    data['rain_rate'] = rain_rate
            elif message_type == 6:
                # solar radiation
                # message examples
                # 61 00 DB 00 43 00 F4 3B
                # 60 00 00 FF C5 00 79 DA (no sensor)
                sr_raw = ((pkt[3] << 2) + (pkt[4] >> 6)) & 0x3FF
                if sr_raw < 0x3FE:
                    data['solar_radiation'] = sr_raw * 1.757936
                    dbg_parse(2, "solar_radiation_raw=0x%04x value=%s"
                              % (sr_raw, data['solar_radiation']))
            elif message_type == 7:
                # solar cell output / solar power (Vue only)
                # message example:
                # 70 01 F5 CE 43 86 58 E2
                """When the raw values are divided by 300 the voltage comes
                in the range of 2.8-3.3 V measured by the machine readable
                format
                """
                solar_power_raw = ((pkt[3] << 2) + (pkt[4] >> 6)) & 0x3FF
                if solar_power_raw != 0x3FF:
                    data['solar_power'] = solar_power_raw / 300.0
                    dbg_parse(2, "solar_power_raw=0x%03x solar_power=%s"
                              % (solar_power_raw, data['solar_power']))
            elif message_type == 8:
                # outside temperature
                # message examples:
                # 80 00 00 33 8D 00 25 11 (digital temp)

                # 81 00 00 59 45 00 A3 E6 (analog temp)
                # 81 00 DB FF C3 00 AB F8 (no sensor)
                temp_raw = (pkt[3] << 4) + (pkt[4] >> 4)  # 12-bits temp value
                if temp_raw != 0xFFC:
                    if pkt[4] & 0x8:
                        # digital temp sensor
                        temp_f = temp_raw / 10.0
                        temp_c = weewx.wxformulas.FtoC(temp_f) # C
                        dbg_parse(2, "digital temp_raw=0x%03x temp_f=%s temp_c=%s"
                                  % (temp_raw, temp_f, temp_c))
                    else:
                        # analog sensor (thermistor)
                        temp_raw /= 4  # 10-bits temp value
                        temp_c = calculate_thermistor_temp(temp_raw)
                        dbg_parse(2, "thermistor temp_raw=%s temp_c=%s"
                                  % (temp_raw, temp_c))
                    if data['channel'] == self.channels['temp_hum_1']:
                        data['temp_1'] = temp_c
                    elif data['channel'] == self.channels['temp_hum_2']:
                        data['temp_2'] = temp_c
                    else:
                        data['temperature'] = temp_c
            elif message_type == 9:
                # 10-min average wind gust
                # message examples:
                # 91 00 DB 00 03 0E 89 85
                # 90 00 00 00 05 00 31 51 (no sensor)
                gust_raw = pkt[3]  # mph
                gust_index_raw = pkt[5] >> 4
                if not(gust_raw == 0 and gust_index_raw == 0):
                    dbg_parse(2, "W10=%s gust_index_raw=%s" %
                              (gust_raw, gust_index_raw))
                    # don't store the 10-min gust data because there is no
                    # field for it reserved in the standard wview schema
            elif message_type == 0xA:
                # outside humidity
                # message examples:
                # A0 00 00 C9 3D 00 2A 87 (digital sensor, variant a)
                # A0 01 3A 80 3B 00 ED 0E (digital sensor, variant b)
                # A0 01 41 7F 39 00 18 65 (digital sensor, variant c)
                # A0 00 00 22 85 00 ED E3 (analog sensor)
                # A1 00 DB 00 03 00 47 C7 (no sensor)
                humidity_raw = ((pkt[4] >> 4) << 8) + pkt[3]
                if humidity_raw != 0:
                    if pkt[4] & 0x08 == 0x8:
                        # digital sensor
                        humidity = humidity_raw / 10.0
                    else:
                        # analog sensor (pkt[4] & 0x0f == 0x5)
                        humidity = humidity_raw * -0.301 + 710.23
                    if data['channel'] == self.channels['temp_hum_1']:
                        data['humid_1'] = humidity
                    elif data['channel'] == self.channels['temp_hum_2']:
                        data['humid_2'] = humidity
                    elif data['channel'] == self.channels['anemometer']:
                        loginf("Warning: humidity sensor of Anemometer Transmitter Kit not in sensor map: %s" % humidity)
                    else:
                        data['humidity'] = humidity
                    dbg_parse(2, "humidity_raw=0x%03x value=%s" %
                              (humidity_raw, humidity))
                    # modification by Luc Heijst
                    if self._log_humidity_raw:
                        # we don't know which bits are used by the old humidity sensor
                        # so we log the full 16 bit code.
                        humidity_raw_full = (pkt[4] << 8) + pkt[3]
                        if self.last_hum is not None and humidity_raw_full != self.last_hum:
                            loginf("rtldavis-luc: humidity_raw= %04x" % humidity_raw_full)
                        self.last_hum = humidity_raw_full
                    # end modification by Luc
            elif message_type == 0xC:
                # unknown message
                # message example:
                # C1 04 D0 00 01 00 E9 A4
                # As we have seen after one day of received data
                # pkt[3] and pkt[5] are always zero;
                # pckt[4] has values 0-3 (ATK) or 5 (temp/hum)
                dbg_parse(3, "unknown pkt[3]=0x%02x pkt[4]=0x%02x pkt[5]=0x%02x" %
                          (pkt[3], pkt[4], pkt[5]))
            elif message_type == 0xE:
                # rain
                # message examples:
                # E0 00 00 05 05 00 9F 3D
                # E1 00 DB 80 03 00 16 8D (no sensor)
                rain_count_raw = pkt[3]
                """We have seen rain counters wrap around at 127 and
                others wrap around at 255.  When we filter the highest
                bit, both counter types will wrap at 127.
                """
                if rain_count_raw != 0x80:
                    rain_count = rain_count_raw & 0x7F  # skip high bit
                    data['rain_count'] = rain_count
                    dbg_parse(2, "rain_count_raw=0x%02x value=%s" %
                              (rain_count_raw, rain_count))
            else:
                # unknown message type
                logerr("unknown message type 0x%01x" % message_type)

        elif data['channel'] == self.channels['leaf_soil']:
            # leaf and soil station
            data['bat_leaf_soil'] = battery_low
            data_type = pkt[0] >> 4
            if data_type == 0xF:
                data_subtype = pkt[1] & 0x3
                sensor_num = ((pkt[1] & 0xe0) >> 5) + 1
                temp_c = DEFAULT_SOIL_TEMP
                temp_raw = ((pkt[3] << 2) + (pkt[5] >> 6)) & 0x3FF
                potential_raw = ((pkt[2] << 2) + (pkt[4] >> 6)) & 0x3FF

                if data_subtype == 1:
                    # soil moisture
                    # message examples:
                    # F2 09 1A 55 C0 00 62 E6
                    # F2 29 FF FF C0 C0 F1 EC (no sensor)
                    if pkt[3] != 0xFF:
                        # soil temperature
                        temp_c = calculate_thermistor_temp(temp_raw)
                        data['soil_temp_%s' % sensor_num] = temp_c
                        dbg_parse(2, "soil_temp_%s=%s 0x%03x" %
                                  (sensor_num, temp_c, temp_raw))
                    if pkt[2] != 0xFF:
                        # soil moisture potential
                        # Lookup soil moisture potential in SM_MAP
                        norm_fact = 0.009  # Normalize potential_raw
                        soil_moisture = lookup_potential(
                            "soil_moisture", norm_fact,
                            potential_raw, temp_c, SM_MAP)
                        data['soil_moisture_%s' % sensor_num] = soil_moisture
                        dbg_parse(2, "soil_moisture_%s=%s 0x%03x" %
                                  (sensor_num, soil_moisture, potential_raw))
                elif data_subtype == 2:
                    # leaf wetness
                    # message examples:
                    # F2 0A D4 55 80 00 90 06
                    # F2 2A 00 FF 40 C0 4F 05 (no sensor)
                    if pkt[3] != 0xFF:
                        # leaf temperature
                        temp_c = calculate_thermistor_temp(temp_raw)
                        data['leaf_temp_%s' % sensor_num] = temp_c
                        dbg_parse(2, "leaf_temp_%s=%s 0x%03x" %
                                  (sensor_num, temp_c, temp_raw))
                    if pkt[2] != 0:
                        # leaf wetness potential
                        # Lookup leaf wetness potential in LW_MAP
                        norm_fact = 0.0  # Do not normalize potential_raw
                        leaf_wetness = lookup_potential(
                            "leaf_wetness", norm_fact,
                            potential_raw, temp_c, LW_MAP)
                        data['leaf_wetness_%s' % sensor_num] = leaf_wetness
                        dbg_parse(2, "leaf_wetness_%s=%s 0x%03x" %
                                  (sensor_num, leaf_wetness, potential_raw))
                else:
                    logerr("unknown subtype '%s' in '%s'" % (data_subtype, temp_raw))

        else:
            logerr("unknown station with channel: %s, raw message: %s" %
                   (data['channel'], raw))
        return data

    @staticmethod
    def setup_units_rtld_schema():
        obs_group_dict['extraTemp1']        = 'group_percent'
        obs_group_dict['extraTemp2']        = 'group_percent'
        obs_group_dict['extraTemp3']        = 'group_percent'
        obs_group_dict['leafTemp2']         = 'group_percent'
        obs_group_dict['consBatteryVoltage'] = 'group_frequency'
        obs_group_dict['hail']              = 'group_frequency'
        obs_group_dict['hailRate']          = 'group_frequency'
        obs_group_dict['heatingTemp']       = 'group_frequency'
        obs_group_dict['heatingVoltage']    = 'group_frequency'


############################## Conf Editor ############################## 

if __name__ == '__main__':
    import optparse

    import weewx
    import weeutil.logger

    weewx.debug = 0

    weeutil.logger.setup('rtldavis', {})

    usage = """%prog [--debug] [--help] [--version]
        [--action=(show-packets] [--cmd=RTL_CMD] 
        [--path=PATH] [--ld_library_path=LD_LIBRARY_PATH]

Actions:
  show-packets: display each packet (default)

"""

    parser = optparse.OptionParser(usage=usage)
    parser.add_option('--version', dest='version', action='store_true',
                      help='display driver version')
    parser.add_option('--debug', dest='debug', action='store_true',
                      help='display diagnostic information while running')
    parser.add_option('--cmd', dest='cmd', default=DEFAULT_CMD,
                      help='rtldavis command with options')
    parser.add_option('--path', dest='path',
                      help='value for PATH')
    parser.add_option('--ld_library_path', dest='ld_library_path',
                      help='value for LD_LIBRARY_PATH')
    parser.add_option('--action', dest='action', default='show-packets',
                      help='actions include show-packets')

    (options, args) = parser.parse_args()

    if options.version:
        print("sdr driver version %s" % DRIVER_VERSION)
        exit(1)

    if options.debug:
        weewx.debug = 1

    if options.action == 'show-packets':
        # display output and parsed/unparsed packets
        mgr = ProcManager()
        mgr.startup(options.cmd, path=options.path,
                    ld_library_path=options.ld_library_path)
        while mgr.running():
            for lines in mgr.get_stderr():
                payload = lines[0].strip()
                if payload:
                    print(payload)
                lines.pop(0)
            for lines in mgr.get_stdout():
                err = lines[0].strip()
                if err:
                    print(err)
                lines.pop(0)
