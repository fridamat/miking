#!/bin/bash
# A simple script
perf stat -r 1 build/boot tytest test/master-thesis/combo_test1.mi
perf stat -r 1 build/boot tytest test/master-thesis/push_last_pop.mi
