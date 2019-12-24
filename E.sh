#!/bin/bash
# A simple script
perf stat -r 100 build/boot tytest test/master-thesis/rep_last.mi > res1.txt
perf stat -r 100 build/boot tytest test/master-thesis/rep_length.mi > res2.txt
perf stat -r 100 build/boot tytest test/master-thesis/rep_nth.mi > res3.txt
