#!/bin/bash
# A simple script
perf stat -r 100 build/boot tytest test/master-thesis/rep_pop.mi > res1.txt
perf stat -r 100 build/boot tytest test/master-thesis/rep_push_last.mi > res2.txt
perf stat -r 100 build/boot tytest test/master-thesis/sequence_tasks.mi > res3.txt
