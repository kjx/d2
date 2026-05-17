#!/bin/bash
. ~/.profile
PREFIX=$(date +%b%d)
for i in $*; do echo; echo; echo ==========;  echo $i $i $i; date; time nlately verify $i --verification-time-limit=10 --isolate-assertions --cores 6 | tee logs/$PREFIX-$i.txt; echo done $i $i $i; date; echo; done;  
