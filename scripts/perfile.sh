#!/bin/bash
. ~/.profile
shopt -s expand_aliases

PREFIX=$(date +%b%d)
for i in $*; do echo; echo; echo ==========;  echo perfile $i $i $i; date; time nnightly verify $i --verification-time-limit=10 --isolate-assertions --cores 6 | tee logs/$PREFIX=$i.txt; echo done perfile $i $i $i; date; echo; done;  
