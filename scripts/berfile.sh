#!/bin/bash
. ~/.profile
PREFIX=$(date +%b%d)
for i in $*; do echo; echo; echo ==========;  echo $i $i $i; date; time nightly verify $i --verification-time-limit=10 --isolate-assertions --cores 6 --progress=batch; date; echo; done;  
