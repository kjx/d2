#!/bin/bash
. ~/.profile
PREFIX=${1:-$(date +%b%d)}
for i in Xlone_Set_Field.dfy Xlone_Via_Map.dfy Xlone_All_Owners.dfy  Xlone_Clone_Clone.dfy Xlone_Field_Map.dfy   Xlone_All_Fields.dfy
  do echo ====================; echo $i;  echo $i;  echo $i; date; time nightly verify $i --verification-time-limit=10 --isolate-assertions  --cores=6 --progress=batch | tee logs/$PREFIX-$i.txt; date;  done; 
