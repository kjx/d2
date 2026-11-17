#!/bin/bash
. ~/.profile
shopt -s expand_aliases


PREFIX=$(date +%b%d)
for i in $*
  do echo; echo; echo ==========
     echo errs $i $i $i;
     date;
     echo ==========

     ERRFILE=$(ls -t logs/*\=$i.txt | head -1)
     echo "grep Err $ERRFILE"
     echo -n "time: "
     cat logs/T$(basename $ERRFILE .txt).time
     grep Err $ERRFILE  | ncn | cut -c -90 | sort -u | sort -t\(   -k2n

    
     echo done perfile $i $i $i; date;
     echo; echo;
done;  
