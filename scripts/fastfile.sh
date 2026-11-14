#!/bin/bash
. ~/.profile
shopt -s expand_aliases

if  [[ $(alias nightly) =~ alias\ nightly=\'(.*)\' ]] 
then
    NIGHTLY=${BASH_REMATCH[1]}
else
      echo "can't get alias"
      exit
fi

PREFIX=$(date +%b%d)
for i in $*
  do echo; echo; echo ==========;
     echo NONICE fastfile $i $i $i;
     date;
     /usr/bin/time -ho logs/T$PREFIX=$i.time $NIGHTLY verify $i $SP $VV --verification-time-limit=15 | tee logs/$PREFIX=$i.txt;
     echo NONICE perfile $i $i $i; date;
     echo; echo;
done;  
