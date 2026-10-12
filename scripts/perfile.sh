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
     echo perfile $i $i $i;
     date;
     /usr/bin/time -ho logs/T$PREFIX=$i.time nice $NIGHTLY verify $i $SP $VV | tee logs/$PREFIX=$i.txt;
     echo done perfile $i $i $i; date;
     echo; echo;
done;  
