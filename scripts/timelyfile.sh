#!/bin/bash
. ~/.profile
shopt -s expand_aliases

if  [[ $(alias lately) =~ alias\ lately=\'(.*)\' ]] 
then
    LATELY=${BASH_REMATCH[1]}
else
      echo "can't get alias"
      exit
fi

PREFIX=$(date +%b%d)
for i in $*
  do echo; echo; echo ==========;
     echo timelyfile $i $i $i;
     date;
     /usr/bin/time -ho logs/T$PREFIX-$i.time nice $LATELY verify $i --verification-time-limit=10 --isolate-assertions --cores 6 | tee logs/$PREFIX-$i.txt;
     echo done timelyfile $i $i $i; date;
     echo; echo;
done;  
