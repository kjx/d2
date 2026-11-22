#!/bin/bash
echo 
date
echo
for i in *.dfy
do
    #printf "%30s: " $i
    LOG=$(ls -1t logs/*-$i.txt 2>/dev/null | head -1)
    if test -f ./$LOG
    then
	if grep -q fini ./$LOG
	then
	    RES=$(grep fini ./$LOG | cut -c 37-) # | cut -w -f  6-)
	    ERR=none
	    if (echo $RES | grep -qv "0 errors") then ERR=errors; fi
	    if (echo $RES | grep -q "time") then ERR=errors; fi
	    #echo RES $ERR $RES
           if test $ERR = none
	   then
	       echo -n
		#echo GREP OK $RES
	   else
	       #echo FUCK $i $RES
               printf "%30s: %s\n" "$i" "$RES"
           fi
	    #grep fini ./$LOG | cut -w -f 6-     
	    #grep fini ./$LOG | cut -c 37-
	else
	    printf "%30s: %s\n" "$i"  " *** crashed *** "
	    #echo " *** crashed *** "
	fi
    else 	    printf "%30s: %s\n" "$i" " -"  #echo " - "
    fi
done
date
