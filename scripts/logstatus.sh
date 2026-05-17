#!/bin/bash
. ~/.profile
FILES=$(ls -t1 logs/*txt | head -40)
grep fini $FILES | grep -v "0 errors" | sort -rnk 8 
grep fini $FILES | grep -i "time out" | sort -rnk 10 

