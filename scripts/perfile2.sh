PREFIX=${1:-$(date +%b%d)}
shift;
for i in $*; do echo; echo; echo ==========;  echo $i $i $i; date; time nlately verify $i --verification-time-limit=10 --isolate-assertions --cores 6 | tee logs/$PREFIX-$i.txt; date; echo; done;  
