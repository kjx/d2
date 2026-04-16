PREFIX=${1:-$(date +%b%d)}
for i in [A-W]*.dfy; do echo; echo; echo ==========;  echo $i $i $i; date; time nlately verify $i --verification-time-limit=10 --isolate-assertions --cores 8 | tee logs/$PREFIX-$i.txt; date; echo; done;  
