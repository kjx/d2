PREFIX=${1:-$(date +%b%d)}
for i in Xlone_Set_Field Xlone_Via_Map Xlone_All_Owners  Xlone_Clone_Clone Xlone_Field_Map   Xlone_All_Fields
  do echo ====================; echo $i;  echo $i;  echo $i; date; time lately verify Xlone.dfy --verification-time-limit=10 --isolate-assertions  --cores=8  --filter-symbol=$i  --progress=Symbol | tee logs/$PREFIX-$i.dfy.txt; date;  done; 
