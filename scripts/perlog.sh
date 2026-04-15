echo
echo
echo 
date
echo
for i in *.dfy
do
   echo "=========================="
   echo $i
   grep fini $(ls -1t logs/*-$i.txt)
done
date
