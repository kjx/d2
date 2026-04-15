echo
echo
echo 
date
echo
for i in Xlone_Set_Field Xlone_Via_Map Xlone_All_Owners  Xlone_Clone_Clone Xlone_Field_Map   Xlone_All_Fields
do
   echo "=========================="
   echo $i
   grep fini $(ls -1t logs/*$i.dfy.txt)
done
date
