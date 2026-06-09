shopt -s expand_aliases
. ~/.profile

for i in  *.dfy; do echo $i; time lately resolve $i | grep Error; echo $i; echo ============================================================== ; done 
