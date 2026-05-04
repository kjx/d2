# do this
# grep -H "^include " *.dfy | perl scripts/tord.perl > tsort.txt
# then this
# dot -Tpdf arch.gv  > arch.pdf

while (<>) {  
    s/([\w-\/]*)\.dfy\:include.*\"([\w-\/]*).dfy\"/ $1 $2/;
    s?(.*)//.*?$1?;
      print $_;
      }
