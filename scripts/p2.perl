# do this
# grep -H "^include " $(cat FILES) glamis.dfy greymalkin.dfy | tr -d - | perl p2.perl > arch.gv
# then this
# dot -Tpdf arch.gv  > arch.pdf

print "strict digraph {\n";
while (<>) {  
      s/([\w-\/]*)\.dfy\:include.*\"([\w-\/]*).dfy\"/ $1 -> $2/;
      print $_;
      }
print "}\n";
