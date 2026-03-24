                      //Graphing.dfy - outputs graphviz scripts
//
//try this:
//time lately run Main.dfy c OF "" "{ rank=min; 3; } {rank=same; 2;} {rank=same; 1;} {rank=max; 0; 00;} { rank=same; i; j}  rankdir="TB"; margin=0; "  --allow-war
//then thid
//csplit DUMP.txt %//STARTGRAPH%; mv xx00  test.gv ; dpdf test.gv ; open test.gv.pdf
//

include "Library.dfy"
include "Klon.dfy"


datatype GraphOptions = GraphOptions (
  graph : string,
  lines : string,
  nodes : string,
  extra : string
)
{
  predicate lineOpt(c : char)   { (lines == "") || (c in lines) }
  predicate nodeOpt(n : string) { (nodes == "") || (n == "") || (n[0] in nodes) }
}


method getGraphOptions(args : seq<string>) returns (gops : GraphOptions)
{
  var ALLLINEOPTS := "OoBbFMR";
  var aa := args;
  if (|args| < 2)
     { print "got no arguments!!\n";
       print "going with dahlia 9 _" + ALLLINEOPTS + " _c _extra...\n";
       aa := ["dahlia", "9"];
       }

   var graph : string := "";
   var lines : string := "";
   var nodes : string := "";
   var extra : string := "";

   if (|aa| > 1) { graph := aa[1]; }
   if (|aa| > 2) { lines := aa[2]; }
   if (|aa| > 3) { nodes := aa[3]; }
   if (|aa| > 4) { extra := aa[4]; }

   print "graph = ", graph, "\n";
   print "lines = ", lines, "\n";
   print "nodes = ", nodes, "\n";
   print "extra = ", extra, "\n";

   gops := GraphOptions(graph, lines, nodes, extra);

   print "ALLLINEOPTS:\n";
   for x := 0 to |ALLLINEOPTS| {
       var opt : char := ALLLINEOPTS[x];
       print opt, " ", gops.lineOpt(opt), "\n";
   }

}











const owner_attrs := "[arrowhead=diamond,penwidth=3,weight=10,layer=owner]"

const nowner_attrs := "[arrowhead=none,penwidth=0,weight=10,layer=bg]"

const bound_attrs := "[arrowhead=diamond,penwidth=3,weight=10,layer=bound,color=pink,constraint=false]"
const AMFO_attrs := "[penwidth=0.1,layer=amfo,weight=1,arrowhead=invempty,constraint=false]"
const AMFB_attrs := "[penwidth=0.1,layer=amfo,weight=1,arrowhead=invempty,constraint=false, color=pink]"
const mapping_attrs := "[penwidth=2,layer=mapping,weight=0,color=blue,constraint=false]"

const refOKOattrs := "[penwidth=2,layer=mapping,weight=0,color=green,constraint=false]"  //both
const refOO_attrs := "[penwidth=2,layer=mapping,weight=0,color=orange,constraint=false,style=dashed]" //  label=O
const refOK_attrs := "[penwidth=2,layer=mapping,weight=0,color=purple ,constraint=false]"
const refNK_attrs := "[penwidth=2,layer=mapping,weight=0,color=red,constraint=false,style=dashed]"  //label=\"X\", fontname=Helvetica,fontsize=30,fontcolor=red,labelOverlay=\"true\"


const field_attrs := "[penwidth=1,layer=fields,weight=0.5,fontsize=9,arrowhead=vee]"
const nfield_attrs := "[penwidth=2,layer=fields,weight=0.5,fontsize=9,arrowhead=vee,color=red,style=dotted]"

method {:verify false}  graphobjectset(s : set<Object>, m : Klon, gops : GraphOptions)
{
  var o := s;

  while o != {}
    decreases o
  {
    var y: Object;
    y :| y in o;
    graphobject(y, gops);
//    print "- - - - - - - -\n";
    o := o - {y};
  }

}






method {:verify false} graphobject(o : Object, gops : GraphOptions)
{
  //ownership

  print "\n//object ", o.nick, "\n";
  if ((|o.nick| > 6)) { print "// ", |o.nick|, " > 6 ",o.nick[0..5],"\n"; }


  if ((|o.nick| > 6) && (o.nick[0..6] == "clone_"))  {
    print o.nick,"[color=\"blue\",fontcolor=\"blue\"]\n";
  }


  var oo := o.owner;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

  if gops.lineOpt('O') { print o.nick, " -> ", y.nick, " ", owner_attrs, "\n"; }
     else { print o.nick, " -> ", y.nick, " ", nowner_attrs, "\n"; }


    oo := oo - {y};
  }

  oo := o.AMFO;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

   if gops.lineOpt('o') {
       if (o != y) { print o.nick, " -> ", y.nick, " ", AMFO_attrs, "\n"; }
   }

    oo := oo - {y};
  }



/////////////////////////
///same as above for bounds.  need to do better than cut & paste  (why?)

   oo := o.bound;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

 if gops.lineOpt('B')
      {  print o.nick, " -> ", y.nick, " ", bound_attrs, "\n"; }

    oo := oo - {y};
  }

  oo := o.AMFB;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

//   if ((o != y) && (y !in o.AMFB))
    if gops.lineOpt('b') { print o.nick, " -> ", y.nick, " ", AMFB_attrs, "\n"; }

    oo := oo - {y};
  }

////////////////////////////

 if  (not(gops.lineOpt('F'))) { return; }

  var fs := o.fields.Keys;

  while fs != {}
    decreases fs
  {
    var f: string;
    f :| f in fs;

    var nf := o.nick;
    var nt := o.fields[f].nick;
    if (gops.nodeOpt(nf) || gops.nodeOpt(nt)) {
            print nf, " -> ", nt,     " ",
                (if (refOK(o,o.fields[f])) then (field_attrs) else (nfield_attrs));
            print "[label=\"", f, "\"]";
            if (f == "contents") { print "[weight=2.5]"; }
            if (f == "next") { print "[weight=5]"; }
            print "\n";
        }
    fs := fs - {f};
  }

}






method graphmapping(m : vmap<Object,Object>, gops : GraphOptions)
  modifies {}
  ensures unchanged(m.Keys,m.Values)
  ensures forall k <- m.Keys   :: unchanged(k)
  ensures forall v <- m.Values :: unchanged(v)
{

  print "\n\n//mapping\n";
  var t := m;
  while t != map[]
    decreases t
  {
    var y: Object;
    y :| y in t.Keys;
    print y.nick, " -> ", t[y].nick, " ", mapping_attrs, "\n";
    t := t - {y};
  }
}



method graphrefs(s : seq<Object>, gops : GraphOptions)
  modifies {}
{
  print "\n\n//refs\n";

    for f := 0 to |s| {
      for t := 0 to |s| {
  //       var attrs := if (refOK(s[f],s[t])) then refOK_attrs else refNK_attrs;

          var attrs := refNK_attrs; //not permitted reference - red, X
          if  (refOK(s[f],s[t])) { attrs := refOK_attrs; } //reference permitted w/ boundary - but not without (purple,. shouldn't happen)
          if  (r_efOO(s[f],s[t])) { attrs := refOO_attrs; } //reference without w/ boundary - but NOT permitted with bounday - ORANGE, "O"
          if ((refOK(s[f],s[t])) && (r_efOO(s[f],s[t]))) { attrs := refOKOattrs; } //OK either way - GREEN


//      if ((s[f].nick == "c") || (s[t].nick == "c"))
//    if (attrs != refNK_attrs) && (s[f].nick in {"a", "b", "c", "d", "e"})
//    if (s[f].nick in {"c", "d", "e"})

     if (gops.nodeOpt(s[f].nick) || gops.nodeOpt(s[t].nick))
        {
        print s[f].nick, " -> ", s[t].nick, " ", attrs, "\n";
       }
    }
   }
}
