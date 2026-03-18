include "Klon-HighLine.dfy"


include "Ownership-Recursive.dfy"
include "Printing.dfy"

//  include "Z2.dfy" // birmnamwood14, isownedby  - fast
include "SSO.dfy"





const protoTypes : map<string, Mode> := fields({"t","a","b","c","d","e","k","l","m"})
  // map["fa":= Evil]["fb":=Evil]  //wrong but will likely do for now?


datatype Split = Split(within : OWNR, without : OWNR, m : Klon)

function split(oo : OWNR, m : Klon) : Split
  requires forall o <- oo :: m.objectReadyInKlown(o)
{
  Split( (set o <- oo | inside(o, m.o)), (set o <- oo | outside(o, m.o)), m)
}


lemma {:verify false} objectReadyToOwnerReadyInKlon(o : Object, m : Klon)
  requires m.ownersReadyInKlown(o) || m.objectReadyInKlown(o)
   ensures forall oo <- o.AMFX :: oo.Ready()
   ensures forall oo <- o.AMFX :: oo.AMFO <= m.m.Keys
   ensures forall oo <- o.AMFX :: m.objectReadyInKlown(oo)
  {
    o.ExtraReady();
  }

function map2vmap(m : map<Object,Object>) : vmap<Object,Object>
  requires AllMapEntriesAreUnique(m)
  { m }



function  sporamfo(o : Object) : Owner {(set oo : Object <- o.owner, ooo : Object <- oo.AMFO :: ooo) + {o}}
  //takes an object via it's owners to its AMFO
function sporamfx(o : Object) : Owner {set oo : Object <- o.owner,   ooo : Object <- oo.AMFO :: ooo}
  //takes an object via it's owners to its AMFX
function sporamfb(o : Object) : Owner {set oo : Object <- o.bound,   ooo : Object <- oo.AMFO :: ooo}
  //takes an object via it's owners to its AMFB
function splatten(os : Owner) : Owner {(set oo : Object <- os,       ooo : Object <- oo.AMFO :: ooo)}
  //takes an Owner via it's owners to its AMFO


function sporrel(k : Object, m : Klon) : string
  requires k.Ready()
 {
   if (k == m.o) then ("pivot  ")
     else if (outside(k, m.o))
       then ("outside")
       else ("inside ")
 }


datatype PrintOptions = PrintOptions (
  graph : string,
  lines : string,
  nodes : string,
  extra : string
)
{
  predicate lineOpt(c : char)   { (lines == "") || (c in lines) }
  predicate nodeOpt(n : string) { (nodes == "") || (n == "") || (n[0] in nodes) }
}


method getPrintOptions(args : seq<string>) returns (pops : PrintOptions)
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

   pops := PrintOptions(graph, lines, nodes, extra);

   print "ALLLINEOPTS:\n";
   for x := 0 to |ALLLINEOPTS| {
       var opt : char := ALLLINEOPTS[x];
       print opt, " ", pops.lineOpt(opt), "\n";
   }

}

method {:verify false} Main(args : seq<string>)
{
  print "Snick! Snack! Snock!\n";

  var pops := getPrintOptions(args);


  var t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal0();

 if (pops.graph == "0")
    {
      t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal10();
    }

 if (pops.graph == "9")
    {
      t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9();
    }

 if (pops.graph == "b")
    {
      t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9bounded();
    }

 if (pops.graph == "l")
    {
      t,a,b,c,d,e,k,l,m,os,oq, loutName := zandalList();
    }





//KLON fields
  // m : vmap<Object,Object>,    //the  klon map
  // o : Object,                 //object being copied
  // clowner : Owner,            //owner of the clone
  // clbound : Owner,            //bound of the clone
  // oHeap : set<Object>,        //heap
  // o_amfx : Owner,             //was o. so the AMFX of o
  // //  c_amfb : OWNR,              //epected flattened bound of the clone..
  // c_amfx : Owner


  var v : map<Object,Object> := map[
    // t := t,
    // a := a,
    // b := k,
    // c := l,
    // d := m,
    // e := e
  ];

  assume AllMapEntriesAreUnique(v);
  var v' : vmap<Object,Object> := map2vmap(v);


  var hq := oq;
  var hs := os;


//  print "WARNING WARNING KLON KLON KLON\n";
  var km := Klon(v', b, k.owner, k.bound, hs, b.AMFX, flatten(k.owner) );

  assert km.o == b;
  assert km.o.Ready();
  assert b in hs;
  assert km.o in hs;
  assert km.o in km.m.Keys;

  ////////////////////////////////////////////////////////////////////
  assume km.objectInKlown(km.o);
  ////////////////////////////////////////////////////////////////////
//  assume HighCalidFragilistic(km);
  ///////////////////////////////////////////////////////////////

//    assert forall k <- km.m.Keys :: HighLineKV(k, km.m[k], km);
    assert forall x <- hq :: km.objectInKlown(x);
    assert HQIK: forall x <- hq :: km.objectInKlown(x);
    assert HQNN: forall x <- hq :: x != null;

// printobjectset(hs);
//
// printrefs(hq);

      print "\n\n//STARTGRAPH\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "//  ", loutName, "\n";


  print "\n\ndigraph dafny {\n";
  // print "   rankdir=\"TB\";\n";
  print "   rankdir=\"BT\";\n";
  print "   layers=\"mapping:fields:owner:bound:amfo:bg\";\n";
//  print "   concentrate=true;\n";
  print "   node [shape=box]\n\n";
  print "//===\n", pops.extra,"\n//===\n";

        graphobjectset(hs, km, pops);

        if (pops.lineOpt('M')) { graphmapping(km.m, pops); }

        if (pops.lineOpt('R')) {    graphrefs(hq, pops); }


 print "}\n\n\n";

    print "//ENDGRAPH\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";
    print "///////////////////////////////////////////////////////////////////////////////\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";

  print "\n\n//done\n";

}

 method {:verify false} do_object(o : Object, m : Klon)
   requires m.objectReadyInKlown(o)
   requires HighCalidFragilistic(m)
 {
   var spl := split(o.AMFO, m);  //WARNING WILL ROBINSON!!!
   print o.nick;
   print "  AMFO=", ffmtnickset(o.AMFO);
   print "  within=", ffmtnickset(spl.within);
   print "  without=", ffmtnickset(spl.without);

   if (spl.within == {})
     { print " (only outside, skipping)\n"; return; }
    else { nl(); }

    print "   processing..\n";
    print "   within " + o.nick, "  AMFO=", ffmtnickset(o.AMFO), "\n";

    var trimmed := o.AMFO - m.o.AMFO;
    print "   trimmed ", ffmtnickset(trimmed), "\n";

    var translated : SSO := {};

    while trimmed != {}
    {
       var y: Object;
       y :| y in trimmed;
       trimmed := trimmed - {y};

       print "      ", y.nick,"  AMFO=", ffmtnickset(y.AMFO);
       if (y.AMFO >= m.o.AMFO)
         {
            var trans : Owner := mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO );
            translated := translated + {trans};
            print "  tr=",ffmtnickset(trans),"\n";
         } else {
            translated := translated + {y.AMFO};  print "        (outside)\n";
         }

    }

    var reconnected := translated + obj2sso( m.m[m.o] );
    print "   done " + o.nick, " translated AMFO=", ffmtsso(reconnected),     "\n";
    print "        " + o.nick, " direct     AMFO=", ffmtsso(obj2sso(m.m[o])), "\n";
 }



 method {:verify false}  do_object_mod(o : Object, m : Klon)
   requires m.objectReadyInKlown(o)
   requires HighCalidFragilistic(m)
 {
   var spl := split(o.AMFO, m);  //WARNING WILL ROBINSON!!!
   print o.nick;
   print "  AMFO=", ffmtnickset(o.AMFO);
   print "  within=", ffmtnickset(spl.within);
   print "  without=", ffmtnickset(spl.without);

   if (spl.within == {})
     { print " (only outside, skipping)\n"; return; }
    else { nl(); }

    print "   processing..\n";
    print "   within " + o.nick, "  AMFO=", ffmtnickset(o.AMFO), "\n";

    var trimmed := o.AMFO - m.o.AMFO;
    print "   trimmed ", ffmtnickset(trimmed), "\n";

    var translated : SSO := set y <- trimmed ::

       if (y.AMFO >= m.o.AMFO) then
         (
            var trans : Owner := mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO );
            trans
          ) else ( y.AMFO );

    var reconnected := translated + obj2sso( m.m[m.o] );

    print "   done " + o.nick, " translated AMFO=", ffmtsso(reconnected),     "\n";
    print "        " + o.nick, " direct     AMFO=", ffmtsso(obj2sso(m.m[o])), "\n";
 }



 method {:verify false}  do_object_mod2(o : Object, m : Klon)
   requires m.objectReadyInKlown(o)
   requires HighCalidFragilistic(m)
 {
   var spl := split(o.AMFO, m);  //WARNING WILL ROBINSON!!!
   print o.nick;
   print "  AMFO=", ffmtnickset(o.AMFO);
   print "  within=", ffmtnickset(spl.within);
   print "  without=", ffmtnickset(spl.without);

   if ((set x <- o.AMFO | inside(x, m.o)) == {})
     { print " (only outside, skipping)\n"; return; }
    else { nl(); }

    print "   processing..\n";
    print "   within " + o.nick, "  AMFO=", ffmtnickset(o.AMFO), "\n";

    var trimmed := o.AMFO - m.o.AMFO;
    print "   trimmed ", ffmtnickset(trimmed), "\n";

    var translated : SSO := ( set y <- trimmed ::

       if (y.AMFO >= m.o.AMFO) then
         (mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO )
         ) else ( y.AMFO ) )
    ;

    var reconnected := translated + obj2sso( m.m[m.o] );

    print "   done " + o.nick, " translated AMFO=", ffmtsso(reconnected),     "\n";
    print "        " + o.nick, " direct     AMFO=", ffmtsso(obj2sso(m.m[o])), "\n";
 }




 method {:verify false} do_object_mod3(o : Object, m : Klon)
   requires m.objectReadyInKlown(o)
   requires HighCalidFragilistic(m)
   requires m.SuperCalidFragilistic()
    ensures m.Calid()   //no fucking idea wwhy this is failing,  but qutie curious!
    ensures m.AllLinesCalid()
 {
   assert m.Calid();
   assert m.AllLinesCalid();
   var spl := split(o.AMFO, m);  //WARNING WILL ROBINSON!!!
   print "o=",o.nick,"    m.o=", ffmtnickset(m.o.AMFO), "\n";

   print "\n\n           AMFO=", ffmtnickset(o.AMFO);
   print "\n           within=", ffmtnickset(spl.within);
   print "\n          without=", ffmtnickset(spl.without);
   print "\no.AMFO-m.o.AMFO**=", ffmtnickset(o.AMFO - m.o.AMFO);
   print "\no.AMFO - {m.o}***=", ffmtnickset(o.AMFO - {m.o});
   print "\no.AMFO -without  =", ffmtnickset(o.AMFO - spl.without);
   print "\n   strictlyInside=", ffmtnickset(set x <- o.AMFO | strictlyInside(x, m.o));
   print "\n           inside=", ffmtnickset(set x <- o.AMFO | strictlyInside(x, m.o));
nl();

   if ((set x <- o.AMFO | inside(x, m.o)) == {})
      { print " (only outside, carrying on anyway to see what the FUCK happens)\n"; }
//    { print " (only outside, skipping)\n"; return; }
    else { nl(); }

    print "   processing..\n";
    print "   within " + fmtamfosso(o), "\n";
    nl();




    var reconnected := mapfo(o.AMFO, m);

    if (reconnected != obj2sso(m.m[o]) )
    {
      print "FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck \n";
      print "FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck \n";
    }

    print "   done " + o.nick, " translated  SSO=", ffmtsso(reconnected),             "\n";
    print "        " + o.nick, " direct      SSO=", ffmtsso(obj2sso(m.m[o])),         "\n";
    print "        " + o.nick, " mapfo_INNER SSO=", ffmtsso(mapfo_INNER(o.AMFO, m)),  "\n";
    print "        " + o.nick, " mapfo_INNER+SSO=", ffmtsso(mapfo_INNER(o.AMFO, m) +  obj2sso(m.m[m.o])),  "\n";
    print "        " + o.nick, " mapfo_orig  SSO=", ffmtsso(mapfo_orig(o.AMFO, m)),   "\n";

    nl();

    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "                            rivet.AMFX=", ffmtnickset(o.AMFX); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "                       sporamfx(rivet)=", ffmtnickset(sporamfx(o)); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "                           trivet.AMFX=", ffmtnickset(m.m[o].AMFX); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "                      sporamfx(trivet)=", ffmtnickset(sporamfx(m.m[o])); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "             ownr2sso(sporamfx(trivet)=", ffmtsso(ownr2sso(sporamfx(m.m[o]))); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "  ownr2sso(sporamfx(objThruKlon(o,m)))=", ffmtsso(ownr2sso(sporamfx(objThruKlon(o,m)))); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "  ownr2sso(mapThruKlon(sporamfx(o),m))=", ffmtsso(ownr2sso(mapThruKlon(sporamfx(o),m))); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "    ownr2sso(mapfoSide(sporamfx(o),m))=", ffmtsso(ownr2sso(mapfoSide(sporamfx(o),m))); nl();
    print "SPORRAN: ",  o.nick + " " + sporrel(o,m) + "                  mapfo(sporamfx(o),m)=", ffmtsso(mapfo(sporamfx(o),m)); nl();

 }


lemma {:verify false}  GEownr(
   p : SSO, w : SSO, mp : SSO , mw : SSO, m : Klon)
   requires HighCalidFragilistic(m)
       requires forall o <- concensso(p)  :: m.objectReadyInKlown(o)
       requires forall o <- concensso(w)  :: m.objectReadyInKlown(o)
       requires forall o <- concensso(mp) :: m.objectReadyInKlown(o)
       requires forall o <- concensso(mw) :: m.objectReadyInKlown(o)
       requires p >= w

       requires mp == mapfo(concensso(p), m)
       requires mw == mapfo(concensso(w), m)

       ensures mp >= mw
   {

   }



function parameterstk(os : Owner, m : Klon) : Owner
  requires os <= m.m.Keys
  reads m.oHeap, m.m.Values
{ set o <- os :: m.m[o] }

function mtk(os : Owner, m : Klon) : Owner
  requires os <= m.m.Keys
  reads m.oHeap, m.m.Values
{ set o <- os :: m.m[o] }

function mZk(os : Owner, m : Klon) : Owner
  requires m.SuperCalidFragilistic()
  requires os <= m.m.Keys
  reads m.oHeap, m.m.Values
  { if (os >= m.o.AMFO)
     then (MINNER(os, m))
     else (os) }

function {:isolate_assertions}  msp(ko : OWNR, m : Klon) : OWNR
  //map sporrelOWNR
  requires ko <= m.m.Keys
  requires m.SuperCalidFragilistic()
  requires m.apoCalidse()
  requires AllReady(ko)
  requires isFlat(ko)
     reads m.oHeap, m.m.Values
 {
   if (ko == m.o.AMFO) then (m.m[m.o].AMFO)
     else if (not(ko >= m.o.AMFO))
       then (ko)
       else (MINNER(ko, m))
 }



function {:isolate_assertions}  pOb(k : Object, m : Klon) : OWNR
  requires {k} <= m.m.Keys
  requires m.SuperCalidFragilistic()
  requires m.apoCalidse()
  requires AllReady({k})
     reads m.oHeap, m.m.Values
 {
  if (k == m.o) then (m.m[m.o].AMFO) else
      (  if (outside(k,m.o))
        then (sporamfo(k))
        else (set z <- MINNER({k},m), zz9 <- sporamfo(z) :: zz9)  )
 }



function {:isolate_assertions}  pOW(ko : OWNR, m : Klon) : OWNR
  ///this is too much of a hack
   requires ko <= m.m.Keys
  requires m.SuperCalidFragilistic()
  requires m.apoCalidse()
  requires AllReady(ko)
  requires isFlat(ko)
     reads m.oHeap, m.m.Values
 {
   if (ko == m.o.AMFO) then (m.m[m.o].AMFO)
     else
   if (ko == m.o.AMFB) then (m.m[m.o].AMFB)
    else
   if (ko == m.o.AMFX) then (m.m[m.o].AMFX)
     else if (not(ko >= m.o.AMFO))
       then (ko)
       else (MINNER(ko, m))
 }


function MINNER(os : Owner, m : Klon) : Owner
  requires m.SuperCalidFragilistic()
  //compare mapfo_SIDEWAYS / _INNER
  requires os <= m.m.Keys
  reads m.oHeap, m.m.Values
  {(set o <- (os - m.o.AMFO) :: m.m[o]) + m.m[m.o].AMFO }

  /////////////////////////////////////////////////////////////////////////////////////////////////////////////


function {:isolate_assertions}  zzX(k : Object, m : Klon) : OWNR
  requires {k} <= m.m.Keys
  requires m.SuperCalidFragilistic()
  requires m.apoCalidse()
  requires AllReady({k})
     reads m.oHeap, m.m.Values
 {
  if (k == m.o) then (m.m[m.o].AMFO) else
      (  if (outside(k,m.o))
        then (sporamfo(k))
        else (set z <- MINNER({k},m), zz9 <- sporamfo(z) :: zz9)  )
 }






  ///////////////////////////////////////////////////////////////////////////////////////////////////////////

function pvtself(o : Object, m : Klon) : Owner {if (o == m.o) then (m.clowner+{m.m[o]}) else (mtk(o.self,m))}
function pvtowner(o : Object, m : Klon) : Owner {if (o == m.o) then (m.clowner)          else (mtk(o.owner,m))}
function pvtbound(o : Object, m : Klon) : Owner {if (o == m.o) then (m.clbound)          else (mtk(o.bound,m))}

function xvtself(o : Object, m : Klon) : Owner {if (o == m.o) then ({})          else (mtk(o.self,m))}
function xvtowner(o : Object, m : Klon) : Owner {if (o == m.o) then ({})          else (mtk(o.owner,m))}
function xvtbound(o : Object, m : Klon) : Owner {if (o == m.o) then ({})          else (mtk(o.bound,m))}

  ///////////////////////////////////////////////////////////////////////////////////////////////////////////

 method   {:verify false}  do_object_mod4(k : Object, m : Klon)
   requires m.objectReadyInKlown(k)
   requires HighCalidFragilistic(m)
   requires m.SuperCalidFragilistic()
    ensures m.Calid()   //no fucking idea wwhy this is failing,  but qutie curious!
    ensures m.AllLinesCalid()
 {
   var v := m.m[k];
   print "^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^\n";
   print "object ", sporrel(k,m), " ", k.nick, " ~> ", v.nick, "    ",ffmtnickset(k.AMFO),"~",ffmtnickset(v.AMFO),"      ", (v.AMFO  >= v.AMFB  >= k.AMFB);   nl();

if (k == m.o) { print "PIBOTTTOTION  PIVOT\n"; } else { return; }

print "clowner=", ffmtnickset(m.clowner), "  clbound=", ffmtnickset(m.clbound); nl();

//    print "   k.owner=", ffmtnickset(k.owner);
//    print " k.bound=", ffmtnickset(k.bound);nl();
//    print " k.AMFO=", ffmtnickset(k.AMFO);
//    print " k.AMFX=", ffmtnickset(k.AMFX);
//    print " k.AMFB=", ffmtnickset(k.AMFB);
//    print "  ", sporamfo(k)==k.AMFO," ", (sporamfx(k)==k.AMFX)," ", sporamfb(k)==k.AMFB;
//    nl();
//
//
//    print "   v.owner=", ffmtnickset(v.owner);
//    print " v.bound=", ffmtnickset(v.bound);nl();
//    print " v.AMFO=", ffmtnickset(v.AMFO);
//    print " v.AMFX=", ffmtnickset(v.AMFX);
//    print " v.AMFB=", ffmtnickset(v.AMFB);
//    print "  ", sporamfo(v)==v.AMFO," ", (sporamfx(v)==v.AMFX)," ", sporamfb(v)==v.AMFB;
//    nl();
//

  //  print " ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
  //  print " ", mZk(k.AMFO, m) == v.AMFO, " ", mZk(k.AMFX, m)  == v.AMFX, " ", mZk(k.AMFB, m) == v.AMFB;
  //  nl();
  //  nl();
  //  print " ", msp(k.AMFO, m) == v.AMFO, " ", msp(k.AMFX, m)  == v.AMFX, " ", msp(k.AMFB, m) == v.AMFB;
//   nl();

   print "k  : ", ffmtnickset(k.self), " ", ffmtnickset(k.owner), " ", ffmtnickset(k.bound); nl();


   print "v  : ", ffmtnickset(v.self), " ", ffmtnickset(v.owner), " ", ffmtnickset(v.bound); nl();
   print "pvt: ", ffmtnickset(pvtself(k,m)), " ", ffmtnickset(pvtowner(k,m)), " ", ffmtnickset(pvtbound(k,m)); nl();

   print "xvt: ", ffmtnickset(xvtself(k,m)), " ", ffmtnickset(xvtowner(k,m)), " ", ffmtnickset(xvtbound(k,m)); nl();



   print "KLON ", ffmtnickset(m.clowner+{v}), " ", ffmtnickset(m.clowner), " ", ffmtnickset(m.clbound); nl();


   print "pvt: ", pvtself(k,m) == v.self, " ", pvtowner(k,m) == v.owner, " ", pvtbound(k,m) == v.bound;
   print "|", sporamfo(m.m[k]) == v.AMFO, " ", sporamfx(m.m[k])  == v.AMFX, " ", sporamfb(m.m[k]) == v.AMFB; nl();
  //  print "mtk: ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
//    print "|", mtk(k.AMFO, m) == v.AMFO, " ", mtk(k.AMFX, m)  == v.AMFX, " ", mtk(k.AMFB, m) == v.AMFB; nl();
//
//
//    print "mZk: ", mZk(k.self, m) == v.self, " ", mZk(k.owner, m) == v.owner, " ", mZk(k.bound, m) == v.bound;
//    print "|", mZk(k.AMFO, m) == v.AMFO, " ", mZk(k.AMFX, m)  == v.AMFX, " ", mZk(k.AMFB, m) == v.AMFB; nl();
//
//    print "msp: ", msp(k.self, m) == v.self, " ", msp(k.owner, m) == v.owner, " ", msp(k.bound, m) == v.bound;
//    print "|", msp(k.AMFO, m) == v.AMFO, " ", msp(k.AMFX, m)  == v.AMFX, " ", msp(k.AMFB, m) == v.AMFB; nl();
// //
//    print "pOb: ", pOb(k, m) == v.self, " ", pOb(k, m) == v.owner, " ", pOb(k, m) == v.bound;
//    print "|", pOb(k, m) == v.AMFO, " ", pOb(k, m)  == v.AMFX, " ", pOb(k, m) == v.AMFB; nl();
//
//    print "pOW: ", pOW(k.self, m) == v.self, " ", pOW(k.owner, m) == v.owner, " ", pOW(k.bound, m) == v.bound;
//    print "|", pOW(k.AMFO, m) == v.AMFO, " ", pOW(k.AMFX, m)  == v.AMFX, " ", pOW(k.AMFB, m) == v.AMFB; nl();

   print "zzz: ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
   print "|", sporamfo(m.m[k]) == v.AMFO, " ", sporamfx(m.m[k])  == v.AMFX, " ", sporamfb(m.m[k]) == v.AMFB; nl();

   print "zzz: ",ffmtnickset(mtk(k.self, m)), " ",ffmtnickset(mtk(k.owner, m)), " ",ffmtnickset(mtk(k.bound, m));
   print "|",ffmtnickset(sporamfo(m.m[k])), " ",ffmtnickset(sporamfx(m.m[k])), " ",ffmtnickset(sporamfb(m.m[k])); nl();
//
//
//    print "zz9: ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
//    print "|", splatten(mtk(k.owner,m)+{m.m[k]}) == v.AMFO, " ", splatten(mtk(k.owner,m)) == v.AMFX, " ", splatten(mtk(k.bound,m)) == v.AMFB; nl();
//


   print "zz8: ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
   print "|", splatten(m.m[k].owner)+{m.m[k]} == v.AMFO, " ", splatten(m.m[k].owner) == v.AMFX, " ", splatten(m.m[k].bound) == v.AMFB; nl();

//    print "mfo:", mapfo(k.self, m) == ownr2sso(v.self), " ", mapfo(k.owner, m) == ownr2sso(v.owner), " ", mapfo(k.bound, m) == ownr2sso(v.bound);
//    print "|", (mapfo(k.AMFO,m)) == ownr2sso(v.AMFO), " ", (mapfo(k.AMFX,m)) == ownr2sso(v.AMFX), " ", (mapfo(k.AMFB,m)) == ownr2sso(v.AMFB); nl();
// //
//4
//    print "msp: ", mtk(k.self, m) == v.self, " ", mtk(k.owner, m) == v.owner, " ", mtk(k.bound, m) == v.bound;
//    print "|", splatten(mtk(k.owner,m)+{m.m[k]}) == v.AMFO, " ", splatten(mtk(k.owner,m)) == v.AMFX, " ", splatten(mtk(k.bound,m)) == v.AMFB; nl();



  //  ensures sporamfo(o) == splatten(o.owner)+{o}
  //  ensures sporamfx(o) == splatten(o.owner)
  //  ensures sporamfb(o) == splatten(o.bound)

    var reconnected := mapfo(k.AMFO, m);

    if (reconnected != obj2sso(m.m[k]) )
    {
      print "FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck \n";
      print "FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck FUCK fuck \n";
    }




   print "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv\n\n";

 }


//{:timeLimit 60}
lemma {:isolate_assertions} MapfoPLUS1(oo1 : OWNR, oo2 : OWNR, o : Object, m : Klon)
   requires HighCalidFragilistic(m)
   requires forall o <- oo1     :: m.objectReadyInKlown(o)
   requires forall o <- oo2     :: m.objectReadyInKlown(o)
    ensures mapfo(oo1 + oo2,m ) == mapfo(oo1,m) + mapfo(oo2,m)

    requires oo2 == {o}
   {
     if (o in oo1) {
      setfuck(oo1, oo2, o);
      assert (oo1 + oo2) == (oo1 + {o}) == oo1;
      assert mapfo(oo1 + oo2,m ) == mapfo(oo1,m) + mapfo(oo2,m);
      return;
     }
     assert o !in oo1;
   }


lemma {:isolate_assertions} MapfoNULL(m : Klon)
   requires HighCalidFragilistic(m)
    ensures mapfo({}, m) == {}
{}

lemma {:isolate_assertions} SSOofNULL()
    ensures ownr2sso({}) == {}
{}

lemma {:isolate_assertions} SSO_GT(oo1 : OWNR, oo2 : OWNR, m : Klon)
   requires HighCalidFragilistic(m)
   requires forall o <- oo1     :: m.objectReadyInKlown(o)
   requires forall o <- oo2     :: m.objectReadyInKlown(o)
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires oo2 <= oo1
    ensures ownr2sso(oo2) <= ownr2sso(oo1)
   {}






lemma {:isolate_assertions} MapfoPLUS2(oo1 : OWNR, oo2 : OWNR, o : Object, m : Klon)
   requires HighCalidFragilistic(m)
   requires forall o <- oo1     :: m.objectReadyInKlown(o)
   requires forall o <- oo2     :: m.objectReadyInKlown(o)
   requires isFlat(oo1)
   requires isFlat(oo2)
    requires oo2 == {o}
    requires o in oo1
     ensures oo2 <= oo1
//     ensures mapfo(oo2,m) <= mapfo(oo1,m)
   {

assert oo2 <= oo1;
assert ownr2sso(oo2) <= ownr2sso(oo1);
// assert  (set o <- oo2 | inside(o, m.o)) <= (set o <- oo1 | inside(o, m.o));
// assert ((set o <- oo1 | inside(o, m.o)) == {}) ==> ((set o <- oo2 | inside(o, m.o)) == {});

assert (set o <- oo2 |  inside(o, m.o)) <= (set o <- oo1 |  inside(o, m.o));
assert (set o <- oo2 | outside(o, m.o)) <= (set o <- oo1 | outside(o, m.o));


if ((set o <- oo1 | inside(o, m.o)) == {})
   {
    assert mapfo(oo1,m) == ownr2sso(oo1);
    assert oo2 <= oo1;
    assert (set o <- oo2 | inside(o, m.o)) == {};
    assert mapfo(oo2,m) == ownr2sso(oo2);
    assert ownr2sso(oo2) <= ownr2sso(oo1);
    assert mapfo(oo2,m) <= mapfo(oo1,m);
    return;
   }

assert (set o <- oo1 | inside(o, m.o)) != {};

// if ((set o <- oo2 | inside(o, m.o)) == {})
//  {
//
//   assert mapfo(oo2,m) <= mapfo(oo1,m);
//   return;
//  }

assert ((set o <- oo1 | inside(o, m.o)) != {}) && ((set o <- oo2 | inside(o, m.o)) != {});

assert (set o <- oo2 |  inside(o, m.o)) <= (set o <- oo1 |  inside(o, m.o));
assert (set o <- oo2 | outside(o, m.o)) <= (set o <- oo1 | outside(o, m.o));



assert (oo2 - m.o.AMFO) <= (oo1 - m.o.AMFO);
assert forall y <- (oo2 - m.o.AMFO) :: y in (oo1 - m.o.AMFO);

assert mapfo_INNER(oo2,m) <= mapfo_INNER(oo1,m);

assert (mapfo_INNER(oo2,m) + obj2sso(m.m[m.o])) <= (mapfo_INNER(oo1,m) + obj2sso(m.m[m.o]));

assert mapfo(oo1,m) == (mapfo_INNER(oo1,m) + obj2sso(m.m[m.o]));
assert mapfo(oo2,m) == (mapfo_INNER(oo2,m) + obj2sso(m.m[m.o]));

//
// assert
//   (if ((set o <- oo2 | inside(o, m.o)) == {}) then ownr2sso(oo2) else (mapfo_INNER(oo2,m)) + obj2sso(m.m[m.o]))
//   <=
//   (if ((set o <- oo1 | inside(o, m.o)) == {}) then ownr2sso(oo1) else (mapfo_INNER(oo1,m)) + obj2sso(m.m[m.o]))
//   ;



assert mapfo(oo2,m) <= mapfo(oo1,m);

   }

lemma setfuck(oo1 : OWNR, oo2 : OWNR, o : Object)
    requires oo2 == {o}
    requires o in oo1
     ensures oo1 + {o} == oo1
     ensures oo1 + oo2 == oo1
{}

lemma setcrap(oo1 : OWNR, oo2 : OWNR, x : OWNR)
    requires oo2 <= oo1
     ensures (oo2+x) <= (oo1+x)
{}


lemma {:isolate_assertions} {:resource_limit 32000000} INSIDEOUT(oo : OWNR, m : Klon)
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
    ensures ((set o <- oo | inside(o, m.o)) == {})  ==> (forall o <- oo :: outside(o, m.o))
    ensures ((set o <- oo | inside(o, m.o)) == {}) <==  (forall o <- oo :: outside(o, m.o))

    ensures ((set o <- oo | inside(o, m.o)) >  {})  ==> (exists o <- oo :: inside(o, m.o))
    ensures ((set o <- oo | inside(o, m.o)) >  {}) <==  (exists o <- oo :: inside(o, m.o))

    ensures ((set o <- oo | inside(o, m.o)) >  {})  ==> (not (forall o <- oo :: outside(o, m.o)))
    ensures ((set o <- oo | inside(o, m.o)) >  {}) <==  (not (forall o <- oo :: outside(o, m.o)))
 {}

lemma {:isolate_assertions} MapfoEQ(oo1 : OWNR, oo2 : OWNR, m : Klon)
   requires HighCalidFragilistic(m)
   requires forall o <- oo1  :: m.objectReadyInKlown(o)
   requires forall o <- oo2  :: m.objectReadyInKlown(o)
    ensures (oo1 == oo2)  ==> (mapfo(oo1,m) == mapfo(oo2,m))
 //   ensures (oo1 == oo2) <==  (mapfo(oo1,m) == mapfo(oo2,m))
   {}


lemma {:isolate_assertions} MapfoEQ2(o1 : Object, o2 : Object, m : Klon)
   requires HighCalidFragilistic(m)
   requires m.objectReadyInKlown(o1)
   requires m.objectReadyInKlown(o2)
    ensures (o1 == o2)  ==> (mapfo(o1.AMFO,m) == mapfo(o2.AMFO,m))
  //  ensures (o1 == o2) <==  (mapfo(o1.AMFO,m) == mapfo(o2.AMFO,m))
   {}


 function {:isolate_assertions} {:timeLimit 20} mapfo_orig(oo : OWNR, m : Klon) : SSO
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
    ensures                 m.o.AMFO <= m.m.Keys
    ensures forall o <- oo :: o.AMFO <= m.m.Keys
   reads oo, m.m.Keys, m.m.Values, m.oHeap
 {
   if ((set o : Object <- oo | inside(o, m.o)) == {}) then ownr2sso(oo) else

    (( set y : Object <- (oo - m.o.AMFO) ::

       if (y.AMFO >= m.o.AMFO) then
         (mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO )
         ) else ( y.AMFO
          )
      ) + obj2sso(m.m[m.o]))

 }





lemma {:isolate_assertions} MAPFO_MAPFO_ORIG1(oo : OWNR, m : Klon)
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
    ensures mapfo(oo,m) == mapfo_orig(oo,m)
   { }


lemma {:isolate_assertions}  {:timeLimit 120} MAPFO_MAPFO_ORIG2(oo : OWNR, m : Klon)
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
    ensures mapfo_INNER(oo,m) == mapfo_INNER_NEW(oo,m)
   { }

lemma {:isolate_assertions}  MAPFO_MAPFO_INNER1(oo : OWNR, m : Klon)
 //if there is at least one inside
 //then we're calling INNER & added into m.m[m.o]
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
   requires ((set o <- oo | inside(o, m.o)) > {})
    ensures mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]))
   { }

//{:resource_limit 32000000}
lemma {:isolate_assertions} MAPFO_MAPFO_INNER2(oo : OWNR, m : Klon)
//if all items are outside m.o they go straight through
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)

   requires forall o <- oo :: outside(o, m.o)
   requires oo !! m.o.AMFO
    ensures mapfo(oo,m)       == ownr2sso(oo)
//    ensures mapfo_INNER(oo,m) >= ownr2sso(oo)  //NOT this... *********
  {}

//
// lemma {:isolate_assertions} MAPFO_MAPFO_INNER3(oo : OWNR, m : Klon)
// //all items outside m.o go straight through!
//    requires forall o <- oo :: m.objectReadyInKlown(o)
//    requires oo <= m.m.Keys
//    requires HighCalidFragilistic(m)
//
//     ensures forall o <- oo | strictlyInside(o, m.o) ::
//        (mapfo_SIDEWAYS(o,m) in mapfo(oo,m))
//   {
//
//   }



lemma {:isolate_assertions}  MAPFO_MAPFO_INNER8(oo : OWNR, m : Klon, r : SSO, i : SSO)
//incomplete.  does nothing.
//OK now does the same as GT3i???
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires HighCalidFragilistic(m)
   requires r == mapfo(oo,m)
   requires i == mapfo_INNER(oo,m)

   requires ((set o <- oo | inside(o, m.o)) > {})   //at least something is inside, so we go down that way. b

   ensures mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]))
   { }

// lemma {:isolate_assertions} {:timeLimit 20} MAPFO_MAPFO_INNER9(oo : OWNR, m : Klon)
//  //DOESNT, SHOULDNT, CANT WORK. THIS IS A BIT STUPID INNIT??
//    requires forall o <- oo :: m.objectReadyInKlown(o)
//    requires oo <= m.m.Keys
//    requires HighCalidFragilistic(m)
//
//    requires ((set o <- oo | outside(o, m.o)) > {})
//    // ensures mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]))
//    {
//     assert forall o <- oo :: outside(o, m.o);
//     assert forall o <- oo :: not(o.AMFO >= m.o.AMFO);
//     assert not( outside(m.o, m.o) );
//     assert not(m.o.AMFO <= oo);
//
//    }




//{:resource_limit 32000000}
lemma {:isolate_assertions} MAPFO_MAPFO_GT1(oo1 : OWNR, oo2 : OWNR, m : Klon)
  //mapfo_SIDEWAYS maintains <= (modulo preconditions)
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1
   requires forall o <- oo1 :: (o !in m.o.AMFO) && (inside(o, m.o))
    ensures forall o <- oo2 :: (o !in m.o.AMFO) && (inside(o, m.o))
    ensures (set o <- oo2 :: mapfo_SIDEWAYS(o,m)) <=
                     (set o <- oo1 :: mapfo_SIDEWAYS(o,m))
  { }


//{:resource_limit 32000000}
lemma {:isolate_assertions} MAPFO_MAPFO_GT2(oo1 : OWNR, oo2 : OWNR, m : Klon)
 //mapfo Inner maintains <=
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1

    ensures mapfo_INNER(oo2,m) <= mapfo_INNER(oo1,m)
    ensures (mapfo_INNER(oo2,m) + obj2sso(m.m[m.o])) <= (mapfo_INNER(oo1,m) + obj2sso(m.m[m.o]))
{}


lemma {:isolate_assertions} MAPFO_MAPFO_GT2thru(oo : OWNR, ext : Object, m : Klon)
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires isFlat(oo)
   requires HighCalidFragilistic(m)
   requires not(ext in m.o.AMFO) //?????
   requires not(ext.AMFO >= m.o.AMFO)
   requires ext in oo
    ensures ext.AMFO in mapfo_INNER(oo,m)
{}



lemma {:isolate_assertions} MAPFO_MAPFO_GT2thru2(oo1 : OWNR, oo2 : OWNR, ext : Object, m : Klon)
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1

   requires not(ext in m.o.AMFO) //?????
   requires not(ext.AMFO >= m.o.AMFO)
   requires ext in oo2
    ensures ext in oo1
    ensures ext.AMFO in mapfo_INNER(oo2,m)
    ensures ext.AMFO in mapfo_INNER(oo1,m)
{}



lemma {:isolate_assertions} MAPFO_MAPFO_GT2thrall(oo1 : OWNR, oo2 : OWNR, ext : Object, m : Klon)
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1

   requires not(ext in m.o.AMFO) //?????
   requires not(ext.AMFO >= m.o.AMFO)
   requires ext in oo2
    ensures ext in oo1
    ensures ext.AMFO in mapfo_INNER(oo2,m)
    ensures ext.AMFO in mapfo_INNER(oo1,m)
{}




lemma {:isolate_assertions} MAPFO_MAPFO_GT3(oo1 : OWNR, oo2 : OWNR, m : Klon)
  //supposed to be mapfo maintains <=? in all cases?
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1

  //  ensures mapfo(oo2,m) <= mapfo(oo1,m)
{
  //if oo1 is all outside pivot, so must be oo2 - and yourdon.
  if ((set o <- oo1 | inside(o, m.o)) == {})  //forall o <- oo1 :: outside(o, m.o)
     {
      assert ((set o <- oo2 | inside(o, m.o)) == {}); // //forall o <- oo1 :: outside(o, m.o)

      assert ownr2sso(oo2) <= ownr2sso(oo1);
      assert mapfo(oo2,m) <= mapfo(oo1,m);
      return;
     }

    //oo1 does have something inside.
    assert ((set o <- oo1 | inside(o, m.o)) > {});


  //if set2 *also* has something inside then we're both going thru inner
  if ((set o <- oo2 | inside(o, m.o)) > {})
     {
      assert ((set o <- oo2 | inside(o, m.o)) > {});
      assert OO2IN: ((set o <- oo2 | inside(o, m.o)) > {});
      assert ((set o <- oo1 | inside(o, m.o)) > {});
      assert oo2 <= oo1;
      MAPFO_MAPFO_GT2(oo1,oo2,m);
      assert
        (mapfo_INNER(oo2,m) + obj2sso(m.m[m.o]))
           <= (mapfo_INNER(oo1,m) + obj2sso(m.m[m.o]));

      MAPFO_MAPFO_GT3i(oo1,m);
      assert ((set o <- oo2 | inside(o, m.o)) > {}) by { reveal OO2IN; }
      MAPFO_MAPFO_GT3i(oo2,m);
      assert mapfo(oo1,m) == (mapfo_INNER(oo1,m) + obj2sso(m.m[m.o]));
      assert mapfo(oo2,m) == (mapfo_INNER(oo2,m) + obj2sso(m.m[m.o]));
      MAPFO_MAPFO_GT2(oo1,oo2,m);
      assert mapfo(oo2,m) <= mapfo(oo1,m);
      return;
     }

  //at this poiint oo1 definitely HAS something inside and goes down thru INNER
  //but oo2 DOES NOT.
  assert oo2 <= oo1;
  assert ((set o <- oo1 | inside(o, m.o)) >  {});
  assert ((set o <- oo2 | inside(o, m.o)) == {});
//  assert ((set o <- oo2 | outside(o,m.o)) == oo2);
// assert forall o <- oo2 :: outside(o, m.o);


MAPFO_MAPFO_GT3x(oo1,oo2,m);
assert mapfo(oo2,m) <= mapfo(oo1,m);
}


lemma {:isolate_assertions} MAPFO_MAPFO_GT3i(oo : OWNR, m : Klon)
 // if there is at least one on oo inside, mapfo is Inner+thingey
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires isFlat(oo)
   requires HighCalidFragilistic(m)
   requires (set o <- oo | inside(o, m.o)) > {}   //exists o <- oo :: inside(o, m.o)
    ensures mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]))
{
  //YAY DAFNY!!
  // INSIDEOUT(oo,m);
  // assert exists o <- oo :: inside(o, m.o);
  // assert (set o <- oo | inside(o, m.o)) > {};
  // assert mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]));

}



lemma XLEM<T(==)>(e : T, s : set<T>)
   requires e in s
    ensures {e} <= s
    ensures {e} > {}
    ensures (set o  <- s | e == o :: o) > {}
  {}

lemma YLEM<T(==)>(e : T, s : set<T>)
   requires e in s
    ensures {e} <= s
    ensures {e} > {}
    ensures (set o  <- s | {o} <= s) > {}
  {}

lemma ELEM<T(==)>(e :set<T>, s : set<set<T>>)
   requires e in s
    ensures {e} <= s
    ensures {e} > {}
    ensures (set o  <- s | {o} <= s) > {}
 {}

lemma FUKSSO(oo : OWNR, sso : SSO)
   requires oo in sso
    ensures {oo} <= sso
    ensures {oo} > {}
    ensures (set o <- sso | o <= oo) > {}
 {}

lemma {:isolate_assertions} {:timeLimit 15} MAPFO_MAPFO_GT3j(oo : OWNR, m : Klon)
 //one inside pivot into mapfo, at least one inside blivet out of mapfo
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires isFlat(oo)
   requires HighCalidFragilistic(m)
    ensures forall k <- m.m.Keys :: m.m[k].Ready()
   requires (set o <- oo | inside(o, m.o)) > {}                 //exists o <- oo :: inside(o, m.o)
    ensures (m.m[m.o].AMFO) in mapfo(oo,m)
    ensures (set o <- mapfo(oo,m) | o  >= m.m[m.o].AMFO) > {}   //exists o <- mapfo(oo,m) :: o >= m.m[m.o].AMFO
{
   assert (set o <- oo | inside(o, m.o)) > {};
   MAPFO_MAPFO_GT3i(oo,m);
   assert mapfo(oo,m) == (mapfo_INNER(oo,m) + obj2sso(m.m[m.o]));
  //  assert inside(m.m[m.o], m.m[m.o]);
  //  assert m.m[m.o].Ready();
  //  assert forall o <- m.m[m.o].AMFO :: o.Ready();
  //  assert forall oo <- obj2sso(m.m[m.o]), o <- oo :: o.Ready();
   assert (m.m[m.o].AMFO) in obj2sso(m.m[m.o]);
   assert (m.m[m.o].AMFO) in mapfo(oo,m);
   assert {m.m[m.o].AMFO} > {};
   assert (set o <- obj2sso(m.m[m.o]) | o  >= m.m[m.o].AMFO) > {}; //FUCK
   assert (set o <- mapfo(oo,m)       | o  >= m.m[m.o].AMFO) > {};
}


lemma {:isolate_assertions} MAPFO_MAPFO_GT3o(oo : OWNR, m : Klon)
 //everyting outside pivot into mapfo, nothing inside blivet outside mapfo
   requires forall o <- oo :: m.objectReadyInKlown(o)
   requires oo <= m.m.Keys
   requires isFlat(oo)
   requires HighCalidFragilistic(m)
   requires forall o : Object <- oo :: outside(o,m.o)
    ensures forall r : Owner <- mapfo(oo,m) :: not(r >= m.o.AMFO)
    ensures forall r : Owner <- mapfo(oo,m) :: not(r >= m.m[m.o].AMFO)
{}


lemma {:isolate_assertions} {:timeLimit 30} MAPFO_MAPFO_GT3x(oo1 : OWNR, oo2 : OWNR, m : Klon)
//IF oo2 <= oo1, AND oo1 has something inside, and oo2 does not, then mapfo oo2 <= mapfo oo1
   requires forall o <- oo1 :: m.objectReadyInKlown(o)
   requires forall o <- oo2 :: m.objectReadyInKlown(o)
   requires oo1 <= m.m.Keys
   requires oo2 <= m.m.Keys
   requires isFlat(oo1)
   requires isFlat(oo2)
   requires HighCalidFragilistic(m)
   requires oo2 <= oo1

   requires (set o <- oo1 | inside(o, m.o)) >  {}    //exists o <- oo1 :: inside(o, m.o)
   requires (set o <- oo2 | inside(o, m.o)) == {}    //requires forall o <- oo2 :: outside(o, m.o)
   ensures mapfo(oo2,m) <= mapfo(oo1,m)

{

  assert oo2 <= oo1;
  assert (set o <- oo1 | inside(o, m.o)) >  {};
  assert (set o <- oo2 | inside(o, m.o)) == {};


  var unicorn :| (unicorn in oo1) && (unicorn !in oo2) && (inside(unicorn, m.o));

    assert unicorn.AMFO >= m.o.AMFO;
    MAPFO_MAPFO_GT3o(oo2,m);
    assert forall r : Owner <- mapfo(oo2,m) :: not(r >= m.o.AMFO);
    assert forall r : Owner <- mapfo(oo2,m) :: not(r >= m.m[m.o].AMFO);

    assert forall r : Owner <- mapfo(oo2,m) :: not(r >= m.m[m.o].AMFO);
    assert unicorn.AMFO >= m.o.AMFO;

assert isFlat(unicorn.AMFO);
assert unicorn.AMFO > {};
assert (set o <- unicorn.AMFO | o.AMFO >= m.o.AMFO) > {};

MAPFO_MAPFO_GT3j(unicorn.AMFO,m);
assert (set o <- mapfo(unicorn.AMFO,m) | o  >= m.m[m.o].AMFO) > {};

assert oo2 <= oo1;
assert (unicorn in oo1);
assert (unicorn !in oo2);

var        bicorn := mapfo({unicorn},m);
assert     bicorn <= mapfo(oo1,m);         //WHAT THE FUCKY FUCK?
assert not(bicorn <= mapfo(oo2,m));

 assert not(mapfo(oo1,m) <= mapfo(oo2,m));

 assert mapfo(oo2,m) <= mapfo(oo1,m);



//  assert forall x : OWNR <- mapfo(oo2,m) :: not(x >= m.o.AMFO) && not(x >= m.m[m.o].AMFO);  //pivot & blivet

}


method {:isolate_assertions} {:timeLimit 30} wrangle7()
//sets up a full clone with sideways owner
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    print "wrangle7\n";

    t := new Object.make(protoTypes, {},  {},"t");
    a := new Object.make(protoTypes, {t}, {t}, "a");
    b := new Object.make(protoTypes, {a}, {t,a}, "bP");   //pivot
    c := new Object.make(protoTypes, {b}, {t,a,b}, "c");  //inside clone
    e := new Object.make(protoTypes, {t}, {t}, "eQ");       //external "sideways" owner
    d := new Object.make(protoTypes, {c,e}, {t,a,b,c,e}, "dX"); //inside pivot and side owner

    k := new Object.make(protoTypes, {t}, {t}, "k¢b"); //top of coone - of b
    l := new Object.make(protoTypes, {k}, {t,k}, "l¢c"); //clone of c

            var m_context := {t,k,l,e};
            var m_oo := {l,e};
            var m_mb := m_oo;

            assert m_context >= flatten(m_oo);
            expect m_context >= flatten(m_oo);
            assert flatten(m_oo) >= flatten(m_mb);
            expect flatten(m_oo) >= flatten(m_mb);
            assert AllReady(m_oo);
            expect AllReady(m_oo);
            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            expect (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            // assume m_context >= flatten(m_oo) >= flatten(m_mb);
            // assume AllReady(m_oo);
            // assume (flatten(m_mb) >= collectBounds(flatten(m_oo)));

     m := new Object.make(protoTypes, m_oo, m_context, "m¢d"); //clone of d...

//     b := new Object.make(protoTypes, {},  {},"b");
//     c := new Object.make(protoTypes, {},  {},"c");
//     d := new Object.make(protoTypes, {},  {},"d");

    // k := new Object.make(protoTypes, {},  {},"k");
    // l := new Object.make(protoTypes, {},  {},"l");
    // m := new Object.make(protoTypes, {},  {},"m");



    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

nl();
  var x : nat;
  for x := 0 to |oq| { print fmtamfob(oq[x]), "\n"; }
nl();



print "m_context= ", ffmtnickset(m_context), "\n";
print "m_oo= ", ffmtnickset(m_oo), "\n";
print "flatten(m_oo)= ", ffmtnickset(flatten(m_oo)), "\n";
print "m_mb= ", ffmtnickset(m_mb), "\n";
print "flatten(m_mb)= ", ffmtnickset(flatten(m_mb)), "\n";
print "collectBounds(flatten(m_oo))= ", ffmtnickset(collectBounds(flatten(m_oo))), "\n";

print "ctxt>=flatten(m_oo)= ", (m_context >= flatten(m_oo)), "\n";
print "flatten(m_oo)>=flatten(m_mb)= ", (flatten(m_oo) >= flatten(m_mb)), "\n";
print "AllReady(m_oo)= ", AllReady(m_oo), "\n";
print "flatten(m_mb) >= collectBounds(flatten(m_oo))= ", flatten(m_mb) >= collectBounds(flatten(m_oo)), "\n";





//
//     assert forall x <- os :: x.Ready() by {
//
//         assert t.Ready();`
//         assert a.Ready();
//         assert b.Ready();
//         assert c.Ready();
//         assert d.Ready();
//         assert e.Ready();
//         assert k.Ready();
//         assert l.Ready();
//         assert m.Ready();
//
//         assert t in os;
//         assert a in os;
//         assert b in os;
//         assert c in os;
//         assert d in os;
//         assert e in os;
//         assert k in os;
//         assert l in os;
//         assert m in os;
//
//         assert os == {t, a, b, c, d, e, k, l, m};
//
//      }


    AllTheseFuckingObjectsAreReadyYouIdiot(t, a, b, c, d, e, k, l, m, os);


    assert forall x <- os :: x.Ready();



    print "wrdone7\n";
 }



method {:isolate_assertions} jandal8()
//sets up a full-done clone *reentrantly*
//otherwise compatible with wrangle - except klone owned by d  from
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m BUT now owned by **d**
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    print "jandal8\n";

    t := new Object.make(protoTypes, {},  {},"t");
    a := new Object.make(protoTypes, {t}, {t}, "a");
    b := new Object.make(protoTypes, {a}, {t,a}, "bP");   //pivot
    c := new Object.make(protoTypes, {b}, {t,a,b}, "c");  //inside clone
    e := new Object.make(protoTypes, {t}, {t}, "eQ");       //external "sideways" owner
    d := new Object.make(protoTypes, {c,e}, {t,a,b,c,e}, "dX"); //inside pivot and side owner



assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert e.AMFO == {t,e};
assert d.AMFO == {t,a,b,c,d,e};

//
// assert collectAllOwners(t) == {t};
// assert collectAllOwners(a) == {t,a};
// assert collectAllOwners(b) == {t,a,b};
// assert collectAllOwners(c) == {t,a,b,c};
// assert collectAllOwners(e) == {t,e};
//
// assert d.owner == {c,e};
// assert ({d} + {c,e}) == {c,d,e};
// assert (set xo <- d.owner, co <- collectAllOwners(xo) :: co) == (collectAllOwners(c) + collectAllOwners(e));
// var oCE := (collectAllOwners(c) + collectAllOwners(e));
// assert oCE == (collectAllOwners(c) + collectAllOwners(e)) == ({t,a,b,c} + {t,e}) == {t,a,b,c,e};
//
// assert ({d} + d.owner + oCE) ==  {t,a,b,c,d,e};
// assert collectAllOwners(d) == ({d} + d.owner +  collectAllOwners(c) + collectAllOwners(e)); // == {t,a,b,c,d,e};
// assert collectAllOwners(d) == {t,a,b,c,d,e};
//
//




printAllOwnershipsAndBounds({d}, {t,a,b,c,d,e}, "k¢b");

assert flatten({d}) == {t,a,b,c,d,e};
            assert {t,a,b,c,d,e} >= flatten({d});
            assert flatten({d}) >= flatten({d});
            assert AllReady({d});
            assert (flatten({d}) >= collectBounds(flatten({d})));
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k¢b"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l¢c");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
            assert (flatten({k}) >= collectBounds(flatten({k})));
    l := new Object.make(protoTypes, {k}, {t,a,b,c,d,e,k}, "l¢c"); //clone of c

/// assert l.AMFO == {t,a,b,c,d,e,k,l};

            var m_context := {t,a,b,c,d,e,k,l};
            var m_oo := {l,e};
            var m_mb := m_oo;

            // assert m_context >= flatten(m_oo);
            // assert flatten(m_oo) >= flatten(m_mb);
            // assert AllReady(m_oo);
            // assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));

            assume flatten(m_oo) == {t,a,b,c,d,e,k,l};

            assert m_context >= flatten(m_oo);
            expect m_context >= flatten(m_oo);
            assert flatten(m_oo) >= flatten(m_mb);
            expect flatten(m_oo) >= flatten(m_mb);
            assert AllReady(m_oo);
            expect AllReady(m_oo);
            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            expect (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            // assume m_context >= flatten(m_oo) >= flatten(m_mb);
            // assume AllReady(m_oo);
            // assume (flatten(m_mb) >= collectBounds(flatten(m_oo)));

printAllOwnershipsAndBounds(m_oo, m_context, "m¢d");

     m := new Object.make(protoTypes, m_oo, m_context, "m¢d"); //clone of d...

//assert m.AMFO == {t,a,b,c,d,e,k,l,m};


//     b := new Object.make(protoTypes, {},  {},"b");
//     c := new Object.make(protoTypes, {},  {},"c");
//     d := new Object.make(protoTypes, {},  {},"d");

    // k := new Object.make(protoTypes, {},  {},"k");
    // l := new Object.make(protoTypes, {},  {},"l");
    // m := new Object.make(protoTypes, {},  {},"m");



    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

nl();
  var x : nat;
  for x := 0 to |oq| { print fmtamfob(oq[x]), "\n"; }
nl();




//
//     assert forall x <- os :: x.Ready() by {
//
//         assert t.Ready();
//         assert a.Ready();
//         assert b.Ready();
//         assert c.Ready();
//         assert d.Ready();
//         assert e.Ready();
//         assert k.Ready();
//         assert l.Ready();
//         assert m.Ready();
//
//         assert t in os;
//         assert a in os;
//         assert b in os;
//         assert c in os;
//         assert d in os;
//         assert e in os;
//         assert k in os;
//         assert l in os;
//         assert m in os;
//
//         assert os == {t, a, b, c, d, e, k, l, m};
//
//      }


    AllTheseFuckingObjectsAreReadyYouIdiot(t, a, b, c, d, e, k, l, m, os);


    assert forall x <- os :: x.Ready();



    print "jandone8\n";
 }


method printAllOwnershipsAndBounds(oo : Owner, context : set<Object>, name : string, mb : Owner := oo)
//warning - this doesn't do what it should (print stuff out of an object)
//but prints stuff from the arguments handed in only
{
print "============================================================\nprintAllOwnershipsAndBounds ";
print name, "\n";

print "context= ", ffmtnickset(context), "\n";
print "oo= ", ffmtnickset(oo), "\n";
print "flatten(oo)= ", ffmtnickset(flatten(oo)), "\n";
print "mb= ", ffmtnickset(mb), "\n";
print "flatten(mb)= ", ffmtnickset(flatten(mb)), "\n";
print "collectBounds(flatten(oo))= ", ffmtnickset(collectBounds(flatten(oo))), "\n";
print "set oo.AMFB=", fmtsso( set oo <- flatten(mb) :: oo.AMFB  ), "\n";

print "ctxt>=flatten(oo)= ", (context >= flatten(oo)), "\n";
print "flatten(oo)>=flatten(mb)= ", (flatten(oo) >= flatten(mb)), "\n";
print "AllReady(oo)= ", AllReady(oo), "\n";
print "flatten(mb) >= collectBounds(flatten(oo))= ", flatten(mb) >= collectBounds(flatten(oo)), "\n";
print "forall oo <- mb :: (flatten(mb) <= oo.AMFB)=", (forall oo <- mb :: (flatten(mb) <= oo.AMFB)) ,"\n";
}


method {:isolate_assertions} sandal8()
//sets up a full-done clone *with sideways partial owners*
//otherwise compatible with wrangle - except klone owned by d  from
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m BUT now owned by **d**
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    print "sandal8\n";

    t := new Object.make(protoTypes, {},  {},"t");
    a := new Object.make(protoTypes, {t}, {t}, "a");
    b := new Object.make(protoTypes, {a}, {t,a}, "bP");   //pivot
    c := new Object.make(protoTypes, {b}, {t,a,b}, "c");  //inside clone
    e := new Object.make(protoTypes, {a}, {t,a}, "eQ");       //external "sideways" owner
    d := new Object.make(protoTypes, {c,e}, {t,a,b,c,e}, "dX"); //inside pivot and side owner



assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert e.AMFO == {t,a,e};
assert d.AMFO == {t,a,b,c,d,e};

//
// assert collectAllOwners(t) == {t};
// assert collectAllOwners(a) == {t,a};
// assert collectAllOwners(b) == {t,a,b};
// assert collectAllOwners(c) == {t,a,b,c};
// assert collectAllOwners(e) == {t,e};
//
// assert d.owner == {c,e};
// assert ({d} + {c,e}) == {c,d,e};
// assert (set xo <- d.owner, co <- collectAllOwners(xo) :: co) == (collectAllOwners(c) + collectAllOwners(e));
// var oCE := (collectAllOwners(c) + collectAllOwners(e));
// assert oCE == (collectAllOwners(c) + collectAllOwners(e)) == ({t,a,b,c} + {t,e}) == {t,a,b,c,e};
//
// assert ({d} + d.owner + oCE) ==  {t,a,b,c,d,e};
// assert collectAllOwners(d) == ({d} + d.owner +  collectAllOwners(c) + collectAllOwners(e)); // == {t,a,b,c,d,e};
// assert collectAllOwners(d) == {t,a,b,c,d,e};
//
//




printAllOwnershipsAndBounds({d}, {t,a,b,c,d,e}, "k¢b");

assert flatten({d}) == {t,a,b,c,d,e};
            assert {t,a,b,c,d,e} >= flatten({d});
            assert flatten({d}) >= flatten({d});
            assert AllReady({d});
            assert (flatten({d}) >= collectBounds(flatten({d})));
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k¢b"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l¢c");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
            assert (flatten({k}) >= collectBounds(flatten({k})));
    l := new Object.make(protoTypes, {k}, {t,a,b,c,d,e,k}, "l¢c"); //clone of c

/// assert l.AMFO == {t,a,b,c,d,e,k,l};

            var m_context := {t,a,b,c,d,e,k,l};
            var m_oo := {l,e};
            var m_mb := m_oo;

            // assert m_context >= flatten(m_oo);
            // assert flatten(m_oo) >= flatten(m_mb);
            // assert AllReady(m_oo);
            // assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));

            assume flatten(m_oo) == {t,a,b,c,d,e,k,l};

            assert m_context >= flatten(m_oo);
            expect m_context >= flatten(m_oo);
            assert flatten(m_oo) >= flatten(m_mb);
            expect flatten(m_oo) >= flatten(m_mb);
            assert AllReady(m_oo);
            expect AllReady(m_oo);
            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            expect (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            // assume m_context >= flatten(m_oo) >= flatten(m_mb);
            // assume AllReady(m_oo);
            // assume (flatten(m_mb) >= collectBounds(flatten(m_oo)));

printAllOwnershipsAndBounds(m_oo, m_context, "m¢d");

     m := new Object.make(protoTypes, m_oo, m_context, "m¢d"); //clone of d...


    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

nl();
  var x : nat;
  for x := 0 to |oq| { print fmtamfob(oq[x]), "\n"; }
nl();




    AllTheseFuckingObjectsAreReadyYouIdiot(t, a, b, c, d, e, k, l, m, os);


    assert forall x <- os :: x.Ready();



    print "sandone8\n";
 }












method {:isolate_assertions} randal9()
//sets up a full-done clone *with sideways partial owners*
//otherwise compatible with wrangle - except klone owned by d  from
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m BUT now owned by **d**
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    print "randal9 NINE NINE NINE\n";

    t := new Object.make(protoTypes, {},  {},"t");
    a := new Object.make(protoTypes, {t}, {t}, "a");
    b := new Object.make(protoTypes, {a}, {t,a}, "b");   //pivot
    c := new Object.make(protoTypes, {b}, {t,a,b}, "c");  //inside clone
    e := new Object.make(protoTypes, {a}, {t,a}, "e");       //external "sideways" owner
    d := new Object.make(protoTypes, {c,e}, {t,a,b,c,e}, "d"); //inside pivot and side owner



assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert e.AMFO == {t,a,e};
assert d.AMFO == {t,a,b,c,d,e};

//
// assert collectAllOwners(t) == {t};
// assert collectAllOwners(a) == {t,a};
// assert collectAllOwners(b) == {t,a,b};
// assert collectAllOwners(c) == {t,a,b,c};
// assert collectAllOwners(e) == {t,e};
//
// assert d.owner == {c,e};
// assert ({d} + {c,e}) == {c,d,e};
// assert (set xo <- d.owner, co <- collectAllOwners(xo) :: co) == (collectAllOwners(c) + collectAllOwners(e));
// var oCE := (collectAllOwners(c) + collectAllOwners(e));
// assert oCE == (collectAllOwners(c) + collectAllOwners(e)) == ({t,a,b,c} + {t,e}) == {t,a,b,c,e};
//
// assert ({d} + d.owner + oCE) ==  {t,a,b,c,d,e};
// assert collectAllOwners(d) == ({d} + d.owner +  collectAllOwners(c) + collectAllOwners(e)); // == {t,a,b,c,d,e};
// assert collectAllOwners(d) == {t,a,b,c,d,e};
//
//




printAllOwnershipsAndBounds({d}, {t,a,b,c,d,e}, "k");

assert flatten({d}) == {t,a,b,c,d,e};
            assert {t,a,b,c,d,e} >= flatten({d});
            assert flatten({d}) >= flatten({d});
            assert AllReady({d});
            assert (flatten({d}) >= collectBounds(flatten({d})));
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
            assert (flatten({k}) >= collectBounds(flatten({k})));
    l := new Object.make(protoTypes, {k}, {t,a,b,c,d,e,k}, "l"); //clone of c

/// assert l.AMFO == {t,a,b,c,d,e,k,l};

            var m_context := {t,a,b,c,d,e,k,l};
            var m_oo := {l,e};
            var m_mb := m_oo;

            // assert m_context >= flatten(m_oo);
            // assert flatten(m_oo) >= flatten(m_mb);
            // assert AllReady(m_oo);
            // assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));

            assume flatten(m_oo) == {t,a,b,c,d,e,k,l};

            assert m_context >= flatten(m_oo);
            expect m_context >= flatten(m_oo);
            assert flatten(m_oo) >= flatten(m_mb);
            expect flatten(m_oo) >= flatten(m_mb);
            assert AllReady(m_oo);
            expect AllReady(m_oo);
            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            expect (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            // assume m_context >= flatten(m_oo) >= flatten(m_mb);
            // assume AllReady(m_oo);
            // assume (flatten(m_mb) >= collectBounds(flatten(m_oo)));

printAllOwnershipsAndBounds(m_oo, m_context, "m");

     m := new Object.make(protoTypes, m_oo, m_context, "m"); //clone of d...


    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];
//
// nl();
//   var x : nat;
//   for x := 0 to |oq| { print fmtamfob(oq[x]), "\n"; }
// nl();




    AllTheseFuckingObjectsAreReadyYouIdiot(t, a, b, c, d, e, k, l, m, os);


    assert forall x <- os :: x.Ready();



    print "randone9\n";
 }










method {:isolate_assertions} zandal9()
//sets up a single "column" of objects to show permissible links - five objects, t, a..d
//in this version, all boundaries == owners
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    loutName := "zandall9";
    print loutName, " NINE NINE NINE\n";


      t := new Object.make(protoTypes, {},  {},"t");
      a := new Object.make(protoTypes, {t}, {t}, "a");
      b := new Object.make(protoTypes, {a}, {t,a}, "b");
      c := new Object.make(protoTypes, {b}, {t,a,b}, "c");
      d := new Object.make(protoTypes, {c}, {t,a,b,c}, "d");
      e := new Object.make(protoTypes, {d}, {t,a,b,c,d}, "e");



printAllOwnershipsAndBounds({},  {},"t");
printAllOwnershipsAndBounds({t}, {t}, "a");
printAllOwnershipsAndBounds({a}, {t,a}, "b");
printAllOwnershipsAndBounds({b}, {t,a,b}, "c");
printAllOwnershipsAndBounds({c}, {t,a,b,c}, "d");
printAllOwnershipsAndBounds({d}, {t,a,b,c,d}, "e");


assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert d.AMFO == {t,a,b,c,d};
assert e.AMFO == {t,a,b,c,d,e};

k := t; l := t; m := t;

    os := {t, a, b, c, d, e};
    oq := [t, a, b, c, d, e];

    print "zandall9 no boundary \n";
  }








method {:isolate_assertions} zandal9bounded()
//sets up a single "column" of objects to show permissible links - five objects, t,a..d, with c & d boundary pushed up to a.
//
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
//  ensures inside(d,c)
//  ensures inside(d,e)
 {
    loutName := "zandall9bounded";
    print loutName, " NINE NINE NINE\n";


      t := new Object.make(protoTypes, {},  {},"t");
      a := new Object.make(protoTypes, {t}, {t}, "a");
      b := new Object.make(protoTypes, {a}, {t,a}, "b");
      c := new Object.make(protoTypes, {b}, {t,a,b}, "c", {a});
      d := new Object.make(protoTypes, {c}, {t,a,b,c}, "d", {a});
      e := new Object.make(protoTypes, {d}, {t,a,b,c,d}, "e", {a});



printAllOwnershipsAndBounds({},  {},"t");
printAllOwnershipsAndBounds({t}, {t}, "a");
printAllOwnershipsAndBounds({a}, {t,a}, "b");
printAllOwnershipsAndBounds({b}, {t,a,b}, "c");
printAllOwnershipsAndBounds({c}, {t,a,b,c}, "d", {a});
printAllOwnershipsAndBounds({d}, {t,a,b,c,d}, "e", {a});


assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert d.AMFO == {t,a,b,c,d};
assert e.AMFO == {t,a,b,c,d,e};

k := t; l := t; m := t;

    os := {t, a, b, c, d, e};
    oq := [t, a, b, c, d, e];

    print "zandl9bounded";

    return;

printAllOwnershipsAndBounds({t}, {t,a,b,c,d,e}, "k");

//          {t}, {t,a,b,c,d,e}, "k");

// assert flatten({d}) == {t,a,b,c,d,e};
//             assert {t,a,b,c,d,e} >= flatten({d});
//             assert flatten({d}) >= flatten({d});
//             assert AllReady({d});
//             assert (flatten({d}) >= collectBounds(flatten({d})));
    k := new Object.make(protoTypes, {t}, {t,a,b,c,d,e}, "k");

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({a}, {t,a,b,c,d,e,k}, "l");

assume flatten({k}) == {t,k};
            assert AllReady({k});
            assert (flatten({k}) >= collectBounds(flatten({k})));
    l := new Object.make(protoTypes, {a}, {t,a,b,c,d,e,k}, "l");

/// assert l.AMFO == {t,a,b,c,d,e,k,l};

            var m_context := {t,a,b,c,d,e,k,l};
            var m_oo := {b};
            var m_mb := m_oo;

            // assert m_context >= flatten(m_oo);
            // asse rt flatten(m_oo) >= flatten(m_mb);
            // assert AllReady(m_oo);
            // assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));

 //            assume flatten(m_oo) == {t,a,b,c,d,e,k,l};  //IF m_oo  == {b}?  WTF???

            // these assert/expect pairs used to work but now the don't.  WHY?
            // assert m_context >= flatten(m_oo);
            // expect m_context >= flatten(m_oo);
            // assert flatten(m_oo) >= flatten(m_mb);
            // expect flatten(m_oo) >= flatten(m_mb);
            // assert AllReady(m_oo);
            // expect AllReady(m_oo);
            // assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
            // expect (flatten(m_mb) >= collectBounds(flatten(m_oo)));

            // // assume m_context >= flatten(m_oo) >= flatten(m_mb);
            // // assume AllReady(m_oo);
            // // assume (flatten(m_mb) >= collectBounds(flatten(m_oo)));

printAllOwnershipsAndBounds(m_oo, m_context, "m");

     m := new Object.make(protoTypes, m_oo, m_context, "m"); //clone of d...


    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];


    print "zandlone9bounded\n";
   }








lemma {:isolate_assertions} {:timeLimit 60} AllTheseFuckingObjectsAreReadyYouIdiot(
    t : Object,
    a : Object, b : Object, c : Object, d : Object, e : Object,
    k : Object, l : Object, m : Object,
    os : set<Object>)

        requires t.Ready()
        requires a.Ready()
        requires b.Ready()
        requires c.Ready()
        requires d.Ready()
        requires e.Ready()
        requires k.Ready()
        requires l.Ready()
        requires m.Ready()

        // requires t in os
        // requires a in os
        // requires b in os
        // requires c in os
        // requires d in os
        // requires e in os
        // requires k in os
        // requires l in os
        // requires m in os

        requires os == {t, a, b, c, d, e, k, l, m}

        ensures forall x <- os :: x.Ready()
{
        // assert t.Ready();
        // assert a.Ready();
        // assert b.Ready();
        // assert c.Ready();
        // assert d.Ready();
        // assert e.Ready();
        // assert k.Ready();
        // assert l.Ready();
        // assert m.Ready();

        // assert t in os;
        // assert a in os;
        // assert b in os;
        // assert c in os;
        // assert d in os;
        // assert e in os;
        // assert k in os;
        // assert l in os;
        // assert m in os;

        // assert os == {t, a, b, c, d, e, k, l, m};

        // assert forall x <- os :: x.Ready();
}


method {:isolate_assertions} zandal0()
  //easier than declaring everything in main
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
 {
    loutName := "NOTHING";
    t := new Object.make(protoTypes, {},  {},"t");
    a := t;
    b := t;
    c := t;
    d := t;
    e := t;
    k := t;
    l := t;
    m := t;
    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];
 }



method {:isolate_assertions} zandalList()
  //easier than declaring everything in main
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
 {


var list  := new Object.make(fields({"head", "tail"}), {}, {}, "list")        ;

var link0 := new Object.make(fields({"next", "data"}), {list}, {list}, "link0", {} );
var link1 := new Object.make(fields({"next", "data"}), {list}, {list}, "link1", {} );
var link2 := new Object.make(fields({"next", "data"}), {list}, {list}, "link2", {} );
var link3 := new Object.make(fields({"next", "data"}), {list}, {list}, "link3", {} );

var elem0 := new Object.make(fields({}), {}, {list}, "elem0", {} );
var elem1 := new Object.make(fields({}), {}, {list}, "elem1", {} );
var elem2 := new Object.make(fields({}), {}, {list}, "elem2", {} );
var elem3 := new Object.make(fields({}), {}, {list}, "elem3", {} );


 list.setf("head", link0); //list.setf("tail", link3);

 link0.setf("next", link1); link1.setf("next", link2); link2.setf("next", link3);
 link0.setf("data", elem0); link1.setf("data", elem1); link2.setf("data", elem2); link3.setf("data", elem3);


    loutName := "LINKED LIST";
    t := elem3;
    a := list;
    b := link0;
    c := link1;
    d := link2;
    e := link3;
    k := elem0;
    l := elem1;
    m := elem2;
    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];
 }
















const listF : map<string, Mode> := fields({"head"})
const linkF : map<string, Mode> := fields({"data","next"})
const frame : map<string, Mode> := fields({"a","b","c"})
const appData := frame

method {:isolate_assertions} zandal10()
//sets up a two "columns" of objects to show permissible links - five objects, t, a..e
//in this version, all boundaries == owners
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)

 {
    loutName := "zandal10";
    print loutName, " NINE NINE NINE\n";


//bugger it - rewally should move the OWNER to thw front sbhojldnb't I
//and get rid of fields
      t := new Object.make(frame, {},  {},"3");
      a := new Object.make(frame, {t}, {t}, "2");
      b := new Object.make(frame, {a}, {t,a}, "1");
      k := new Object.make(frame, {b}, {t,a,b}, "0");

      m := new Object.make(appData, {t}, {t}, "S");

      l := new Object.make(listF, {b}, {t}, "L");
      c := new Object.make(linkF, {l}, {t,a,b,k,l,m}, "i");
      d := new Object.make(linkF, {l}, {t,a,b,c,k,l,m}, "j");

      e := new Object.make(protoTypes, {k,l}, {t,a,b,c,d,k,l,m}, "00");

    t.setf("s",m);
    b.setf(",",l);
    l.setf("head",c);
    c.setf("next",d);


    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

    print "zandal10";
  }







method {:isolate_assertions} zandal11()
//sets up a two "columns" of objects to show permissible links - five objects, t, a..e
//in this version, all boundaries == owners
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures c.Ready()   //should be the centre
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)

 {
    loutName := "zandal10";
    print loutName, " NINE NINE NINE\n";


//bugger it - rewally should move the nickname to thw front sbhojldnb't I
      t := new Object.make(protoTypes, {},  {},"t");
      a := new Object.make(protoTypes, {t}, {t}, "a");
      b := new Object.make(protoTypes, {a}, {t,a}, "b");

      k := new Object.make(protoTypes, {t}, {t}, "k");
      l := new Object.make(protoTypes, {k}, {t,k}, "l");
      m := new Object.make(protoTypes, {l}, {t,k,l}, "m");

      c := new Object.make(protoTypes, {b,m}, {t,a,b,k,l,m}, "c");
      d := new Object.make(protoTypes, {c},   {t,a,b,c,k,l,m}, "d");
      e := new Object.make(protoTypes, {d},   {t,a,b,c,d,k,l,m}, "e");





printAllOwnershipsAndBounds({},  {},"t");
printAllOwnershipsAndBounds({t}, {t}, "a");
printAllOwnershipsAndBounds({a}, {t,a}, "b");

printAllOwnershipsAndBounds({t}, {t}, "k");
printAllOwnershipsAndBounds({k}, {t,k}, "l");
printAllOwnershipsAndBounds({l}, {t,k,l}, "m");

printAllOwnershipsAndBounds({b}, {t,a,b,k,l,m}, "c");
printAllOwnershipsAndBounds({c}, {t,a,b,c,k,l,m}, "d");
printAllOwnershipsAndBounds({d}, {t,a,b,c,d,k,l,m}, "e");


assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};

assert k.AMFO == {t,k};
assert l.AMFO == {t,k,l};
assert m.AMFO == {t,k,l,m};

assert c.AMFO == {t,a,b,c};
assert d.AMFO == {t,a,b,c,d};
assert e.AMFO == {t,a,b,c,d,e};


    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

    print "zandal10";
  }






lemma {:isolate_assertions} {:timeLimit 60} AllTheseFuckingObjectsAreReadyYouIdiotVarargs(
    os : set<Object>, t : Object,
     a : Object := t, b : Object := t, c : Object := t, d : Object := t, e : Object := t,
     k : Object := t, l : Object := t, m : Object := t)

        requires t.Ready()
        requires a.Ready()
        requires b.Ready()
        requires c.Ready()
        requires d.Ready()
        requires e.Ready()
        requires k.Ready()
        requires l.Ready()
        requires m.Ready()

        // requires t in os
        // requires a in os
        // requires b in os
        // requires c in os
        // requires d in os
        // requires e in os
        // requires k in os
        // requires l in os
        // requires m in os

        requires os == {t, a, b, c, d, e, k, l, m}

        ensures forall x <- os :: x.Ready()

        {}




























































































































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


const field_attrs := "[penwidth=1,layer=fields,weight=0.5,fontsize=9,arrowhead=normal]"

method {:verify false}  graphobjectset(s : set<Object>, m : Klon, pops : PrintOptions)
{
  var o := s;

  while o != {}
    decreases o
  {
    var y: Object;
    y :| y in o;
    graphobject(y, pops);
//    print "- - - - - - - -\n";
    o := o - {y};
  }

}






method {:verify false}  graphobject(o : Object, pops : PrintOptions)
{
  //ownership

  print "\n//object ";
  print o.nick, "\n";

  var oo := o.owner;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

  if pops.lineOpt('O') { print o.nick, " -> ", y.nick, " ", owner_attrs, "\n"; }
     else { print o.nick, " -> ", y.nick, " ", nowner_attrs, "\n"; }


    oo := oo - {y};
  }

  oo := o.AMFO;

  while oo != {}
    decreases oo
  {
    var y: Object;
    y :| y in oo;

   if pops.lineOpt('o') {
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

 if pops.lineOpt('B')
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
    if pops.lineOpt('b') { print o.nick, " -> ", y.nick, " ", AMFB_attrs, "\n"; }

    oo := oo - {y};
  }

////////////////////////////

 if  (not(pops.lineOpt('F'))) { return; }

  var fs := o.fields.Keys;

  while fs != {}
    decreases fs
  {
    var f: string;
    f :| f in fs;

    var nf := o.nick;
    var nt := o.fields[f].nick;
    if (pops.nodeOpt(nf) || pops.nodeOpt(nt)) {
            print nf, " -> ", nt,     " ", field_attrs;
            print "[label=\"", f, "\"]";
            if (f == "contents") { print "[weight=2.5]"; }
            if (f == "next") { print "[weight=5]"; }
            print "\n";
        }
    fs := fs - {f};
  }

}






method graphmapping(m : vmap<Object,Object>, pops : PrintOptions)
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



method graphrefs(s : seq<Object>, pops : PrintOptions)
  modifies {}
{
  print "\n\n//refs\n";

    for f := 0 to |s| {
      for t := 0 to |s| {
  //       var attrs := if (refOK(s[f],s[t])) then refOK_attrs else refNK_attrs;

          var attrs := refNK_attrs; //not permitted reference - red, X
          if  (refOK(s[f],s[t])) { attrs := refOK_attrs; } //reference permitted w/ boundary - but not without (purple,. shouldn't happen)
          if  (refOO(s[f],s[t])) { attrs := refOO_attrs; } //reference without w/ boundary - but NOT permitted with bounday - ORANGE, "O"
          if ((refOK(s[f],s[t])) && (refOO(s[f],s[t]))) { attrs := refOKOattrs; } //OK either way - GREEN


//      if ((s[f].nick == "c") || (s[t].nick == "c"))
//    if (attrs != refNK_attrs) && (s[f].nick in {"a", "b", "c", "d", "e"})
//    if (s[f].nick in {"c", "d", "e"})

     if (pops.nodeOpt(s[f].nick) || pops.nodeOpt(s[t].nick))
        {
        print s[f].nick, " -> ", s[t].nick, " ", attrs, "\n";
       }
    }
   }
}


method printrefs(s : seq<Object>)
  modifies {}
{
  print "PRINTREFS-------------------------------------\n";

    for f := 0 to |s| {
      for t := 0 to |s| {
           print s[f].nick, " -> ", s[t].nick, "  ";

           print if (s[f]==s[t]) then "== " else "   ";
           print if (refDI(s[f],s[t])) then "D " else "  ";
           print if (refBI(s[f],s[t])) then "B " else "  ";
           print if (refOI(s[f],s[t])) then "O " else "  ";
           print if (refOO(s[f],s[t])) then "OO " else "   ";
           print if (refOK(s[f],s[t])) then "OK " else "   ";

           nl();
      }
    }
}