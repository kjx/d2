include "Klon-HighLine.dfy"

include "Example.dfy"
include "Xlone-Main.dfy"

include "Ownership-Recursive.dfy"
include "Printing.dfy"
include "Graphing.dfy"


//try this:
  //time lately run Main.dfy c OF "" "{ rank=min; 3; } {rank=same; 2;} {rank=same; 1;} {rank=max; 0; 00;} { rank=same; i; j}  rankdir="TB"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//then thid
//csplit DUMP.txt %//STARTGRAPH%; mv xx00  test.gv ; dpdf test.gv ; open test.gv.pdf
//
//should take out both SSO and split
// include "SSO.dfy" // ..ARGH!!
//
// datatype Split = Split(within : OWNR, without : OWNR, m : Klon)
//
// function split(oo : OWNR, m : Klon) : Split
//   requires forall o <- oo :: m.objectReadyInKlown(o)
// {
//   Split( (set o <- oo | inside(o, m.o)), (set o <- oo | outside(o, m.o)), m)
// }



const protoTypes : map<string, Mode> := fields({"t","a","b","c","d","e","k","l","m"})
  // map["fa":= Evil]["fb":=Evil]  //wrong but will likely do for now?








method {:verify false} Main(args : seq<string>)
 decreases * //sob
{
  print "Snick! Snack! Snock!\n";

  var gops := getGraphOptions(args);

  var t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal0();

 if (gops.graph == "7") { t,a,b,c,d,e,k,l,m,os,oq, loutName := wrangle7(); }
 if (gops.graph == "8") { t,a,b,c,d,e,k,l,m,os,oq, loutName := jandal8(); }
 if (gops.graph == "s") { t,a,b,c,d,e,k,l,m,os,oq, loutName := sandal8(); }
 if (gops.graph == "r") { t,a,b,c,d,e,k,l,m,os,oq, loutName := randal9(); }

 if (gops.graph == "9") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9(); }
 if (gops.graph == "b") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9bounded(); }
 if (gops.graph == "c") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9capsul(); }
 if (gops.graph == "d") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9tapsul(); }
 if (gops.graph == "r") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9rusty(); }
 if (gops.graph == "i") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal9inverted(); }

 if (gops.graph == "0") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal10(); }
 if (gops.graph == "1") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandal11(); }
 if (gops.graph == "l") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandalList(); }
 if (gops.graph == "t") { t,a,b,c,d,e,k,l,m,os,oq, loutName := zandalThreads(); }

 if (gops.graph == "E") { print "launch E\n"; ExampleMain(args[1..]); return; }
 if (gops.graph == "X") { print "launch X\n"; XloneMain(args[1..]); return; }



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
  print "//===\n", gops.extra,"\n//===\n";

        graphobjectset(hs, km, gops);

        if (gops.lineOpt('M')) { graphmapping(km.m, gops); }

        if (gops.lineOpt('R')) {    graphrefs(hq, gops); }


if (loutName == "zandall9rusty") {
    print "subgraph clustert {pencolor=invis; rankdir=\"RL\"; t; \n";
    print "subgraph clustera {pencolor=invis; rankdir=\"RL\"; a; \n";
    print "subgraph clusterb {pencolor=invis; rankdir=\"RL\"; b; \n";
    print "subgraph clusterc {pencolor=invis; rankdir=\"RL\"; c; \n";
    print "subgraph clusterd {pencolor=invis; rankdir=\"RL\"; d; \n";
    print "subgraph clustere {pencolor=invis; rankdir=\"RL\"; e; \n";
    print "}}}}}}\n";
    print "  b -> a [pencolor=invis;  weight=100000; ]\n";
    print "  c -> b [pencolor=invis;  weight=100000; ]\n";
    print "  d -> c [pencolor=invis;  weight=100000; ]\n";
    print "  e -> d [pencolor=invis;  weight=100000; ]\n";

}


 print "}\n\n\n";

    print "//ENDGRAPH\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";
    print "///////////////////////////////////////////////////////////////////////////////\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";

  print "\n\n//done\n";

}




///////////////////////////////////////////////////////////////////////////////////////


method {:isolate_assertions} {:timeLimit 30} wrangle7()
//sets up a full clone with sideways owner
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, name : string)
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
    name := "wrangle7";
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
//            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
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
//print "collectBounds(flatten(m_oo))= ", ffmtnickset(collectBounds(flatten(m_oo))), "\n";

print "ctxt>=flatten(m_oo)= ", (m_context >= flatten(m_oo)), "\n";
print "flatten(m_oo)>=flatten(m_mb)= ", (flatten(m_oo) >= flatten(m_mb)), "\n";
print "AllReady(m_oo)= ", AllReady(m_oo), "\n";
  //print "flatten(m_mb) >= collectBounds(flatten(m_oo))= ", flatten(m_mb) >= collectBounds(flatten(m_oo)), "\n";


    AllTheseFuckingObjectsAreReadyYouIdiot(t, a, b, c, d, e, k, l, m, os);


    assert forall x <- os :: x.Ready();



    print "wrdone7\n";
 }

///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////


method {:isolate_assertions} jandal8()
//sets up a full-done clone *reentrantly*
//otherwise compatible with wrangle - except klone owned by d  from
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m BUT now owned by **d**
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, name : string)
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
    name := "jandal8";

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
            assert nuBoundsOK({d},{d});
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k¢b"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l¢c");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
            assert nuBoundsOK({k},{k});
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
//            assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
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


method {:isolate_assertions} sandal8()
//sets up a full-done clone *with sideways partial owners*
//otherwise compatible with wrangle - except klone owned by d  from
//pivot is b, external owner is e, orig is b,c,d, d has owner c & sideowner e, clone is k l m BUT now owned by **d**
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, name : string)
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
    name := "sandal8";

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
            assert nuBoundsOK({d},{d});
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k¢b"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l¢c");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
            assert nuBoundsOK({k},{k});
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
//            assert (flatten(m_mb) >= aounds(flatten(m_oo)));
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
           os : set<Object>, oq : seq<Object>, name : string)
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
    name := "randal9";

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
     //      assert (flatten({d}) >= collectBounds(flatten({d})));
    k := new Object.make(protoTypes, {d}, {t,a,b,c,d,e}, "k"); //top of coone - of b

/// assert k.AMFO == {t,a,b,c,d,e,k};

printAllOwnershipsAndBounds({k}, {t,a,b,c,d,e,k}, "l");

assume flatten({k}) == {t,a,b,c,d,e,k};
            assert {t,a,b,c,d,e,k} >= flatten({k});
            assert flatten({k}) >= flatten({k});
            assert AllReady({k});
//          assert (flatten({k}) >= collectBounds(flatten({k})));
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
        //    assert (flatten(m_mb) >= collectBounds(flatten(m_oo)));
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
//sets up a single "row" of objects to show permissible links - five objects, t, a..d
//in this version, all boundaries == owners
//
//time lately run Main.dfy c ORB "" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//time lately run Main.dfy c ORB "c" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//csplit -s  DUMP.txt %//STARTGRAPH%  ///ENDGRAPH/ ; dpdf xx00; open xx00.pdf
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
//sets up a single "row" of objects to show permissible links - five objects, t,a..d, with c & d boundary pushed up to a.
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

k := t; l := t; m := t;

    os := {t, a, b, c, d, e};
    oq := [t, a, b, c, d, e];

    print "zandl9bounded\n";
   }












method {:isolate_assertions} zandal9capsul()
//
//aims to show a capsul
//
//time lately run Main.dfy c ORB "" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//csplit -s  DUMP.txt %//STARTGRAPH%  ///ENDGRAPH/ ; dpdf xx00; open xx00.pdf

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
    loutName := "zandall9capsul";
    print loutName, " NINE NINE NINE\n";


      t := new Object.make(protoTypes, {},  {},"t",{});
      a := new Object.make(protoTypes, {t}, {t}, "a",{});
      b := new Object.make(protoTypes, {a}, {t,a}, "b",{});
      c := new Object.make(protoTypes, {b}, {t,a,b}, "c", {});
      d := new Object.make(protoTypes, {c}, {t,a,b,c}, "d", {});
      e := new Object.make(protoTypes, {d}, {t,a,b,c,d}, "e", {});

      m := new Object.make(protoTypes, {}, {t}, "X", {});

assert t.AMFO == {t};
assert a.AMFO == {t,a};
assert b.AMFO == {t,a,b};
assert c.AMFO == {t,a,b,c};
assert d.AMFO == {t,a,b,c,d};
assert e.AMFO == {t,a,b,c,d,e};

k := t; l := t;

    os := {t, a, b, c, d, e, m};
    oq := [t, a, b, c, d, e, m];

    print "zandl9capsul";

    return;
   }

//{:timeLimit 15}
  method {:isolate_assertions}  zandal9tapsul()
//aims to show a capsule - bounding eveything at {t} not {}
//time lately run Main.dfy d ORB "" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | grep -v SATAN | tee DUMP.txt
//
//time lately run Main.dfy d ORB "" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | grep -v SATAN |  grep -v X | tee DUMP.txt
//
//csplit -s  DUMP.txt %//STARTGRAPH%  ///ENDGRAPH/ ; dpdf xx00; open xx00.pdf

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
    loutName := "zandall9tapsul";
    print loutName, " NINE NINE NINE\n";


      l := new Object.make(protoTypes, {},  {},"SATAN", {});
      k := new Object.make(protoTypes, {l},  {},"SATAN2", {l});

      t := new Object.make(protoTypes, {l},  {l},"t", {l});
      a := new Object.make(protoTypes, {t}, {l,t}, "a", {t});
      b := new Object.make(protoTypes, {a}, {l,t,a}, "b", {t});
      c := new Object.make(protoTypes, {b}, {l,t,a,b}, "c", {t});
      d := new Object.make(protoTypes, {c}, {l,t,a,b,c}, "d", {t});
      e := new Object.make(protoTypes, {d}, {l,t,a,b,c,d}, "e", {t});

      m := new Object.make(protoTypes, {a}, {t}, "X", {a});


// assert t.AMFO == {t};
// assert a.AMFO == {t,a};
// assert b.AMFO == {t,a,b};
// assert c.AMFO == {t,a,b,c};
// assert d.AMFO == {t,a,b,c,d};
// assert e.AMFO == {t,a,b,c,d,e};

// k := t; // l := t; //m := t;

    os := {m, t, a, b, c, d, e, k, l};
    oq := [m, t, a, b, c, d, e, k, l];

    print "zandl9tapsul";

    return;
   }




//{:timeLimit 15}
  method {:isolate_assertions}  zandal9rusty()
//aims to show a capsule - bounding eveything at {t} not {}
//
//.time lately run Main.dfy r  ORB "cX" "rankdir=\"RL\"; margin=0;"  --allow-warnings --no-verify | grep -v SATAN | tee DUMP.txt
//csplit -s  DUMP.txt %//STARTGRAPH%  ///ENDGRAPH/ ; dpdf xx00; open xx00.pdf

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
    loutName := "zandall9rusty";
    print loutName, " RUST RUST RUST\n";


      l := new Object.make(protoTypes, {},  {},"SATAN", {});
      k := new Object.make(protoTypes, {l},  {},"SATAN2", {l});

      t := new Object.make(protoTypes, {l},  {l},"t", {l});
      a := new Object.make(protoTypes, {t}, {l,t}, "a", {t});
      b := new Object.make(protoTypes, {a}, {l,t,a}, "b", {t});
      c := new Object.make(protoTypes, {a}, {l,t,a,b}, "c", {t});
      d := new Object.make(protoTypes, {a}, {l,t,a,b,c}, "d", {t});
      e := new Object.make(protoTypes, {a}, {l,t,a,b,c,d}, "e", {t});

      m := new Object.make(protoTypes, {a}, {t}, "X", {a});




// assert t.AMFO == {t};
// assert a.AMFO == {t,a};
// assert b.AMFO == {t,a,b};
// assert c.AMFO == {t,a,b,c};
// assert d.AMFO == {t,a,b,c,d};
// assert e.AMFO == {t,a,b,c,d,e};

// k := t; // l := t; //m := t;

    os := {m, t, a, b, c, d, e, k, l};
    oq := [m, t, a, b, c, d, e, k, l];

    print "zandl9rusty";

    return;
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

        requires os == {t, a, b, c, d, e, k, l, m}

        ensures forall x <- os :: x.Ready()
{}


method {:isolate_assertions} zandal0()
  //placebo easier than declaring everything in main
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



method {:isolate_assertions} {:timeLimit 20} zandalList()
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


var list  := new Object.make(fields({"head"}), {}, {}, "list");

var link0 := new Object.make(fields({"next", "data"}), {list}, {list}, "link0", {list} );
var link1 := new Object.make(fields({"next", "data"}), {list}, {list}, "link1", {list} );
var link2 := new Object.make(fields({"next", "data"}), {list}, {list}, "link2", {list} );
var link3 := new Object.make(fields({"next", "data"}), {list}, {list}, "link3", {list} );

var elem0 := new Object.make(fields({}), {}, {list}, "elem0", {} );
var elem1 := new Object.make(fields({}), {}, {list}, "elem1", {} );
var elem2 := new Object.make(fields({}), {}, {list}, "elem2", {} );
var elem3 := new Object.make(fields({}), {}, {list}, "elem3", {} );


 list.usetf("head", link0); //list.setf("tail", link3);

 link0.setf("next", link1); link1.setf("next", link2); link2.       setf("next", link3);
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
const frame : map<string, Mode> := fields({"a","b","c","ret"})
const appData := frame


lemma shit()
  ensures listF == fields({"head"})
  ensures "head" in listF
  ensures linkF == fields({"data","next"})
  ensures "next"  in linkF
  ensures frame == fields({"a","b","c","ret"})
  ensures appData == frame
 {}





method {:isolate_assertions} {:timeLimit 30} zandalThreads()
  //easier than declaring everything in main
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
 ensures t.Ready()
 ensures a.Ready()
 ensures b.Ready()
 ensures d.Ready()
 ensures e.Ready()
 ensures k.Ready()
 ensures l.Ready()
 ensures m.Ready()
 ensures AllReady(os)
 {
// {rank=same} subgraph cluster1 {pencolor=invis;  t1; 10; 11; 12; 13; 14; }   subgraph cluster2 { pencolor=invis; t2; 20; 21; 22; 23; } subgraph {edge [style=invis;] node [style=invis] 14 -> X;  21 -> X;}

//{rank=same} subgraph cluster1 {pencolor=invis;  t1; 10; 11; 12; 13; 14; }   subgraph cluster2 { pencolor=invis; t2; 20; 21; 22; 23; } subgraph x {edge [style=invis;] 10 -> X;  20 -> X;}  splines=ortho

//.time lately run Main.dfy c OR "" " {rank=same} subgraph cluster1 {pencolor=invis;  t1; 10; 11; 12; 13; 14; }   subgraph cluster2 { pencolor=invis; t2; 20; 21; 22; 23; } subgraph clusterX {pencolor=invis; edge [style=invis;] 14 -> X;  23 -> X;}  " --allow-warnings --no-verify

//time lately run Main.dfy 0 OF "" "{ rank=same; rankdir=TB; 3; 2; 1; 0; }   rankdir="LR"; margin=0; "



assert nuBoundsOK({},{});

var topLeft  := new Object.make(fields({}), {}, {}, "t1", {});
var topRite  := new Object.make(fields({}), {}, {}, "t2", {});

var left  := new Object.make(fields({}), {topLeft}, {topLeft},            "10", {topLeft});

var left0 := new Object.make(fields({}), {left},  flatten({left}),        "11", {left} );
var left1 := new Object.make(fields({}), {left},  flatten({left}),        "12", {left} );
var left2 := new Object.make(fields({}), {left},  flatten({left}),        "13", {left} );
var left3 := new Object.make(fields({}), {left2}, flatten({left,left2}) , "14", {left2} );

//.var world := new Object.make(fields({}), {}, {}, "world", {} );

var rite   := new Object.make(fields({}), {topRite}, {topRite}, "20", {topRite} );

var rite0 := new Object.make(fields({}), {rite}, flatten({rite}), "21", {rite} );
var rite1 := new Object.make(fields({}), {rite}, flatten({rite}), "22", {rite} );
var rite2 := new Object.make(fields({}), {rite}, flatten({rite}), "23", {rite} );

{
  var context := flatten({left3,rite2});
  var oo      := {left3,rite2};
  var mb      := {left3,rite2};
    assert context >= flatten(oo) >= flatten(mb);
    assert flatten(oo) >= flatten(mb);
//    assert forall o <- flatten(oo) :: o.Ready();
    assert nuBoundsOK(oo, mb);
 }
var xxxx := new Object.make(fields({}), {left3,rite2}, flatten({left3,rite2}), "X", {left3,rite2} );

print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";
print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";
print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";
printownership(left0);
printownership(left3);
printownership(rite0);
printownership(rite2);
printownership(xxxx);


nl();
nl();
print "refOK(left3,xxxx) = refOK(",left3.nick,",",xxxx.nick,") = ",refOK(left3,xxxx),"\n";

print "refOK(rite2,xxxx) = refOK(",rite2.nick,",",xxxx.nick,") = ",refOK(rite2,xxxx),"\n";
nl();
printrefs( [ left0, left3, rite0, rite2, xxxx ] );
nl();
print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";
print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";
print "TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP TRUMP\n";


loutName := "Threads";
t := left;
a := rite;
b := left0;
c := left1;
d := left2;
e := left3;
k := rite0;
l := rite1;
m := xxxx;
os := {t, a, b, c, d, e, k, l, m, rite2};
oq := [t, a, b, c, d, e, k, l, m, rite2];

assume {:axiom} AllReady({t, a, b, c, d, e, k, l, m, rite2});
assume AllReady(os);

}







method {:isolate_assertions} zandal9inverted()
//sets up a single "row" of objects to show permissible links - five objects, t, a..d
//in this version, all boundaries == owners
//
//time lately run Main.dfy c ORB "" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//time lately run Main.dfy c ORB "c" "rankdir=\"RL\"; margin=0; "  --allow-warnings --no-verify | tee DUMP.txt
//csplit -s  DUMP.txt %//STARTGRAPH%  ///ENDGRAPH/ ; dpdf xx00; open xx00.pdf
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
    loutName := "zandall9inverted";
    print loutName, " ENIN ENIN ENIN\n";


      t := new Object.make(protoTypes, {},  {},"t");
      a := new Object.make(protoTypes, {t}, {t}, "a", {});
      b := new Object.make(protoTypes, {a}, {t,a}, "b", {});
      c := new Object.make(protoTypes, {b}, {t,a,b}, "c", {});
      d := new Object.make(protoTypes, {c}, {t,a,b,c}, "d", {});
      e := new Object.make(protoTypes, {d}, {t,a,b,c,d}, "e", {});

    k := t;
    l := t;
    m := t;

    os := {t, a, b, c, d, e};
    oq := [t, a, b, c, d, e];

    print "zandall9 inverted!!! \n";
  }










  method {:isolate_assertions} {:timeLimit 30} zandal10()
  returns (t : Object, a : Object, b : Object , c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
     //an early attmpet at a list (actual one is in Example.dfy)
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

      l := new Object.make(listF, {b}, {t,a,b}, "L");           assert l.fieldModes == listF;
      c := new Object.make(linkF, {l}, {t,a,b,k,l,m}, "i");     assert c.fieldModes == linkF;
      d := new Object.make(linkF, {l}, {t,a,b,c,k,l,m}, "j");

      e := new Object.make(protoTypes, {k,l}, {t,a,b,c,d,k,l,m}, "00");

    t.setf("a",m);
    b.setf("a",l);

    shit();
    assume ("head" in l.fieldModes.Keys) && (l.fieldModes["head"] == Evil);
    l.setf("head",c);
    assume ("next" in c.fieldModes.Keys) && (c.fieldModes["next"] == Evil);
    assume c.Valid();
    c.setf("next",d);

    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

AllTheseFuckingObjectsAreReadyYouIdiotVarargs(os, t, a, b, c, d, e, k, l, m);

    print "zandal10";
  }







method {:isolate_assertions} zandal11()
  returns (t : Object, a : Object, b : Object, c : Object, d : Object, e : Object,
           k : Object, l : Object, m : Object,
           os : set<Object>, oq : seq<Object>, loutName : string)
   ///this is the one the shows multiple ownersjip example
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
    loutName := "zandal11   ";
    print loutName, " NINE NINE NINE\n";

//bugger it - rewally should move the nickname to thw front sbhojldnb't I
      t := new Object.make(protoTypes, {},  {},"t");
assert t.AMFO == {t};
      a := new Object.make(protoTypes, {t}, {t}, "a");
assert a.AMFO == {t,a};
      b := new Object.make(protoTypes, {a}, {t,a}, "b");
assert b.AMFO == {t,a,b};

      k := new Object.make(protoTypes, {t}, {t}, "k");
assert k.AMFO == {t,k};
      l := new Object.make(protoTypes, {k}, {t,k}, "l");
assert l.AMFO == {t,k,l};
      m := new Object.make(protoTypes, {l}, {t,k,l}, "m");
assert m.AMFO == {t,k,l,m};

      c := new Object.make(protoTypes, {b,m}, {t,a,b,    k,l,m}, "c");
assert c.AMFO == {t,a,b,c,k,l,m};
      d := new Object.make(protoTypes, {c},   {t,a,b,c,  k,l,m}, "d");
assert d.AMFO == {t,a,b,c,d,  k,l,m};
      e := new Object.make(protoTypes, {d},  {t,a,b,c,d,k,l,m}   , "e");
// assert e.AMFO == d.AMFO + {e};
// assert e.AMFO == {t,a,b,c,d,e,k,l,m};

// printAllOwnershipsAndBounds({},  {},"t");
// printAllOwnershipsAndBounds({t}, {t}, "a");
// printAllOwnershipsAndBounds({a}, {t,a}, "b");
//
// printAllOwnershipsAndBounds({t}, {t}, "k");
// printAllOwnershipsAndBounds({k}, {t,k}, "l");
// printAllOwnershipsAndBounds({l}, {t,k,l}, "m");
//
// printAllOwnershipsAndBounds({b}, {t,a,b,k,l,m}, "c");
// printAllOwnershipsAndBounds({c}, {t,a,b,c,k,l,m}, "d");
// printAllOwnershipsAndBounds({d}, {t,a,b,c,d,k,l,m}, "e");

//     assert t.AMFO == {t};
//     assert a.AMFO == {t,a};
//     assert b.AMFO == {t,a,b};
//
//     assert k.AMFO == {t,k};
//     assert l.AMFO == {t,k,l};
//     assert m.AMFO == {t,k,l,m};
//
//     assert c.AMFO == {t,a,b,c,k,l,m};
//     assert d.AMFO == {t,a,b,c,d,  k,l,m};
//     assert e.AMFO == {t,a,b,c,d,e,k,l,m};
//

    os := {t, a, b, c, d, e, k, l, m};
    oq := [t, a, b, c, d, e, k, l, m];

    print "zandal11\n";
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

        requires os == {t, a, b, c, d, e, k, l, m}

        ensures forall x <- os :: x.Ready()

        {}



























































































































/////////////////////////////////////////////////////
///// bottom of the table swill
//TODO TO LEMMERS

//
// lemma {:isolate_assertions} MapfoEQ(oo1 : OWNR, oo2 : OWNR, m : Klon)
//    requires HighCalidFragilistic(m)
//    requires forall o <- oo1  :: m.objectReadyInKlown(o)
//    requires forall o <- oo2  :: m.objectReadyInKlown(o)
//     ensures (oo1 == oo2)  ==> (mapfo(oo1,m) == mapfo(oo2,m))
//  //   ensures (oo1 == oo2) <==  (mapfo(oo1,m) == mapfo(oo2,m))
//    {}
//
//
// lemma {:isolate_assertions} MapfoEQ2(o1 : Object, o2 : Object, m : Klon)
//    requires HighCalidFragilistic(m)
//    requires m.objectReadyInKlown(o1)
//    requires m.objectReadyInKlown(o2)
//     ensures (o1 == o2)  ==> (mapfo(o1.AMFO,m) == mapfo(o2.AMFO,m))
//   //  ensures (o1 == o2) <==  (mapfo(o1.AMFO,m) == mapfo(o2.AMFO,m))
//    {}

//
// //compare eeardline!
//  function {:isolate_assertions} {:timeLimit 20} mapfo_orig(oo : OWNR, m : Klon) : SSO
//    requires forall o <- oo :: m.objectReadyInKlown(o)
//    requires oo <= m.m.Keys
//    requires HighCalidFragilistic(m)
//     ensures                 m.o.AMFO <= m.m.Keys
//     ensures forall o <- oo :: o.AMFO <= m.m.Keys
//    reads oo, m.m.Keys, m.m.Values, m.oHeap
//  {
//    if ((set o : Object <- oo | inside(o, m.o)) == {}) then ownr2sso(oo) else
//
//     (( set y : Object <- (oo - m.o.AMFO) ::
//
//        if (y.AMFO >= m.o.AMFO) then
//          (mapThruKlon( (y.AMFO - m.o.AMFO), m ) +  ( m.m[m.o].AMFO )
//          ) else ( y.AMFO
//           )
//       ) + obj2sso(m.m[m.o]))
//
//  }
