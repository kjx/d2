include "Xlone.dfy"
include "Xlone-Seed.dfy"
include "Graphing.dfy"

const protoTypesX : map<string, Mode> :=
      map["jat":= Evil]
         ["dat":= Evil]
         ["cat":= Evil]
         ["rat":= Evil]
         ["nxt":= Evil]
         ["eye":= Evil]
         ["kye":= Evil]
         ["lat":= Evil]
         ["fucker" := Evil]


method {:verify false} XloneMain(s : seq<string>)
 decreases *
{
  print "Main()\n";

 if ((|s| > 1) && (|s[1]| > 0)) {

  print "xxx", (s[1][0]), "xxx\n";

   match (s[1][0]) {
     case '0' =>  Main0();
     case '1' =>  Main1(s[2..]);
     case '5' =>  Main5(s[2..]);  //yeah "5"

     case '2' =>  Main2();
     case '3' =>  Main3();
     case '4' =>  Main4();
     case _ => {}
  }
  print "Exit, pursued by a bear\n";
 }
}


//{:verify false} //{:only}
method {:isolate_assertions} {:timeLimit 0}  makeDemo() returns (t : Object, a : Object, b : Object, os : set<Object>)
  ensures t in os
  ensures a in os
  ensures b in os
  ensures forall o <- os :: o.Ready()
//  ensures forall o <- os :: o.AllOwnersAreWithinThisHeap(os)
  ensures forall o <- os :: o.AllOutgoingReferencesWithinThisHeap(os)

  ensures forall o <- os :: o.fieldModes == protoTypesX
  ensures COK(a, os)
  ensures CallOK(os)
  ensures {"eye","kye"} <=  a.fields.Keys
  ensures {"lat", "dat", "cat", "rat"} <= a.fields["eye"].fields.Keys
{

assert CallOK({}, {}) by { NothingShallComeOfNothing({}, {}); }

t := new Object.make(protoTypesX, {}, {}, "t");
//   t
//   a      b c
//   d        cc
//   e f g h

assert t.Ready();
assert COK(t, {t}) by { reveal COK(); }

// protoTypesX 8-)
// cat dat eye fucker jat kye lat nxt rat/

assert t.AMFX == {};
assert forall o : Object <- {t}, ooo <- o.AMFO :: o.AMFO >= ooo.AMFO;

assert CallOK({t},{t}) by { reveal COK(), CallOK(); }

assert t.owner == {};
assert t.bound == {};
assert t.AMFB  == {};
assert flatten({}) == {};
assert flatten({t}) == {t};

assert proposeBounds({t}) == {};
assert myBoundsOK({t},{});
assert t.AMFB >= flatten({});


a := new Object.make(protoTypesX, {t}, {t}, "a");

b := new Object.make(protoTypesX, {t}, {t}, "b");

var c := new Object.make(protoTypesX, {t}, {t}, "c");

reveal CallOK(), COK();
assert CallOK({c}, {t,c});
var cc := new Object.make(protoTypesX, {c}, {t,c}, "cc");


reveal CallOK(), COK();
assert CallOK({a}, {t,a});
var d := new Object.make(protoTypesX, {a}, {t,a}, "d");

assert CallOK({d}, {t,a,d});
var e := new Object.make(protoTypesX, {d}, {t,a,d}, "e"); //we're gonna clone this one..?

assert CallOK({e}, {t,a,d,e});
var f := new Object.make(protoTypesX, {e}, {t,a,d,e}, "f");

assert CallOK({f},  {t,a,d,e,f});
var g := new Object.make(protoTypesX, {f},  {t,a,d,e,f},   "g");

assert CallOK({g}, {t,a,d,e,f,g});
var h := new Object.make(protoTypesX, {g}, {t,a,d,e,f,g}, "h");

assert CallOK({g}, {t,a,d,e,f,g});
var i := new Object.make(protoTypesX, {g}, {t,a,d,e,f,g}, "i");
assert CallOK({e}, {t,a,d,e,f,g,h});
var j := new Object.make(protoTypesX, {e}, {t,a,d,e,f,g,h}, "j");
assert CallOK({e}, {t,a,d,e,f,g,h});
var k := new Object.make(protoTypesX, {e}, {t,a,d,e,f,g,h}, "k");
assert CallOK({e},  {t,a,d,e,f,g,h});
var l := new Object.make(protoTypesX, {e}, {t,a,d,e,f,g,h}, "l");


assert t.Ready();

assert a.Ready();
assert b.Ready();
assert c.Ready();
assert d.Ready();
assert e.Ready();
assert f.Ready();
assert g.Ready();
assert h.Ready();
assert i.Ready();
assert j.Ready();
assert k.Ready();
assert l.Ready();

os := {t,   a, b, c, cc, d, e, f, g, h, i, j, k, l};
var ot := [t,   a, b, c, cc, d, e, f, g, h, i, j, k, l];

a.fields := map["eye":=d]["kye":=c];
c.fields := map["eye":=cc];
d.fields := map["lat":= e]["dat":=f]["cat":=g]["rat":= h];
e.fields := map["eye":=f];
f.fields := map["nxt":=l];
l.fields := map["nxt":=j];
j.fields := map["nxt":=k];

assert COK(a,os);

assert d.AllFieldsAreDeclared();
assert d.AllFieldsContentsConsistentWithTheirDeclaration();
assert d.AllOutgoingReferencesAreOwnership(os);

print "REALLY REALLY DAVE? ", d.AllOutgoingReferencesAreOwnership(os),"\n";
print "why am I printing out all the fields of object d? - \n";
printobjfields(d);


assert d.AllOutgoingReferencesAreOwnership(os);

assert d.AllOutgoingReferencesWithinThisHeap(os);
assert COK(d,os);

assert CallOK(os);

}

// {:verify false} //{:only}
method {:verify false} Main0()
  decreases *
{

print "Main0\n";

var t, a, b, os := makeDemo();
var orig := os;
var oq := set2seq(os);

assert forall o : Object <- os :: (o.Ready());

print "|os| == ", |os|, "\n";

print "+++++++++++++\n";
print "original store (os)\n";
print "+++++++++++++\n";
printobjectset(os);
print "+++++++++++++\n";

print "done setup\n";

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// var ros := walkies(d, d, isomap, os);

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

print "about to Xlone a\n";

assert CallOK(os);
assert COK(a, os);
assert CallOK(a.owner,os) by { reveal COK(), CallOK(); }

assert forall o <- os :: (o.Ready());
//assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));

assert forall x <- os ::  x.AllOutgoingReferencesWithinThisHeap(os);


////////////////////////////////////////////////////////////

var k := a;

var m : Klon := sheepKlon(k, {b}, os);


//
//
//
//
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
//
//
//       print "\n\n//STARTGRAPH\n";
//       print "////////////////////////////////////////////////////////////////////////////////\n";
//       print "////////////////////////////////////////////////////////////////////////////////\n";
//       print "////////////////////////////////////////////////////////////////////////////////\n";
//       print "//  ", "CLONEY=WONEY", "\n";
//
// //  gops := GraphOptions(graph, lines, nodes, extra);
// var gops := GraphOptions("",    "OF",  "",    "");
//
//   print "\n\ndigraph dafny {\n";
//   print "   rankdir=\"BT\";\n";
//   print "   layers=\"mapping:fields:owner:bound:amfo:bg\";\n";
//   print "   node [shape=box]\n\n";
//
//   graphobjectset(os, m, gops);
//
//   graphmapping(m.m, gops);
//
//  //   graphrefs(os, gops);
//
//  print "}\n\n\n";
//
//     print "//ENDGRAPH\n";
//     print "////////////////////////////////////////////////////////////////////////////////\n";
//     print "///////////////////////////////////////////////////////////////////////////////\n";
//     print "////////////////////////////////////////////////////////////////////////////////\n";
//
//
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
// /// PREGRAPH
//
//

os := m.hns();

/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH


      print "\n\n//STARTGRAPH\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "//  ", "CLONEY=WONEY", "\n";

//  gops := GraphOptions(graph, lines, nodes, extra);
var gops := GraphOptions("",    "OF",  "",    "");

  print "\n\ndigraph dafny {\n";
  print "   rankdir=\"BT\";\n";
  print "   layers=\"mapping:fields:owner:bound:amfo:bg\";\n";
  print "   node [shape=box]\n\n";

  graphobjectset(os, m, gops);

  graphmapping(m.m, gops);

 //   graphrefs(os, gops);

 print "}\n\n\n";

    print "//ENDGRAPH\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";
    print "///////////////////////////////////////////////////////////////////////////////\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";


/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH









assert m.Calid();
assert m.ownersInKlown(a);

print "+++++++++++++\n";
print "original store (orig)\n";
print "+++++++++++++\n";
printobjectset(orig);
print "+++++++++++++\n";
print "clones rm.Values - orig\n";
print "+++++++++++++\n";
printobjectset(m.m.Values - orig);
print "+++++++++++++\n";
printmapping(m.m);
//
// print "\n\n\n\nwaiting...\\n\n";
//
// var context : set<Object> := rm.oHeap + rm.ns();
// assert os <= context;
// assert rm.m.Values <= context;
//
// var oz := set2seq(context);
//
//
//
// // var result : bool :=  jeSuisClone(a, rm, context);
//
// var result : bool :=  istEinKlon(c, rm, context);
//
// print "istEinKlon = ", result;
//
// print "\n\n";
//
// print "\n$$$$$$$$$$$$$$$$$$\n";
// //                HeyHoLetsGo(rm);
//
//
//       for i := 0 to |oz|
//        {
//          printobj(oz[i]);
//          print "  AMFO==";
//          printown(oz[i].AMFO);
//
//         var oo := oz[i].AMFO;
//         if (oo >= rm.o.AMFO) { print "  (inside)\n"; } else { print "  (outside)\n";}
//
//         if (oz[i] in rm.m.Keys)  {
//             print "  mapsto ";
//             printobj(rm.m[oz[i]]);
//
//             if (oz[i].AMFO <= rm.m.Keys)
//               {
//                 print "\n mapThruKlon ==";
//                 printown( mapThruKlon(oo, rm));
//                 print "\n   calc      ==";
//                 // printown( calculateClownership(oo, rm));
//                 // print "\n   mTKlown   ==";
//                 // printown( mapThruKlown(oo, rm));
//                 // print "\n   mTKlownII ==";
//                 // printown( mapThruKlownIfInside(oo, rm));
//                 // print "\n   OLDmapTKl ==";
//                 // printown( OLDmapThruKlown(oo, rm));
//               }
//              else
//              {
//               print "  but AMFO not in Keys??? extra bits:";
//               printown( oz[i].AMFO - rm.m.Keys );
//              }
//             print "\n";
//         }
//         else {
//           print "  NOT IN rm.m\n";
//         }
//
//        }
//
//

print "\n$$$$$$$$$$$$$$$$$$\n";


print "\nDone\n";
}
// end


method {:verify false} Main1(s : seq<string>)
 decreases *
 {


print "Main1\n";

for x := 0 to |s| {
  print x, "  ", s[x],"\n";
}

var t := new Object.make(protoTypesX, {}, {}, "kernel");
var a := new Object.make(protoTypesX, {t}, {t},         "screen");
var b := new Object.make(protoTypesX, {a}, {t},         "window1");
var c := new Object.make(protoTypesX, {b}, {t},         "textbox");
var d := new Object.make(protoTypesX, {a}, {a,t},       "font");
var e := new Object.make(protoTypesX, {a}, {a,t},       "window2");
var f := new Object.make(protoTypesX, {b}, {t,a,c},     "text");
var g := new Object.make(protoTypesX, {f}, {t,a,c,f},   "line1");
var h := new Object.make(protoTypesX, {f}, {t,a,c,f,g}, "line2");
var i := new Object.make(protoTypesX, {f}, {t,a,d},     "line3");
// var j := new Object.make(protoTypesX, {c}, {t,a,d},     "j");
// var k := new Object.make(protoTypesX, {c}, {t,a,e},     "k");
// var l := new Object.make(protoTypesX, {c}, {t,a,e},     "l");

a.fields := map["font":=d,"win":=b];
b.fields := map["next":=e,"sub":=c];
c.fields := map["font":=d,"text":=f];
f.fields := map["nxt":=g,"1":=g,"2":=h,"3":=i,"fnt":=d];
g.fields := map["nxt":=h];
h.fields := map["nxt":=i];



var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i };//, j, k, l };
var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i ];//, j, k, l ];

print "|os| == ", |os|, "\n";
var orig := os;

// print "+++++++++++++\n";
// print "original store (os)\n";
// print "+++++++++++++\n";
// printobjectset(os);
// print "+++++++++++++\n";

print "done setup\n";

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// var ros := walkies(d, d, isomap, os);

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

print "about to Xlone a\n";

assert CallOK(os);
assert COK(a, os);
assert CallOK(a.owner,os) by { reveal COK(), CallOK(); }

assert forall o <- os :: (o.Ready());
//assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));

assert forall x <- os ::  x.AllOutgoingReferencesWithinThisHeap(os);

/////////////////////////////////////////////////////       ///////

var m : Klon :=  sheepKlon(t,{t},os);

if ((|s| > 0) && (|s[0]| > 0)) {
    if (s[0][0] == 'd')  // deeep
        {
      var k := a;
      m := sheepKlon(k, {t}, os);
      // var v := new Object.make(k.fieldModes, m.clowner, m.oHeap, "clone_of_" + k.nick, m.clbound);
      // m := m.CalidKV(k,v);
      // var rm := Xlone_All_Fields(k,v,m);
      // var ra := v;
      // m := rm;
        }
      else if (s[0][0] == 's')  // shallow
      {
      var k := f;
      m := sheepKlon(k, {t}, os);
      // var v := new Object.make(k.fieldModes, m.clowner, m.oHeap, "clone_of_" + k.nick, m.clbound);
      // m := m.CalidKV(k,v);
      // v.fields :=   k.fields;
      // var rm := m;
      // var ra := v;
      // m := rm;
      }
      else if (s[0][0] == 'k')  // sheep *k*lone
      {
      var k := f;
      m := sheepKlon(k, {b}, os);
      // var v := new Object.make(k.fieldModes, m.clowner, m.oHeap, "clone_of_" + k.nick, m.clbound);
      // m := m.CalidKV(k,v);
      // var rm := Xlone_All_Fields(k,v,m);
      //   var ra := v;
      // m := rm;
      }  else if (s[0][0] == 'n')  // noclone
      { print "//noclone\n"; }
 }






os := m.hns();

/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH


      print "\n\n//STARTGRAPH\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "//  ", "CLONEY=WONEY", "\n";

//  gops := GraphOptions(graph, lines, nodes, extra);
var gops := GraphOptions("",    "OF",  "",    "");

  print "\n\ndigraph dafny {\n";
  print "   rankdir=\"TB\";\n";
  print "   layers=\"mapping:fields:owner:bound:amfo:bg\";\n";
  print "   node [shape=box]\n\n";

  print "{rank=same}\n";

  //pencolor=invis;

  print "subgraph cluster1 {pencolor=invis; kernel; subgraph cluster11 {pencolor=invis; screen; window1; textbox; window2 font} }\n";
  print "subgraph cluster2 {pencolor=invis; text; line1; line2; line3;}\n";

  graphobjectset(os, m, gops);

  graphmapping(m.m, gops);

 //   graphrefs(os, gops);

 print "}\n\n\n";

    print "//ENDGRAPH\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";
    print "///////////////////////////////////////////////////////////////////////////////\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";


/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH





//
//
//
//
// assert a in rm.m.Keys;
// assert rm.from(m);
// assert m.Calid();
// assert m.ownersInKlown(a);
//
// print "+++++++++++++\n";
// print "original store (orig)\n";
// print "+++++++++++++\n";
// printobjectset(orig);
// print "+++++++++++++\n";
// print "clones rm.Values - orig\n";
// print "+++++++++++++\n";
// printobjectset(rm.m.Values - orig);
// print "+++++++++++++\n";
// printmapping(rm.m);



// print "\n\n\n\nwaiting...\\n\n";
//
// var context : set<Object> := rm.oHeap + rm.ns();
// assert os <= context;
// assert rm.m.Values <= context;
//
// var oz := set2seq(context);
//
//
//
// // var result : bool :=  jeSuisClone(a, rm, context);
//
// var result : bool :=  istEinKlon(c, rm, context);
//
// print "istEinKlon = ", result;
//
// print "\n\n";
//
// print "\n$$$$$$$$$$$$$$$$$$\n";
// //                HeyHoLetsGo(rm);
//
//
//       for i := 0 to |oz|
//        {
//          printobj(oz[i]);
//          print "  AMFO==";
//          printown(oz[i].AMFO);
//
//         var oo := oz[i].AMFO;
//         if (oo >= rm.o.AMFO) { print "  (inside)\n"; } else { print "  (outside)\n";}
//
//         if (oz[i] in rm.m.Keys)  {
//             print "  mapsto ";
//             printobj(rm.m[oz[i]]);
//
//             if (oz[i].AMFO <= rm.m.Keys)
//               {
//                 print "\n mapThruKlon ==";
//                 printown( mapThruKlon(oo, rm));
//                 print "\n   calc      ==";
//                 // printown( calculateClownership(oo, rm));
//                 // print "\n   mTKlown   ==";
//                 // printown( mapThruKlown(oo, rm));
//                 // print "\n   mTKlownII ==";
//                 // printown( mapThruKlownIfInside(oo, rm));
//                 // print "\n   OLDmapTKl ==";
//                 // printown( OLDmapThruKlown(oo, rm));
//               }
//              else
//              {
//               print "  but AMFO not in Keys??? extra bits:";
//               printown( oz[i].AMFO - rm.m.Keys );
//              }
//             print "\n";
//         }
//         else {
//           print "  NOT IN rm.m\n";
//         }
//
//        }
//
//

print "\n$$$$$$$$$$$$$$$$$$\n";


print "\nDone\n";

}
// end






























method {:verify false} Main5(s : seq<string>)
 decreases *
 {

print "Main5\n";

for x := 0 to |s| {
  print x, "  ", s[x],"\n";
}

var t := new Object.make(protoTypesX, {}, {}, "t");

var l := new Object.make(protoTypesX, {t}, {t},       "l");
var r := new Object.make(protoTypesX, {t}, {t},       "r");

var o := new Object.make(protoTypesX, {l}, {t,l},     "o");
var p := new Object.make(protoTypesX, {l}, {t,l},     "p");
var q := new Object.make(protoTypesX, {l}, {t,l},     "q");

var b := new Object.make(protoTypesX, {p}, {t,l,p},     "b", {l});
var a := new Object.make(protoTypesX, {b}, {t,l,p,b},   "a", {l});
var c := new Object.make(protoTypesX, {b}, {t,l,p,b},   "c", {l});

a.fields := map["x":=o];
b.fields := map["x":=q,"c":=c];
c.fields := map["x":=q,"c":=a];


var os : set<Object> := {t,  l, r, o, p, q, a, b, c};
var oq : seq<Object> := [t,  l, r, o, p, q, a, b, c];

print "|os| == ", |os|, "\n";
var orig := os;

// print "+++++++++++++\n";
// print "original store (os)\n";
// print "+++++++++++++\n";
// printobjectset(os);
// print "+++++++++++++\n";

print "done setup\n";

//assert isIsomorphicMappingOWNED(d, d, isomap, os);

// var ros := walkies(d, d, isomap, os);

print "%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%\n";

print "about to Xlone a\n";

assert CallOK(os);
assert COK(a, os);
assert CallOK(a.owner,os) by { reveal COK(), CallOK(); }

assert forall o <- os :: (o.Ready());
//assert forall o <- os :: (o.AllOwnersAreWithinThisHeap(os));

assert forall x <- os ::  x.AllOutgoingReferencesWithinThisHeap(os);

/////////////////////////////////////////////////////       ///////

var m : Klon := sheepKlon(t,{t},os);

//
//       var k := b;
//       m := seed(k, {r}, os);
//       var v := new Object.make(k.fieldModes, m.clowner, m.oHeap, "clone_of_" + k.nick, m.clbound);
//       m := m.CalidKV(k,v);
//       var rm := Xlone_All_Fields(k,v,m);
//       m := rm;




os := m.hns();
var ot := set2seq(os);

/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH


      print "\n\n//STARTGRAPH\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "////////////////////////////////////////////////////////////////////////////////\n";
      print "//  ", "CLONEY=WONEY", "\n";

//  gops := GraphOptions(graph, lines, nodes, extra);
var gops := GraphOptions("",    "OBR",  "",    "");

  print "\n\ndigraph dafny {\n";
  print "   rankdir=\"BT\";\n";
  print "   layers=\"mapping:fields:owner:bound:amfo:bg\";\n";
  print "   node [shape=box]\n\n";

  print "{rank=same}\n";

  //pencolor=invis;

  print "subgraph cluster1 {pencolor=invis; rankdir=\"LR\";  t; r;\n";
  print "   subgraph cluster11 {pencolor=invis; l;\n";
  print "     subgraph cluster111 {pencolor=invis; o; q;\n";
  print "        subgraph cluster3 { p;   \n";
  print               "subgraph cluster2 {pencolor=invis; rankdir=\"RL\"; {rank=sink; b;}  subgraph cluster21 { a; c;}}}}}}\n";

if ((b in m.m.Keys) && (m.m[b].nick == "clone_of_b")) {
  print "subgraph cluster3 {pencolor=invis; rankdir=\"TB\"; {rank=sink; clone_of_b;}  subgraph cluster21 {pencolor=invis; rankdir=\"TB\"; clone_of_a; clone_of_c;}}\n";
}

  graphobjectset(os, m, gops);

  graphmapping(m.m, gops);

  graphrefs(ot, gops);  //was commennt out earlier

 print "}\n\n\n";

    print "//ENDGRAPH\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";
    print "///////////////////////////////////////////////////////////////////////////////\n";
    print "////////////////////////////////////////////////////////////////////////////////\n";


/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH
/// POSTGRAPH





//
//
//
//
// assert a in rm.m.Keys;
// assert rm.from(m);
// assert m.Calid();
// assert m.ownersInKlown(a);
//
// print "+++++++++++++\n";
// print "original store (orig)\n";
// print "+++++++++++++\n";
// printobjectset(orig);
// print "+++++++++++++\n";
// print "clones rm.Values - orig\n";
// print "+++++++++++++\n";
// printobjectset(rm.m.Values - orig);
// print "+++++++++++++\n";
// printmapping(rm.m);



// print "\n\n\n\nwaiting...\\n\n";
//
// var context : set<Object> := rm.oHeap + rm.ns();
// assert os <= context;
// assert rm.m.Values <= context;
//
// var oz := set2seq(context);
//
//
//
// // var result : bool :=  jeSuisClone(a, rm, context);
//
// var result : bool :=  istEinKlon(c, rm, context);
//
// print "istEinKlon = ", result;
//
// print "\n\n";
//
// print "\n$$$$$$$$$$$$$$$$$$\n";
// //                HeyHoLetsGo(rm);
//
//
//       for i := 0 to |oz|
//        {
//          printobj(oz[i]);
//          print "  AMFO==";
//          printown(oz[i].AMFO);
//
//         var oo := oz[i].AMFO;
//         if (oo >= rm.o.AMFO) { print "  (inside)\n"; } else { print "  (outside)\n";}
//
//         if (oz[i] in rm.m.Keys)  {
//             print "  mapsto ";
//             printobj(rm.m[oz[i]]);
//
//             if (oz[i].AMFO <= rm.m.Keys)
//               {
//                 print "\n mapThruKlon ==";
//                 printown( mapThruKlon(oo, rm));
//                 print "\n   calc      ==";
//                 // printown( calculateClownership(oo, rm));
//                 // print "\n   mTKlown   ==";
//                 // printown( mapThruKlown(oo, rm));
//                 // print "\n   mTKlownII ==";
//                 // printown( mapThruKlownIfInside(oo, rm));
//                 // print "\n   OLDmapTKl ==";
//                 // printown( OLDmapThruKlown(oo, rm));
//               }
//              else
//              {
//               print "  but AMFO not in Keys??? extra bits:";
//               printown( oz[i].AMFO - rm.m.Keys );
//              }
//             print "\n";
//         }
//         else {
//           print "  NOT IN rm.m\n";
//         }
//
//        }
//
//

print "\n$$$$$$$$$$$$$$$$$$\n";


print "\nDone\n";

}
// end
























method {:verify false} Main2() {

print "main showing RefOK etc\n";

var t := new Object.make(protoTypesX, {}, {}, "t");

//   t
//   a       b       c
//   d  e            f
//  ij kl            g
//                   h

var a := new Object.make(protoTypesX, {t}, {t},         "a");
var b := new Object.make(protoTypesX, {t}, {t},         "b");
var c := new Object.make(protoTypesX, {t}, {t},         "c");
var d := new Object.make(protoTypesX, {a}, {a,t},       "d");
var e := new Object.make(protoTypesX, {a}, {a,t},       "e");
var f := new Object.make(protoTypesX, {c}, {t,a,c},     "f");
var g := new Object.make(protoTypesX, {f}, {t,a,c,f},   "g");
var h := new Object.make(protoTypesX, {g}, {t,a,c,f,g}, "h");
var i := new Object.make(protoTypesX, {c}, {t,a,d},     "i");
var j := new Object.make(protoTypesX, {c}, {t,a,d},     "j");
var k := new Object.make(protoTypesX, {c}, {t,a,e},     "k");
var l := new Object.make(protoTypesX, {c}, {t,a,e},     "l");


var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l };
var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

//   for i := 0 to |oq|
//     {
//       var o : Object := oq[i];
//
//       assert o.Ready();
//
//       print "\n=============================================================\n";
//       print "=============================================================\n";
//
//       printobject(o);
//     }
//    print "\n\n";


print "\n\nOwnership - Inside =========================\n";
print "Ownership - Inside =========================\n\n";

//       for i := 0 to |oq|
//        {
//          printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (inside(oq[i],oq[j])) then "i" else " ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+"<="+oq[j].nick) else "    ");
         print " ";
}
         print "\n";

       }
  print "\n\n";
  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";





var matrix : seq<string>:= [
"x            ",
"xx           ",
"x x          ",
"x  x         ",
"xx  x        ",
"xx   x       ",
"x  x  x      ",
"x  x  xx     ",
"x  x  xxx    ",
"x  x     x   ",
"x  x      x  ",
"x  x       x ",
"x  x        x"
];

  print "\n\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (inside(oq[i],oq[j]), (matrix[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";



print "ownerInsideOwner ownerInsideOwner ownerInsideOwner ownerInsideOwner\n";
print "ownerInsideOwner ownerInsideOwner ownerInsideOwner ownerInsideOwner\n";

      for i := 0 to |matrix|
       {
         for j := 0 to |matrix[0]|
          {
         print match (ownerInsideOwner(oq[i].AMFO,oq[j].AMFO), (matrix[i][j]) )
           case (true,  'x') => "o"  //OK
           case (true,  ' ') => "M"  //missing
           case (false, ' ') => " "
           case (false, 'x') => "F"; //false posiutive, ie FUCKED
          }
         print "\n";
       }
print "\n";


print "FUCKED FUCKED FUCKED FUCKED FUCKED\n";
print "FUCKED FUCKED FUCKED FUCKED FUCKED\n";

print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}

//uncomment to print out a new "matrix"
//
//
//   print "\n[\n";
//
//       for i := 0 to |oq|
//        {
//          print "\"";
//
//          for j := 0 to |oq|
// {
//          print (if (refOK(oq[i],oq[j])) then ("x") else " ");
// }
//          if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}
//
//        }
// print "]\n";


var keanu :=
[
"xxxx         ",
"xxxxxx       ",
"xxxx         ",
"xxxx  x  xxxx",
"xxxxxx       ",
"xxxxxx       ",
"xxxx  xx xxxx",
"xxxx  xxxxxxx",
"xxxx  xxxxxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx"
];


  print "\n\n";

      for i := 0 to |keanu|
       {
         for j := 0 to |keanu[0]|
          {
         print match (refOK(oq[i],oq[j]), (keanu[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";





}

// end main2




method {:verify false} Main3() {

print "main poking at bound etc\n";
print "Object G has bound at object t\n";

var t := new Object.make(protoTypesX, {}, {}, "t");

//   t
//   a       b       c
//   d  e            f
//  ij kl            g
//                   h

var a := new Object.make(protoTypesX, {t}, {t},         "a");
var b := new Object.make(protoTypesX, {t}, {t},         "b");
var c := new Object.make(protoTypesX, {t}, {t},         "c");
var d := new Object.make(protoTypesX, {a}, {a,t},       "d");
var e := new Object.make(protoTypesX, {a}, {a,t},       "e");
var f := new Object.make(protoTypesX, {c}, {t,a,c},     "f");
var g := new Object.make(protoTypesX, {f}, {t,a,c,f},   "G", {t});
var h := new Object.make(protoTypesX, {g}, {t,a,c,f,g}, "H", {g});
var i := new Object.make(protoTypesX, {d}, {t,a,d},     "i");
var j := new Object.make(protoTypesX, {d}, {t,a,d},     "j");
var k := new Object.make(protoTypesX, {e}, {t,a,e},     "k");
var l := new Object.make(protoTypesX, {e}, {t,a,e},     "l");

print "a->d : ", refOK(a,d), "\n";
print "a->e : ", refOK(a,e), "\n";

var os : set<Object> := {t,   a, b, c, d, e, f, g, h, i, j, k, l };
var oq : seq<Object> := [t,   a, b, c, d, e, f, g, h, i, j, k, l ];

assert forall o <- oq :: o.Ready();

print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}




  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";


var keanu :=
[
"xxxx         ",
"xxxxxx       ",
"xxxx         ",
"xxxx  x  xxxx",
"xxxxxx       ",
"xxxxxx       ",
"xxxx  xx xxxx",
"xxxx  xxxxxxx",
"xxxx  xxxxxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx",
"xxxx  x  xxxx"
];


  print "\n\n";

      for i := 0 to |keanu|
       {
         for j := 0 to |keanu[0]|
          {
         print match (refOK(oq[i],oq[j]), (keanu[i][j]) )
           case (true,  'x') => "o"  //OK, true positive
           case (true,  ' ') => "F"  //false positive
           case (false, ' ') => " "  //OK, true negative
           case (false, 'x') => "M"; //false negative
          }
         print "\n";
       }
print "\n";


print "\nDone\n\n";





} //end Main3


method {:verify false} Main4() {

print "long and thin study of bounds\n";

var t := new Object.make(protoTypesX, {}, {}, "t");  //top;

print "   t\n";

var depth  : nat := 5;
var prev   := t;
var os := {t};
var oq := [t];

var o2 : Object? := null;

for i := 0 to depth
{
  var spine := new Object.make(protoTypesX, {prev}, os, "o"+natToString(i));

  if (i == 1)  {o2 := prev;}

  var pbound := {prev};
  if (i == 2) {pbound := {};}
  if (i == 3) {pbound := {o2};}

  var peer  := new Object.make(protoTypesX, {prev}, os, "p"+natToString(i), pbound);
  prev := spine;

  os := os + {spine, peer};
  oq := oq + [spine, peer];
}

print "Ownership - Directly Inside =========================\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print " owns ";

         for j := 0 to |oq|
{
         print (if (directlyInside(oq[j],oq[i])) then (oq[j].nick+" ") else "");
}
         print "\n";

       }
  print "\n\n";


print "Owners & Bound =========================\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);

         print " owner=";
         for j := 0 to |oq|
         {
         print (if (directlyInside(oq[i],oq[j])) then (oq[j].nick+" ") else "");
         }

         print " bound=";
         for j := 0 to |oq|
         {
         print (if (directlyBounded(oq[i],oq[j])) then (oq[j].nick+" ") else "");
         }

         print "\n";

       }
  print "\n\n";




//
//
// print "Ownership - Directly Inside =========================\n\n";
//
//       for i := 0 to |oq|
//        {
//         print oq[i].nick;
// //         printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (directlyInside(oq[i],oq[j])) then (oq[i].nick+"<<"+oq[j].nick) else "      ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";


print "Ownership - Inside =========================\n\n";

//       for i := 0 to |oq|
//        {
//          printobj(oq[i]);
//          print "  ";
//
//          for j := 0 to |oq|
// {
//          print (if (inside(oq[i],oq[j])) then "i" else " ");
//          print " ";
// }
//          print "\n";
//
//        }
//   print "\n\n";

      for i := 0 to |oq|
       {
        print oq[i].nick;
//         printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (inside(oq[i],oq[j])) then (oq[i].nick+"<="+oq[j].nick) else "      ");
         print " ";
}
         print "\n";

       }
  print "\n\n";



print "\n\nREFERENCE OK refOK =========================\n";
print "REFERENCE OK refOK =========================\n\n";

      for i := 0 to |oq|
       {
         print oq[i].nick;
         //printobj(oq[i]);
         print "  ";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then (oq[i].nick+"->"+oq[j].nick) else "    ");
         print " ";
}
print "\n";
}




  print "\n[\n";

      for i := 0 to |oq|
       {
         print "\"";

         for j := 0 to |oq|
{
         print (if (refOK(oq[i],oq[j])) then ("x") else " ");
}
         if (i < (|oq|-1))  { print "\",\n";} else { print "\"\n";}

       }
print "]\n";


} //end Main4
