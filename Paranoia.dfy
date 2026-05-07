include "Object.dfy"
include "Printing.dfy"
include "Ownership-Recursive.dfy"

method Main(args : seq<string>)
{




print "////////////////////////////////////////////////\n";
print "correct\n\n";

Chain(args);
MainTop(args);
MainMid(args);

print "////////////////////////////////////////////////\n";
print "wrong\n\n";

MainWrong1(args);
MainWrong2(args);

print "////////////////////////////////////////////////\n";
print "done\n";
}


method  {:isolate_assertions} Chain(args : seq<string>)
{
  print "Chain\n";

  var T := new Object.make(fields({"fld"}), {},  {},            "T", {});
  var t := new Object.make(fields({"fld"}), {T}, {T},           "t", {T});

  var a := new Object.make(fields({"fld"}), {t}, {T,t},         "a", {t});
  var b := new Object.make(fields({"fld"}), {a}, {T,t,a},       "b", {a});
  var c := new Object.make(fields({"fld"}), {b}, {T,t,a,b},     "c", {b});
  var d := new Object.make(fields({"fld"}), {c}, {T,t,a,b,c},   "d", {c});
  var e := new Object.make(fields({"fld"}), {d}, {T,t,a,b,c,d}, "e", {d});

  printbounds(T);
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}



method  {:isolate_assertions} MainWrong1(args : seq<string>)
{
  print "Wrong1\n";

  var T := new Object.make(fields({"fld"}), {},  {},            "T", {});
  var t := new Object.make(fields({"fld"}), {T}, {T},           "t", {T});

  var a := new Object.make(fields({"fld"}), {t}, {T,t},         "a", {t});
  var b := new Object.make(fields({"fld"}), {a}, {T,t,a},       "b", {});
  var c := new Object.make(fields({"fld"}), {b}, {T,t,a,b},     "c", {b});
  var d := new Object.make(fields({"fld"}), {c}, {T,t,a,b,c},   "d", {t});
  var e := new Object.make(fields({"fld"}), {d}, {T,t,a,b,c,d}, "e", {d});

  printbounds(T);
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}




method  {:isolate_assertions} MainWrong2(args : seq<string>)
{
  print "Wrong2\n";

  var T := new Object.make(fields({"fld"}), {},  {},            "T", {});
  var t := new Object.make(fields({"fld"}), {T}, {T},           "t", {T});

  var a := new Object.make(fields({"fld"}), {t}, {T,t},         "a", {t});
  var b := new Object.make(fields({"fld"}), {a}, {T,t,a},       "b", {a});
  var c := new Object.make(fields({"fld"}), {b}, {T,t,a,b},     "c", {T});
  var d := new Object.make(fields({"fld"}), {c}, {T,t,a,b,c},   "d", {c});
  var e := new Object.make(fields({"fld"}), {d}, {T,t,a,b,c,d}, "e", {d});

  printbounds(T);
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}


method  {:isolate_assertions} MainTop(args : seq<string>)
{
  print "Top\n";

  var T := new Object.make(fields({"fld"}), {},  {},            "T", {});
  var t := new Object.make(fields({"fld"}), {T}, {T},           "t", {});
  var a := new Object.make(fields({"fld"}), {t}, {T,t},         "a", {});
  var b := new Object.make(fields({"fld"}), {a}, {T,t,a},       "b", {});
  var c := new Object.make(fields({"fld"}), {b}, {T,t,a,b},     "c", {});
  var d := new Object.make(fields({"fld"}), {c}, {T,t,a,b,c},   "d", {});
  var e := new Object.make(fields({"fld"}), {d}, {T,t,a,b,c,d}, "e", {});

  printbounds(T);
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}



method  {:isolate_assertions} MainMid(args : seq<string>)
{
  print "Yaunch\n";  //

  var T := new Object.make(fields({"fld"}), {},  {},            "T", {});
  var t := new Object.make(fields({"fld"}), {T}, {T},           "t", {T});
  var a := new Object.make(fields({"fld"}), {t}, {T,t},         "a", {t});
  var b := new Object.make(fields({"fld"}), {a}, {T,t,a},       "b", {a});
  var c := new Object.make(fields({"fld"}), {b}, {T,t,a,b},     "c", {});
  var d := new Object.make(fields({"fld"}), {c}, {T,t,a,b,c},   "d", {});
  var e := new Object.make(fields({"fld"}), {d}, {T,t,a,b,c,d}, "e", {});

  printbounds(T);
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}



//
// method  {:isolate_assertions} XMain(args : seq<string>)
// {
//     print "Xaunch\n";
//
//     var T :=     new Object.make(fields({"fld"}), {},   {},         "T");
//     var t :=     new Object.make(fields({"fld"}), {T},  {T},        "t");
//     var azero := new Object.make(fields({"fld"}), {t},  {T,t},      "azero", {});
//     var atttt := new Object.make(fields({"fld"}), {t},  {T,t},      "atttt", {T});
//     var ateee := new Object.make(fields({"fld"}), {t},  {T,t},      "ateee", {t});
//
//
//
//     printbounds(T);
//     printbounds(t);
//
//     printbounds(azero);
//     printbounds(ateee);
//
//     print "done\n";
// }
//
//
//






method printbounds(o : Object)
{
      printobj(o);
      print "\n  bound:";
      printset(o.bound);
      print "\n  owner:";
      printset(o.owner);
      print "\n    AMFB:";
        printset(o.AMFB);
      print "\n    AMFX:";
        printset(o.AMFX);
        if (not(o.AMFX >= o.AMFB)) {print "  FUCKED AMFX";}
      print "\n    AMFO:";
        printset(o.AMFO);
        if (not(o.AMFO == o.AMFX+{o})) {print "  FUCKED AMFO";}
      print "\n      proposed bounds:";
        printset(froposeBounds(o.owner));
//        if (nuBoundsOK(o.owner, froposeBounds(o.self))) {print " ok";} else {print "REALLY REWALLYU FUCKED!!!";}


      var oo := o.owner;
      var mb := o.bound;

      print "\n      (flatten(oo) >= flatten(mb)) ", (flatten(oo) >= flatten(mb));
      print "\n   ditto ((o.AMFB) >= flatten(mb)) ", (flatten(oo) >= flatten(mb)) && (forall o <- oo :: ((o.AMFB+{o}) >= flatten(mb)));
      print "\n               only of o.AMFB > {} ", (flatten(oo) >= flatten(mb)) && (forall o <- oo :: (o.AMFB > {}) ==> ((o.AMFB+{o}) >= flatten(mb)));
      print "\n               only if o.AMFX > {} ", (flatten(oo) >= flatten(mb)) && (forall o <- oo :: (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb)));


      print "\n";
//        if (not(forall oo <- o.owner :: ( (oo.AMFB > {}) ==> (o.AMFB <= oo.AMFB)))) {
          // if (not(nuBoundsOK(o.owner,o.bound))) {
          //   print "SO YOU REALLY FUCKED UP DIDN'T YOU!!!\n";
          //   print "SO YOU REALLY FUCKED UP DIDN'T YOU!!!\n";
          //   print "SO YOU REALLY FUCKED UP DIDN'T YOU!!!\n";
          // }
      //printobjfields(o);
}

//
// function froposeBounds(os : set<Object>) : (b : Owner)
//  //propose boubnsf but it;'s a function withtout READY as a precondition.
//  //  ensures myBoundsOK(os, b)
//  {
//     var all : set<Object> := set o <- os, a <- o.bound :: a;
//     set a <- all | forall o <- os :: a in o.AMFB
//  }
//



method {:isolate_assertions} Paranoia_boundless_chain(t : Object, a : Object, b : Object, c : Object, d : Object, e : Object)
   requires t.owner == {}
   requires t.bound == {}
   requires Paranoid(t)
    ensures t.AMFO == {t}
    ensures t.AMFB == {t}

   requires a.owner == {t}
   requires a.bound == {t}
   requires Paranoid(a)
    ensures a.AMFO == {t,a}
    ensures a.AMFB == {t,a}

   requires b.owner == {a}
   requires b.bound == {a}
   requires Paranoid(b)
    ensures b.AMFO == {t,a,b}
    ensures b.AMFB == {t,a,b}

   requires c.owner == {b}
   requires c.bound == {b}
   requires Paranoid( c)
    ensures c.AMFO == {t,a,b,c}
    ensures c.AMFB == {t,a,b,c}

   requires d.owner == {c}
   requires d.bound == {c}
   requires Paranoid(d)
    ensures d.AMFO == {t,a,b,c,d}
    ensures d.AMFB ==  {t,a,b,c,d}

   requires e.owner == {d}
   requires e.bound == {d}
   requires Paranoid(e)
    ensures e.AMFO == {t,a,b,c,d,e}
    ensures e.AMFB == {t,a,b,c,d,e}
{
  printbounds(t);
  printbounds(a);
  printbounds(b);
  printbounds(c);
  printbounds(d);
  printbounds(e);
}




predicate {:isolate_assertions} Paranoid(o : Object)
    //well-formdness of ownership
    reads {}
    decreases o.AMFO
  {
    && (o.self  == o.owner + {o})
    && (o.AMFB == flatten(o.bound))
    && (o.AMFX == flatten(o.owner))
    && (o.AMFO == flatten(o.self ))
    && (o.AMFO == o.AMFX + {o})
    && (isFlat(o.AMFB))
    && (isFlat(o.AMFO))
    && (isFlat(o.AMFX))
    && (o.AMFO > o.AMFX >= o.AMFB)
    && (forall oo <- o.AMFX  :: ((o.AMFO > oo.AMFO)))// && Paranoid(oo)))
    && (paranoidBounds02(o.owner, o.bound))
    && (o !in o.AMFX) && (o !in o.owner) &&  (o !in o.bound)
  }


predicate paranoidBoundsOK(oo : Owner, mb : Owner)   {flatten(oo) >= flatten(mb)}

predicate paranoidBounds01(oo : Owner, mb : Owner)   {flatten(oo) >= flatten(mb)}
predicate paranoidBounds02(oo : Owner, mb : Owner)   {(flatten(oo) >= flatten(mb)) && (forall o <- oo :: ((o.AMFB) >= flatten(mb)))}
