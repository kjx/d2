include "Ownership.dfy"

type Bound = Owner


predicate myBoundsOK(oo : Owner, mb : Bound)
 //basic defiintin: my flattened boumd must be outside any owners bound(s)
 { forall o <- oo :: o.AMFB >= flatten(mb) }

lemma testBounds1(oo : Owner, mb : Bound)
  //bound of {} is always OK
 requires AllReady(oo)
  ensures myBoundsOK(oo, {})
  {}

lemma testBounds3(oo : Owner, mb : Bound)
 //bound {} of even at owner {}
   ensures myBoundsOK({}, {})
  {}

lemma testBounds4(oo : Owner, mb : Bound)
 //kinda just repeats the defn
  requires AllReady(oo)
  requires forall o <- oo :: o.AMFB >= flatten(mb)
   ensures myBoundsOK(oo, mb)
  {}

lemma  {:isolate_assertions} {:timeLimit 20} testBounds5(oo : Owner, mb : Bound)
  requires AllReady(oo)
  requires forall o <- oo :: (o.bound == o.owner)
   ensures forall o <- oo :: (o.AMFB == o.AMFX)
  requires forall o <- oo :: o.AMFX >= flatten(mb)
   ensures forall o <- oo :: o.AMFB >= flatten(mb)

   ensures myBoundsOK(oo, mb)
  {
    // calc {
    //     forall o <- oo :: (o.bound == o.owner);
    //     forall o <- oo :: (o.AMFB == o.AMFX);
    //     forall o <- oo :: o.AMFX >= flatten(mb);
    //     forall o <- oo :: o.AMFB >= flatten(mb);
    //      myBoundsOK(oo, mb);
    // }
  }



lemma testBounds6(oo : Owner, mb : Bound, o : Object, b : Bound)
  requires AllReady(oo)
  requires AllReady(mb)
  requires oo == {o}   //singleton
  requires mb == o.bound
   ensures isFlat(o.AMFB)
   ensures (set o <- oo, ooo <- o.AMFB :: ooo ) == o.AMFB == flatten(o.bound)
   ensures forall o <- oo :: o.AMFB >= flatten(mb)
   ensures myBoundsOK(oo, mb)
  {}

lemma testBounds10(oo : Owner, mb : Bound)
    requires AllReady(oo)
    requires forall o <- oo :: o.AMFB >= flatten(mb)
     ensures forall b <- flatten(mb), o <- oo :: b in o.AMFB
  {}

lemma testBounds11(oo : Owner, mb : Bound)
    requires AllReady(oo)
    requires forall b <- flatten(mb), o <- oo :: b in o.AMFB
     ensures forall o <- oo :: o.AMFB >= flatten(mb)
     ensures myBoundsOK(oo, mb)
  {}



lemma   {:isolate_assertions} {:timeLimit 20}  testBounds12(oo : Owner, mb : Bound)
    requires AllReady(oo)
//    requires mb == (set o <- oo | forall b <- mb :: inside(b,o))
//    requires mb == (set o <- flatten(oo) | forall b <- flatten(mb) :: inside(b,o))
    requires mb == (set o <- oo | forall b <- o.AMFB:: inside(o,b))

  // ensures forall o <- oo :: o.AMFB >= flatten(mb)
     // ensures myBoundsOK(oo, mb)
  { }

//    mb == (set o <- oo | forall b <- mb :: inside(b,o))
//
//
// lemma {:isolate_assertions} {:timeLimit 20}  testIntersets


lemma testBounds13(a : Object, b : Object, c : Object, d : Object)
//simple row
     requires c.AMFB == {b,a}
     requires b.AMFB == {a}
     requires a.AMFB == {}
      ensures myBoundsOK( {a,b,c}, {})
      {}




lemma testBounds14(a : Object, b : Object, c : Object, d : Object)
//simple row
     requires c.AMFB == {a}
     requires b.AMFB == {a}
     requires a.AMFB == {}
     requires a.AMFO == {a}
      ensures myBoundsOK( {c,b}, {a})
      {
        assert flatten( {a} ) == {a};
      }



lemma testBounds15(a : Object, b : Object, c : Object, d : Object)
//simple row
     requires c.AMFB == {b,a}
     requires b.AMFB == {a}
     requires a.AMFB == {}
     requires a.AMFX == {}
     requires a.Ready()
      ensures a.AMFO == {a}
      ensures flatten({a}) == {a}
      ensures myBoundsOK( {c,b}, {a})
      {
        // assert {b,a} >= {a};
        // assert {a} >= {a};
        // assert c.AMFB >= flatten({a});
      }


method proposeBoundsFLAT(os : set<Object>) returns (b : Bound)
 //computes the intersection of the *flattened* bounds of each owner
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o : Object <- os, oo <- o.AMFB :: oo;
    b := set a <- all | forall o <- os :: a in o.AMFB;
 }


method proposeBounds(os : set<Object>) returns (b : Bound)
 //computes the intersection of the *flattened* bounds of each owner
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.bound :: a;
    b := set a <- all | forall o <- os :: a in o.AMFB;
 }
