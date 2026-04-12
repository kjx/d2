//include "Ownership.dfy"
include "Ownership-Recursive.dfy"

type Bound = Owner

predicate myBoundsOK(oo : Owner, mb : Bound)
 //basic defiintin: my flattened boumd must be outside any owners bound(s)
//  { (forall o <- oo :: o.AMFB >= flatten(mb)) }
//bnst so far    { (forall o <- oo :: flatten(mb) <= o.AMFB) }
//next trial
 {
  && (flatten(oo) >= flatten(mb))
//  && (forall o <- oo ::( ((o.AMFB) >= flatten(mb))))
   && (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))))
  }

predicate subBound(o : Object, mb : Bound)
  {
//     (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))
     (o.AMFX > {}) ==> ((o.AMFB) >= flatten(mb))
  }
//  ensures (whole.AMFO > {}) ==> ({part}+part.AMFB)   <= ({whole}+whole.AMFB)
//  ensures (whole.AMFO > {}) ==> ({whole}+whole.AMFB) >= ({part}+part.AMFB)


lemma boundSanity(part : Object, whole : Object, po : Object)
 decreases part.AMFO
  requires part.Ready() && whole.Ready()
  requires strictlyInside(part,whole)
  requires myBoundsOK(part.owner, part.bound)
   ensures part.AMFO > part.AMFB
   ensures whole.AMFO > whole.AMFB

  requires po in part.owner
   ensures po.Ready()
   ensures (part.owner == {po}) ==> (po.AMFO >= po.AMFB)
   ensures (part.owner == {po}) ==> (flatten(part.owner) == po.AMFO)
   ensures (part.owner == {po}) ==> (flatten(part.owner) >= flatten(part.bound))
   ensures (flatten(part.owner) >= flatten(part.bound))
   ensures (part.owner == {po}) ==> (po.AMFX > {}) ==> ((po.AMFB+{po}) >= flatten(part.bound))
   ensures (part.owner == {po}) ==> (po.AMFX > {}) ==> (flatten(part.bound)) <= (po.AMFB+{po})
   ensures subBound(po, part.bound)

//   ensures (whole.AMFO > {}) ==> (whole.AMFB > {})
{}

//next trial
// && (flatten(oo) >= flatten(mb)) //aka effectiveowner is INSIDE effectivebound
// && (forall o <- oo :: o.AMFB >= flatten(mb))

lemma testBounds1(oo : Owner, mb : Bound)
  //bound of {} is always OK
 requires AllReady(oo)
 requires AllReady(mb)
  ensures myBoundsOK(oo, {})
  {}

lemma testBounds3(oo : Owner, mb : Bound)
 //bound {} of even at owner {}
   ensures myBoundsOK({}, {})
  {}

lemma testBounds4(oo : Owner, mb : Bound)
 //kinda just repeats the defn
  requires flatten(oo) >= flatten(mb)
  requires AllReady(oo)
  requires AllReady(mb)
  requires forall o <- oo :: o.AMFB+{o} >= flatten(mb)   //PLUSo
   ensures myBoundsOK(oo, mb)
  {}

lemma  {:isolate_assertions} {:timeLimit 20} testBounds5(oo : Owner, mb : Bound)
  requires AllReady(oo)
  requires flatten(oo) >= flatten(mb)
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
    requires flatten(oo) >= flatten(mb)
    requires AllReady(oo)
    requires forall b <- flatten(mb), o <- oo :: b in o.AMFB+{o} //PLUSo
     ensures forall o <- oo :: (o.AMFB+{o}) >= flatten(mb)   ///how come no PLUSo????
     ensures(forall o <- oo :: ((o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))))
     ensures myBoundsOK(oo, mb)
  {}



lemma   {:isolate_assertions} {:timeLimit 20}  testBounds12(oo : Owner, mb : Bound)    //BROKENl
    requires flatten(oo) >= flatten(mb)
    requires AllReady(oo)
//    requires mb == (set o <- oo | forall b <- mb :: inside(b,o))
//    requires mb == (set o <- flatten(oo) | forall b <- flatten(mb) :: inside(b,o))
//    requires mb == (set o <- oo | forall b <- o.AMFB :: inside(o,b))
//    requires mb == (set o <- oo | forall b <- o.AMFB+{o} :: inside(o,b))
//    ensures forall o <- oo :: (o.AMFB+{o}) >= flatten(mb)
//    ensures myBoundsOK(oo, mb)
  { }


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
     requires c.AMFO == {c,b,a}
     requires b.AMFB == {a}
     requires b.AMFO == {a,b}
     requires a.AMFB == {}
     requires a.AMFO == {a}
      ensures myBoundsOK( {c,b}, {a})
      {
        assert flatten( {a} ) == {a};
      }



lemma testBounds15(a : Object, b : Object, c : Object, d : Object)
//simple row
     requires c.AMFB == {b,a}
     requires c.AMFO == {b,a,c}
     requires b.AMFB == {a}
     requires b.AMFO == {b,a}
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



//////////////////////////////////////////////////////////////////////
////////
/////// note all these proposedBNounds doesn't indlude the PLUSo

method proposeBoundsFLAT(os : set<Object>) returns (b : Bound)
 //computes the intersection of the *flattened* bounds of each owner
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o : Object <- os, oo <- o.AMFB :: oo;
    b := set a <- all | forall o <- os :: a in o.AMFB;
 }


method opposeBounds(os : set<Object>) returns (b : Bound)
 //computes the intersection of the nominal bounds of each owner
  requires AllReady(os)
   ensures myBoundsOK(os, b)
   ensures b == proposeBounds(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.bound :: a;
    b := set a <- all | forall o <- os :: a in o.AMFB;
 }

 function proposeBounds(os : set<Object>) : (b : Bound)
 //propose boubnsf but it;'s a function
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.bound :: a;
    set a <- all | forall o <- os :: a in o.AMFB
 }


 function froposeBounds(os : set<Object>) : (b : Bound)
 //propose boubnsf but it;'s a function withtout READY as a precondition.
//   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.bound :: a;
    set a <- all | forall o <- os :: a in (o.AMFB)
 }

lemma {:isolate_assertions} froposeGetsBoundsOK(os : set<Object>, fp  : set<Object>)
    requires froposeBounds(os) == fp
    requires AllReady(os)
     ensures froposeBounds(os) == fp
     ensures proposeBounds(os) == fp

     ensures myBoundsOK(os, fp)
{}


//////////////////////////////////////////////////////////////////////

lemma {:isolate_assertions} {:timeLimit 30} TransitiveBounds(part : Object,  whole : Object)
 decreases part.AMFO
  requires part.Ready() && whole.Ready()
  requires inside(part,whole)
  requires SingleOwnership(part)
   ensures SingleOwnership(whole)
   ensures myBoundsOK(part.owner, part.bound)
   // ensures part.AMFB <= whole.AMFB //contravariuant
   // ensures (whole.AMFO > {}) ==> (part.AMFB) <= (whole.AMFB) //contravariuant
  ensures forall o <- whole.owner ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(whole.bound)))
  {
     InsideRecInside2(part, whole);
     assert myBoundsOK(part.owner, part.bound);
       assert (flatten(part.owner) >= flatten(part.bound));
       assert (forall o <- part.owner ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(part.bound))));

    if  ((part == whole) || (whole in part.owner)) { return; }

assert part.AMFO > {};

    assert (exists x <- part.owner :: recInside(x,whole));

    var next :| ((next in part.owner) && recInside(next,whole));
    InsideRecInside1(next, whole);
assert next in part.owner;
assert SingleOwnership(part);
assert |part.owner| == 1;
LemmaIsSingleton(part.owner);
assert forall x <- part.owner :: x == next;
assert (part.owner == {next}); //SingleOwnership
assert (forall o <- part.owner ::((o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(part.bound))));

//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// ////
    assert next.Ready();
    assert myBoundsOK(next.owner, next.bound);

    assert (flatten(next.owner) >= flatten(next.bound));
    assert (flatten(part.owner) >= flatten(part.bound));

    assert (forall o <- next.owner ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(next.bound))));
//  {
//   && (flatten(oo) >= flatten(mb))
//   && (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))))
//   }
//// //// //// //// //// //// //// //// //// //// //// //// //// //// //// //// ////

   TransitiveBounds(next,whole);
}


lemma OneIsOne(n : Object, nn : set<Object>)
  requires n in nn
  requires |nn| == 1
   ensures exists x :: x in nn
   ensures forall y <- nn, z <- nn :: y == z
   ensures forall z <- nn :: z == n
   ensures nn == {n}
 {
  LemmaIsSingleton(nn);
 }



predicate {:isolate_assertions} SingleOwnership(o : Object)
  requires o.Ready()
 decreases o.AMFO
  {
    && ((|o.owner| < 2))
    && ((|o.owner| == 1) ==> (forall oo <- o.owner :: SingleOwnership(oo)))
  }