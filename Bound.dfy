//include "Ownership.dfy"
include "Ownership-Recursive.dfy"

type Bound = Owner

predicate  myBoundsOK(oo : Owner, mb : Bound)
 //basic defiintin: my flattened boumd must be outside any owners bound(s)
//  { (forall o <- oo :: o.AMFB >= flatten(mb)) }
//bnst so far    { (forall o <- oo :: flatten(mb) <= o.AMFB) }
//next trial
 {
  && (flatten(oo) >= flatten(mb))
  && (forall o <- oo :: flatten(o.ownerBound()) >= flatten(mb))
//  && (forall o <- oo ::( ((o.AMFB) >= flatten(mb))))
//  && (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))))
  }


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

//   ensures (whole.AMFO > {}) ==> (whole.AMFB > {}) /// basically horrid here.
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
  requires forall o <- oo :: flatten(o.ownerBound()) >= flatten(mb)
   ensures myBoundsOK(oo, mb)
  {}

lemma  {:isolate_assertions} {:timeLimit 20} testBounds5(oo : Owner, mb : Bound)
  requires AllReady(oo)
  requires flatten(oo) >= flatten(mb)
  requires forall o <- oo :: (o.bound == o.owner)
   ensures forall o <- oo :: (o.AMFB == o.AMFX)
  requires forall o <- oo :: o.AMFX >= flatten(mb)
   ensures forall o <- oo :: o.AMFB >= flatten(mb)
  requires forall o <- oo :: flatten(o.ownerBound()) >= flatten(mb)
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



lemma {:isolate_assertions} testBounds6(oo : Owner, mb : Bound, o : Object, b : Bound)
  requires AllReady(oo)
  requires AllReady(mb)
  requires oo == {o}   //singleton
  requires mb == o.ownerBound()
  requires flatten(oo) >= flatten(mb)
   ensures isFlat(o.AMFB)
   ensures (set o <- oo, ooo <- o.AMFB :: ooo ) == o.AMFB == flatten(o.bound)
//   ensures forall o <- oo :: o.AMFB >= flatten(mb)
   ensures forall o <- oo :: flatten(o.ownerBound()) >= flatten(mb)
   ensures myBoundsOK(oo, mb)
  {
    assert mb == o.ownerBound();
    assert forall o <- oo :: o.ownerBound() == mb;
    assert forall o <- oo :: flatten(o.ownerBound()) == flatten(mb);


  }

lemma testBounds10(oo : Owner, mb : Bound)
    requires AllReady(oo)
    requires forall o <- oo :: o.AMFB >= flatten(mb)
     ensures forall b <- flatten(mb), o <- oo :: b in o.AMFB
  {}

lemma testBounds11(oo : Owner, mb : Bound)
    requires flatten(oo) >= flatten(mb)
    requires AllReady(oo)
    requires forall o <- oo :: flatten(o.ownerBound())>= flatten(mb)
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




lemma {:isolate_assertions} testBounds14(a : Object, b : Object, c : Object)
//learning from this method - setup owner and bound, NOT AMFX and friends...
     requires a.Ready() && b.Ready() && c.Ready()
      ensures c.AMFB == {a}
      ensures c.AMFO == {c,b,a}
     requires c.owner == {b}
     requires c.bound == {a}
     requires b.AMFB == {a}
     requires b.AMFO == {a,b}
      ensures b.owner == {a}
      ensures b.bound == {a}
     requires a.AMFB == {}
     requires a.AMFO == {a}
      ensures myBoundsOK( {}, {})    //a
      ensures myBoundsOK( {a}, {a})  //b
      ensures myBoundsOK( {b}, {a})  //c
      ensures myBoundsOK( {b}, {} )  //c?

      {
        assert flatten( {a} ) == {a};
        assert flatten( {b} ) == {a,b};
        assert flatten( {c} ) == {a,b,c};

        assert flatten({}) >= flatten({});
        assert flatten({b}) >= flatten({a});
        assert flatten({c}) >= flatten({a});

        assert a.ownerBound() == {a};

        assert b.owner == {a};
        assert b.bound == {a};
        assert b.owner == b.bound;
        assert b.ownerBound() == {b};

        assert c.bound == {a};
        assert c.ownerBound() == {a};
      }



lemma testBounds15(a : Object, b : Object, c : Object)
//simple row
     requires a.Ready() && b.Ready() && c.Ready()
     requires c.bound == {b}
     requires c.owner == {b}
     requires b.bound == {a}
     requires b.owner == {a}
     requires a.bound == {}
     requires a.owner == {}
      ensures flatten({a}) == {a}
      ensures myBoundsOK( {c,b}, {a})
      ensures myBoundsOK( {b},   {a})
      ensures myBoundsOK( {c},   {a})
      ensures myBoundsOK( {c},   {b})
  { }


lemma testBounds16(a : Object, b : Object, c : Object)
//less simple row
     requires a.Ready() && b.Ready() && c.Ready()
     requires c.bound == {a}
     requires c.owner == {b}
     requires b.bound == {a}
     requires b.owner == {a}
     requires a.bound == {}
     requires a.owner == {}
      ensures flatten({a}) == {a}
      ensures myBoundsOK( {c,b}, {a})
      ensures myBoundsOK( {b},   {a})
      ensures myBoundsOK( {c},   {a})
  { }


//////////////////////////////////////////////////////////////////////
////////
/////// note all these proposedBNounds doesn't indlude the ?PLUS?
///////     - I've no idea what that is!
///////

method proposeBoundsFLAT(os : set<Object>) returns (b : Bound)
 //computes the intersection of the *flattened* bounds of each owner in os...
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o : Object <- os, oo <- o.AMFB :: oo;
    b := set a <- all | forall o <- os :: a in o.AMFB;
 }


method {:isolate_assertions}  opposeBounds(os : set<Object>) returns (b : Bound)
 //computes the intersection of the nominal bounds of each owner
 //does it?  are we sure?
 //keeping it around because a) paranoia & b) "opposeBounds" is a funny name...
  requires AllReady(os)
   ensures myBoundsOK(os, b)
   ensures b == proposeBounds(os)
 {
    var all : set<Object> := set o <- os, a <- o.ownerBound() :: a;
    b := set a <- all | forall o <- os :: flatten({a}) <= flatten(o.ownerBound());
 }

 function proposeBounds(os : set<Object>) : (b : Bound)
 //propose boubnsf but it;'s a function
  requires AllReady(os)
   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.ownerBound() :: a;
    set a <- all | forall o <- os :: flatten({a}) <= flatten(o.ownerBound())

   //set a <- all | forall o <- os :: a in flatten(o.ownerBound())
 // set a <- all | forall o <- os :: flatten({a}) <= flatten(o.ownerBound())
 //   set a <- all | forall o <- os :: flatten(o.ownerBound()) >= a.AMFO

 }
//
// lemma SAME_SAME_BOUNDS(os : set<Object>, all : set<Object>)
//   requires AllReady(os)
//   requires all == set o <- os, a <- o.ownerBound() :: a
// //   ensures myBoundsOK(os, (set a <- all | forall o <- os :: a in flatten(o.ownerBound())))
//   // ensures myBoundsOK(os, (set a <- all | forall o <- os :: a in o.ownerBound()))
//  //  ensures myBoundsOK(os, (set a <- all | forall o <- os :: a.AMFO >= flatten(o.ownerBound())))
//    ensures myBoundsOK(os, set a <- all | forall o <- os :: flatten({a}) <= flatten(o.ownerBound()))
//    ensures myBoundsOK(os, set a <- all | forall o <- os :: flatten(o.ownerBound()) >= flatten({a}))
//    {
//    }


 function froposeBounds(os : set<Object>) : (b : Bound)
 //os - prooposed owners for an object
 //propose boubnsf but it;'s a function withtout READY as a precondition.
 //which mean it can be used to set default argument values (ege in make())
 //but can't guarantee anything
//   ensures myBoundsOK(os, b)
 {
    var all : set<Object> := set o <- os, a <- o.ownerBound() :: a;
  //  set a <- all | forall o <- os :: flatten({a}) <= flatten(o.ownerBound())
    set a <- all | forall o <- os ::  flatten(o.ownerBound()) >= flatten({a})
 }

lemma {:isolate_assertions} froposeGetsBoundsOK(os : set<Object>, fp  : set<Object>)
    requires froposeBounds(os) == fp
    requires AllReady(os)
     ensures froposeBounds(os) == fp
     ensures proposeBounds(os) == fp

     ensures myBoundsOK(os, fp)
{}

lemma {:isolate_assertions} OneNilOwner(a : Object)
  requires a.Ready()
  requires exists o : Object <- a.owner :: o.ownerBound() == {}
   ensures a.bound == {}
{
  assert myBoundsOK(a.owner, a.bound);
  assert forall o <- a.owner :: flatten(o.ownerBound()) >= flatten(a.bound);
  assert flatten( {} ) == {};
  assert exists o : Object <- a.owner :: o.ownerBound() == {};
  assert exists o : Object <- a.owner :: flatten(o.ownerBound()) == {};
  assert {} >= flatten(a.bound);
  assert {} >= flatten(a.bound);
  assert {} ==        (a.bound);
}


lemma {:isolate_assertions} OneNilAMFO(a : Object, o : Object)
  decreases a.AMFO
  requires a.Ready()
  requires o in a.AMFO
  requires o.ownerBound() == {}
   ensures a.bound == {}
{
  if (o == a) { return; }
  assert o != a;

  if (o in a.owner) { OneNilOwner(a); return;  }
  assert o !in a.owner;

  assert exists x <- a.owner ::  o in x.AMFO;
  var next :| (next in a.owner) && (o in next.AMFO);
  OneNilAMFO(next, o);
  assert next.bound == {};
  OneNilOwner(a);
  assert a.bound == {};
}


//////////////////////////////////////////////////////////////////////
lemma {:isolate_assertions} TransitiveBounds(part : Object,  whole : Object)
 decreases part.AMFO
  requires part.Ready() && whole.Ready()
  requires inside(part,whole)
   ensures myBoundsOK(part.owner, part.bound)
   ensures myBoundsOK(whole.owner, whole.bound)
   ensures part.AMFO >=  whole.AMFO
   ensures part.AMFO  > part.AMFB
   ensures whole.AMFO > whole.AMFB
//   ensures part.AMFB >= whole.AMFB
   ensures (forall o <- part.owner  :: flatten(o.ownerBound()) >= part.AMFB)
   ensures (forall o <- whole.owner :: flatten(o.ownerBound()) >= whole.AMFB)
  ensures forall o <- whole.owner ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= whole.AMFB))
//   ensures (forall o <- part.owner  :: flatten(o.ownerBound()) >= whole.AMFB)
{
 InsideRecInside2(part, whole);
     assert myBoundsOK(part.owner, part.bound);
       assert (flatten(part.owner) >= flatten(part.bound));
       assert (forall o <- part.owner ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(part.bound))));

    if  ((part == whole) || (whole in part.owner)) { return; }

}

lemma {:isolate_assertions} {:verify false} OLD_TransitiveBounds(part : Object,  whole : Object)
 /// warning - this reqhires SingleOwnership ie is BAD
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

  lemma SingleOwnershipIsSingletonOwnership(o : Object)
   requires o.Ready()
   requires SingleOwnership(o)
    ensures forall x <- o.owner, y <- o.owner :: x == y
    {
      LemmaIsSingleton(o.owner);
    }