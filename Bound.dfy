include "Ownership.dfy"


type Bound = Owner


predicate myBoundsOK(oo : Owner, mb : Bound) { forall o <- oo :: o.AMFB >= flatten(mb) }

lemma testBounds1(oo : Owner, mb : Bound)
 requires AllReady(oo)
  ensures myBoundsOK(oo, {})
  {}

lemma testBounds3(oo : Owner, mb : Bound)
  requires AllReady(oo)
   ensures myBoundsOK({}, {})
  {}

lemma testBounds4(oo : Owner, mb : Bound)
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
//   ensures isFlat(mb) //AND THIS ONEA
//                                                                                                                                                                                                                                                                                        ensures flatten(mb) == mb  //NO this is WRONG
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
  {


  }

//    mb == (set o <- oo | forall b <- mb :: inside(b,o))