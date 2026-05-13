include "Ownership-Recursive.dfy"

/////////////////////////////////////////////////////////////////////////////////////////////////////////////

function CAOWEO(o : Object) : (rv : Owner)
//collectAllOwnersWithoutExtraOwners
  decreases o.AMFO
   requires o.Ready()
    ensures rv <= o.AMFO
    { {o} + (set xo <- o.owner, co <- CAOWEO(xo) :: co) }

function recOwners(o : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    ensures rv <= o.AMFO
    ensures forall r <- rv :: r.Ready()
    { {o} + (set xo <- o.owner, co <- recOwners(xo) :: co) }

lemma RecOwnersIsRecFlat(k : Object, rv : Owner)
    requires k.Ready()
    requires rv == recOwners(k)
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures isRecFlat(rv)
    {
      if (k.owner == {})
       { assert isRecFlat(rv); return; }

     forall oo <- k.owner ensures (isRecFlat(recOwners(oo))) //by
       {
        RecOwnersIsRecFlat(oo,recOwners(oo));
        assert recOwners(oo) <= rv;
        assert isRecFlat(recOwners(oo));
       }

    }

lemma RecOwnersToAMFO0(o : Object, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires rv == recOwners(o)
  //   ensures rv >= collectAllOwnersWithoutExtraOwners(o)
{}


// lemma {:timeLimit 10} RecOwnerCAOWEO(o : Object) returns (rv : Owner)
//    decreases o.AMFO
//     requires o.Ready()
//      ensures rv == recOwners(o)
//      ensures rv == CAOWEO(o)
//      ensures rv == o.AMFO
//    {
//     rv := {o};
//     if (o.owner == {})
//       {
//         assert o.AMFO       == {o};
//         assert CAOWEO(o)    == {o};
//         assert recOwners(o) == {o};
//       } else {
//         var oo := o.owner;
//         while (oo > {})
//           decreases oo
//         {
//           var x :| x in oo;
//           assert x in oo;
//           assert oo decreases to (oo - {x});
//           var oo := oo - {x};
//           var rx := RecOwnerCAOWEO(x);
//           rv := rv + rx;
//         }
//       }
//    }

lemma FYCKED_RecOwnersBaseLine(k : Object, rv : Owner)
 requires k.Ready()
 requires rv == recOwners(k)
decreases k.AMFO
  // ensures rv == CAOWEO(k)
  // ensures rv == collectAllOwnersWithoutExtraOwners(k)
  // ensures rv == k.AMFO
  ensures isFlat(k.AMFO)
  //  ensures isFlat(rv)
{}

lemma {:timeLimit 10} RecOwnersIsCAOWEO0(o : Object, ro : Owner, rv : Owner)
   decreases o.AMFO
    requires o.Ready()

    requires ro == recOwners(o)
     ensures AllReady(ro)
     ensures (o.owner == {}) ==> (ro == {o})
     ensures o.owner <= ro //ERR
     ensures forall x <- o.owner :: recOwners(x) <= ro
     //ensures o.AMFO == ro
{}

lemma {:timeLimit 10} RecOwnersIsCAOWEO1(o : Object, ro : Owner, rv : Owner)
   decreases o.AMFO
    requires o.Ready()

    requires rv == CAOWEO(o)
     ensures AllReady(rv)
     ensures (o.owner == {}) ==> (rv == {o})
     ensures o.owner <= rv
     ensures forall x <- o.owner :: CAOWEO(x) <= rv
    //ensures o.AMFO == rv
{}

lemma {:timeLimit 120} RecOwnersIsCAOWEO2(o : Object, ro : Owner, rv : Owner)
   decreases o.AMFO
    requires o.Ready()

    requires ro == recOwners(o)
    requires rv == CAOWEO(o)
  //   ensures rv == ro //ERR
{
  forall x <- o.owner ensures (CAOWEO(x) <= rv) //by
    {
      RecOwnersIsCAOWEO0(x, recOwners(x), CAOWEO(x));
      RecOwnersIsCAOWEO1(x, recOwners(x), CAOWEO(x));
      RecOwnersIsCAOWEO2(x, recOwners(x), CAOWEO(x));
    }
  RecOwnersIsCAOWEO0(o, recOwners(o), CAOWEO(o));
  RecOwnersIsCAOWEO1(o, recOwners(o), CAOWEO(o));
//  RecOwnersIsCAOWEO2(o, recOwners(o), CAOWEO(o));
}




// lemma {:timeLimit 120} RecOwnersIsCAOWEO8(o : Object, ro : Owner, rv : Owner)
//    decreases o.AMFO
//     requires o.owner == {}
//     requires o.Ready()
//     requires ro == recOwners(o)
//     requires rv == CAOWEO(o)
//      ensures rv == ro //ERR
// {}

lemma RecOwnersIsCAOWEO9(o : Object, ro : Owner, rv : Owner)
   decreases o.AMFO
    requires o.owner > {}
    requires o.Ready()
    requires ro == recOwners(o)
    requires rv == CAOWEO(o)
     ensures rv == ro
{
 forall oo <- o.owner ensures (recOwners(oo) == CAOWEO(oo)) //by
  {
    if (oo.owner == {}) {assert recOwners(oo) == CAOWEO(oo) == {oo}; }
      else
      {
        RecOwnersIsCAOWEO9(oo,recOwners(oo),CAOWEO(oo));
      }
  }
}



lemma RecOwnersIsFlat(o : Object, ro : Owner, rv : Owner)
   decreases o.AMFO
    requires o.owner > {}
    requires o.Ready()
    requires ro == recOwners(o)
    requires rv == CAOWEO(o)
     ensures rv == ro //ERR
{
 forall oo <- o.owner ensures (recOwners(oo) == CAOWEO(oo)) //by
  {
    if (oo.owner == {}) {assert recOwners(oo) == CAOWEO(oo) == {oo}; }
      else
      {
        RecOwnersIsCAOWEO9(oo,recOwners(oo),CAOWEO(oo));
      }
  }
}




function recFlatten(oo : Owner) : (rv : Owner)
  //set version of recOwners --- all the owners of oo including oo
  requires AllReady(oo)
  requires forall o <- oo :: o.Ready()
 decreases allAMFOs(oo)
//ensures isFlat(rv)
//  ensures isRecFlat(rv)
   {set o : Object <- oo, ooo <- recOwners(o) :: ooo}


lemma RecFlattenFlatten(oo : Owner)
   requires AllReady(oo)
   requires forall o <- oo :: o.Ready()
  decreases allAMFOs(oo)
   // ensures recFlatten(oo) == flatten(oo)
   // ensures recFlatten(oo) == (set o : Object <- oo :: collectAllOwnersWithoutExtraOwners(o))

   { }


predicate pivotlyOutside(p : Object, w : Object) : (rv : bool)
  //  ensures rv == ((p == w) || outside(p,w))
  //  ensures rv == (not(p.AMFO > w.AMFO))
    {((p == w) || outside(p,w))}

function recOwnersInside(k : Object, pivot : Object) : (rv : Owner)
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: strictlyInside(r, pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if (not(strictlyInside(k, pivot)))
      then ({})
      else ({k} + (set oo <- k.owner, ooo <- recOwnersInside(oo, pivot) :: ooo))
  }

// lemma RecOwnersInsideClosedForm(k : Object, pivot : Object, rv : Owner)
//     requires k.Ready()
//     requires pivot.Ready()
//     requires rv == recOwnersInside(k,pivot)
//    decreases k.AMFO
//      ensures rv <= k.AMFO
//      ensures forall r <- rv :: strictlyInside(r, pivot)
//      ensures rv == set r <- recOwners(k) | strictlyInside(r, pivot)
//   {}






datatype Running = Running(inside : bool, fringe : bool, pivot : bool)
function newRunning() : Running { Running(true, true, true) }

datatype RV = RV(owners : Owner, inside : Owner, outside : Owner, fringe : Owner, pivot : Owner)
 {
  function merge(r : RV, running : Running) : RV {
      var rv := this.(owners := owners+r.owners);
      var rv := if (running.inside) then rv.(inside := inside+r.inside) else rv;
//    var rv := if (running.outside) then rv.(outside := outside+r.outside) else rv;
      var rv := if (running.fringe) then rv.(fringe := fringe+r.fringe) else rv;
      var rv := if (running.pivot) then rv.(pivot := pivot+r.pivot) else rv;
      rv }
  lemma Merge(r : RV, running : Running, rv : RV)
   //placeholder in case Dafny can't work just with the definition of merge function
    requires rv == merge(r, running)
     ensures rv.owners == owners+r.owners
   {}
 }
function newRV() : RV {RV({}, {}, {}, {}, {})}

lemma {:isolate_assertions} ClassifyOwners(k : Object, pivot : Object, running' : Running := newRunning()) returns (rv : RV)
   requires k.Ready()
   requires pivot.Ready()
  decreases k.AMFO
    ensures rv.owners == recOwners(k)
    ensures running'.inside ==> (rv.inside == recOwnersInside(k, pivot))
    ensures running'.fringe ==> (rv.fringe == recOwnersFringe(k, pivot))
    ensures running'.pivot  ==> (rv.pivot  == recOwnersPivot(k, pivot))
{
  rv := newRV();
  var running := running';

//owners base case
  rv := rv.(owners := {k});
//inside base case
  if (running.inside) {
    if (not(strictlyInside(k, pivot))) { rv := rv.(inside :=  {});  assert rv.inside == recOwnersInside(k, pivot);  running := running.(inside := false); }
    else { rv := rv.(inside :=  {k}); }  }
  assert  (running'.inside && not(running.inside)) ==> (rv.inside == recOwnersInside(k, pivot));
//fringe base case
  var fringeLocal := {};
  if (running.fringe) {
    if (k == pivot) { rv := rv.(fringe := {}); fringeLocal := {}; assert rv.fringe == recOwnersFringe(k, pivot);  running := running.(fringe := false); }
    else {
      if (outside(k, pivot)) { rv := rv.(fringe := {k}); fringeLocal := {k}; assert rv.fringe == recOwnersFringe(k, pivot);  running := running.(fringe := false); }
    }
    assert (running'.fringe && not(running.fringe)) ==> (rv.fringe == recOwnersFringe(k, pivot));
  }
//pivot base case
  if (running.pivot) {
    if (inside(k, pivot)) { rv := rv.(pivot := recOwners(pivot)); }
                     else { rv := rv.(pivot := {}); }
    assert rv.pivot == recOwnersPivot(k, pivot);  running := running.(pivot := false);
    }
  assert (running'.pivot && not(running.pivot)) ==> (rv.pivot == recOwnersPivot(k, pivot));


//if we were running but aren't any more, we've got the right answer
  assert (running'.inside && not(running.inside)) ==> (rv.inside == recOwnersInside(k, pivot));
  assert (running'.fringe && not(running.fringe)) ==> (rv.fringe == recOwnersFringe(k, pivot));
  assert (running'.pivot  && not(running.pivot )) ==> (rv.pivot  == recOwnersPivot(k, pivot));

//the recursive cases
  var todo : Owner  := k.owner;

  while (todo > {})
    decreases todo
//invariant while running (owners is always running; pivot is never running
    invariant rv.owners == {k} + (set xo <- (k.owner - todo), co <- recOwners(xo) :: co)
    invariant running.inside ==> (rv.inside == {k} + (set oo <- (k.owner - todo), ooo <- recOwnersInside(oo,pivot) :: ooo))
    invariant running.fringe ==> (rv.fringe == fringeLocal + (set oo <- (k.owner - todo), ooo <- recOwnersFringe(oo,pivot) :: ooo))
    invariant not(running.pivot)

//invariants where we were called running but are now not running - i.e. no recursive call for that aspect.
    invariant (running'.inside && not(running.inside)) ==> (rv.inside == recOwnersInside(k, pivot))
    invariant (running'.fringe && not(running.fringe)) ==> (rv.fringe == recOwnersFringe(k, pivot))
    invariant (running'.pivot  && not(running.pivot))  ==> (rv.pivot  == recOwnersPivot(k, pivot))
    {
       assert (running'.inside && not(running.inside)) ==> (rv.inside == recOwnersInside(k, pivot));
       assert (running'.fringe && not(running.fringe)) ==> (rv.fringe == recOwnersFringe(k, pivot));
       assert (running'.pivot  && not(running.pivot))  ==> (rv.pivot  == recOwnersPivot(k, pivot));

      var each: Object;
      each :| each in todo;
      todo := todo - {each};

      var r := ClassifyOwners(each, pivot, running);
         assert r.owners == recOwners(each);
         assert running.inside ==> (r.inside == recOwnersInside(each, pivot));
         assert running.fringe ==> (r.fringe == recOwnersFringe(each, pivot));
         assert running.pivot  ==> (r.fringe == recOwnersPivot(each, pivot));

      var prv := rv;
      rv := prv.merge(r,running);

       assert running.inside ==> (rv.inside == {k}         + (set oo <- (k.owner - todo), ooo <- recOwnersInside(oo,pivot) :: ooo));
       assert running.fringe ==> (rv.fringe == fringeLocal + (set oo <- (k.owner - todo), ooo <- recOwnersFringe(oo,pivot) :: ooo));

       assert (running'.inside && not(running.inside)) ==> (rv.inside == recOwnersInside(k, pivot));
       assert (running'.fringe && not(running.fringe)) ==> (rv.fringe == recOwnersFringe(k, pivot));
       assert (running'.pivot  && not(running.pivot))  ==> (rv.pivot  == recOwnersPivot(k, pivot));
    }
      // assert (running.inside) ==> (running'.inside);
      // assert (running.fringe) ==> (running'.fringe);

//summary owners
    assert (k.owner - todo) == k.owner;
    assert                    rv.owners == {k} + (set xo <- (k.owner),  co <- recOwners(xo) :: co);
//summary inside
    assert running.inside ==> (rv.inside == {k}         + (set oo <- k.owner, ooo <- recOwnersInside(oo,pivot) :: ooo));
    assert running.fringe ==> (rv.fringe == fringeLocal + (set oo <- k.owner, ooo <- recOwnersFringe(oo,pivot) :: ooo));
    assert not(running.pivot);

    assert running'.inside ==> (rv.inside == recOwnersInside(k, pivot));
    assert running'.fringe ==> (rv.fringe == recOwnersFringe(k, pivot));
    assert running'.pivot  ==> (rv.pivot  == recOwnersPivot(k, pivot));
}



//
// lemma {:isolate_assertions} {:timeLimit 20} ClassifyOwners(k : Object, pivot : Object) returns (rv : RV)
//    requires k.Ready()
//    requires pivot.Ready()
//    decreases k.AMFO
//    ensures rv.owners == recOwners(k)
// {
//   rv := newRV();
//   rv := rv.(owners:= {k});    //  { {k} + (set xo <- k.owner, co <- ClassifyOwners(xo,pivot). :: co) }
//
//   if (k.owner == {}) {
//     return;
//   }
//
//   assert forall each <- k.owner :: k.AMFO decreases to each.AMFO;
//
//   var todo : Owner  := k.owner;
//   var each : Object :| each in todo;
//   todo := todo - {each};
//   assert todo + {each} + rv.owners == k.owner+{k};
//   assert k.AMFO decreases to each.AMFO;
//   assert todo   decreases to  todo - {each};
//   while todo >= {}
//     decreases todo
//     invariant todo + {each} + rv.owners == k.owner+{k}
//     invariant k.AMFO decreases to each.AMFO
//     invariant todo   decreases to each.AMFO
//    {
//      assert k.AMFO decreases to each.AMFO;
//      assert todo   decreases to todo - {each};
//
//      var r := ClassifyOwners(each, pivot);
//
//      assert r.owners == recOwners(each);
//      rv := rv.merge(r);
//
//     if (todo > {}) {
//       each :| each in todo;
//       todo := todo - {each};
//       assert todo + {each} + rv.owners == k.owner+{k};
//       assert k.AMFO decreases to each.AMFO;
//       assert todo   decreases to todo - {each};
//       }
//   assert k.AMFO decreases to each.AMFO;
//   assert todo   decreases to todo - {each};
//
//    }
//
//   assert rv.owners == recOwners(k);
//
// }


function recOwnersOutside(k : Object, pivot : Object) : (rv : Owner)
 //if k is the pivot or outside it, then all owners
 //otherwise nothing
   requires k.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: pivotlyOutside(r, pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if ((k == pivot) || outside(k,pivot))
      then (recOwners(k))
      else ({})
  }

function recOwnersPivot(k : Object, pivot : Object) : (rv : Owner)
///if k inside pviot then pivot * owners
//opthwerise not
   requires k.Ready()
   requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
   //  ensures rv <= recOwners(k)
     ensures forall r <- rv :: outside(r, pivot) || (r == pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if (inside(k, pivot))
      then (recOwners(pivot))
      else ({})
  }

function recOwnersFringe(k : Object, pivot : Object) : (rv : Owner)
    requires k.Ready()
   decreases k.AMFO
     ensures forall r <- rv :: outside(r,pivot)
     ensures rv <= k.AMFO
     ensures rv <= recOwners(k)
  {
    if (k == pivot) then {} else (
        if (outside(k, pivot))
          then ({k})
          else (set oo <- k.owner, ooo <- recOwnersFringe(oo, pivot) :: ooo)
    )
  }

lemma RecOwnersFringeAreOutside(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
     ensures forall r <- recOwnersFringe(k, pivot) :: outside(r,pivot)
    //  ensures forall r <- recOwnersFringe(k, pivot) :: exists x <- recOwnersPivot(k, pivot) :: r in x.owner
   decreases k.AMFO
  {}

lemma  {:timeLimit 10} RecOwnerTrans(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures pivot in recOwners(k)
     ensures recOwners(pivot) <= recOwners(k)

     ensures forall x <- recOwners(k) :: inside(k,x)
     ensures forall x <- recOwners(k) :: x in recOwners(k)
     ensures forall x <- recOwners(k) :: recOwners(pivot) <= recOwners(k)
 {
   if (pivot == k) { assert recOwners(k) >= recOwners(pivot); return; }
   if (inside(k, pivot)) {
        assert exists x <- k.owner :: inside(x,pivot);
        var x :| x in k.owner && inside(x,pivot);
        RecOwnerTrans(x, pivot);
        assert recOwners(x) >= recOwners(pivot);
        assert recOwners(k) >= recOwners(pivot);
   }
 }

lemma RecFlattenOthers(k : Object, others : Owner)
    requires k.Ready()
    requires AllReady(others)
    requires recOwners(k) >= others
   decreases k.AMFO
     ensures isRecFlat(recOwners(k))
     ensures forall o <- others :: inside(k,o)
     ensures recOwners(k) >= recFlatten(others)
        { RecOwnersIsRecFlat(k,recOwners(k)); }

predicate isRecFlat(os : Owner) : (rv : bool)
  requires forall o <- os :: o.Ready()
//   ensures rv == (forall o <- os, oo <- recOwners(o) :: oo in os)
   {forall o <- os :: recOwners(o) <= os}

lemma LESSISMORE(less : Owner, more : Owner)
  ensures (less <= more) <==> (forall o <- less :: o in more)
{}

lemma LESSISMORE2(os : Owner, rv : bool)
 decreases allAMFOs(os)
  requires forall o <- os :: o.Ready()
  requires rv == isRecFlat(os)
   ensures rv == (forall o <- os :: recOwners(o) <= os)
   ensures rv == (forall o <- os, oo <- recOwners(o) :: oo in os)
 {
  if (os == {}) { assert rv;
                  assert (forall o <- os, oo <- recOwners(o) :: oo in os);
                  return; }

  forall o : Object <- os, oo <- recOwners(o) ensures (rv ==> (oo in os)) //by
    {
      assert rv ==> (recOwners(o) <= os);
      LESSISMORE(recOwners(o),os);
      assert rv ==> (oo in os);
    }
 }

lemma  {:timeLimit 10} RecOwnerSanity0(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersInside(k,pivot) <= recOwners(k)
     ensures forall x <- recOwnersInside(k,pivot) :: inside(x,pivot)
 {}

lemma  {:timeLimit 10} RecOwnerSanity1(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersFringe(k,pivot) <= recOwners(k)
     ensures forall x <- recOwnersFringe(k,pivot) :: outside(x,pivot)
     ensures forall o <- recOwnersFringe(k,pivot) :: exists x <- recOwnersInside(k,pivot) :: o in x.owner
{}

lemma  {:timeLimit 10} RecOwnerSanity2(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersFringe(k,pivot) <= recOwners(k)
     ensures recFlatten(recOwnersFringe(k,pivot)) <= recOwners(k)
  //   ensures forall o <- recFlatten(recOwnersFringe(k,pivot)) :: exists x <- recOwners(k) :: o in recOwners(x)
{
  RecFlattenOthers(k,recOwnersFringe(k,pivot));
}

lemma  {:timeLimit 10} RecOwnerSanity3(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersPivot(k,pivot) == recOwners(pivot)
{}

lemma  {:timeLimit 10} RecOwnerSanity3bis(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires not(inside(k, pivot))
   decreases k.AMFO
     ensures recOwnersPivot(k,pivot) == {}
{}

lemma  {:timeLimit 10} RecOwnerSanity4(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
//       ensures recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot))
     {
      if (k == pivot) {assert recOwners(k) == recOwners(pivot) == recOwnersPivot(k,pivot);
                       assert recOwnersInside(k,pivot) == {};
                       assert recOwnersFringe(k,pivot) == {};
                       assert recFlatten(recOwnersFringe(k,pivot)) == {};
                       assert recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));
                       return; }

      if (outside(k, pivot)) {assert recOwnersFringe(k,pivot) == {k};
                              assert recOwnersInside(k,pivot) == {};
                              assert recOwners(k) == recFlatten({k}) == recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot);
                              assert recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));
                              return;  }

      assert strictlyInside(k, pivot);

      // assert recOwnersFringe(k,pivot) == {k};
      // assert recOwnersInside(k,pivot) == {};
      // assert recOwners(k) == recFlatten({k}) == recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot);
//      assert recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));


      // assert recOwnersFringe(k,pivot) == (set x : Object <- recOwners(k) :: outside(x,pivot) && exists y : Object <- recOwners(k) :: inside(y,pivot) && (x in y.owner));
      // assert recOwnersInside(k,pivot) == (set x : Object <- recOwners(k) :: strictlyInside(x,pivot));

//ERER    assert recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));



          // then ({k})
          // else (set oo <- k.owner, ooo <- recOwnersFringe(oo, pivot) :: ooo)


//      asasssume recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));

     }

lemma  {:timeLimit 10} RecOwnerSanity5(k : Object, pivot : Object)
  //no ougoing owners (except beyond the pivot)
    requires k.Ready()
    requires pivot.Ready()
    requires strictlyInside(k,pivot)
    requires forall x <- k.AMFO :: strictlyInside(x,pivot) ==> forall y <- x.owner :: inside(y,pivot)
   decreases k.AMFO
     ensures recOwnersFringe(k, pivot) == {}
 //  ensures recOwners(k) == (recOwnersInside(k,pivot) + recOwnersPivot(k,pivot))
     {}



lemma  {:timeLimit 10} RecOwnerSanity6(k : Object, pivot : Object)
  //no ougoing owners (except beyond the pivot)
    requires k.Ready()
    requires pivot.Ready()
    requires strictlyInside(k,pivot)
   decreases k.AMFO
     ensures recOwnersInside(k,pivot) !! recFlatten(recOwnersFringe(k,pivot)) !! {pivot}   //fringe could own pivot, pivot cannot own fringef331 313333333331ff11f111ffr333331333
     ensures recOwnersInside(k,pivot) !! recFlatten({pivot})
     ensures (recFlatten(recOwnersFringe(k,pivot)) * recFlatten({pivot})) >= {}
     {}
