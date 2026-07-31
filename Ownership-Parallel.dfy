include "Ownership-Recursive.dfy"
include "Ownership-Lemmata.dfy"

/////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// mostly junk attempts to get shit to work what doesnt.
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
   //this never works :-)  ensures rv ==  {o} + (set xo <- o.owner, co <- recOwners(xo) :: co)
    ensures rv >=  {o} + (set xo <- o.owner, co <- recOwners(xo) :: co)
    { {o} + (set xo <- o.owner, co <- recOwners(xo) :: co) }

function {:verify false} recTRUMP_Broken(o : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    ensures rv <= o.AMFO
    ensures forall r <- rv :: r.Ready()
    ensures rv ==  {o} + (set xo <- o.owner, co <- recTRUMP_Broken(xo) :: co)
    ensures rv >=  {o} + (set xo <- o.owner, co <- recTRUMP_Broken(xo) :: co)
    { {o} + (set xo <- o.owner, co <- recTRUMP_Broken(xo) :: co) }

lemma {:verify false} I_AM_THE_FUCKER_BROKEN(o : Object, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires forall r <- rv :: r.Ready()
  requires rv == {o} + (set xo <- o.owner, co <- recOwners(xo) :: co)
   ensures (o.owner == {}) ==> (rv == recOwners(o))
   ensures rv == recOwners(o)
{
  if (o.owner == {}) {
      assert recOwners(o) == {o};
      assert recOwners(o) == {o} + (set xo <- o.owner, co <- recOwners(xo) :: co);
      return;
   }
   assert o.Ready();
   assert forall oo <- o.owner :: oo.Ready();
   assert AllReady( allAMFOs(o.owner) );
   assert AllReady( o.AMFO );
   assert o.owner > {};
   var todo := o.owner;
   assert AllReady(todo);
   var fuckrv := {o};
   assert fuckrv == {o} + set x : Object <- (o.owner - todo), yy : Object <- recOwners(x) :: yy;
   while (todo > {})
       decreases todo
 //      invariant fuckrv == {o} + set x : Object <- (o.owner - todo), yy : Object <- recOwners(x) :: yy
 //      invariant o.Ready()
//      invariant AllReady( allAMFOs(o.owner) )
 //      invariant AllReady( todo )
    {
      var next : Object;
      next :| next in todo;
OF_COURSE_I_FJUCKING_DECREASE(todo, next);
      assert next in todo;
      assert todo > (todo - {next});
      assert todo decreases to todo - {next};
      todo := todo - {next};

      //var nextrv := {next} + (set xo : Object <- next.owner, co <- recOwners(xo) :: co);
      var nextrv := recOwners(next);
      assert nextrv == {next} + (set xo : Object <- next.owner, co <- recOwners(xo) :: co);
      I_AM_THE_FUCKER_BROKEN(next,nextrv);
      assert nextrv == recOwners(next);
      fuckrv := fuckrv + nextrv;
      assert  fuckrv == {o} + set x : Object <- (o.owner - todo), yy : Object <- recOwners(x) :: yy;
    }
   assert fuckrv == {o} + set x : Object <- (o.owner - todo), yy : Object <- recOwners(x) :: yy;
   assert todo == {};
   assert fuckrv == {o} + set x : Object <- (o.owner), yy : Object <- recOwners(x) :: yy;
}

  //  forall xx : Object <- o.owner ensures (true) {
  //                    rv == {o} + (set xo <-           o.owner, co <- recOwners(xo) :: co)
  //    I_AM_THE_FUCKER(xx,  {xx} + (set xo : Object <- xx.owner, co <- recOwners(xo) :: co));
  //    assert recOwners(xx) == {xx} + (set xo <- xx.owner, co <- recOwners(xo) :: co);=

// function recOwners2(o : Object) : (rv : Owner)
//   decreases o.AMFO
//    requires o.Ready()
//     ensures rv <= o.AMFO
//     ensures forall r <- rv :: r.Ready()
//     ensures rv == recOwners(o)
//     { (set xo <- o.owner, co <- recOwners(xo)+{o} :: co) }


function prefixedPaths(o : Object, paths : set<seq<Object>>) : (rv : set<seq<Object>>)
  { set p <- paths :: [o] + p }

predicate pathFromTo(p : seq<Object>,f : Object, t : Object)
  decreases p
  requires |p| > 0
 {
  || (p == [f] == [t])    //too cute?
  || (&& (|p| > 1)
      && (p[0] == f)
      && (p[|p|-1] == t)
      && (p[1] in f.owner)
      && (pathFromTo(p[1..], p[1], t))
  )
 }



predicate pathFrom(p : seq<Object>,f : Object)
  decreases p
  requires |p| > 0
 {
  || (p == [f])    //too cute?
  || (&& (|p| > 1)
      && (p[0] == f)
      && (p[1] in f.owner)
      && (pathFrom(p[1..], p[1]))
  )
 }

function allObjectsInPaths(paths : set<seq<Object>>) : Owner
  {set p <- paths, o <- p :: o }

lemma {:verify false} allPathsGetAllOwners_BROKEN(k : Object)
  requires k.Ready()
  {
    var allPaths := recOwnerPaths(k);
    var allObjects := allObjectsInPaths(allPaths);
    assert allObjects == recOwners(k);
  }

lemma {:verify false} recOwnersAndPathsTogether_BROKEN(o : Object) returns (rp : set<seq<Object>>, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    // ensures forall ps <- rp, r <- ps :: r in o.AMFO
    // ensures forall ps <- rp, r : Object <- ps :: r.Ready()
    // ensures forall p <- rp :: (|p| > 0) && (p[0] == o) && (p[|p|-1].owner == {})
    // ensures forall p <- rp :: (|p| > 0) && pathFrom(p,o)
    // ensures allObjectsInPaths(rp) == recOwners(o)
    ensures rp == recOwnerPaths(o)
    ensures rv == recOwners(o)
    {
     var todo : Owner  := o.owner;

     rp := {};
     rv := {o};

     while (todo > {})
       decreases todo
       invariant rp == set x : Object <- (o.owner - todo), xx <- recOwnerPaths(x) :: [x]+xx
       invariant rv == {o} + set x : Object <- (o.owner - todo), xx : Object <- recOwners(x) :: xx
        {
          var each: Object;
          each :| each in todo;
          todo := todo - {each};

          var ep, ev := recOwnersAndPathsTogether_BROKEN(each);
                                      assert ep == recOwnerPaths(each);
                                      assert ev == recOwners(each);
          var eep := (set p <- ep :: [each]+p);
          var eev := {each} + ev;   var eev0 := ev;

          rp := rp + eep;
                                      assert rp == set x : Object <- (o.owner - todo), xx <- recOwnerPaths(x) :: [x]+xx;

          rv := rv + eev;   var rv0 := rv + {each} + eev0;
                                      assert rv0 == rv;
                                      assert rv == {o} + set x : Object <- (o.owner - todo), xx : Object <- recOwners(x) :: xx;
        }
    assert rp == set x : Object <- (o.owner - todo), xx <- recOwnerPaths(x) :: [x]+xx;
    assert todo == {};
    assert rp == set x : Object <- (o.owner), xx <- recOwnerPaths(x) :: [x]+xx;

   // assert rp == set x   : Object <- o.owner, xx <- recOwnerPaths(x)  :: [x]+xx;
    //assert rp == (set xo          <- o.owner, co <- recOwnerPaths(xo) :: [o]+co);
    assert rp == recOwnerPaths(o);


// assume rp == recOwnerPaths(o);

    assert  rv == {o} + set x : Object <- (o.owner - todo), xx : Object <- recOwners(x) :: xx;
    assert todo == {};
    assert  rv == {o} + set x : Object <- o.owner, xx : Object <- recOwners(x) :: xx;
    assert  rv == {o} + (set xo <- o.owner, co <- recOwners(xo) :: co);
I_AM_THE_FUCKER_BROKEN(o,rv);
    var roo :=  recOwners(o);
    assert rv >= roo;
    assert rv <= roo;

    assert rv == recOwners(o);
    }

lemma OF_COURSE_I_FJUCKING_DECREASE( todo : Owner, next : Object )
  requires next in todo
   ensures todo > (todo-{next})
   ensures todo decreases to (todo-{next})
   {}


function recOwnerPaths(o : Object) : (rv : set<seq<Object>>)
  decreases o.AMFO
   requires o.Ready()
    ensures forall ps <- rv, r <- ps :: r in o.AMFO
    ensures forall ps <- rv, r : Object <- ps :: r.Ready()
    ensures forall p <- rv :: (|p| > 0) && (p[0] == o) && (p[|p|-1].owner == {})
    ensures forall p <- rv :: (|p| > 0) && pathFrom(p,o)
    ensures allObjectsInPaths(rv) <= o.AMFO
    // ensures allObjectsInPaths(rv) >= o.AMFO
    { (set xo <- o.owner, co <- recOwnerPaths(xo) :: [o]+co) }




function findallPathsFromTo1(f : Object, t : Object) : (rp : set<seq<Object>>)
    decreases f.AMFO
     requires f.Ready()
     requires t.Ready()
     requires f != t
     requires inside(f,t)
     requires t.owner == {}
      ensures forall p <- rp:: (|p| > 0) && pathFromTo(p,f,t)
  { set p <- recOwnerPaths(f) | (|p| > 0) && pathFromTo(p,f,t) }


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
     ensures o.owner <= ro
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
   // ensures recFlatten(oo) == (set o : Object <- oo :: collectAllOwnersWithoutExtraOwners(o))

   { }


predicate pivotlyOutside(p : Object, w : Object) : (rv : bool)
   //WTF Does this mean?  it means outsideOrEquals!
  //  ensures rv == ((p == w) || outside(p,w))
  //  ensures rv == (not(p.AMFO > w.AMFO))
    {((p == w) || outside(p,w))}

function recOwnersInsideOLD(k : Object, pivot : Object) : (rv : Owner)
 //returns all k's owners that are *strictly* inside the pivot
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: strictlyInside(r, pivot)
    // ensures forall r <- recOwners(k) :: strictlyInside(r, pivot) ==> (r in rv)
//     ensures rv == set r <- recOwners(k) | strictlyInside(r, pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if (not(strictlyInside(k, pivot)))
      then ({})
      else ({k} + (set oo <- k.owner, ooo <- recOwnersInside(oo, pivot) :: ooo))
  }


function recOwnersInside(k : Object, pivot : Object) : (rv : Owner)
 //returns all k's owners that are *strictly* inside the pivot
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: strictlyInside(r, pivot)
  {
    if (strictlyInside(k, pivot))
      then ({k} + (set oo <- k.owner, ooo <- recOwnersInside(oo, pivot) :: ooo))
      else ({})
  }


function rocOwnersInside(k : Object, pivot : Object) : (rv : Owner)
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: strictlyInside(r, pivot)
     ensures forall r <- recOwners(k) :: strictlyInside(r, pivot) ==> (r in rv)
     ensures forall r <- rv :: strictlyInside(r, pivot)
     ensures forall r <- rv :: r in recOwners(k)
     ensures forall r <- rv :: r in k.AMFO
     ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
     ensures (set r <- k.AMFO | strictlyInside(r, pivot)) == rv
 //      ensures rv == recOwnersInside(k, pivot)
  { RecOwnersIsAMFO(k);
    set r <- recOwners(k) | strictlyInside(r, pivot) }


//{:verify false}
lemma RecOwnersInsideClosedForm(k : Object, pivot : Object, rv : Owner)
    requires k.Ready()
    requires pivot.Ready()
    requires rv == recOwnersInside(k,pivot)
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: strictlyInside(r, pivot)
    // ensures forall r <- recOwners(k) :: strictlyInside(r, pivot) ==> (r in rv)
     ensures forall r <- rv :: strictlyInside(r, pivot)
     ensures forall r <- rv :: r in recOwners(k)
     ensures forall r <- rv :: r in k.AMFO
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
   //  ensures (set r <- k.AMFO | strictlyInside(r, pivot)) == rv
  //   ensures recOwnersInside(k,pivot) == (set r <- k.AMFO | strictlyInside(r, pivot))
   // ensures rv == set r <- recOwners(k) | strictlyInside(r, pivot)
   //  ensures rv == rocOwnersInside(k,pivot)
  { RecOwnersIsAMFO(k); }



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

    assert                     (rv.owners == recOwners(k));
    assert running'.inside ==> (rv.inside == recOwnersInside(k, pivot));
    assert running'.fringe ==> (rv.fringe == recOwnersFringe(k, pivot));
    assert running'.pivot  ==> (rv.pivot  == recOwnersPivot(k, pivot));

    // if (running'.inside && running'.fringe && running'.pivot) {
    //    assert rv.owners == rv.inside +  recFlatten(rv.fringe) + rv.pivot;
    // }
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
 //if k is the pivot or outside it, then all k's owners
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


function recOwnersOutside2(k : Object, pivot : Object) : (rv : Owner)
 //if k is the pivot or outside it, then all k's owners
 //otherwise nothing
   requires k.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
     ensures forall r <- rv :: pivotlyOutside(r, pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if ((k == pivot) || outside(k,pivot))
      then ({k} + set oo <- k.owner, ooo <- recOwnersOutside2(oo,pivot) :: ooo)
      else       (set oo <- k.owner, ooo <- recOwnersOutside2(oo,pivot) :: ooo)
  }


function recOwnersPivot(k : Object, pivot : Object) : (rv : Owner)
///if k inside pviot then pivot * owners
//opthwerise not
   requires k.Ready()
   requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
    ensures rv <= recOwners(k)
     ensures forall r <- rv :: outside(r, pivot) || (r == pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if (inside(k, pivot))
      then (recOwners(pivot))
      else ({})    ///?
  }

function recOwnersPivot2(k : Object, pivot : Object) : (rv : Owner)
///if k inside pviot then pivot * owners
//opthwerise not
   requires k.Ready()
   requires pivot.Ready()
   decreases k.AMFO
     ensures rv <= k.AMFO
    ensures rv <= recOwners(k)
     ensures forall r <- rv :: outside(r, pivot) || (r == pivot)
   //  ensures forall r <- k.AMFO :: strictlyInside(r, pivot) ==> (r in rv)
  {
    if (inside(k, pivot))
      then (recOwners(pivot))
      else (set oo <- k.owner, ooo <- recOwnersPivot2(oo,pivot) :: ooo)
  }

  lemma RecOwnersOutsidePivot(k : Object, pivot : Object)
   decreases k.AMFO
    requires k.Ready()
    requires pivot.Ready()
    requires (k == pivot) || outside(k,pivot)
     ensures not(strictlyInside(k, pivot))
     ensures forall oo <- k.owner :: k.Ready()
     ensures forall oo <- k.owner :: outside(oo,pivot)
     ensures (strictlyInside(k, pivot)) != ((k == pivot) || outside(k, pivot))
     ensures recOwnersOutside2(k,pivot) == recOwners(k)
{}

  lemma RecOwnersInsidePivot(k : Object, pivot : Object)
   decreases k.AMFO
    requires k.Ready()
    requires pivot.Ready()
    requires strictlyInside(k,pivot)
     ensures not( (k == pivot)   ||      outside(k,pivot))
     ensures not( (k == pivot))  &&  not(outside(k,pivot))
//     ensures forall oo <- k.owner :: outside(oo,pivot)
    //  ensures (strictlyInside(k, pivot)) != ((k == pivot) || outside(k, pivot))
     ensures recOwnersInside(k,pivot) == set o <- recOwners(k) | strictlyInside(o, pivot)
     {
      k.ExtraReady();
     }


//
//     ensures (recOwnersOutside2(k,pivot) + recOwnersInside(k,pivot) == recOwners(k))
// {
//
// ///rec owners inside
//     if (strictlyInside(k, pivot)) {
//
//     }
//       then ({k} + (set oo <- k.owner, ooo <- recOwnersInside(oo, pivot) :: ooo))
//       else ({})
//
//
// }


lemma RecOwnersIsAMFO(k : Object)
  decreases k.AMFO
   requires k.Ready()
    ensures recOwners(k) == k.AMFO
    { RecOwnersIsAMFO1(k); RecOwnersIsAMFO2(k); }

lemma RecOwnersIsAMFO1(k : Object)
  decreases k.AMFO
   requires k.Ready()
    ensures recOwners(k) >= k.AMFO
    {}

lemma RecOwnersIsAMFO2(k : Object)
  decreases k.AMFO
   requires k.Ready()
    ensures recOwners(k) <= k.AMFO
    {
      assert k in recOwners(k);
      assert k in k.AMFO;
    }


function recOwnersFringe(k : Object, pivot : Object) : (rv : Owner)
    requires k.Ready()
   decreases k.AMFO
     ensures forall r <- rv :: outside(r,pivot)
//     ensures forall i <- recOwners(k), j <- i.owner | strictlyInside(i, pivot) && outside(j,pivot) :: j in rv
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
 //    ensures recOwnersFringe(k, pivot) == set i <- recOwners(k), j <- i.owner | strictlyInside(i, pivot) && pivotlyOutside(j,pivot) :: j
    //  ensures forall r <- recOwnersFringe(k, pivot) :: exists x <- recOwnersInside(k, pivot) :: r in x.owner
   decreases k.AMFO
  {}

lemma RecOwnerTrans(k : Object, pivot : Object)
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

lemma RecOwnerSanity0(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersInside(k,pivot) <= recOwners(k)
     ensures forall x <- recOwnersInside(k,pivot) :: inside(x,pivot)
 //hmm    ensures forall x <- recOwners(k) | inside(x,pivot) ::  x in recOwnersInside(k,pivot)
 {}

lemma RecOwnerSanity1(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersFringe(k,pivot) <= recOwners(k)
     ensures forall x <- recOwnersFringe(k,pivot) :: outside(x,pivot)
     ensures forall o <- recOwnersFringe(k,pivot) :: exists x <- recOwnersInside(k,pivot) :: o in x.owner
{}

lemma RecOwnerSanity2(k : Object, pivot : Object)
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

lemma RecOwnerSanity3(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersPivot(k,pivot) == recOwners(pivot)
{}

lemma RecOwnerSanity3bis(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires not(inside(k, pivot))
   decreases k.AMFO
     ensures recOwnersPivot(k,pivot) == {}
{}

lemma RecOwnerSanity3alpha(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwners(k) == recOwnersOutside(k,pivot) + recOwnersInside(k,pivot)
{}

lemma RecOwnerSanity3beta(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
    requires inside(k, pivot)
   decreases k.AMFO
     ensures recOwnersOutside(k,pivot) == recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot)
{}

lemma RecOwnerSanity4(k : Object, pivot : Object)
    requires k.Ready()
    requires pivot.Ready()
   decreases k.AMFO
     ensures recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot))
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

      assert not(outside(k, pivot));  assert not(not(inside(k, pivot)));  assert inside(k,pivot);  assert(k != pivot);
      assert strictlyInside(k, pivot);

   //   assert recOwnersInside(k,pivot) == set o <- recOwners(k) | strictlyInside(o,pivot);
      assert recOwnersPivot(k,pivot)  == recOwners(pivot);

      assert recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot));
     }


lemma {:isolate_assertions} RecOutsideOutside(k : Object, pivot : Object)
     requires k.Ready()
     requires pivot.Ready()
    decreases k.AMFO
     requires outside(k,pivot)
      ensures forall o <- recOwners(k) ::  outside(o, pivot)
    {}



lemma {:isolate_assertions} RecOwnerInside(k : Object, pivot : Object)
     requires k.Ready()
     requires pivot.Ready()
    decreases k.AMFO
    // requires inside(k,pivot)
     requires pivot in k.owner
      ensures pivot in k.AMFO
      ensures pivot in recOwners(k)
    { RecOwnersIsAMFO(k); }


function amfoOwners(k : Object) : Owner {k.AMFO}

lemma {:isolate_assertions} RecOwnerClassify4(k : Object, pivot : Object)
     requires k.Ready()
     requires pivot.Ready()
    decreases k.AMFO
 //    ensures recOwners(k) == (recOwnersInside(k,pivot) +  recFlatten(recOwnersFringe(k,pivot)) + recOwnersPivot(k,pivot))
     {
        var owners := recOwners(k);
        assert forall f <- owners :: inside(k,f);

        forall o <- owners ensures (strictlyInside(o,pivot)) //by
         {
            assert strictlyInside(o,pivot) != pivotlyOutside(o, pivot);

            if (pivotlyOutside(o, pivot)) {






            }

         }

        var pivown := set o <- owners | strictlyInside(o,pivot);
        assert pivot !in pivown;
        assert recOwners(pivot) !! pivown;
        assert forall f <- pivown :: inside(k,f);
        assert pivown <= owners;

           var sea_outside := owners - pivown;
        assert pivown !! sea_outside;
        assert owners == pivown + sea_outside;

        assert forall o : Object <- recOwners(k), io <- o.owner :: io in recOwners(k);
        assert forall o : Object <- owners, io <- o.owner :: io in owners;


           var fringe := set i : Object <- pivown, io <- i.owner | outside(io, pivot) :: io;
        assert fringe == set i : Object <- owners, io <- i.owner | strictlyInside(i,pivot) && outside(io, pivot) :: io;
        assert pivot !in fringe;
        assert forall f <- fringe :: outside(f,pivot);
        assert forall f <- fringe ::  inside(k,f);
        assert fringe <= owners;
        assert pivown + fringe <= owners;
        assert fringe <= sea_outside;


           var flatFringe := set i : Object <- pivown, io <- (recOwners(i) - {i}) | outside(io, pivot) :: io;
        assert flatFringe == set i : Object <- owners, io <- recOwners(i) | strictlyInside(i,pivot) && outside(io, pivot) :: io;
        assert pivot !in flatFringe;
        assert forall f <- flatFringe :: outside(f,pivot);
        assert forall f <- flatFringe ::  inside(k,f);
        assert flatFringe <= owners;
        assert pivown + flatFringe <= owners;
        assert flatFringe <= sea_outside;

           var flatPivot := recOwners(pivot);
        assert forall f <- flatPivot :: pivotlyOutside(f,pivot);
        assert forall f <- flatPivot ::  inside(k,f);
        assert flatPivot <= owners;
        assert (pivown + flatFringe + flatPivot) <= owners;
        assert flatPivot <= sea_outside;
        assert flatFringe + flatPivot <= sea_outside;


        assert pivown !! flatFringe;
        assert pivown !! flatPivot;
        assert pivown !! (flatFringe + flatPivot);

        assert flatFringe !! {pivot};

        assert flatPivot  * fringe >= {};  //may or may not be Vroomfondel
         //may or may not be Vroomfondel


        assert forall o <- sea_outside :: not(strictlyInside(o,pivot));

        assert flatPivot  <= sea_outside;
        assert flatFringe <= sea_outside;



        assert sea_outside == flatPivot + flatFringe;




//         assert forall o <- owners ::
//            && (strictlyInside(o,pivot) <==> (o in pivown))
//            && (pivotlyOutside(o,pivot) <==> ((o in flatPivot) || (o in flatFringe)))
//            ;
//
//         assert owners <= pivown + flatFringe + flatPivot;


//         assert owners >= pivown + flatFringe + flatPivot;

 //       assert owners == pivown + flatFringe + flatPivot;

     }



lemma {:isolate_assertions} RecOwnerClassifyAMFO(k : Object, pivot : Object)
     requires k.Ready()
     requires pivot.Ready()
     requires inside(k,pivot) //is this wha we want???????
    decreases k.AMFO
 //    ensures amfoOwners(k) == (amfoOwnersInside(k,pivot) +  recFlatten(amfoOwnersFringe(k,pivot)) + amfoOwnersPivot(k,pivot))
     {
           var owners := amfoOwners(k);
        assert forall f <- owners :: inside(k,f);

           var pivown := set o <- owners | strictlyInside(o,pivot);
        assert pivot !in pivown;
        assert amfoOwners(pivot) !! pivown;
        assert forall f <- pivown :: inside(k,f);
        assert pivown <= owners;

           var sea_outside := owners - pivown;
        assert pivown !! sea_outside;
        assert owners == pivown + sea_outside;

        assert forall o : Object <- amfoOwners(k), io <- o.owner :: io in amfoOwners(k);
        assert forall o : Object <- owners, io <- o.owner :: io in owners;


           var fringe := set i : Object <- pivown, io <- i.owner | outside(io, pivot) :: io;
        assert fringe == set i : Object <- owners, io <- i.owner | strictlyInside(i,pivot) && outside(io, pivot) :: io;
        assert pivot !in fringe;
        assert forall f <- fringe :: outside(f,pivot);
        assert forall f <- fringe ::  inside(k,f);
        assert fringe <= owners;
        assert pivown + fringe <= owners;
        assert fringe <= sea_outside;


           var flatFringe := set i : Object <- pivown, io <- (amfoOwners(i) - {i}) | outside(io, pivot) :: io;   //dont need to -i cos i inside pivot
        assert flatFringe == set i : Object <- owners, io <- (amfoOwners(i) - {i}) | strictlyInside(i,pivot) && outside(io, pivot) :: io;
        assert pivot !in flatFringe;
        assert forall f <- flatFringe :: outside(f,pivot);
        assert forall f <- flatFringe ::  inside(k,f);
        assert flatFringe <= owners;
        assert pivown + flatFringe <= owners;
        assert flatFringe <= sea_outside;

           var flatPivot := amfoOwners(pivot);
        assert forall f <- flatPivot :: pivotlyOutside(f,pivot);
        assert flatPivot <= owners;
        assert forall f <- flatPivot :: inside(k,f);
        assert (pivown + flatFringe + flatPivot) <= owners;
        assert flatPivot <= sea_outside;
        assert flatFringe + flatPivot <= sea_outside;


        assert pivown !! flatFringe;
        assert pivown !! flatPivot;
        assert pivown !! (flatFringe + flatPivot);

        assert flatFringe !! {pivot};

        assert flatPivot  * fringe >= {};  //may or may not be Vroomfondel
         //may or may not be Vroomfondel


        assert forall o <- sea_outside :: not(strictlyInside(o,pivot));

        assert flatPivot  <= sea_outside;
        assert flatFringe <= sea_outside;
        assert flatPivot + flatFringe <= sea_outside;

//         assert (flatPivot + flatFringe >= sea_outside)
//          by {
//           forall o <- sea_outside ensures (o in (flatPivot + flatFringe)) //by
//            {
//             assert inside(k,o);   assert o in owners;
//             assert not(strictlyInside(o,pivot));
//
//             assert exists x : Object <- pivown :: o in x.owner;
//
//            }
//         }


//         assert forall o <- owners ::
//            && (strictlyInside(o,pivot) <==> (o in pivown))
//            && (pivotlyOutside(o,pivot) <==> ((o in flatPivot) || (o in flatFringe)))
//            ;
//
//         assert owners <= pivown + flatFringe + flatPivot;


//         assert owners >= pivown + flatFringe + flatPivot;

 //       assert owners == pivown + flatFringe + flatPivot;

     }


lemma RecOwnerSanity5(k : Object, pivot : Object)
  //????no ougoing owners (except beyond the pivot)
  //assuming no "sidewayws owners"  then ....
    requires k.Ready()
    requires pivot.Ready()
    requires strictlyInside(k,pivot)
    requires forall x <- k.AMFO :: strictlyInside(x,pivot) ==> forall y <- x.owner :: inside(y,pivot)
   decreases k.AMFO
     ensures recOwnersFringe(k, pivot) == {}
//     ensures recOwners(k) == (recOwnersInside(k,pivot) + recOwnersPivot(k,pivot))
     {}



lemma RecOwnerSanity6(k : Object, pivot : Object)
  //????no ougoing owners (except beyond the pivot)
    requires k.Ready()
    requires pivot.Ready()
    requires strictlyInside(k,pivot)
   decreases k.AMFO
     ensures recOwnersInside(k,pivot) !! recFlatten(recOwnersFringe(k,pivot)) !! {pivot}   //fringe could own pivot, pivot cannot own fringe
     ensures recOwnersInside(k,pivot) !! recFlatten({pivot})
     ensures (recFlatten(recOwnersFringe(k,pivot)) * recFlatten({pivot})) >= {}
     {}










































































lemma {:isolate_assertions} AllWholeInsidePart(partO : Owner, wholeO : Owner)
   //HOW THE FUCK DOES THIS HELP AT ALL???
  requires AllReady(partO)
  requires AllReady(wholeO)
  requires flatten(partO) >= flatten(wholeO)
   ensures forall o <- flatten(wholeO) :: o in flatten(partO)
  {}


lemma {:isolate_assertions} MappedAllWholeInsidePart(partO : Owner, wholeO : Owner, m : Klon)
  requires AllReady(partO)
  requires AllReady(wholeO)
  requires flatten(partO) >= flatten(wholeO)
  requires partO  <= m.m.Keys
  requires wholeO <= m.m.Keys
   ensures forall o <- flatten(wholeO) :: o in flatten(partO)
 //  ensures mapThruKlon(partO,m) >= mapThruKlon(wholeO,m)
//   ensures forall o <- mapThruKlon(wholeO,m) :: o in mapThruKlon(partO,m)
//   ensures forall o <- flatten(mapThruKlon(wholeO,m)) :: o in flatten(mapThruKlon(partO,m))
  {}


lemma {:isolate_assertions} DivotInsidePivot(oo : Owner, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)

  requires oo <= m.m.Keys
  requires exists o <- oo :: o.AMFO > m.o.AMFO

   ensures flatten(oo) >= m.o.AMFO
  {}



lemma {:isolate_assertions} DOESN_TWORK_RivetInsideBlivet(oo : Owner, co : Owner, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)

  requires oo <= m.m.Keys
 // requires oo > {}
  // requires exists o <- oo :: o.AMFO > m.o.AMFO
  requires mflat(oo) >= m.o.AMFO
   ensures forall o <- m.o.AMFO :: o in  mflat(oo)
   ensures m.o in mflat(oo)

 // requires flatten(oo) >= m.o.AMFO             /// more flexible but let's walk before we run - doesn't verify with this

  requires oo <= m.m.Keys
  requires co == mapThruKlon(oo, m)
//
//   ensures forall o <- oo :: klonLine(o, m.m[o], m)
//
//
//    ensures forall o <- oo :: (o == m.o)     <==> (m.m[o] == m.c)
//    ensures forall o <- oo :: inside(o, m.o) <==> inside(m.m[o], m.c)
//    ensures forall o <- oo :: inside(o, m.o) <==> inside(m.m[o], m.c)

   ensures mflat(oo) >= m.o.AMFO
//   ensures mflat(co) >= m.c.AMFO
  {}




lemma {:isolate_assertions} FlattenMapsTheSame(oo : Owner, bb : Bound, co : Owner, cb : Bound, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)
  requires AllReady(bb)
  requires AllReady(co)
  requires AllReady(cb)

  requires oo <= m.m.Keys
  requires bb <= m.m.Keys
  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(bb, m)

  requires forall o <- oo :: o.AMFO > m.o.AMFO
  requires forall o <- bb :: o.AMFO > m.o.AMFO

  requires oo != bb
  requires flatten(oo) == flatten(bb)
//   ensures flatten(co) == flatten(cb)
{
  assert flatten(bb) >= bb;
  assert flatten(oo) >= flatten(bb);

  assert flatten(co) >= co;
  assert flatten(cb) >= cb;



//
//   forall  o <- oo  ensures (m.m[o] in co) //
//     {
//       assert o.Ready() && (o in o.AMFO) && (o in oo);
//       assert flatten({o}) == o.AMFO;
//       assert o.AMFO <= flatten(oo);
//       assert o.AMFO <= flatten(bb);
//       assert flatten({o}) <= flatten(bb);
//
//       assert m.m[o] in mapThruKlon(oo, m);
//
//       var c := m.m[o];
//       assert c in co;
//       assert o in flatten(bb);
//       assert c in flatten(co);
//       assert c in flatten(cb);
//       assert o.AMFO <= flatten(bb);
//       assert c.AMFO <= flatten(co);
//     }




//  assert forall o <- flatten(oo) :: flatten({o}) == o.AMFO;

  // assert forall o <- flatten(oo) :: o            in flatten(bb);
  // assert forall o <-        (oo) :: flatten({o}) <= flatten(oo);

//  assert forall o <-        (oo) :: flatten(mapThruKlon({o},m)) <= flatten(cb);


}


lemma {:isolate_assertions} TOO_EASY_TO_WORK(oo : Owner, bb : Bound, co : Owner, cb : Bound, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)
  requires AllReady(bb)
  requires AllReady(co)
  requires AllReady(cb)

  requires {} < oo <= m.m.Keys
  requires bb <= m.m.Keys
  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(bb, m)

  requires oo != bb
  requires flatten(oo) >= flatten(bb)
//   ensures flatten(co) >= flatten(cb)
{
 // assert oo >= bb;  //shouldb't work

  forall o <- oo ensures (true)
  {


  }
}




lemma {:verify false} DOESNT_WORK_EITHER(oo : Owner, bb : Bound, co : Owner, cb : Bound, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)
  requires AllReady(bb)
  requires AllReady(co)
  requires AllReady(cb)

  requires {} < oo <= m.m.Keys
  requires bb <= m.m.Keys
  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(bb, m)

  requires oo != bb
  requires mflat(oo) >= mflat(bb)
   ensures mflat(co) >= mflat(cb)
{
 // assert oo >= bb;  //shouldb't work

  forall o <- oo ensures (true)
  {


  }
}


//
//   assert forall o <- flatten(bb) :: o            in flatten(oo);
//   assert forall o <-        (bb) :: flatten({o}) <= flatten(oo);
//
//   assert forall o <-        (bb) :: mapThruKlon({o},m) <= mapThruKlon(bb,m);
//   assert forall o <-        (bb) :: flatten(mapThruKlon({o},m)) <= flatten(cb);
//
//   assert forall o <-        (bb) :: mapThruKlon({o},m) <= mapThruKlon(oo,m);
//   assert forall o <-        (bb) :: flatten(mapThruKlon({o},m)) <= flatten(co);
//
//   assert forall o <- mapThruKlon(bb,m) :: flatten(            {o}   ) <= flatten(cb);
//
//
//   assert forall o <-        (cb) :: flatten(            {o}   ) <= flatten(cb);
//
//   assert forall o <- bb :: flatten({o}) <= flatten(oo);
//   assert forall o <- bb :: flatten(mapThruKlon({o},m)) <= flatten(mapThruKlon(oo,m));



  //assert forall o <-        (cb) :: flatten({o}) <= flatten(co);


  // assert forall o <-        (cb) :: flatten(            {o}   ) <= flatten(co);

//  assert forall o <-        (bb) :: flatten(mapThruKlon({o},m)) <= flatten(co);
//  assert forall o <-        (bb) :: flatten(mapThruKlon({o},m)) <= flatten(co);



lemma {:verify false} FlattenInsideGEQ(oo : Owner, bb : Bound, co : Owner, cb : Bound, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(oo)
  requires AllReady(bb)
  requires AllReady(co)
  requires AllReady(cb)

  requires flatten(oo) >= m.o.AMFO

  requires oo <= m.m.Keys
  requires bb <= m.m.Keys
  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(bb, m)

  requires myBoundsOK(oo,bb)
  // ensures myBoundsOK(co,cb)
 {
  assert (flatten(oo) >= flatten(bb));

   if (m.o.AMFO > flatten(bb))
     {
      assert forall x <- flatten(bb) :: outside(x, m.o);
      assert forall x <- flatten(bb) :: m.m[x] == x;
      assert mapThruKlon(bb,m) == cb == bb;
      assert flatten(cb) == flatten(bb);

      assert flatten(oo) >= flatten(bb);
      assert flatten(oo) >= m.o.AMFO;
      assert flatten(m.clbound) >= m.c.AMFB;
      assert flatten(co) >= flatten(cb);

      assert (m.c.AMFO) >= flatten(m.o.bound);

//      assert (flatten(co) >= flatten(cb));
     }

 }
