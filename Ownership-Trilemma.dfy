include "Ownership-Recursive.dfy"
include "Set-Lemmata.dfy"
include "Ownership-Recursive.dfy"
//include "Ownership-Parallel.dfy"
include "Context.dfy"


///this file containts the "trilemma" to prove (potential) owners are where they aught to be
///before those owners actually exist.  Three main parts:
/// 1. Trilemma / Trilennnna structure itself
/// 2.
/// 3. efintions that classify actual owners
/// 4. equivalence proofs...
/// 5. there is a light that never goes out

///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///
/// 1. Trilemma / Trilennnna structure itself


datatype Trilennnna = Trilennnna(owners : Owner, flatness : OWNR, pivot : Object, above : Owner, middle : Owner, below : Owner)
{
  predicate Valid() {
    && (flatness    == flatten(owners))
    && (below == flattenStrictlyInside(owners, pivot))
    && (middle == (if (pivot in flatness) then (pivot.AMFO) else {}))
    && (above  == flattenOutside(owners, pivot))
    && (flatness    == above + middle + below)
  }

  lemma ExtraValid()
     requires Valid()
      ensures (below == allStrictlyInside(flatness,pivot))
  {}

  lemma LEMMA_below()
    requires Valid()
     ensures below == (set x <- flatness | strictlyInside(x,pivot))
     ensures below == allStrictlyInside(flatness,pivot)
     ensures PRED_below1()
     ensures PRED_below2()
      {}

  predicate PRED_below1() {below == (set x <- flatness | strictlyInside(x,pivot))}
  predicate PRED_below2() {below == allStrictlyInside(flatness,pivot)}

}




type Trilemma = t : Trilennnna | t.Valid() witness * //ARGH ARGH

function makeTrilemma(owners : Owner, flatness : OWNR, pivot : Object, above : Owner, middle : Owner, below : Owner) : Trilemma
    requires (flatness == flatten(owners))
    requires (below == (set x <- flatness | strictlyInside(x,pivot)))
    requires (middle == (if (pivot in flatness) then (pivot.AMFO) else {}))
    requires (above  == flattenOutside(owners, pivot))
    requires (flatness == above + middle + below)

 {
   Trilennnna(owners,flatness,pivot,above,middle,below) as Trilemma
 }


///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///
/// 2.  the defintion of new bounds that we hope will work.

function proposeOwnerAndBound(kowner : Owner, kbound : Bound, m : Klon) : (r : (Owner, Bound))
  requires AllReady(kowner)
  requires AllReady(kbound)
  requires m.m.Keys >= kowner
  requires m.m.Keys >= kbound
  requires myBoundsOK(kowner, kbound)
  requires klonReady(m)
  requires klonCalid(m)
   ensures myBoundsOK(r.0, r.1)
     reads m.hns()
 {
   var rowner := mapThruKlon(kowner, m);
   var rbound := mapThruKlon(kbound, m);
   //ici c'est la problème
   assume myBoundsOK(rowner, rbound);
   (rowner, rbound)
 }



///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///
/// 3. defintions that classify actual owners



function collectAllOutside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures (o == pivot) || not(inside(o,pivot)) ==> (rv == o.AMFO)
    ensures (o == pivot) ==> (rv == pivot.AMFO)
//    ensures inside(o,pivot) ==> (rv >= pivot.AMFO)
    {
      if (not(strictlyInside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- collectAllOutside(oo, pivot) :: ooo)
    }

function collectAllOutside'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures (o == pivot) ==> (rv == pivot.AMFO)
    ensures not(inside(o,pivot)) ==> (rv == o.AMFO)
//    ensures inside(o,pivot) ==> (rv >= pivot.AMFO)
//see _LEMMA3 = rv >= pivot.AMFO
//    ensures not( strictlyInside(o,pivot) || (o == pivot) ) ==> (rv == o.AMFO)
    {
      STRICTLY_COME_INSIDE(o,pivot);

      if (o == pivot) then (pivot.AMFO) //==pivot.amfo
        else if (not(inside(o,pivot))) then (o.AMFO)
          else
           (assert strictlyInside(o,pivot);
           (set oo <- o.owner, ooo <- collectAllOutside'(oo, pivot) :: ooo))

      // if (not(strictlyInside(o,pivot))) then (o.AMFO)
      //     else (set oo <- o.owner, ooo <- collectAllOutside(oo, pivot) :: ooo)

    }

lemma collectAllOutside_LEMMA4(o : Object, pivot : Object, rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires rv == collectAllOutside(o,pivot)
    ensures (o == pivot) ==> (rv == pivot.AMFO)
    ensures strictlyInside(o,pivot) ==> (rv >= pivot.AMFO)
{
   if (not(strictlyInside(o,pivot))) {return;}
   assert strictlyInside(o,pivot);
   ThereIsALightThatNeverGoesOut(o,pivot);
   if (pivot in o.owner) { assert collectAllOutside(pivot, pivot) == pivot.AMFO; assert rv >= pivot.AMFO; return; }
   assert pivot !in o.owner;
   assert exists x <- o.owner :: strictlyInside(x,pivot);
   var x :| x in o.owner && strictlyInside(x,pivot);
   var xrv := collectAllOutside(x,pivot);
   collectAllOutside_LEMMA4(x, pivot, xrv);
   assert xrv >= pivot.AMFO;
}

//COPIED from BROWNE!!!
function collectAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners strictly inside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- collectAllInside(oo, pivot) :: ooo)
    }

function collectOutsideOnlyPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
//   requires o.Ready()
//   requires pivot.Ready()
    ensures strictlyInside(o,pivot)                      ==> (rv == pivot.AMFO)
    ensures (o == pivot)                                 ==> (rv == pivot.AMFO)
    ensures (strictlyInside(o,pivot) || (o == pivot))    ==> (rv == pivot.AMFO)
//    ensures (inside(o,pivot))                            ==> (rv == pivot.AMFO)

    ensures not(strictlyInside(o,pivot) || (o == pivot)) ==> (rv == {})
 // ensures (outside(o,pivot))                           ==> (rv == {})

    ensures (if (strictlyInside(o,pivot) || (o == pivot)) then (rv == pivot.AMFO) else (rv == {}))
    ensures rv == if (strictlyInside(o,pivot) || (o == pivot)) then (pivot.AMFO) else ({})
 // ensures (if (inside(o,pivot)) then (rv == pivot.AMFO) else (rv == {}))
 // ensures rv == if (inside(o,pivot)) then (pivot.AMFO) else ({}))
    ensures (rv == {}) || (rv == pivot.AMFO)
    ensures forall p  <- pivot.AMFO :: pivot.AMFO >= p.AMFO
    ensures forall r <- rv :: pivotlyOutside(r, pivot)
    ensures forall r <- rv :: r in o.AMFO
    ensures forall r <- rv :: pivot.AMFO >= r.AMFO
    {
      assume o.Ready();
      assume pivot.Ready();
      pivot.ExtraReady();
//      if (inside(o,pivot)) then (pivot.AMFO) else ({})
     if (strictlyInside(o,pivot)) then (pivot.AMFO)
      else if (o == pivot) then (pivot.AMFO)
        else ({})
    }

lemma StrictlyNotStrictly(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures strictlyInside(o,pivot)                    ==> inside(o,pivot)
    ensures (o == pivot)                               ==> inside(o,pivot)
    ensures (strictlyInside(o,pivot) || (o == pivot))  ==> inside(o,pivot)
    ensures (strictlyInside(o,pivot) || (o == pivot)) <==  inside(o,pivot)
    ensures (strictlyInside(o,pivot) != (o == pivot)) <==> inside(o,pivot)
{
  if (inside(o,pivot))
    {
      assert o.AMFO >= pivot.AMFO;

      if (o.AMFO == pivot.AMFO)
        {
          AXIOMAMFOS(o,pivot);
          assert o == pivot;
          return;
        }

      assert o.AMFO > pivot.AMFO;
      assert strictlyInside(o,pivot);
    }
}

function collectOutsideOnlyPivot'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures strictlyInside(o,pivot)                      ==> (rv == pivot.AMFO)
    ensures (o == pivot)                                 ==> (rv == pivot.AMFO)
    ensures (strictlyInside(o,pivot) || (o == pivot))    ==> (rv == pivot.AMFO)
//  ensures (inside(o,pivot))                            ==> (rv == pivot.AMFO)

    ensures not(strictlyInside(o,pivot) || (o == pivot)) ==> (rv == {})
 // ensures (outside(o,pivot))                           ==> (rv == {})

    ensures (if (strictlyInside(o,pivot) || (o == pivot)) then (rv == pivot.AMFO) else (rv == {}))
    ensures rv == if (strictlyInside(o,pivot) || (o == pivot)) then (pivot.AMFO) else ({})
 // ensures (if (inside(o,pivot)) then (rv == pivot.AMFO) else (rv == {}))
 // ensures rv == if (inside(o,pivot)) then (pivot.AMFO) else ({}))
    {
     if (o == pivot) then (pivot.AMFO)
      else if (strictlyInside(o,pivot)) then (pivot.AMFO)
        else ({})
    }

// predicate pivotside(part : Object, whole : Object) reads {} { inside(whole,part) }
//    ///i.e (x == pivot) or (pivot inherits_from x)...
// function allPivotside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | pivotside(o,whole) }
//
// function flattenPivotside(ownrs : OWNR, pivot : Object) : (rv : Owner)
//   ensures forall r <- rv :: pivotside(r,pivot)
//   ensures forall r <- flatten(ownrs) :: pivotside(r,pivot) ==> r in rv
// { set x <- flatten(ownrs) | pivotside(x,pivot) }

function flattenOutsideExceptPivot(ownrs : OWNR, pivot : Object) : (rv : Owner)
 { set x <- flatten(ownrs), xx <- collectOutsideExceptPivot(x, pivot) :: xx }
function flattenOutsideOnlyPivot(ownrs : OWNR, pivot : Object) : (rv : Owner)
 { set x <- flatten(ownrs), xx <- collectOutsideOnlyPivot(x, pivot) :: xx }

function collectOutsideExceptPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
    ensures forall r <- rv :: outside(r, pivot)
    ensures forall r <- rv :: r in o.AMFO
    {
      assume o.Ready();
      assume pivot.Ready();
      if (not(inside(o,pivot))) then (o.AMFO)
        else if (o == pivot) then ({})
          else (set oo <- o.owner, ooo <- collectOutsideExceptPivot(oo, pivot) :: ooo)
    }

function collectOutsideExceptPivot'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures forall r <- rv :: outside(r, pivot)
    {
      assume o.Ready();
      assume pivot.Ready();
      if (o == pivot) then ({})
        else if (not(inside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- collectOutsideExceptPivot'(oo, pivot) :: ooo)
    }



function collectAllBoth(oo : Object, pivot : Object) : (rv : set<Object>)
  decreases oo.AMFO
   requires oo.Ready()
     { collectAllOutside(oo,pivot) + collectAllInside(oo,pivot) }

function amfoBinary(oo : Object, pivot : Object) : (rv : Owner)
  //2-argument version of .AMFO for use as an argument..
  decreases oo.AMFO
   requires oo.Ready()
     { oo.AMFO }

























lemma collectOutsideOnlyPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures collectOutsideOnlyPivot(o,pivot) == collectOutsideOnlyPivot'(o,pivot)
{}

lemma collectOutsideExceptPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures collectOutsideExceptPivot(o,pivot) == collectOutsideExceptPivot'(o,pivot)
{}







lemma collectAllOutside_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures collectAllOutside(o,pivot) == collectAllOutside'(o,pivot)
{
    if (o == pivot) {
      assert collectAllOutside(o,pivot)  == o.AMFO;
      assert collectAllOutside'(o,pivot) == o.AMFO;
      assert collectAllOutside(o,pivot) == collectAllOutside'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);
      assert collectAllOutside(o,pivot)  == o.AMFO;
      assert collectAllOutside'(o,pivot) == o.AMFO;
      assert collectAllOutside(o,pivot) == collectAllOutside'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
}

lemma collectAllOutside_LEMMA1(o : Object, pivot : Object)
  //outside' includes EXCEPT pivot'
   decreases o.AMFO
    requires o.Ready()
     ensures collectAllOutside'(o,pivot) >= collectOutsideExceptPivot'(o,pivot)
{}

lemma collectAllOutside_LEMMA1noprime(o : Object, pivot : Object)
  //outside includes EXCEPT pivot
   decreases o.AMFO
    requires o.Ready()
     ensures collectAllOutside(o,pivot) >= collectOutsideExceptPivot(o,pivot)
{}

lemma {:verify false} collectAllOutside_LEMMA2noprime(o : Object, pivot : Object)  //broken
//outside includes ONLY pivot  -- TOO HARD BASKET, have prime version working
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllOutside(o,pivot) >= collectOutsideOnlyPivot(o,pivot)
{}



lemma collectAllOutside_LEMMA8(o : Object, pivot : Object)
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures forall x <- collectAllOutside(o,pivot) ::
                || (x in collectOutsideExceptPivot(o,pivot))
                || (x in collectOutsideOnlyPivot(o,pivot))
{}

lemma collectAllOutside_LEMMA6(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
    requires inside(o,pivot)
     ensures pivot.AMFO <= collectAllOutside(o,pivot)
    {
      pivot.ExtraReady();
      assert forall p <- pivot.AMFO :: pivotlyOutside(p,pivot);
      assert forall p <- pivot.AMFO :: pivot.AMFO >= {p};
   //HERE///
    }

lemma collectAllOutside_LEMMA9(o : Object, pivot : Object)
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllOutside(o,pivot) <= (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot))
     ensures collectAllOutside(o,pivot) >= (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot))
     ensures collectAllOutside(o,pivot) == (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot))
{
  collectAllOutside_LEMMA8(o,pivot);
  assert forall x <- collectOutsideExceptPivot(o,pivot) :: x in collectAllOutside(o,pivot);

 if (inside(o,pivot)) {
      assert collectOutsideOnlyPivot(o,pivot) == pivot.AMFO;
      assert o.AMFO >= pivot.AMFO;
      var rv := collectAllOutside(o,pivot);
      collectAllOutside_LEMMA4(o, pivot, rv);
      assert rv >= pivot.AMFO;
      assert collectAllOutside(o,pivot) >= collectOutsideOnlyPivot(o,pivot);
 } else {
    assert outside(o, pivot);
      assert collectOutsideOnlyPivot(o,pivot) == {};
      assert collectAllOutside(o,pivot) > {};
      assert collectAllOutside(o,pivot) > collectOutsideOnlyPivot(o,pivot);
 }

 assert collectAllOutside(o,pivot) >= collectOutsideOnlyPivot(o,pivot);
}




lemma flattenOutsideOnlyExceptOnlyPivot_LEMMA1(os : Owner,  pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
   decreases allAMFOs(os)
    requires AllReady(os)
    requires forall o <- os :: o.Ready()
    requires pivot.Ready()
    requires left0 == flattenOutsideExceptPivot(os,pivot)
    requires left1 == flattenOutsideOnlyPivot(os,pivot)
    requires right == flattenOutside(os,pivot)
//     ensures left0 + left1 == right
{

  assert forall o <- left0 :: outside(o, pivot);
  assert forall o <- left0 :: o in flatten(os);
  assert forall o <- left1 :: pivotlyOutside(o, pivot);
  assert forall o <- left1 :: o in flatten(os);

  assert (left0 + left1) <= right;
//
//     assert (left0 + left1) == right;
//     assert (left1 + left0) == right;
}


lemma flattenAllOutside_LEMMA9(os : Owner, pivot : Object)
   decreases allAMFOs(os)
    requires AllReady(os)
    requires forall o <- os :: o.Ready()
    requires pivot.Ready()
  //  requires forall o <- os :: (collectAllOutside'(o,pivot) == (collectOutsideExceptPivot'(o,pivot) + collectOutsideOnlyPivot'(o,pivot)))
  //   ensures flattenOutside(os,pivot) == (flattenOutsideExceptPivot(os,pivot) + flattenOutsideOnlyPivot(os,pivot))
{
  forall o <- os ensures collectAllOutside(o,pivot) == (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot)) //by
    {
      collectAllOutside_LEMMA9(o,pivot);
      assert collectAllOutside(o,pivot) == (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot));
      // collectAllOutside_LEMMA0(o,pivot);
      // collectOutsideExceptPivot_LEMMA0(o,pivot);
      // collectOutsideOnlyPivot_LEMMA0(o,pivot);
      // assert collectAllOutside(o,pivot) == (collectOutsideExceptPivot(o,pivot) + collectOutsideOnlyPivot(o,pivot));
    }

assert (flattenOutsideExceptPivot(os,pivot) + flattenOutsideOnlyPivot(os,pivot)) ==
((set x <- flatten(os), xx <- collectOutsideExceptPivot(x, pivot) :: xx)
 + (set x <- flatten(os), xx <- collectOutsideOnlyPivot(x, pivot) :: xx));

 assert (flattenOutsideExceptPivot(os,pivot) + flattenOutsideOnlyPivot(os,pivot)) ==
  (set x <- flatten(os), xx <- (collectOutsideExceptPivot(x, pivot) + collectOutsideOnlyPivot(x, pivot)) :: xx);


    assert flattenOutside(os,pivot) == (flattenOutsideExceptPivot(os,pivot) + flattenOutsideOnlyPivot(os,pivot));
}


lemma flattenOutsideOnlyExceptPivot_LEMMA0(os : Owner, pivot : Object, oExcept : Owner, oOnly : Owner)
   decreases allAMFOs(os)
    requires AllReady(os)
    requires forall o <- os :: o.Ready()
    requires pivot.Ready()
    requires oExcept == flattenOutsideExceptPivot(os,pivot)
    requires oOnly ==   flattenOutsideOnlyPivot(os,pivot)
{
    assert oExcept ==  (flattenOutsideExceptPivot(os,pivot));
    assert oOnly   ==  (flattenOutsideOnlyPivot(os,pivot));

    assert oExcept == (set x <- flatten(os), xx <- collectOutsideExceptPivot(x, pivot) :: xx);
    assert oOnly   == (set x <- flatten(os), xx <- collectOutsideOnlyPivot(x, pivot) :: xx);


}





lemma {:timeLimit 30} collectAllBoth_LEMMA8(o : Object, pivot : Object)
 //collectAllBoth == collectAllOwnersWithoutExtraOwners(o) --- ie argh() or flatten({o})
 ///verifies on nightly-2026-08-29-f3c2fed/github/dafny/dafny at least
 //and on       nightly-2026-09-08-98ac8c0/github/dafny/dafn
 //but not on lately='/Users/kjx/work/dafny/backup/nightly-2026-04-22-13bdccd/github/dafny/dafny'
   decreases o.AMFO, 1
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o)
{
  if (o.owner == {})
    { assert collectAllBoth(o,pivot) == {o}; assert collectAllOwnersWithoutExtraOwners(o) == {o}; return; }

forall oo <- o.owner ensures ( collectAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo) ) //by
  {
    collectAllBoth_LEMMA8(oo, pivot);
    assert collectAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo);
}

assert forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo);


forall oo <-  collectAllBoth(o,pivot) ensures ( oo in collectAllOwnersWithoutExtraOwners(o) ) //by
  {
    assert oo in collectAllBoth(o,pivot);
    if (oo == o) { assert oo in collectAllOwnersWithoutExtraOwners(o); }
      else
      {
        ThereIsALightThatNeverGoesOut(o, oo);
      }
  }
}


lemma collectAllBoth_LEMMA9(o : Object, pivot : Object)
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllBoth(o,pivot) == (collectAllOutside(o,pivot) + collectAllInside(o,pivot))
{
collectAllBoth_LEMMA0({o}+o.owner,pivot);
}


lemma collectAllBoth_LEMMA8a(o : Object, pivot : Object)
  //outside splits into Only & Except
   decreases o.AMFO, 2
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllBoth(o,pivot) == argh(o)
{
  collectAllBoth_LEMMA8(o,pivot);
  assert collectAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o);
  collectAllAMFO3(o);
  assert collectAllOwnersWithoutExtraOwners(o) == argh(o);
  assert collectAllBoth(o,pivot) == argh(o);
}


lemma collectAllOutside_LEMMA2(o : Object, pivot : Object)  //broken
//outside' includes ONLY pivot'
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures collectAllOutside'(o,pivot) >= collectOutsideOnlyPivot'(o,pivot)
{
    if (o == pivot) {
      assert collectAllOutside'(o,pivot)  == o.AMFO;
      assert collectOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert collectAllOutside'(o,pivot) >= collectOutsideOnlyPivot'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);    // isn't this FUCKED??
      assert collectAllOutside'(o,pivot)  == o.AMFO;
      assert collectOutsideOnlyPivot'(o,pivot) == {};
      assert collectAllOutside'(o,pivot) >= collectOutsideOnlyPivot'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
    assert o.AMFO >= pivot.AMFO;
    assert pivot.Ready();
    assert pivot in pivot.AMFO;
    assert pivot in o.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      collectAllOutside_LEMMA3(o,pivot,collectAllOutside'(o,pivot));
      // assert collectAllOutside'(o,pivot)  == (set oo <- o.owner, ooo <- collectAllOutside'(oo, pivot) :: ooo);
      assert collectAllOutside'(o,pivot)  >= pivot.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      assert collectOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert collectAllOutside'(o,pivot) >= collectOutsideOnlyPivot'(o,pivot); //ERR
}



lemma collectAllOutside_LEMMA3(o : Object, pivot : Object, rv : Owner)
//collectAllOutside prime alqays inclues pivot...
   decreases o.AMFO
    requires o.Ready()
    requires pivot in o.AMFO
    requires rv == collectAllOutside'(o,pivot)
     ensures rv >= pivot.AMFO
   {
    STRICTLY_COME_INSIDE(o,pivot);
    WHOLE_ENCHILADA(o,pivot.AMFO);   //I don't expect to do this routinely...
    WHOLE_READY(o,pivot);

      if (o == pivot) {
        assert collectAllOutside'(o,pivot)  == pivot.AMFO;
        assert collectOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
        assert collectAllOutside'(o,pivot) >= collectOutsideOnlyPivot'(o,pivot);
        return;
      }

    assert (inside(o,pivot) && (o != pivot)) ==> strictlyInside(o,pivot);
    assert strictlyInside(o,pivot);

    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
    var nrv := collectAllOutside'(next,pivot);
    collectAllOutside_LEMMA3(next,pivot,nrv);
//
//       var po : Owner := (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  );
//       var no : Owner := (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  );
//
//       var rec : set<(Owner, Owner)> :=
//          (  set xo <- o.owner :: walkOutsidePivotAndNotPivot(xo, pivot)  );
//
//       compress(po,no,rec);

}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


lemma collectAllBoth_LEMMA0(soup : set<Object>,  pivot : Object) // left0 : set<Object>, left1 : set<Object>, right : set<Object>)
 //establishes collectAllBoth == collectAllOutside + collectAllInside based solely on definitions
 //then 'upscales' that to sets etc

  requires forall o <- soup :: o.Ready()

   ensures forall o <- soup :: collectAllBoth(o,pivot) == collectAllOutside(o, pivot) + collectAllInside(o, pivot)

   ensures forall o <- soup :: collectAllBoth(o,pivot) >= collectAllInside(o, pivot)
   ensures forall o <- soup :: collectAllBoth(o,pivot) >= collectAllOutside(o, pivot)

   ensures forall o <- soup, oo <- collectAllBoth(o,pivot) ::  oo in (collectAllOutside(o, pivot) + collectAllInside(o, pivot))
   ensures forall o <- soup, oo <- collectAllBoth(o,pivot) :: (oo in collectAllOutside(o, pivot)) || (oo in collectAllInside(o, pivot))
//LUXON   ensures forall o <- soup, oo <- collectAllBoth(o,pivot) :: (oo in collectAllOutside(o, pivot)) != (oo in collectAllIntside(o, pivot))

   ensures (set o <- soup, oo <- collectAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- (collectAllOutside(o, pivot) + collectAllInside(o, pivot)) :: oo)
   ensures (set o <- soup, oo <- collectAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- collectAllOutside(o, pivot) :: oo)
         + (set o <- soup, oo <- collectAllInside(o, pivot) :: oo)

  //  ensures  ((set o <- soup, oo <- collectAllOutside(o, pivot) :: oo) + (set o <- soup, oo <- collectAllInside(o, pivot) :: oo))
  //         == (set o <- soup, oo <- amfoBinary(o, pivot) :: oo)

   ensures forall oo <- soup, ooo <- collectAllBoth(oo,pivot) :: (ooo in  collectAllOutside(oo, pivot)) || (ooo in collectAllInside(oo,pivot))
   ensures forall oo <- soup, ooo <- collectAllBoth(oo,pivot) :: (ooo in (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)))
   ensures forall oo <- soup, ooo <- collectAllBoth(oo,pivot) :: (ooo in (collectAllInside(oo,pivot) + collectAllOutside(oo,pivot)))   //Inside-Outside OK here

  {}


//
// lemma letsDoIt(soup : set<Object>,  pivot : Object, left0 : set<Object>, left1 : set<Object>, right : set<Object>)
//   requires AllReady(soup)
//    ensures forall o <- soup :: o.Ready()
//    ensures forall o <- soup :: id(o).Ready()
//    ensures forall o <- soup :: rd(o).Ready()
//   requires forall o <- soup :: o.Ready()
//   requires forall o <- soup :: id(o).Ready()
//   requires forall o <- soup :: rd(o).Ready()
// //  requires (left0 + left1) == right  ///WTF WTF
//   requires left0 == (set o <- soup, oo <- collectAllOutside(o, pivot) :: oo)
//   requires left1 == (set o <- soup, oo <-  collectAllInside(o, pivot) :: oo)
//   requires right == (set o <- soup, oo <-    collectAllBoth(o, pivot) :: oo)
//
//    ensures (set o <- soup, oo <- collectAllOutside(o, pivot) :: oo) +  (set o <- soup, oo <-  collectAllInside(o, pivot) :: oo) ==  (set o <- soup, oo <-    collectAllBoth(o, pivot) :: oo)
//    ensures left0 + left1 == right
//   {
//     //  assert forall o <- soup :: o.Ready();
//     //  forall o <- soup ensures (o.Ready())
//     //   {
//     //     o.ExtraReady(); 4trrr
//     //   }
//   }


lemma collectAllBoth_LEMMA1(seed : Object,  pivot : Object, left0 : set<Object>, left1 : set<Object>, right : set<Object>)
  requires seed.Ready()
  requires left0 == (set o <- seed.owner, oo <- collectAllOutside(o, pivot) :: oo)
  requires left1 == (set o <- seed.owner, oo <-  collectAllInside(o, pivot) :: oo)
  requires right == (set o <- seed.owner, oo <-    collectAllBoth(o, pivot) :: oo)
   ensures left0 <= right
   ensures left1 <= right
   ensures left0 + left1 <= right
{
    assert AllReady(seed.owner);
    assert forall o <- seed.owner :: collectAllInside(o, pivot)  <= collectAllBoth(o, pivot);
    assert forall o <- seed.owner :: collectAllOutside(o, pivot) <= collectAllBoth(o, pivot);
    assert left0 <= right;
    assert left1 <= right;
  }

lemma BLANCHE(o : Object, pivot : Object)
 //given amfoBinary == collectAllBoth, lifts to set
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: amfoBinary(oo,pivot) == collectAllBoth(oo,pivot)
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo)
{}

lemma LANCHIN(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: oo.AMFO              == (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot))
     ensures forall oo <- o.owner :: amfoBinary(oo,pivot) == collectAllBoth(oo,pivot)
{
    // assert forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot);
    // assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // forall oo <- o.owner ensures
}

lemma LANCHOUT(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)\
{
    assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // assert forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot);
    assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
    // assert (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT1(o : Object, pivot : Object)  //WORKS!!
 //amfoBinary == AMFO
   decreases o.AMFO
    requires o.Ready()
//    requires strictlyInside(o,pivot)
//defn     requires forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
{
    assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
//     assert forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot);
//     assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
//     assert (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT3(o : Object, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
//given collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)
 //(set collectAllOutside) + set (collectAllInside) == set (collectAllooutside+collectAll(Inside)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot) //WHY? - cos if nothing's strictlyInside the pivot, who gives a FUCK
    requires left0 == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot)) :: ooo)
    requires left1 == (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot)) :: ooo)
    requires right == (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot)) :: ooo)   //TYPO - was "Outside"
 //  ensures right == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)
     ensures forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)
     ensures left0+left1 == right
     ensures left1+left0 == right
//     ensures right == (set oo <- o.owner, ooo <- (collectAllBoth(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot)) :: ooo) >= (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
     ensures (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot)) :: ooo) <= (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
     ensures (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
{
    assert (left0 + left1) >= right;
///CTFO PROG

    assert left0 <= right;
    assert left1 <= right;
    assert (left0 + left1) <= right;

    assert (left0 + left1) == right;
    assert (left1 + left0) == right;

///OLDER STUFF
//     assert    forall oo <- o.owner :: (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) == (collectAllInside(oo,pivot) + collectAllOutside(oo,pivot));
//
//
// //    assert forall oo <- o.owner, ooo <- collectAllOutside(oo,pivot) :: ooo in right;
//     assert forall oo <- o.owner :: collectAllInside(oo,pivot) <= collectAllInside(oo,pivot) + collectAllOutside(oo,pivot);     //Inside-Outside OK here
//     assert forall oo <- o.owner :: collectAllOutside(oo,pivot) <= collectAllOutside(oo,pivot) + collectAllInside(oo,pivot);     //Inside-Outside OK here1
// ///  assert    forall oo <- o.owner, ooo <- collectAllOutside(oo,pivot) :: ooo in right;
// assert    forall oo <- o.owner, ooo <-  collectAllInside(oo,pivot) :: ooo in right;
// // assert    forall oo <- o.owner, ooo <-  collectAllOutside(oo,pivot) + collectAllInside(oo,pivot) :: ooo in right;
// // assert    forall oo <- o.owner, ooo <-  collectAllInside(oo,pivot) + collectAllOutside(oo,pivot) :: ooo in right;   //Inside-Outside OK here

    // assert right == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo);
    // assert right == (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot) + collectAllOutside(oo,pivot)) :: ooo);    //Inside-Outside OK here

    // assert left0         <= right;
    // assert         left1 <= right;
    // assert left0 + left1 <= right;

//      gefucked2(o, pivot, collectAllBoth, (x,y)=> (collectAllOutside(x,y) + collectAllInside(x,y)) );
      // assert forall oo <- o.owner :: collectAllBoth(oo,pivot) == collectAllOutside(oo,pivot) + collectAllInside(oo,pivot);
      // assert (set oo <- o.owner, ooo <- collectAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo);
}

lemma collectAllBoth_LEMMA2(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
{

///WORKS -->
assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (collectAllOutside(oo,pivot)) :: y);

assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- collectAllOutside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- collectAllInside(oo,pivot)  :: y) );

assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- collectAllInside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- collectAllOutside(oo,pivot)  :: y) );    //Inside-Outside OK here

assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in collectAllBoth(oo,pivot);

////DOESNT WORK:

//LUXON
// assert forall oo <- o.owner, x <- collectAllBoth(oo,pivot) ::
//          x in ((set oo <- o.owner, y <- collectAllInside(oo,pivot) :: y)
//              + (set oo <- o.owner, y <- collectAllOutside(oo,pivot):: y));
//LUXON
// assert forall oo <- o.owner, x <- collectAllBoth(oo,pivot) ::
//          (x in (set oo <- o.owner, y <- collectAllInside(oo,pivot)  :: y))
//       != (x in (set oo <- o.owner, y <- collectAllOutside(oo,pivot) :: y));
//
//LUXON
// assert forall oo <- o.owner :: collectAllOutside(oo,pivot) !! collectAllInside(oo,pivot);

////DOESNT WORK:

//    var right := (set oo <- o.owner, ooo <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: ooo);

// assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (collectAllInside(oo,pivot) + collectAllOutside(oo,pivot)) :: y);      //Inside-Outside OK here
// assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (collectAllOutside(oo,pivot) + collectAllInside(oo,pivot)) :: y);

    // assert forall oo <- o.owner, x <- collectAllOutside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- collectAllInside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- right :: (x in collectAllOutside(oo,pivot)) || (x in collectAllInside(oo,pivot));

    // assert right == (set oo <- o.owner, ooo <- (collectAllInside(oo,pivot) + collectAllOutside(oo,pivot)) :: ooo);
    // assert forall oo <- o.owner, ooo <- collectAllOutside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner, ooo <- collectAllInside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner :: collectAllInside(oo,pivot) <= collectAllInside(oo,pivot) + collectAllOutside(oo,pivot);
}



///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///
/// 4. equivalence proofs...











lemma gefucked2(o : Object, pivot : Object, a : (Object, Object) --> Owner, b : (Object, Object) --> Owner)
  requires o.Ready()
  requires forall oo <- o.owner ::
     && a.requires(oo,pivot)
     && b.requires(oo,pivot)
     && a(oo,pivot) == b(oo,pivot)

  // requires forall oo <- o.owner :: a.requires(oo,pivot)
  // requires forall oo <- o.owner :: b.requires(oo,pivot)
  // requires forall oo <- o.owner :: a(oo,pivot) == b(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  a(oo,pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  b(oo,pivot) :: r )
{}


///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
///
/// 5. there is a light that never goes out
///
/// (almost certainly belongs off in Ownership.dfy - or Ownership-Smiths.dfy)


lemma {:timeLimit 30} ThereIsALightThatNeverGoesOut(part : Object, whole : Object)
  //at least one of part's direct owners is on the way to whole.
  requires part.Ready()
  requires whole.Ready()
  requires inside(part,whole)
  ensures (part == whole) || (exists x <- part.owner :: inside(x, whole))
{
  //    InsideRecInside2(part, whole);444

  if (part == whole) {
    assert ((part == whole) || (exists x <- part.owner :: inside(x, whole)));
    return; }

  assert part != whole;
  assert (exists x <- part.owner :: inside(x,whole));
}


ghost function {:isolate_assertions} YouCan'tGetThereFromHereBut(part : Object, whole : Object) : (next : Object)
  //return next - a "direct owner" of part that is on the way up to "whole"
  decreases part.AMFO

  requires part.Ready()
  requires whole.Ready()
  requires part != whole
  requires inside(part,whole)

  ensures next in part.owner
  ensures strictlyInside(part, next)
  ensures inside(next,whole)
  ensures (part.AMFO decreases to next.AMFO)
{
  InsideRecInside2(part, whole);
  assert recInside(part, whole);
  ThereIsALightThatNeverGoesOut(part, whole);

  assert exists x <- part.owner :: inside(x, whole);

  var next : Object :| next in part.owner && inside(next, whole);

  assert part !in part.owner;
  assert next  in part.owner;
  assert part.AMFO > next.AMFO;
  assert (part.AMFO decreases to next.AMFO);
  assert inside(next,whole);

  next
}



lemma collect_ALL_OUTSIDE_FROM_INSIDE_REACHES_PIVOT(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires inside(o,pivot)
   requires pivot in o.AMFO //hhmm
    ensures pivot.AMFO <= collectAllOutside'(o, pivot)
{
    WHOLE_ENCHILADA(o,pivot.AMFO);
    if (o == pivot) {
      assert pivot.AMFO <=  collectAllOutside'(o, pivot);
      return;
    }
    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
}
