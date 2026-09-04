include "Ownership-Recursive.dfy"
include "Set-Lemmata.dfy"
include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
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
    && (below == (set x <- flatness | strictlyInside(x,pivot)))
    && (middle == (if (pivot in flatness) then (pivot.AMFO) else {}))
    && (above  == flattenOutside(owners, pivot))
    && (flatness    == above + middle + below)
  }

  predicate ExtraValid() { flatness == (above + middle + below) }


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



function skipAllOutside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures (o == pivot) || not(inside(o,pivot)) ==> (rv == o.AMFO)
    {
      if (not(strictlyInside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo)
    }

function skipAllOutside'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures (o == pivot) ==> (rv == pivot.AMFO)
    ensures not(inside(o,pivot)) ==> (rv == o.AMFO)
//see _LEMMA3 = rv >= pivot.AMFO
//    ensures not( strictlyInside(o,pivot) || (o == pivot) ) ==> (rv == o.AMFO)
    {
      STRICTLY_COME_INSIDE(o,pivot);

      if (o == pivot) then (pivot.AMFO) //==pivot.amfo
        else if (not(inside(o,pivot))) then (o.AMFO)
          else
           (assert strictlyInside(o,pivot);
           (set oo <- o.owner, ooo <- skipAllOutside'(oo, pivot) :: ooo))

      // if (not(strictlyInside(o,pivot))) then (o.AMFO)
      //     else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo)

    }

//COPIED from BROWNE!!!
function skipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners strictly inside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- skipAllInside(oo, pivot) :: ooo)
    }

function skipOutsideOnlyPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
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
    {
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

function skipOutsideOnlyPivot'(o : Object, pivot : Object) : (rv : set<Object>)
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

function skipOutsideExceptPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(inside(o,pivot))) then (o.AMFO)
        else if (o == pivot) then ({})
          else (set oo <- o.owner, ooo <- skipOutsideExceptPivot(oo, pivot) :: ooo)
    }



function skipOutsideExceptPivot'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (o == pivot) then ({})
        else if (not(inside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- skipOutsideExceptPivot'(oo, pivot) :: ooo)
    }


function skipAllBoth(oo : Object, pivot : Object) : (rv : set<Object>)
  decreases oo.AMFO
   requires oo.Ready()
     { skipAllOutside(oo,pivot) + skipAllInside(oo,pivot) }

function amfoBinary(oo : Object, pivot : Object) : (rv : Owner)
  //2-argument version of .AMFO for use as an argument..
  decreases oo.AMFO
   requires oo.Ready()
     { oo.AMFO }


function id(o : Object) : Object {o}
function rd(o : Object) : Object requires o.Ready() {o}


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//
// lemma ANTI_TRUMP(o : Object, pivot : Object)
//    decreases o.AMFO
//     requires o.Ready()
// //    requires strictlyInside(o,pivot)  --- org outside more likely?  - do we know any?
// //    ensures skipAllOutside(o,pivot) == skipOutsideExceptPivot(o,pivot) + skipOutsideExceptPivot(o,pivot)
//     {
//       assert skipAllOutside(o,pivot) ==
//         if (not(strictlyInside(o,pivot))) then (o.AMFO)
//           else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo);
//
//       assert skipOutsideOnlyPivot(o, pivot) ==
//           if (strictlyInside(o,pivot)) then (pivot.AMFO)
//             else if (o == pivot) then (pivot.AMFO)
//               else ({});
//
//
//       assert skipOutsideExceptPivot(o, pivot) ==
//           ( if (not(inside(o,pivot))) then (o.AMFO)
//               else if (o == pivot) then ({})
//                 else (set oo <- o.owner, ooo <- skipOutsideExceptPivot(oo, pivot) :: ooo) );
//
//     }



lemma skipOutsideOnlyPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipOutsideOnlyPivot(o,pivot) == skipOutsideOnlyPivot'(o,pivot)
{}

lemma skipOutsideExceptPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipOutsideExceptPivot(o,pivot) == skipOutsideExceptPivot'(o,pivot)
{
//   if (o == pivot) {
//     assert skipOutsideExceptPivot(o,pivot)  == ;
//     assert skipOutsideExceptPivot(o,pivot)' == ;
//
//     assert skipOutsideExceptPivot(o,pivot) == skipOutsideExceptPivot'(o,pivot);
//     return;
}

lemma skipAllOutside_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipAllOutside(o,pivot) == skipAllOutside'(o,pivot)
{
    if (o == pivot) {
      assert skipAllOutside(o,pivot)  == o.AMFO;
      assert skipAllOutside'(o,pivot) == o.AMFO;
      assert skipAllOutside(o,pivot) == skipAllOutside'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);
      assert skipAllOutside(o,pivot)  == o.AMFO;
      assert skipAllOutside'(o,pivot) == o.AMFO;
      assert skipAllOutside(o,pivot) == skipAllOutside'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
}

lemma skipAllOutside_LEMMA1(o : Object, pivot : Object)
  //outside' includes EXCEPT pivot'
   decreases o.AMFO
    requires o.Ready()
     ensures skipAllOutside'(o,pivot) >= skipOutsideExceptPivot'(o,pivot)
{}

lemma skipAllOutside_LEMMA1noprime(o : Object, pivot : Object)
  //outside includes EXCEPT pivot
   decreases o.AMFO
    requires o.Ready()
     ensures skipAllOutside(o,pivot) >= skipOutsideExceptPivot(o,pivot)
{}

lemma {:verify false} skipAllOutside_LEMMA2noprime(o : Object, pivot : Object)  //broken
//outside includes ONLY pivot  -- TOO HARD BASKET, have prime version working
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllOutside(o,pivot) >= skipOutsideOnlyPivot(o,pivot)
{}

lemma skipAllOutside_LEMMA8(o : Object, pivot : Object)
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
     ensures forall x <- skipAllOutside'(o,pivot) ::
                || (x in skipOutsideExceptPivot'(o,pivot))
                || (x in skipOutsideOnlyPivot'(o,pivot))
{}

//
//
// lemma {:verify false} skipAllOutside_LEMMA8a(o : Object, pivot : Object)
//   //outside splits into Only & Except
//    decreases o.AMFO
//     requires o.Ready()
//      ensures forall x <- skipAllOutside'(o,pivot) ::
//                    (x in skipOutsideExceptPivot'(o,pivot)) ==> (x !in skipOutsideOnlyPivot'(o,pivot))
// {}
//
// lemma {:verify false}  skipAllOutside_LEMMA8b(o : Object, pivot : Object)
//   //outside splits into Only & Except
//    decreases o.AMFO
//     requires o.Ready()
//      ensures forall x <- skipAllOutside'(o,pivot) ::
//                    (x !in skipOutsideExceptPivot'(o,pivot)) <== (x in skipOutsideOnlyPivot'(o,pivot))
// {}
//
// lemma {:verify false}  skipAllOutside_LEMMA8c(o : Object, pivot : Object)
//   //outside splits into Only & Except
//    decreases o.AMFO
//     requires o.Ready()
//      ensures forall x <- skipAllOutside'(o,pivot) ::
//                    (x in skipOutsideExceptPivot'(o,pivot))
//                 != (x in skipOutsideOnlyPivot'(o,pivot))
// {}


lemma skipAllOutside_LEMMA9(o : Object, pivot : Object)   //WORKS!!!
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllOutside'(o,pivot) == (skipOutsideExceptPivot'(o,pivot) + skipOutsideOnlyPivot'(o,pivot))
{
  skipAllOutside_LEMMA8(o,pivot);
  skipAllOutside_LEMMA1(o,pivot);
  skipAllOutside_LEMMA2(o,pivot);
}

lemma {:timeLimit 30} skipAllBoth_LEMMA8(o : Object, pivot : Object, other : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o)

    // requires (o.owner == {other}) || (o.owner == {})

//    requires (o.owner > {}) ==> (o.owner == {other})
//   requires (o.owner > {}) ==> (other.owner == {})

//     ensures skipAllBoth(o,pivot) == o.AMFO //amfoBinary(o,pivot)
 ensures skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o)
{
  if (o.owner == {})
    { assert skipAllBoth(o,pivot) == {o}; assert collectAllOwnersWithoutExtraOwners(o) == {o}; return; }

forall other <- o.owner ensures ( skipAllBoth(other,pivot) == collectAllOwnersWithoutExtraOwners(other) ) //by
  {
//    assert other.owner == {};
    skipAllBoth_LEMMA8(other, pivot, other);
    assert skipAllBoth(other,pivot) == collectAllOwnersWithoutExtraOwners(other);

    // assert collectAllOwnersWithoutExtraOwners(o) == {o} + collectAllOwnersWithoutExtraOwners(other);
    // assert skipAllBoth(other,pivot) == {o} + skipAllBoth(other,pivot);

 //  assert skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o);
}

assert forall other <- o.owner :: skipAllBoth(other,pivot) == collectAllOwnersWithoutExtraOwners(other);


forall other <-  skipAllBoth(o,pivot) ensures ( other in collectAllOwnersWithoutExtraOwners(o) ) //by
  {
    assert other in skipAllBoth(o,pivot);
    if (other == o) { assert other in collectAllOwnersWithoutExtraOwners(other); }
      else
      {
        ThereIsALightThatNeverGoesOut(o, other);
      }
  }



assert  skipAllBoth(o,pivot) == {o} + (set other <- o.owner, ooo <-  skipAllBoth(other,pivot) :: ooo);
// assert  collectAllOwnersWithoutExtraOwners(o) ==  {o} + (set other <- o.owner, ooo <-  collectAllOwnersWithoutExtraOwners(o) :: ooo);
//
//  assert skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o);
}

//  if (o.owner == {other})
//   {
//     assert other.owner == {};
//     skipAllBoth_LEMMA8(other, pivot, other);
//     assert skipAllBoth(other,pivot) == collectAllOwnersWithoutExtraOwners(other);
//     assert collectAllOwnersWithoutExtraOwners(o) == {o} + collectAllOwnersWithoutExtraOwners(other);
//     assert skipAllBoth(o,pivot) == {o} + skipAllBoth(other,pivot);
//
//     assert skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o);
//     return;
// }
//
//
//   forall oo <- o.owner ensures (skipAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo)) //by
//    {
//      skipAllBoth_LEMMA8(oo, pivot);
// //     assert  (skipAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo));
//    }
//   assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllOwnersWithoutExtraOwners(oo) :: ooo);
// }

//
// lemma skipAllBoth_LEMMA8q(o : Object, pivot : Object)
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//      requires skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o)
//      requires forall oo <- o.owner :: skipAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo)
//      ensures (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllOwnersWithoutExtraOwners(oo) :: ooo)
// {}
//
// lemma skipAllBoth_LEMMA8s(o : Object, pivot : Object)
//    decreases o.AMFO
//     requires o.Ready()
//     requires pivot.Ready()
//     //requires skipAllBoth(o,pivot) == collectAllOwnersWithoutExtraOwners(o)
//      requires forall oo <- o.owner :: skipAllBoth(oo,pivot) == collectAllOwnersWithoutExtraOwners(oo)
//      ensures (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- collectAllOwnersWithoutExtraOwners(oo) :: ooo)
// {}

lemma skipAllBoth_LEMMA9(o : Object, pivot : Object)   //WORKS!!!
  //outside splits into Only & Except
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllBoth(o,pivot) == (skipAllOutside(o,pivot) + skipAllInside(o,pivot))
{
skipAllBoth_LEMMA0({o}+o.owner,pivot);
}


lemma skipAllOutside_LEMMA2(o : Object, pivot : Object)  //broken
//outside' includes ONLY pivot'
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot)
{
    if (o == pivot) {
      assert skipAllOutside'(o,pivot)  == o.AMFO;
      assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);    // isn't this FUCKED??
      assert skipAllOutside'(o,pivot)  == o.AMFO;
      assert skipOutsideOnlyPivot'(o,pivot) == {};
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
    assert o.AMFO >= pivot.AMFO;
    assert pivot.Ready();
    assert pivot in pivot.AMFO;
    assert pivot in o.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      skipAllOutside_LEMMA3(o,pivot,skipAllOutside'(o,pivot));
      // assert skipAllOutside'(o,pivot)  == (set oo <- o.owner, ooo <- skipAllOutside'(oo, pivot) :: ooo);
      assert skipAllOutside'(o,pivot)  >= pivot.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot); //ERR
}



lemma skipAllOutside_LEMMA3(o : Object, pivot : Object, rv : Owner)
//skipAllOutside prime alqays inclues pivot...
   decreases o.AMFO
    requires o.Ready()
    requires pivot in o.AMFO
    requires rv == skipAllOutside'(o,pivot)
     ensures rv >= pivot.AMFO
   {
    STRICTLY_COME_INSIDE(o,pivot);
    WHOLE_ENCHILADA(o,pivot.AMFO);   //I don't expect to do this routinely...
    WHOLE_READY(o,pivot);

      if (o == pivot) {
        assert skipAllOutside'(o,pivot)  == pivot.AMFO;
        assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
        assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
        return;
      }

    assert (inside(o,pivot) && (o != pivot)) ==> strictlyInside(o,pivot);
    assert strictlyInside(o,pivot);

    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
    var nrv := skipAllOutside'(next,pivot);
    skipAllOutside_LEMMA3(next,pivot,nrv);
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


lemma skipAllBoth_LEMMA0(soup : set<Object>,  pivot : Object) // left0 : set<Object>, left1 : set<Object>, right : set<Object>)
 //establishes skipAllBoth == skipAllOutside + skipAllInside based solely on definitions
 //then 'upscales' that to sets etc

  requires forall o <- soup :: o.Ready()

   ensures forall o <- soup :: skipAllBoth(o,pivot) == skipAllOutside(o, pivot) + skipAllInside(o, pivot)

   ensures forall o <- soup :: skipAllBoth(o,pivot) >= skipAllInside(o, pivot)
   ensures forall o <- soup :: skipAllBoth(o,pivot) >= skipAllOutside(o, pivot)

   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) ::  oo in (skipAllOutside(o, pivot) + skipAllInside(o, pivot))
   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) :: (oo in skipAllOutside(o, pivot)) || (oo in skipAllInside(o, pivot))
//LUXON   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) :: (oo in skipAllOutside(o, pivot)) != (oo in skipAllIntside(o, pivot))

   ensures (set o <- soup, oo <- skipAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- (skipAllOutside(o, pivot) + skipAllInside(o, pivot)) :: oo)
   ensures (set o <- soup, oo <- skipAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo)
         + (set o <- soup, oo <- skipAllInside(o, pivot) :: oo)

  //  ensures  ((set o <- soup, oo <- skipAllOutside(o, pivot) :: oo) + (set o <- soup, oo <- skipAllInside(o, pivot) :: oo))
  //         == (set o <- soup, oo <- amfoBinary(o, pivot) :: oo)

   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in  skipAllOutside(oo, pivot)) || (ooo in skipAllInside(oo,pivot))
   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)))
   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)))   //Inside-Outside OK here

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
//   requires left0 == (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo)
//   requires left1 == (set o <- soup, oo <-  skipAllInside(o, pivot) :: oo)
//   requires right == (set o <- soup, oo <-    skipAllBoth(o, pivot) :: oo)
//
//    ensures (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo) +  (set o <- soup, oo <-  skipAllInside(o, pivot) :: oo) ==  (set o <- soup, oo <-    skipAllBoth(o, pivot) :: oo)
//    ensures left0 + left1 == right
//   {
//     //  assert forall o <- soup :: o.Ready();
//     //  forall o <- soup ensures (o.Ready())
//     //   {
//     //     o.ExtraReady(); 4trrr
//     //   }
//   }


lemma skipAllBoth_LEMMA1(seed : Object,  pivot : Object, left0 : set<Object>, left1 : set<Object>, right : set<Object>)
  requires seed.Ready()
  requires left0 == (set o <- seed.owner, oo <- skipAllOutside(o, pivot) :: oo)
  requires left1 == (set o <- seed.owner, oo <-  skipAllInside(o, pivot) :: oo)
  requires right == (set o <- seed.owner, oo <-    skipAllBoth(o, pivot) :: oo)
   ensures left0 <= right
   ensures left1 <= right
   ensures left0 + left1 <= right
{
    assert AllReady(seed.owner);
    assert forall o <- seed.owner :: skipAllInside(o, pivot)  <= skipAllBoth(o, pivot);
    assert forall o <- seed.owner :: skipAllOutside(o, pivot) <= skipAllBoth(o, pivot);
    assert left0 <= right;
    assert left1 <= right;
  }

lemma BLANCHE(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: amfoBinary(oo,pivot) == skipAllBoth(oo,pivot)
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
    //  requires forall oo <- o.owner :: (set ooo <- oo.AMFO :: ooo) == (set ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
    //   ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)

{
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    // assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
  //  forall oo <- o.owner ensures (skipAllBoth(oo,pivot) == amfoBinary(oo,pivot)) { gefucked(o,pivot,skipAllBoth,amfoBinary); }
}

lemma LANCHIN(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: oo.AMFO              == (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot))
     ensures forall oo <- o.owner :: amfoBinary(oo,pivot) == skipAllBoth(oo,pivot)
{
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    // assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // forall oo <- o.owner ensures
}

lemma LANCHOUT(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)\
{
    assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
    // assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT1(o : Object, pivot : Object)  //WORKS!!
 //amfoBinary == AMFO
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
//defn     requires forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
{
    assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
//     assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
//     assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
//     assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT3(o : Object, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
//given skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)
 //(set skipAllOutside) + set (skipAllInside) == set (skipAllooutside+skipAll(Inside)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot) //WHY? - cos if nothing's strictlyInside the pivot, who gives a FUCK
    requires left0 == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo)
    requires left1 == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo)
    requires right == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo)
//    requires right == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)
    //  ensures left0+left1 == right
    //  ensures left1+left0 == right
//     ensures right == (set oo <- o.owner, ooo <- (skipAllBoth(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) >= (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) <= (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)    //Inside-Outside OK here
{
    assert left0 + left1 >= right;
    assert    forall oo <- o.owner :: (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) == (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot));

//    assert forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
    assert forall oo <- o.owner :: skipAllInside(oo,pivot) <= skipAllInside(oo,pivot) + skipAllOutside(oo,pivot);     //Inside-Outside OK here
    assert forall oo <- o.owner :: skipAllOutside(oo,pivot) <= skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);     //Inside-Outside OK here1
///  assert    forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
assert    forall oo <- o.owner, ooo <-  skipAllInside(oo,pivot) :: ooo in right;
// assert    forall oo <- o.owner, ooo <-  skipAllOutside(oo,pivot) + skipAllInside(oo,pivot) :: ooo in right;
// assert    forall oo <- o.owner, ooo <-  skipAllInside(oo,pivot) + skipAllOutside(oo,pivot) :: ooo in right;   //Inside-Outside OK here

    // assert right == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
    // assert right == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: ooo);    //Inside-Outside OK here

    // assert left0         <= right;
    // assert         left1 <= right;
    // assert left0 + left1 <= right;

//      gefucked2(o, pivot, skipAllBoth, (x,y)=> (skipAllOutside(x,y) + skipAllInside(x,y)) );
      // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
      // assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma skipAllBoth_LEMMA2(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
{

///WORKS -->
assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllOutside(oo,pivot)) :: y);

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- skipAllOutside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- skipAllInside(oo,pivot)  :: y) );

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- skipAllInside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- skipAllOutside(oo,pivot)  :: y) );    //Inside-Outside OK here

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in skipAllBoth(oo,pivot);

////DOESNT WORK:

//LUXON
// assert forall oo <- o.owner, x <- skipAllBoth(oo,pivot) ::
//          x in ((set oo <- o.owner, y <- skipAllInside(oo,pivot) :: y)
//              + (set oo <- o.owner, y <- skipAllOutside(oo,pivot):: y));
//LUXON
// assert forall oo <- o.owner, x <- skipAllBoth(oo,pivot) ::
//          (x in (set oo <- o.owner, y <- skipAllInside(oo,pivot)  :: y))
//       != (x in (set oo <- o.owner, y <- skipAllOutside(oo,pivot) :: y));
//
//LUXON
// assert forall oo <- o.owner :: skipAllOutside(oo,pivot) !! skipAllInside(oo,pivot);

////DOESNT WORK:

//    var right := (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);

// assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: y);      //Inside-Outside OK here
// assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: y);

    // assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- skipAllInside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- right :: (x in skipAllOutside(oo,pivot)) || (x in skipAllInside(oo,pivot));

    // assert right == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: ooo);
    // assert forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner :: skipAllInside(oo,pivot) <= skipAllInside(oo,pivot) + skipAllOutside(oo,pivot);
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



lemma SKIP_ALL_OUTSIDE_FROM_INSIDE_REACHES_PIVOT(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires inside(o,pivot)
   requires pivot in o.AMFO //hhmm
    ensures pivot.AMFO <= skipAllOutside'(o, pivot)
{
    WHOLE_ENCHILADA(o,pivot.AMFO);
    if (o == pivot) {
      assert pivot.AMFO <=  skipAllOutside'(o, pivot);
      return;
    }
    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
}
