include "Klon.dfy"
include "Set-Lemmata.dfy"

//first chunk is "recursice ownership"
//rest is - likely not needed?


///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

//
// inside vs inside
//

lemma ownersReady(part : Object)
   requires part.Ready()
  decreases part.AMFO
    ensures forall whole <- part.owner :: whole.Ready()
  {}

predicate recInside(part : Object, whole : Object) : (r : bool)
     requires part.Ready()
    decreases part.AMFO
{
  || (part == whole)
  || (exists x <- part.owner :: recInside(x,whole))
}


function collectAllOwners(o : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   ensures rv <= o.AMFO
{
  {o} + o.owner + (set xo <- o.owner, co <- collectAllOwners(xo) :: co)
}

function collectAllXOwners(o : Object) : (rv : Owner)
  // decreases o.AMFO
   requires o.Ready()
  //  ensures rv <= o.AMFO
{
  o.owner + (set oo <- o.owner, ooo <- collectAllOwners(oo) :: ooo)
}

lemma CXO(o : Object)
//  decreases o.AMFO
  requires o.Ready()
//   ensures rv <= o.AMFO
  ensures collectAllOwners(o) == (collectAllXOwners(o) + {o})
{}



function collectAllOwnersWithoutExtraOwners(o : Object) : (rv : Owner)
  decreases o.AMFO
  requires o.Ready()
   ensures rv <= o.AMFO
    {  {o} + (set xo <- o.owner, co <- collectAllOwnersWithoutExtraOwners(xo) :: co)  }

lemma ExtraOwnersDon'tMatterToTheCollection(o : Object)
  decreases o.AMFO
   requires o.Ready()
    ensures collectAllOwners(o) == collectAllOwnersWithoutExtraOwners(o)
{}

function {:isolate_assertions} collectAllOwnersButForOwners(oo : Owner) : (rv : Owner)
  decreases allAMFOs(oo)
   requires AllReady(oo)
    { oo + (set o <- oo, ooo <- collectAllOwnersButForOwners(o.owner) :: ooo) }
//
// lemma {:isolate_assertions} OwnersSchmonersCollectionEmAll(o : Object)
//   decreases o.AMFO
//    requires o.Ready()
//     ensures collectAllOwnersWithoutExtraOwners(o) == collectAllOwnersButForOwners({o})
// {
//   if (o.owner == {}) {
//         assert collectAllOwnersWithoutExtraOwners(o) == {o};
//         assert collectAllOwnersButForOwners({o}) == {o};
//         assert collectAllOwnersWithoutExtraOwners(o) == collectAllOwnersButForOwners({o});
//     } else {
//         forall oo <- o.owner ensures ( collectAllOwnersWithoutExtraOwners(oo) == collectAllOwnersButForOwners({oo}) )
//           {
//             OwnersSchmonersCollectionEmAll(oo);
//             assert collectAllOwnersWithoutExtraOwners(oo) == collectAllOwnersButForOwners({oo});
//           }
//
// assert (set xo <- o.owner, co <- collectAllOwnersWithoutExtraOwners(xo) :: co)
//     ==  collectAllOwnersButForOwners(o.owner);
//
// // assert
// //      ({o} + (set xo <- o.owner, co <- collectAllOwnersWithoutExtraOwners(xo) :: co))
// //         == ({o} + (set  co <- collectAllOwnersButForOwners(o.owner) :: co) );
//     }
// }
//
//
// lemma {:isolate_assertions} SchmonersOwnersCollectionEmAll(oo : Owner)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//     ensures collectAllOwnersButForOwners(oo) == (set o <- oo, ooo <- collectAllOwnersWithoutExtraOwners(o) :: ooo)
// {}
//
//
//
// lemma {:isolate_assertions} {:timeLimit 60}  SchmonersSingles(oo : Owner)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//    requires forall o <- oo :: o.Ready()
//     ensures collectAllOwnersButForOwners({}) == {}
//     ensures (forall o <- oo :: o.owner == {}) ==> (collectAllOwnersButForOwners(oo) == oo)
//     ensures collectAllOwnersButForOwners(oo) == ( oo + (set o <- oo, ooo <- collectAllOwnersButForOwners(o.owner) :: ooo) )
//   //  ensures collectAllOwnersButForOwners(oo) == (set o <- oo, ooo <- collectAllOwnersButForOwners({o}) :: ooo)
// {
//   forall o <- oo ensures (
//
//      collectAllOwnersButForOwners(oo) == ( oo + (set o <- oo, ooo <- collectAllOwnersButForOwners(o.owner) :: ooo) )
//    )
//   { SchmonersSingles(o.owner); }
// }
//
//
// function  {:isolate_assertions} zlork(oo : Owner) : (rv : OWNR)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//   { oo + (set o <- oo, ooo <- flown(o.owner) :: ooo) }
//
//
// lemma ISALLFUICKED(oo : Owner)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//     ensures zlork(oo) == (oo + (set o <- oo, ooo <- flown(o.owner) :: ooo))

lemma {:isolate_assertions} InsideCollectAllOwners(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires recInside(part, whole)
  ensures  collectAllOwners(part) >= collectAllOwners(whole)
{
  recInsideCollectsAllOwners1(part,whole);
  assert whole in collectAllOwners(part);
  collectAllAMFO(part);
  // assert collectAllOwners(part) == part.AMFO;
  // assert part.AMFO >= whole.AMFO;
  collectAllAMFO(whole);
  //assert collectAllOwners(part) >= collectAllOwners(whole);
}


lemma collectAllAMFO(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   o.AMFO == collectAllOwners(o)
  {}

lemma collectAllAMFO1(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   o.AMFO == collectAllOwnersWithoutExtraOwners(o)
  {}
//
// lemma {:isolate_assertions} collectAllAMFO2(o : Object, z : Object)
//   decreases o.AMFO
//   requires  o.Ready()
//   requires (|o.owner| == 1) ==> (o.owner == {z})
//    ensures ( o.owner == {}) ==> (o.AMFO == {o})
//    ensures ( o.owner == {}) ==> (collectAllOwnersButForOwners({o}) == {o})
//    ensures ( o.owner == {z}) ==> (o.AMFO == {o} + z.AMFO)
//    ensures ( o.owner == {z}) ==> (collectAllOwnersButForOwners({o}) == ({o} + collectAllOwnersButForOwners({z})))
//    ensures o.AMFO == {o} + set z <- o.owner, zz <- z.AMFO :: zz
//    ensures collectAllOwnersButForOwners({o}) == ({o} + set z <- o.owner, zz <- collectAllOwnersButForOwners({z})  :: zz)
//
// //  ensures   o.AMFO == collectAllOwnersButForOwners({o})
//   {}

// lemma FlattenAllOwners(o : Object)
//  decreases o.AMFO
//   requires o.Ready()
//    ensures o.AMFO == collectAllOwners(o) == flatten({o})
//    ensures
//   {}


lemma recInsideCollectsAllOwners1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires recInside(part,whole)
  ensures  (whole in collectAllOwners(part))
{}

lemma recInsideCollectsAllOwners2(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()

  requires whole in collectAllOwners(part)
  ensures recInside(part,whole)
{}


lemma recInsideCollectsAllOwners3(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()

  ensures recInside(part,whole) <==> (whole in collectAllOwners(part))
{}

lemma recInsideCollectsAllOwners4(part : Object, whole : Object)
 decreases part.AMFO
  requires part.Ready()
  requires whole.Ready()
  requires inside(part, whole)
   ensures (whole in collectAllOwners(part))
{
//   assert inside(part, whole);
   InsideRecInside2(part, whole);
//   assert recInside(part, whole);
   recInsideCollectsAllOwners3(part, whole);
}



lemma recInsideAMFO1(part : Object, whole : Object)
  decreases part.AMFO
  requires part.Ready()
  requires whole.Ready() //why not?

  requires (whole in part.AMFO)
  ensures  recInside(part,whole)
{}

lemma recInsideAMFO2(part : Object, whole : Object)
  decreases part.AMFO
  requires  part.Ready()
  requires  whole.Ready() //why not?
  requires  recInside(part,whole)
  ensures   (whole in part.AMFO)
{}

lemma InsideRecInside1(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready() //why not?
   requires recInside(part,whole)
   ensures     inside(part,whole)
   {
      recInsideCollectsAllOwners1(part,whole);
      assert (whole in collectAllOwners(part));
      collectAllAMFO(part);
      assert (whole in part.AMFO);
      AXIOMAMFO(part, whole);
   }


lemma InsideRecInside2(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready() //why not?
   requires    inside(part,whole)
   ensures  recInside(part,whole)
   {
    assert  inside(part,whole);
    assert  part.AMFO >= whole.AMFO;
    AXIOMAMFOREVERSE(part,whole);
    assert whole in part.AMFO;
    collectAllAMFO(part);
    assert (whole in collectAllOwners(part));
    recInsideCollectsAllOwners2(part,whole);
    assert recInside(part,whole);
   }

///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////

lemma AXIOMFLAT(a : Object, b : Object)
  requires a.Ready()
  requires b.Ready()
  ensures  (a == b)  ==> (flatten({a}) == flatten({b}))
  ensures  (a == b) <==  (flatten({a}) == flatten({b}))
  ensures  (a == b) <==> (flatten({a}) == flatten({b}))
  ensures  (a != b) <==> (flatten({a}) != flatten({b}))
{}


lemma  {:isolate_assertions} FLATAMFO(a : Object)
  requires a.Ready()
   ensures a.AMFO == flatten({a})
   ensures forall oo <- a.AMFO :: inside(a,oo)
   ensures forall oo <- flatten({a}) :: inside(a,oo)
   ensures a in a.AMFO
   ensures a in flatten({a})
{
  a.ExtraReady();
  assert forall oo <- a.AMFX ::   outside(oo,a);
  assert forall oo <- a.AMFX ::not(inside(oo,a));
  assert forall oo <- a.AMFX ::    inside(a,oo);
  assert inside(a,a);
  assert forall oo <- a.AMFO ::    inside(a,oo);
}


lemma {:isolate_assertions} AXIOMFLATOWNERS(a : Object, b : Owner)
  requires a.Ready()
  requires AllReady(b)

  requires flatten({a}) == flatten(b)

//  ensures a.AMFO == flatten({a})
  ensures a in b
  ensures forall oo <- flatten(b) :: inside(a,oo)
{}

lemma AXIOMAMFOS(a : Object, b : Object)
  // equal AMFOs iff same objects
  requires a.Ready()
  requires b.Ready()
  ensures  (a == b)  ==> (a.AMFO == b.AMFO)
  ensures  (a == b) <==  (a.AMFO == b.AMFO)
  ensures  (a == b) <==> (a.AMFO == b.AMFO)
  ensures  (a != b) <==> (a.AMFO != b.AMFO)
{}

lemma  {:isolate_assertions} AXIOMOWNERSFLAT(a : Owner, b : Owner)
  requires AllReady(a)
  requires AllReady(b)
   ensures  (a == b)  ==> (flatten(a) == flatten(b))
   ensures  (a != b)  <== (flatten(a) != flatten(b))

  //  ensures  (a == b) <==  (flatten(a) == flatten(b))
  //  ensures  (a == b) <==> (flatten(a) == flatten(b))
//    ensures  (a != b) <==> (flatten(a) != flatten(b))
{}



lemma AXIOMAMFO(part : Object, whole : Object)
// o in AMFO ==> o.AMFO <= AMFO
   requires  part.Ready()
   requires  whole      in part.AMFO
   ensures   whole.AMFO <= part.AMFO
   ensures   inside(part,whole)
   { }

lemma AXIOMAMFOREVERSE(part : Object, whole : Object)
// inside(part,whole) ==> whole in part.AMFO
   requires   part.Ready()
   requires   whole.Ready()
   requires   part.AMFO >= whole.AMFO    ///why both?
   requires   inside(part,whole)         ///why both?
   ensures    whole in part.AMFO
   {
    assert whole in whole.AMFO;
   }



lemma {:isolate_assertions} AXIOMAMFODIRECT0(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready()
   requires part.owner == {whole}
    ensures part.AMFX == whole.AMFO
{ }


lemma {:isolate_assertions} AXIOMAMFODIRECT(part : Object, whole : Object)
// inside(part,whole) ==> whole in part.AMFO
   requires part.Ready()
   requires whole.Ready()
   requires part.AMFX == whole.AMFO
    ensures whole in part.owner
    ensures forall w <- part.owner :: inside(whole, w)
    ensures isFlat(part.AMFX)
{
   assert part.AMFX == whole.AMFO;
   assert isFlat(part.AMFX);

   FLATAMFO(whole);
   assert forall w <- whole.AMFO :: inside(whole, w);
   assert whole in whole.AMFO;
   assert forall w <- whole.self :: inside(whole, w);
}

//should go off to flatten... or owners-flatten.dfy...
predicate goodFlatten(o : Object, myAMFO : Owner)
    requires o.Ready()
   decreases o.AMFO
   {
    && (o in myAMFO)
    && (o.owner <= myAMFO)
    && (forall x <- o.owner :: goodFlatten(x, myAMFO))
   }

lemma {:isolate_assertions}  LetsBeGood1(o : Object)
   requires o.Ready()
  decreases o.AMFO
    ensures isFlat(o.AMFO) <==  goodFlatten(o, o.AMFO)
{}

lemma {:isolate_assertions}  LetsBeGood2(o : Object)
   requires o.Ready()
   requires o.owner == {}
  decreases o.AMFO
    ensures o in o.AMFO
    ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
{}

// lemma {:isolate_assertions}  LetsBeGood3(o : Object)
//    requires o.Ready()
//    requires o.owner > {}
//   decreases o.AMFO
//     ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
// {
//   LetsBeGood3a(o, o.AMFO);
// }

// lemma {:isolate_assertions}  LetsBeGood3a(o : Object, a : OWNR)
//    requires o.Ready()
//    requires o.owner > {}
//   decreases o.AMFO
//     ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
//     ensures (o in o.AMFO)
//     ensures isFlat(o.AMFO)  ==> (o.owner <= a)
//     ensures isFlat(o.AMFO)  ==> (forall x <- o.owner :: goodFlatten(x, a))
// {
//  forall x <- o.owner ensures goodFlatten(x, a)
// {
//     LetsBeGood3a(x, o.AMFO);
//  }
// }

// lemma {:isolate_assertions}  LetsBeGood4(o : Object)
//    requires o.Ready()
//   decreases o.AMFO
//     ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
// {}


//shoiuld these be per object or per onwerE??
predicate goodCloneOwnership(left : Object, right : Object, m : Klon)
///checks left' ownership matches right, based on the Klojn
   requires left.Ready()
   requires right.Ready()
   requires m.objectInKlown(left)
   requires right.AMFO <= m.m.Values
   requires right in invert(m.m).Keys
  decreases left.AMFO, right.AMFO
  {
    && (m.m[left] == right)
    && (|left.owner| == |right.owner|)
    && (forall x <- left.owner  :: m.m[x]         in right.owner)
    && (forall x <- right.owner :: invert(m.m)[x] in left.owner)
    && (forall x <- left.owner  :: goodCloneOwnership(x, m.m[x], m))
  }

predicate goodCloneOwnershipWithin(left : Object, right : Object, pivot : Object,  m : Klon)
///checks left' ownership matches right, based on the Klojn
   requires left.Ready()
   requires right.Ready()
   requires m.objectInKlown(left)
   requires right.AMFO <= m.m.Values
   requires right in invert(m.m).Keys
  decreases left.AMFO, right.AMFO
  {
    && (inside(left, pivot))
    && (m.m[left] == right)
    && (|left.owner| == |right.owner|)
    && (forall x <- left.owner  :: m.m[x]         in right.owner)
    && (forall x <- right.owner :: invert(m.m)[x] in left.owner)
    && (forall x <- left.owner  :: goodCloneOwnership(x, m.m[x], m))
  }


lemma {:isolate_assertions}  prog_is_paranoid(left : Object, right : Object, pivot : Object,  m : Klon)
///checks left' ownership matches right, based on the Klojn
  decreases left.AMFO, right.AMFO
   requires left.Ready()
   requires right.Ready()
   requires m.objectInKlown(left)
   requires right.AMFO <= m.m.Values
   requires right in invert(m.m).Keys
   requires m.SuperCalidFragilistic()
   requires goodCloneOwnership(left, right, m)
    ensures (left == m.o) ==> (right == m.m[m.o])
    ensures not(inside(left, m.o)) ==> (m.m[left] == left)
    //ensures (strictlyInside(left, m.o)) ==> strictlyInside(m.m[left], m.m[m.o]) // HHMMMMM
  {}

predicate {:isolate_assertions} noExternalOwners(k : Object, m : Klon)
 requires k.Ready()
 { forall x <- k.AMFX :: colinear(x.AMFO,m.o.AMFO) }

datatype RelativeOwnerRelation = Pivot | Inside | Outside | External

function relatives(o : Object, m : Klon) : RelativeOwnerRelation
  {
    if (o == m.o) then Pivot
      else if (inside(o, m.o)) then Inside
      else if (inside(m.o, o)) then Outside
      else External
  }

lemma {:isolate_assertions} TestNoExternalOwners1(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: colinear(x.AMFO,m.o.AMFO)
{}

lemma {:isolate_assertions} TestNoExternalOwners2(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: (inside(x,m.o)) || (inside(m.o,x))
{}

lemma {:isolate_assertions} TestNoExternalOwners3(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: relatives(x, m) != External
{}

lemma {:isolate_assertions} TestRecombine(p0 : OWNR, w0 : OWNR, p1 : OWNR)
    requires AllReady(p0)
    requires AllReady(w0)
    requires AllReady(p1)
    requires p0 != w0
    requires p0 > w0
    requires sub(p0,w0) + w0 == p1
     ensures p1 == p0
{}



//================================================================

function  {:isolate_assertions} flown(oo : Owner) : (rv : OWNR)
  decreases allAMFOs(oo)
   requires AllReady(oo)
    ensures AllReady(rv)
   // ensures isFlown(rv)
  { (set o <- oo, ooo <- flown(o.owner) :: ooo) + oo }
//  { (set o <- oo, ooo <- flown({o}) :: ooo) }   //nice but loops & doesn't call owner!!!!!
//    { (set o <- oo, ooo <- (flown(o.owner) + {o}) :: ooo) }

function  {:isolate_assertions} flownr(o : Object) : (rv : OWNR)
  requires o.Ready()
   { flown({o}) }
//   ensures rv == o.AMFO // it does. but...
//   { flown(o.owner) + {o} }   //earlier versuon - clearly I was askeeo at hte keyboard

function  {:isolate_assertions} {:timeLimit 20} flowin(oo : Owner, pivot : Owner) : (rv : Owner)
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires AllReady(pivot)
   ensures rv <= flown(oo)
           { flown(oo) - flown(pivot) }

function  {:isolate_assertions} {:timeLimit 20} flowrin(o : Object, pivot : Object) : (rv : Owner)
 decreases o.AMFO
  requires o.Ready()
  requires pivot.Ready()
   ensures rv <= flown({o})
           { flowin({o},{pivot}) } //  { flown({o}) - flown({pivot}) }
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
///
/// large amounts below removed because ConnectingTheDots0 showed a far more
/// direct lowleve approach worked fine!
///
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
///--  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  --  -- 3
//
// predicate isMinimal(w : Object, whole : Owner, fhole : Owner)
//  //is w NOT the owner of any obkject in fhole?
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//   requires w in whole
//   { forall x <- fhole :: not(strictlyInside(x,w)) }
//  // { forall x <- fhole :: w !in x.AMFX }
//
// function {:isolate_assertions} allMinimal(whole : Owner, fhole : Owner) : (r : Owner)
//  //returns subset of minimal elements of flown(whole) / fhole
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//    ensures r <= fhole
//  { set x <- whole | isMinimal(x, whole, fhole) }
//
// lemma {:isolate_assertions} existsMinimal(whole : Owner, fhole : Owner)
// //this surely cannot work!
//   requires whole != {}
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//    ensures exists w <- whole :: isMinimal(w, whole, fhole)
// {
//   if |whole| == 1 {
//     var w : Object := ExtractFromSingleton(whole);
//     OwnershipIsAcyclic(w);
//
//     assert  isMinimal(w, whole, fhole);
//     return;
//      }
//
//      assert  exists w <- whole :: isMinimal(w, whole, fhole);
// }
//
//
// predicate mowner(minimal : Object, s : Owner)
//   //minimal ownerhsip within whole - rippd out of dafny std lib
//   { minimal in s && forall x <- s | inside(x, minimal) :: inside(minimal, x) }
//
// //  { minimal in s && forall x | x in s && lessOrEqual(x, minimal) :: lessOrEqual(minimal, x) }
//
// function {:isolate_assertions} allMowner(whole : Owner, fhole : Owner) : (r : Owner)
//  //returns subset of minimal elements of flown(whole) / fhole
//  //should decide is this in WHOLE or FHOLE
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//    ensures r <= fhole
//  { set x <- whole | mowner(x,whole) }
// //  { set x <- whole | isMinimal(x, whole, fhole) }
//
//
//
// lemma {:isolate_assertions} existsMowner(whole : Owner, fhole : Owner)
// //this surely cannot work!
//   requires whole != {}
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//    ensures exists w <- whole :: mowner(w, whole)
// {
//   if |whole| == 1 {
//     var w : Object := ExtractFromSingleton(whole);
//     OwnershipIsAcyclic(w);
//     assert mowner(w, whole);
//     return;
//      }
//
//
//
//
//
//
// assert exists w <- whole :: mowner(w, whole);
// }
//
//
// lemma {:isolate_assertions} withoutMinimal(whole : Owner, fhole : Owner, minimal : Owner, min : Object, mhole : Owner)
//   requires AllReady(whole)
//   requires AllReady(fhole)
//   requires fhole == frown(whole)
//   requires minimal <= whole
//   requires minimal == allMinimal(whole, fhole)
//   requires min in minimal
//   requires mhole == frown({min})
//    ensures (fhole decreases to (fhole - {min}))
//    {}
//
//
//
//
//
// lemma {:isolate_assertions} FrownFratten(oo : Owner)
//   requires AllReady(oo)
//   requires AllReady(frown(oo))  //jusgt easier than whatevs
//  decreases allAMFOs(oo)
//
//    ensures oo <= frown(oo)
//
//    ensures  (oo  == {}) ==> (frown({}) == {})
//
//    ensures (|oo| == 1 ) ==> (var o : Object :| o in oo; frown({o}) == (frown(o.owner) + {o}))
//
//    ensures (|oo| >= 1 ) ==> (var o : Object :| o in oo; frown(oo) == frown({o}) + frown(oo - {o}))
// //
// //    ensures (|oo| >= 1 ) ==> (var o : Object :| o in oo; frown(oo) == (frown(o.owner) + {o} + frown(oo - {o})))
// //    ensures (|oo| >= 1 ) ==> (var o : Object :| o in oo; frown(oo) == (frown({o}) + frown(oo - {o})))
// //    ensures (|oo| >= 1 ) ==> (var o : Object :| o in oo; frown(oo) == (frown({o}) + frown(oo - {o})) + oo)
//
// ///   ensures (set o : Object <- oo, ooo : Object <- frown(o.owner) :: ooo) + oo == frown(oo)  // isnd;'t this the *definition*?  FUCK?
//
// {
//    if (oo == {}) { assert frown(oo) == {};  return; }
//
//    if (|oo| == 1) { var o : Object :| o in oo; assert frown({o}) == frown(o.owner) + {o}; return;  }
//
//   // if (|oo| == 1) { var o : Object :| o in oo; assert frown(oo) == frown(o.owner) + oo; return; }   //this formlation does not work if listed bnefore the one asbove, & I dunno why
//
//   assert |oo| > 1;
//
//   var o :| o in allMinimal(oo, frown(oo));
//
//   var rest := oo - {o};
//   assert oo == rest + {o};
//
//    assert allAMFOs(oo) decreases to allAMFOs(rest);
//    assert allAMFOs(oo) decreases to allAMFOs({o});
//
//    assert SMALLER: {o} <= oo;
//    assert  o in oo;
//    assert AllReady(oo);  assert o.Ready(); assert AllReady({o});
//
//  //    assert (allAMFOs(oo) decreases to allAMFOs({o})) by { assert o in oo; assert (oo-{o}) !! {o}; }
//   // FrownFratten({o}) by { assume (allAMFOs(oo) decreases to allAMFOs({o})); }  //prog too late to fix!
//
//
// //  var rest : Owner  := oo - {o};
//
//      assert AllReady(oo);  assert AllReady(rest);
//      assert (allAMFOs(oo) decreases to allAMFOs(rest)) by {
//                                                             assert rest !! {o};
//                                                             assert oo == rest + {o};
//                                                             assert o  in allAMFOs({o});
//                                                           //  assert oo > rest;
//                                                             OwnershipIsAcyclic(o);
//
//                                                             assert o  in allAMFOs(oo);
//                                                             assert o !in allAMFOs(rest);
//
//                                                             assert allAMFOs(oo) > allAMFOs(rest);
//                                                             assert (allAMFOs(oo) decreases to allAMFOs(rest));
//     }
//
//
//
//
//
//
// Sub3(oo, {o}, rest) by { reveal SMALLER; assert oo >= {o}; }
//
// assert AllReady(oo);  assert o.Ready(); assert AllReady({o}); assert AllReady(rest);
//
// assert frown(oo) == frown({o}) + frown(rest) by { Frown3({o},rest,oo); }
//
//
// //  there is progress. it is SLOW
//  }


lemma Sub3( a : Owner, b : Owner, c : Owner)
  requires AllReady(a)
  requires AllReady(b)
  requires AllReady(c)
  requires a >= b
  requires a >= c
  requires       a  -       b  ==       c
   ensures       c  +       b  ==       a
{
  SetMinus3(a,b,c);
}

lemma Frown3( a : Owner, b : Owner, c : Owner)
  requires AllReady(a)
  requires AllReady(b)
  requires AllReady(c)
  requires       a  +       b  ==       c
   ensures frown(a) + frown(b) == frown(c)
{}


 lemma  {:isolate_assertions} OwnershipIsAcyclic(o : Object)
  requires o.Ready()
   ensures o !in allAMFOs(o.owner)
   ensures o !in allAMFXs(o.owner)
   ensures o !in o.AMFX //isn't this the same as all the rest?
   ensures o !in frown(o.owner)
   ensures forall oo <- o.AMFX :: not(inside(oo,o))
   {
    assert AllReady(o.owner);
    FlattenFlownFrown({o}); FlownAllAMFOs({o});  FlownMyAMFO(o);
    assert frown(o.owner) == o.AMFX;
   }

// function  {:isolate_assertions} FR2(oo : Owner) : (r : Owner)
//    requires |oo| > 1
//    requires AllReady(oo)
//     ensures r <= frown(oo)
//   decreases allAMFOs(oo)
//   { var o : Object :| o in oo;
//     var rest := oo - {o};
//     Frown3( {o}, rest, oo);
//     assert ({o}) + (oo - {o}) == oo;
//     assert frown({o}) + frown(oo - {o}) == frown(oo);
//     frown({o}) + frown(oo - {o}) }

 function  {:isolate_assertions} frown(oo : Owner) : (rv : OWNR)
  requires AllReady(oo)
  decreases allAMFOs(oo)
 { (set o <- oo, ooo <- frown(o.owner) :: ooo) + oo }

// lemma {:isolate_assertions} FlownFlatten(oo : Owner)
//
// NO LONGER NEEDED  5 Nov
//
//   requires AllReady(oo)
//  decreases allAMFOs(oo)
//    ensures oo <= flown(oo)
//    ensures (set o : Object <- oo, ooo : Object <- flown(o.owner) :: ooo)  <=  flown(oo)
//    ensures (set o : Object <- oo, ooo : Object <- o.AMFO :: ooo)  <=  flatten(oo)
//    ensures (set o : Object <- oo, ooo : Object <- flown(o.owner) :: ooo)  + oo == flown(oo)
//    ensures (set o : Object <- oo, ooo : Object <- frown(o.owner) :: ooo)  + oo == frown(oo)
//    ensures (set o : Object <- oo, ooo : Object <- o.AMFO :: ooo) + oo ==  flatten(oo)
//    ensures flown(oo) == flatten(oo)
//     {
//       if (oo == {})
//          { assert flown(oo) == flatten(oo) == {}; }
//
//     forall o <- oo ensures (flown({o}) == flatten({o}))  //by
//        {
//         assert o.Ready();
//         assert o.AMFO < allAMFOs(oo);
//         assert allAMFOs({o}) < allAMFOs(oo);
//
//         if (|oo| > 1) { FlownFlatten({o}); }
//
//         assert (flown({o}) == flatten({o}));
//        }
//        assert forall o <- oo :: flown({o}) == flatten({o});
//        assert flown(oo) == flatten(oo);
//   }
//
//   { (set o <- oo, ooo <- flown(o.owner) :: ooo) + oo }
//
//   {(set o <- os, oo <- o.AMFO :: oo) + os}


predicate {:isolate_assertions} isFlown(os : Owner)
  decreases allAMFOs(os)
   requires AllReady(os)
  //flown analogue o isFlat
//  {flown(os) == os}
//    {forall o <- os, oo <- flown({o}) :: oo in os}
//  {forall o <- os :: flown({o}) <= os}
//   { os == (set o <- os, ooo <- (flown(o.owner)+{o}) :: ooo) }
   {forall o <- os ::  (flown(o.owner)+{o}) <= os}




ghost function recFlown(os : Owner) : Owner
  decreases os
  { if (os == {}) then {}
       else (var z :| z in os; z.AMFO + recFlown(os - {z})) }


ghost predicate {:isolate_assertions} isRecFlown(os : Owner)
  decreases allAMFOs(os)
   requires AllReady(os)
  //flown analogue o isFlat
//  {flown(os) == os}
//    {forall o <- os, oo <- flown({o}) :: oo in os}
//  {forall o <- os :: flown({o}) <= os}
//   { os == (set o <- os, ooo <- (flown(o.owner)+{o}) :: ooo) }

//   {forall o <- os ::  (recFlown({o}) <= os)}
  {recFlown(os) == os}




///----------------------------------------------------------------------

lemma {:isolate_assertions} FlownIsFlatten0(oo : Owner)
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires oo == {}
   ensures flatten(oo) == flown(oo)
{}


lemma {:isolate_assertions} FlownIsFlatten1(oo : Owner)
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires |oo| == 1
   ensures (forall o <- oo :: flatten({o}) == {o} + flatten(o.owner))
   ensures (forall o <- oo ::   flown({o}) == {o} +   flown(o.owner))
  //  ensures (forall o <- oo :: flatten({o}) == flown({o}))
  // ensures flatten(oo) == flown(oo)
{}


lemma {:isolate_assertions}  FlownIsFlatten2(o : Object)
 decreases allAMFOs({o})
  requires AllReady({o})
  requires AllReady(o.owner)
  ensures flatten({o}) == flown({o})
{
FlattenFlownFrown({o});
}
//
//  assert AllReady(o.owner);
//  assert forall oo <- o.owner :: oo.Ready();
//  assert OORDY: forall oo <- o.owner :: oo.Ready()  by { reveal AllReady(); assert AllReady(o.owner);  }
//
//   if (o.owner == {})
//      {
//         assert o.AMFO ==  {o};
//         assert flatten({o})  ==  {o};
//         assert f lown({o})  ==  {o};
//         return;
//      }
//     forall x <- o.owner ensures (flatten({x}) == flown({x}))
//        { FlownIsFlatten2(x); }
//
//     assert forall x <- o.owner :: (flatten({x}) == flown({x}));
//
//     assert flatten({o}) == {o} + flatten(o.owner);
//     assert flown({o}) == {o} + flown(o.owner);
//
//     assert AllReady(o.owner);
//
//     assert flatten(o.owner) == (set x <- o.owner, xx <- x.AMFO :: xx) + o.owner;
//     assert AllReady(o.owner); assert forall oo <- o.owner :: oo.Ready()  by { assert AllReady(o.owner);  }
//     assert flown(o.owner) == (set o : Object <- o.owner, ooo <- flown(o.owner) :: ooo) + o.owner by { assert AllReady(o.owner);  }
//     assert flown(o.owner) == (set x <- o.owner, xx <- flown({x}) :: xx) + o.owner;
//
//     assert flatten({o}) == {o} + flatten(o.owner);
//     assert flown({o}) == {o} + flown(o.owner);
//
// assert  flatten({o}) == flown({o});

lemma {:isolate_assertions}  FlownIsFlatten3(oo : Owner)
 decreases allAMFOs(oo)
  requires AllReady(oo)
   ensures flatten(oo) == allAMFOs(oo)
   {}

lemma {:isolate_assertions} {:timeLimit 30} FlownIsFlatten4(o : Object)
 decreases o.AMFO
  requires o.Ready()
   ensures flatten({o}) == flown({o})
   ensures o.AMFX == flatten(o.owner) == flown(o.owner)
{
  FlattenFlownFrown({o});
  FlownIsFlatten1({o});
FlownAllAMFOs(o.owner);
}

lemma {:isolate_assertions}  FlownrIsFlatten5(o : Object)
 decreases o.AMFO
  requires o.Ready()
   ensures (flown(o.owner) + {o}) == flown({o}) == flownr(o)
   ensures o.AMFO == o.AMFX + {o}
   ensures o.AMFO == flatten(o.owner) + {o} == flatten({o})
   ensures o.AMFO == collectAllOwners(o)
   ensures o.AMFO ==(flown(o.owner) + {o})
 {
  FlownIsFlatten4(o);
 }



lemma {:isolate_assertions} {:timeLimit 20} TryFlownrWhenYouWantToFlattenAnOwner(o : Object)
 decreases o.AMFO
  requires o.Ready()
   ensures flownr(o) ==  flown(o.owner)+{o}
   ensures (flown(o.owner)+{o}) == flown(o.owner+{o}) == flown({o})
   {}

lemma {:isolate_assertions} {:timeLimit 30} FlownrIsAMFX(o : Object)
 decreases o.AMFO
  requires o.Ready()
   ensures (flown(o.owner)+{o}) == flown(o.owner+{o})
   ensures o.AMFX == flatten(o.owner) == flown(o.owner)
    //  ensures o.AMFO + {o} == AIS
   ensures flatten({o}) == flown({o})
   {}

// function  {:isolate_assertions} {:timeLimit 20} flowinWTF(oo : Owner, pivot : Owner) : (rv : Owner)
//   decreases allAMFOs(oo)
//   requires AllReady(oo)
//    ensures rv <= allAMFOs(oo)
//    ensures forall r <- rv :: objectInsideOwner(r, pivot)
//   { set o <- oo, ooo <- flown(o.owner)
//       | objectInsideOwner(ooo, pivot) :: ooo }


lemma {:isolate_assertions} FlowinPrefix(oo : OWNR, pivoto : OWNR)
  //ahh FUCK = issue here is a set of individually "flat" owwners  (set<OWNR>)
  //is not quite the same a flat set of owners :-) (OWNR)
  //grrr o : Object is Ready
  //grrrr oo : Owner is AllReady  (should it be more? don't think so, it's a"local owner")
  //grrrrr AMFO : OWNR is isFlat ??  (anf should that encopaas Ready - yes of course..
  //for this method to work, needs to be flat ie OWNRS
  requires AllReady(oo)
  requires AllReady(pivoto)
  requires oo > pivoto

  requires isFlat(oo)
  requires isFlat(pivoto)

//   assert flatten(oo) > flatten(pivoto);
//   assert flatten(oo) == (oo);
//   assert flatten(pivoto) == (pivoto);

   ensures flowin(oo,pivoto) + flown(pivoto) == flown(oo)
{
  assert flatten(oo) > flatten(pivoto);
  assert flatten(oo) == (oo);
  assert flatten(pivoto) == (pivoto);
}

lemma {:isolate_assertions}  FlownrPrefix1(o : Object, pivot : Object)
  requires o.Ready()
  requires pivot.Ready()
  requires strictlyInside(o,pivot)
   ensures flowrin(o,pivot) + flownr(pivot) == flownr(o)
{
FlownrIsFlatten5(o);
  assert flownr(o) == (o.AMFO);
FlownrIsFlatten5(pivot);
  assert flownr(pivot) == (pivot.AMFO);
  assert flowrin(o,pivot) ==  (o.AMFO- pivot.AMFO);
  assert flowrin(o,pivot) !=  (o.AMFX); //NOTE NOT EQUALS
// FlowinPrefix(o.AMFO, pivot.AMFO);
  assert flowin(o.AMFO,pivot.AMFO) + flown(pivot.AMFO) == flown(o.AMFO);
  assert  flowrin(o,pivot) + flownr(pivot) == flownr(o);
}

lemma {:isolate_assertions} FlownMyAMFO(o : Object)
 decreases o.AMFO
 requires o.Ready()
  ensures o.AMFB == frown(o.bound) == flown(o.bound) == flatten(o.bound)
  ensures o.AMFX == frown(o.owner) == flown(o.owner) == flatten(o.owner)
  ensures o.AMFO == frown(o.self) == flown(o.self) == flatten(o.self)
  ensures o.AMFO == frown({o}) == flown({o}) == flatten({o})
 {
FlattenFlownFrown(o.bound); FlattenFlownFrown(o.owner); FlattenFlownFrown(o.self); FlattenFlownFrown({o});
FlownAllAMFOs(o.bound); FlownAllAMFOs(o.owner); FlownAllAMFOs(o.self); FlownAllAMFOs({o});

   assert o.AMFB == frown(o.bound) == flown(o.bound) == flatten(o.bound);
   assert o.AMFX == frown(o.owner) == flown(o.owner) == flatten(o.owner);
   assert o.AMFO == frown(o.self) == flown(o.self) == flatten(o.self) == (o.AMFX + {o});

  if (o.owner == {}) {
     assert flown( {} ) == {};
     assert o.AMFX == {};
     assert {} == o.AMFX == flown(o.owner); return;
      }

 }




lemma {:isolate_assertions} {:timeLimit 30} {:verify false} FlattenFlownFrown(oo : Owner)
 decreases allAMFOs(oo)
 requires AllReady(oo)
  ensures flatten(oo) == flown(oo) == frown(oo) == allAMFOs(oo)
 {
  if (oo == {}) {
     assert frown( {} ) == {};
     assert flown( {} ) == {};
     assert flatten( {} ) == {};
     assert allAMFXs( {} ) == {};

     assert flatten(oo) == flown(oo) == frown(oo) == allAMFOs(oo) == {};
     return;
     }

  forall o <- oo ensures (o.AMFX == flatten(o.owner) == flown(o.owner) == frown(o.owner) == allAMFOs(o.owner))
     { assert o.Ready();
       FlattenFlownFrown(o.owner);
       FLATTEN_ALLAMFOS(o.owner);
       assert flatten(o.owner) == allAMFOs(o.owner);
      }
 }




lemma {:isolate_assertions} FlownAllAMFOs(oo : Owner)
 decreases allAMFOs(oo)
 requires AllReady(oo)
  ensures forall o <- oo :: o.AMFX == flatten(o.owner)
  ensures forall o <- oo :: o.AMFO == flatten({o})
  ensures flatten(oo) == set o <- oo, ooo <- o.AMFO :: ooo
  ensures flatten(oo) == set o <- oo, ooo <- flatten({o}) :: ooo

 {

  forall o <- oo ensures (o.AMFX == flatten(o.owner) == flown(o.owner) == frown(o.owner))
     { assert o.Ready();
       FlattenFlownFrown(o.owner);
     }

assert forall o <- oo :: o.AMFX == flatten(o.owner);
assert forall o <- oo :: o.AMFX == flown(o.owner);
assert forall o <- oo :: o.AMFX == frown(o.owner);

assert forall o <- oo :: o.AMFO == flatten({o});
assert forall o <- oo :: o.AMFO == flown({o});
assert forall o <- oo :: o.AMFO == frown({o});

assert flatten(oo) == set o <- oo, ooo <- flatten({o}) :: ooo;

 }




















lemma {:isolate_assertions} NonCachedDefinitionsForPaper1(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()

   ensures (f==t)     == (ownerEquals(f.self, t.self))

//   ensures refDI(f,t) == (f in t.owner)
//   ensures refDI(f,t) == (f.AMFO == t.AMFX)  //AMDI_FINT
//   ensures refDI(f,t) == (flatten({f}) == flatten(t.owner))
//   ensures refDI(f,t) == ownerEquals(f.self, t.owner)

  //  ensures refBI(f,t) == (f.AMFB >= t.AMFX)
  //  ensures refBI(f,t) == (flatten(f.bound) >= flatten(t.owner))
  //  ensures refBI(f,t) == ownerInside(f.bound, t.owner)

{
  Cache(f); Cache(t);
}


predicate refBF(f : Object, t : Object) {if (f.AMFB > {}) then (f.AMFB >=  t.AMFX) else (false)}  //GREENLAND //AMFB_GEQ_GT  //AMFB-NOT-NULL
predicate refB2(f : Object, t : Object) {(f.AMFB > {}) &&  (f.AMFB >=  t.AMFX)}  //GREENLAND //AMFB_GEQ_GT  //AMFB-NOT-NULL

predicate refBW(f : Object, t : Object) {outgoingAllowed(f) && ownerInside(f.bound, t.owner)}
predicate refBX(f : Object, t : Object) {if (outgoingAllowed(f)) then (ownerInside(f.bound, t.owner)) else (false)}

//{:timeLimit 30}
lemma {:isolate_assertions} NonCachedDefinitionsForPaper2(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  ensures refBF(f,t) == if (f.AMFB > {}) then (f.AMFB >=  t.AMFX) else (false)
   ensures refBF(t,f) == refBI(t,f)
   ensures refBI(t,f) == refBF(t,f)
//   ensures refBI(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)

// ensures refBW(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
//  ensures refBX(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
 //    ensures refBX(t,f) == if (f.AMFB > {}) then (f.AMFB >=  t.AMFX) else (false)


// ensures refBX(t,f) ==  if (outgoingAllowed(f)) then (ownerInside(f.bound, t.owner)) else (false)

   ensures refBF(t,f) == refBW(t,f)
   ensures refBI(t,f) == refBW(t,f)
   ensures refBI(t,f) == refBX(t,f)

 // ensures refBF(t,f) == (f.AMFB > {}) && (f.AMFB >=  t.AMFX)
 // ensures refBI(f,t) == (f.AMFB > {}) && (f.AMFB >=  t.AMFX)
{}

  // lemma {:isolate_assertions} {:timeLimit 30} NonCachedDefinitionsForPaper3(f : Object, t : Object)
  //   requires f.Ready()
  //   requires t.Ready()
  //   requires not(outgoingAllowed(f))
  //    ensures refBF(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
  // {
  //   assert f.AMFB == {};
  //   assert not(f.AMFB > {});
  //   assert not ((f.AMFB > {}) && (f.AMFB >=  t.AMFX));
  //   assert not(refBF(t,f));
  //   assert outgoingAllowed(f) == false;
  //   assert (outgoingAllowed(f) && ownerInside(f.bound, t.owner)) == false;
  //
  // //  assert false == refBF(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner);
  // }
  //
  // //{:timeLimit 30}
  // lemma {:isolate_assertions} {:timeLimit 30} NonCachedDefinitionsForPaper9(f : Object, t : Object)
  //   requires f.Ready()
  //   requires t.Ready()
  //   ensures refBF(f,t) == if (f.AMFB > {}) then (f.AMFB >=  t.AMFX) else (false)
  //    ensures refBF(t,f) == refBI(t,f)
  //    ensures refBI(t,f) == refBF(t,f)
  //    ensures refBI(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
  //
  // //   ensures refBW(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
  // //   ensures refBX(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner)
  //  //     ensures refBX(t,f) == if (f.AMFB > {}) then (f.AMFB >=  t.AMFX) else (false)
  //
  //
  // // ensures refBX(t,f) ==  if (outgoingAllowed(f)) then (ownerInside(f.bound, t.owner)) else (false)
  //
  //   // ensures refBF(t,f) == refBW(t,f)
  //    ensures refBI(t,f) == refBW(t,f)
  //    ensures refBI(t,f) == refBX(t,f)
  //
  // //   ensures refBF(t,f) == (f.AMFB > {}) && (f.AMFB >=  t.AMFX)
  // //   ensures refBI(f,t) == (f.AMFB > {}) && (f.AMFB >=  t.AMFX)
  // {
  //   assert (outgoingAllowed(f)) == (f.AMFB > {});
  //
  //   if (f.AMFB == {})
  //     {
  //      assert outgoingAllowed(f) == false;
  //      var a := (outgoingAllowed(f) && ownerInside(f.bound, t.owner));
  //      assert a == (outgoingAllowed(f) && ownerInside(f.bound, t.owner));
  //      assert (outgoingAllowed(f) && ownerInside(f.bound, t.owner)) == false;
  //      assert a == false;
  //      assert refBI(f,t) == false;
  //      assert a == refBI(f,t);
  //      assert a == (outgoingAllowed(f) && ownerInside(f.bound, t.owner));
  //      assert refBI(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner);
  //     }
  //
  //   if (f.AMFB > {})
  //     {
  //      assert outgoingAllowed(f);
  //      assert ownerInside(f.bound, t.owner) == (f.AMFB >=  t.AMFX);
  //      assert refBI(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner);
  //     }
  //
  //   assert refBI(t,f) == outgoingAllowed(f) && ownerInside(f.bound, t.owner);
  // }





predicate outgoingAllowed(f : Object) {f.bound > {}}
//predicate ownerEquals(l : Owner, r : Owner)  { flatten(l) == flatten(r)}
// predicate ownerInside(l : Owner, r : Owner)  { flatten(l) >= flatten(r)}  //currently a definition in OutDamnedSpot...


lemma {:isolate_assertions} Cache(o : Object)
  requires o.Ready()
   ensures o.AMFX == flatten(o.owner)
   ensures o.AMFX == flown(o.owner)
   ensures o.AMFX == frown(o.owner)
   ensures o.AMFO == flatten({o})
   ensures o.AMFO == flown({o})
   ensures o.AMFO == frown({o})
   ensures o.AMFB == flatten(o.bound)
   ensures o.AMFB == flown(o.bound)
   ensures o.AMFB == frown(o.bound)
{
   FlattenFlownFrown(o.bound);
   FlattenFlownFrown(o.owner);
   FlattenFlownFrown({o});
}
