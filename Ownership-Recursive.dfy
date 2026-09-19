include "Klon.dfy"
include "Set-Lemmata.dfy"
//include "BROWNE.dfy"

//first chunk is "recursive ownership"
//rest is - likely not needed?
// last chunk is "ownerishjp smiths"


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
  decreases o.AMFO
   requires o.Ready()
    ensures rv < o.AMFO
    ensures rv <= o.AMFX
//  ensures rv == o.AMFX
{
  o.owner + (set oo <- o.owner, ooo <- collectAllXOwners(oo) :: ooo)
}

// lemma CXO(o : Object)
// //  decreases o.AMFO
//   requires o.Ready()
// //   ensures rv <= o.AMFO
//   ensures collectAllOwners(o) == (collectAllXOwners(o) + {o})
// {
//   if (o.owner == {})
//    {
//     assert collectAllOwners(o) == {o};
//     assert collectAllXOwners(o) == {};
//     assert {o} == {} + {o};
//     assert collectAllOwners(o) == (collectAllXOwners(o) + {o});
//    }
//    else
//    {
//     assume  collectAllOwners(o) == (collectAllXOwners(o) + {o});
//    }
//
// }



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

function collectAllOwnersButForOwners(oo : Owner) : (rv : Owner)
  decreases allAMFOs(oo)
   requires AllReady(oo)
    { oo + (set o <- oo, ooo <- collectAllOwnersButForOwners(o.owner) :: ooo) }
//
// lemma OwnersSchmonersCollectionEmAll(o : Object)
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
// lemma SchmonersOwnersCollectionEmAll(oo : Owner)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//     ensures collectAllOwnersButForOwners(oo) == (set o <- oo, ooo <- collectAllOwnersWithoutExtraOwners(o) :: ooo)
// {}
//
//
//
// lemma {:timeLimit 60}  SchmonersSingles(oo : Owner)
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
// function zlork(oo : Owner) : (rv : OWNR)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//   { oo + (set o <- oo, ooo <- flown(o.owner) :: ooo) }
//
//
// lemma ISALLFUICKED(oo : Owner)
//   decreases allAMFOs(oo)
//    requires AllReady(oo)
//     ensures zlork(oo) == (oo + (set o <- oo, ooo <- flown(o.owner) :: ooo))

lemma InsideCollectAllOwners(part : Object, whole : Object)
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

lemma collectAllAMFO2(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   o.AMFO == argh(o)
  {}


lemma collectAllAMFO3(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   collectAllOwnersWithoutExtraOwners(o) == argh(o)
  {}




// lemma collectAllAMFO2(o : Object, z : Object)
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



lemma InsideRecInside(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready() //why not?
   requires inside(part,whole) || recInside(part,whole)
    ensures inside(part,whole)  ==> recInside(part,whole)
    ensures inside(part,whole) <==  recInside(part,whole)
    ensures inside(part,whole) <==> recInside(part,whole)
   {
     if recInside(part,whole) { InsideRecInside1(part,whole); }
     if    inside(part,whole) { InsideRecInside2(part,whole); }
   }




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


lemma FLATAMFO(a : Object)
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


lemma AXIOMFLATOWNERS(a : Object, b : Owner)
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

lemma Unready_AXIOMAMFOS(a : Object, b : Object)
  // equal AMFOs iff same objects
  ensures (a == b)  ==> (a.AMFO == b.AMFO)
  ensures (a == b) <==  (a.AMFO == b.AMFO)
  ensures (a == b) <==> (a.AMFO == b.AMFO)
  ensures (a != b) <==> (a.AMFO != b.AMFO)
  ensures a.Ready()
  ensures b.Ready()
{
  assume a.Ready(); assume b.Ready();
}

lemma AXIOMOWNERSFLAT(a : Owner, b : Owner)
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
   ensures   part.AMFO >= whole.AMFO
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



lemma AXIOMAMFODIRECT0(part : Object, whole : Object)
   requires part.Ready()
   requires whole.Ready()
   requires part.owner == {whole}
    ensures part.AMFX == whole.AMFO
{ }


lemma AXIOMAMFODIRECT(part : Object, whole : Object)
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

lemma LetsBeGood1(o : Object)
   requires o.Ready()
  decreases o.AMFO
    ensures isFlat(o.AMFO) <==  goodFlatten(o, o.AMFO)
{}

lemma LetsBeGood2(o : Object)
   requires o.Ready()
   requires o.owner == {}
  decreases o.AMFO
    ensures o in o.AMFO
    ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
{}

// lemma LetsBeGood3(o : Object)
//    requires o.Ready()
//    requires o.owner > {}
//   decreases o.AMFO
//     ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
// {
//   LetsBeGood3a(o, o.AMFO);
// }

// lemma LetsBeGood3a(o : Object, a : OWNR)
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

// lemma LetsBeGood4(o : Object)
//    requires o.Ready()
//   decreases o.AMFO
//     ensures isFlat(o.AMFO)  ==> goodFlatten(o, o.AMFO)
// {}


//shoiuld these be per object or per onwerE??
predicate goodCloneOwnership(left : Object, right : Object, m : Klon)
///checks left' ownership matches right, based on the Klojn
   requires left.Ready()
   requires right.Ready()
   requires m.objectInKlon(left)
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
   requires m.objectInKlon(left)
   requires right.AMFO <= m.m.Values
   requires right in invert(m.m).Keys
  decreases left.AMFO, right.AMFO
  {
    && (inside(left, pivot))
    && (m.m[left] == right)
    && (|left.owner| == |right.owner|)
    && (forall x <- left.owner  :: m.m[x]         in right.owner)
    && (forall x <- right.owner :: invert(m.m)[x] in left.owner)
    && (forall x <- left.owner  :: goodCloneOwnershipWithin(x, m.m[x],pivot,m))
  }



























lemma prog_is_paranoid(left : Object, right : Object, pivot : Object,  m : Klon)
///checks left' ownership matches right, based on the Klojn
  decreases left.AMFO, right.AMFO
   requires klonReady(m)
   requires klonCalid(m)
   requires left.Ready()
   requires right.Ready()
   requires m.objectInKlon(left)
   requires right.AMFO <= m.m.Values
   requires right in invert(m.m).Keys
   requires goodCloneOwnership(left, right, m)
    ensures (left == m.o) <==> (right == m.m[m.o])
    ensures not(inside(left, m.o)) <==> (m.m[left] == left)
  //  ensures (strictlyInside(left, m.o)) <==> strictlyInside(right, m.m[m.o]) // HHMMMMM
  {}

predicate noExternalOwners(k : Object, m : Klon)
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

lemma TestNoExternalOwners1(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: colinear(x.AMFO,m.o.AMFO)
{}

lemma TestNoExternalOwners2(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: (inside(x,m.o)) || (inside(m.o,x))
{}

lemma TestNoExternalOwners3(k : Object, x : Object, m : Klon)
  requires k.Ready()
  requires x.Ready()
  requires m.SuperCalidFragilistic()
  requires noExternalOwners(k,m)
   ensures forall x <- k.AMFX :: relatives(x, m) != External
{}

lemma TestRecombine(p0 : OWNR, w0 : OWNR, p1 : OWNR)
    requires AllReady(p0)
    requires AllReady(w0)
    requires AllReady(p1)
    requires p0 != w0
    requires p0 > w0
    requires sub(p0,w0) + w0 == p1
     ensures p1 == p0
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


ghost function YouCan'tGetThereFromHereBut(part : Object, whole : Object) : (next : Object)
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
