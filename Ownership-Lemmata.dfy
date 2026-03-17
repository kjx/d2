include "Ownership.dfy"


lemma FlattenIsFlat(os : Owner)
  requires AllReady(os)
   ensures isFlat(flatten(os))
  {
    var fs := flatten(os);
    assert os <= fs;
    assert (set o <- os, oo <- o.AMFO :: oo) <= fs;
    assert fs == (set o <- os, oo <- o.AMFO :: oo) + os;
    assert forall o : Object <- os, oo : Object <- o.AMFO :: oo in fs;
    assert forall o : Object <- fs, oo : Object <- o.AMFO :: oo in fs;
    assert isFlat(fs);
    assert isFlat(flatten(os));
  }


lemma FlattenIsOwners0(os : Owner)
  requires AllReady(os)
   ensures os <= (flatten(os))
   ensures flatten(os) + os == flatten(os)
{}

lemma FlattenIsOwners1(os : Owner)
  requires (forall o <- os :: o in o.AMFO)
   ensures os <= (set o <- os, oo <- o.AMFO :: oo)
   ensures (set o <- os, oo <- o.AMFO :: oo)  + os == (set o <- os, oo <- o.AMFO :: oo)
{}



lemma AllReadyMeansEachObject0(os : Owner)
  ensures forall o <- os :: o.Ready() ==> (o in o.AMFO)
{}

lemma AllReadyMeansEachObject1(os : Owner)
 requires AllReady(os)
  ensures forall o <- os :: o in o.AMFO
{}





lemma {:isolate_assertions} SubAMFOsNonU(partO : OWNR, wholeO : OWNR)
    //partO is the "key" we're copying, "wholeO" is the piivo, top of the object ot b cloned
    requires partO > wholeO  //ownerws trictk inside OWNR- sees to work either way!
     ensures sub(partO,wholeO) + wholeO == partO
{}

lemma FlattenEq4(l : Owner, r : Owner, fl : OWNR, fr : OWNR)
   requires  l == r
   requires fl == flatten(l)
   requires fr == flatten(r)
    ensures fl == fr
{}

lemma FlattenEq2(l : Owner, r : Owner)
   requires  l == r
    ensures flatten(l) == flatten(r)
{}

// lemma NEWFlatten0(a : Object)
//   requires a.AMFX == flatten(a.owner)
//   requires a.AMFO == a.AMFX + {a}
//    ensures flatten(a.self) == a.AMFO
// {}

lemma Flatten0(a : Object)
  requires a.Ready()
   ensures flatten(a.self) == a.AMFO
{}

// lemma Flatten1(a : Object)         //REVERT
//   ensures flatten({a})    == a.AMFO     //REVERT
// {}     //REVERT

lemma Flatten2(a : Owner, b : Owner)
  ensures flatten(a) + flatten(b) == flatten(a+b)
{}

lemma FlattenIncludesArgument(o : Owner)
   ensures o <= flatten(o)
    {}

lemma {:isolate_assertions} FlattenExtraReady(o : Object)
     requires o.Ready()
      ensures o.self  <= o.AMFO
      ensures o.owner <= o.AMFX <= o.AMFO
      ensures o.bound <= o.AMFB <= o.AMFX <= o.AMFO
    {}

lemma FlatMeFlatMyOwners(o : Object,  oo : Owner)
  requires o.Ready()
  requires AllReady(oo)
  requires isFlat(oo)

  requires o in oo
   ensures o.AMFO <= oo
{}

predicate AllTheseOwnersAreFlatOK(os : set<Object>, context : set<Object> := os)
{ && flatten(os) <= context }



lemma AMFOsisAMFOs(o : Object)
  requires o.Ready()
  ensures forall oo <- o.AMFO | oo != o :: (o.AMFO > oo.AMFO)
  ensures forall oo <- o.AMFO | oo != o :: strictlyInside(o, oo)
  ensures forall oo <- o.AMFO           :: inside(o, oo)
{}

///=====================================================================================
///
/// spare stuff that as lurking in Ownership that seems pretty damn preipheral.
///  dunno how much is needed vs how much is junk vs how much is
///
///=====================================================================================
///=====================================================================================
///=====================================================================================






































lemma DirectlyInside(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires directlyInside(part, whole)
   ensures inside(part,whole)
   ensures strictlyInside(part,whole)
{
//  FlattenInsideFlat(whole,flatten(part.owner));
}

lemma OnlyInside(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires onlyInside(part, whole)
   ensures inside(part,whole)
   ensures strictlyInside(part,whole)
{
  // FlattenInsideFlat(whole,flatten(part.owner));
}




lemma {:isolate_assertions } DreddOwner(whole : Object, part : Object)
  //NOTE argumenets are backwards, order is f->t not  part / whole
  //if whole (f) inside part(t) owner list then...whole (directly )owns part
  requires whole.Ready()
  requires part.Ready()
  requires whole in part.owner
   ensures whole in flatten(part.owner)
   ensures flatten({whole}) <= flatten(part.owner) < flatten({part})
   ensures flatten({part}) > flatten(part.owner) >= flatten({whole})
   ensures part.AMFO > part.AMFX >= whole.AMFO
   ensures ownerInsideOwner(flatten(part.owner), flatten({whole}))
   ensures inside(part,whole)
{
}


lemma FlattenInsideFlat(f : Object, fs : Owner)
  // (f in fs && isFlat(fs)) ==> (flatten({f}) <= fs)
  requires f.Ready()
  requires AllReady(fs)
   ensures ((f in fs && isFlat(fs)) ==> (flatten({f}) <= fs))
  requires isFlat(fs)
  requires f in fs
   ensures flatten({f}) <= fs
{}



lemma ownerInsideSanity(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
   ensures inside(part, whole)        ==> ownerInside(part.owner, whole.owner)
   ensures inside(part, whole)       <==> ownerInside(part.self , whole.self )
   ensures (part.AMFB >= whole.AMFB) <==> ownerInside(part.bound, whole.bound)
  {}




lemma InsideObjectsInsideOwners0(part : Object, whole : Object)
  //CULL requires part.Ready()
  //CULL requires whole.Ready()
   ensures inside(part,whole) == ownerInsideOwner(part.AMFO, whole.AMFO)
{}

lemma {:isolate_assertions} InsideObjectsInsideOwners1(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
  requires f.AMFB >  t.AMFX //REENLAND
///  requires f.AMFO >= t.AMFX   ///WRONG assic O-as-D, f->t ==> f inside T.owner
   ensures refOK(f,t)
{}
