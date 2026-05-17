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
















//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==
//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==
//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==


lemma {:isolate_assertions} abcd(a : Object, b : Object, c : Object, d : Object, m : Klon)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()
  requires d.Ready()

  requires klonReady(m)
  requires klonCalid(m)

  requires m.objectInKlown(a)
  requires m.objectInKlown(b)
  requires m.m[a] == c
  requires m.m[b] == d

  requires a in b.owner   //WORKS!
  //requires inside(b,a)   //DOESNT WORK!

  requires strictlyInside(a, m.o)

   ensures c.owner == mapThruKlon(a.owner, m)
   ensures d.owner == mapThruKlon(b.owner, m)

   ensures inside(b,a)
   ensures inside(d,c)
  {}





lemma {:isolate_assertions} ac(a : Object, c : Object, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)

  requires a.Ready()
  requires c.Ready()

  // requires m.objectInKlown(a)
  // requires m.m[a] == c

  requires m.ownersInKlown(a)
  requires klonLine(a,c,m)

  requires strictlyInside(a, m.o)

  requires m.ownersInKlown(a)
  requires c.owner == mapThruKlon(a.owner, m)
   ensures strictlyInside(c, m.c)
  { }



// recFlatOwn - recursive verison of AMFO..

function {:isolate_assertions} recFlatOwn0(o : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    {  {o} + (set xo <- o.owner, co <- recFlatOwn0(xo) :: co)  }


lemma RecFlatOwnIsAMFO(o : Object)
  decreases o.AMFO
   requires o.Ready()
    ensures recFlatOwn0(o) == o.AMFO
  {}


function {:isolate_assertions} recFlatOwn(o : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    ensures rv == o.AMFO
    { RecFlatOwnIsAMFO(o); recFlatOwn0(o) }

//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==
//
// deals with flatten in terms of RFO recuesive version of AMFO
//
// function {:isolate_assertions} {:timeLimit 15} flatten(os : Owner) : (fs : Owner)
//      reads {}
//    ensures os <= fs
//     {(set o <- os, oo <- o.AMFO :: oo) + os}



function {:isolate_assertions} {:timeLimit 15} flattenRFO(os : Owner) : (fs : Owner)
//version of flatten defined in terms of refFlatOwn instead of AMFO
    requires AllReady(os)
    requires forall o <- os :: o.Ready()
     reads {}
 //   ensures os <= fs
    {os + (set o <- os, oo <- recFlatOwn(o) :: oo)}


lemma {:isolate_assertions} {:timeLimit 30} FlatRFOIsFlatten(os : Owner)
  //wrapper over the horrible defintion below - SetRFOIsSetAMFO
  decreases allAMFOs(os)
   requires AllReady(os)
   requires forall o <- os :: o.Ready()
    ensures flattenRFO(os) == flatten(os)
  {
    SetRFOIsSetAMFO(os);
  }


lemma {:isolate_assertions} {:timeLimit 10} SetRFOIsSetAMFO(os : Owner)
  //aux defintion that flatten == flattenRFO
  decreases allAMFOs(os)
   requires AllReady(os)
   requires forall o <- os :: o.Ready()
   ensures ((set o <- os, oo <- recFlatOwn(o) :: oo) == (set o <- os, oo <- o.AMFO :: oo))
   ensures ((os+(set o <- os, oo <- recFlatOwn(o) :: oo))== (os+(set o <- os, oo <- o.AMFO :: oo)))
   ensures flattenRFO(os) == flatten(os)
{
  forall o <- os ensures (recFlatOwn(o) == o.AMFO)
    {
      RecFlatOwnIsAMFO(o);
    }
}


//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==
//
//native recursive flatten
//
//
// function {:isolate_assertions} {:timeLimit 15} recFlatten(os : Owner) : (fs : Owner)
//   //flatten defined recursively...
//    requires AllReady(os)
//   decreases allAMFOs(os)
//  {os + (set o <- os, co <- recFlatten(o.owner) :: co)}
//
//
// function {:isolate_assertions} rfo(o : Object) : (rv : Owner)
//   decreases o.AMFO
//    requires o.Ready()
//     {  {o} + (set xo <- o.owner, co <- rfo(xo) :: co)  }
//
//
// lemma {:isolate_assertions} {:timeLimit 30} FUCKED_RecFlattenIsFlatten(os : Owner)
//   decreases allAMFOs(os)
//    requires AllReady(os)
//    ensures recFlatten(os) == flatten(os)
//   { }
//
//
// lemma {:isolate_assertions} {:timeLimit 30} FUCKED_OneObjectReCFLATTEN(o : Object)
//   decreases o.AMFO
//    requires o.Ready()
//    ensures recFlatten({o}) == recFlatOwn(o)
//   {}


function mamfo(o : Object) : Owner  decreases o.AMFO, 1       requires o.Ready() {{o} + mflat(o.owner)}

function {:isolate_assertions} {:timeLimit 30} mflat(oo : Owner) : Owner  decreases allAMFOs(oo), 2 requires forall o <- oo :: o.Ready()  {set o : Object <- oo, ooo <- mamfo(o) :: ooo}

//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==//==
//
// aux relationsbi opbeetwen AMFO & FLATTEN

lemma AMFOtoFLATTEN(o : Object)
 requires o.Ready()
 ensures o.AMFO == {o} + flatten(o.owner)
 {}

lemma FLATTENtoAMFO(o : Object)
 requires o.Ready()
 ensures flatten({o}) == o.AMFO
 {}



 lemma {:isolate_assertions} {:timeLimit 15} FRFOFLAT(os : Owner)
  decreases allAMFOs(os)
   requires AllReady(os)
   requires forall o <- os :: o.Ready()
    ensures flattenRFO(os) == flatten(os)
    {
       if (os == {})
        {
          assert flattenRFO({}) == flatten({});
          return;
        } else {
           forall o <- os ensures (recFlatOwn(o) == o.AMFO) //by
              { RecFlatOwnIsAMFO(o); }

           assert ((set o <- os, oo <- recFlatOwn(o) :: oo) == (set o <- os, oo <- o.AMFO :: oo))
                     by { forall o <- os ensures (recFlatOwn(o) == o.AMFO) { RecFlatOwnIsAMFO(o); } }


//            forall o <- os ensures (recFlatten(o.owner) == flatten(o.owner)) {
//               if (o.owner == {}) {assert {} == recFlatten(o.owner) == flatten(o.owner); }
//               if (|o.owner| == 1)
//                     {
//                       assert recFlatten(o.owner) == flatten(o.owner);
//                     }
//
//
//            }
        }
    }


//
//
//  lemma {:isolate_assertions} {:timeLimit 15} RecFlattenIsFlatten(os : Owner)
//   decreases allAMFOs(os)
//    requires AllReady(os)
//     ensures recFlatten(os) == flatten(os)
//     {
//        if (os == {})
//         {
//           return;
//         } else {
//            forall o <- os ensures (recFlatten(o.owner) == flatten(o.owner)) {
//               if (o.owner == {}) {assert {} == recFlatten(o.owner) == flatten(o.owner); }
//               if (|o.owner| == 1)
//                     {
//                       assert recFlatten(o.owner) == flatten(o.owner);
//                     }
//
//
//            }
//         }
//     }