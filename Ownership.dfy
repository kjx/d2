include "Library.dfy"
include "Object.dfy"
include "Bound.dfy"

//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//  core geometry
//
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

//object geometry

predicate inside(part : Object, whole : Object) : (rv : bool) reads {}  { part.AMFO >= whole.AMFO }

predicate inside3(part : Object, middle : Object, whole : Object) : (rv : bool) reads {}
   { part.AMFO >= middle.AMFO >= whole.AMFO }

predicate bounded(part : Object, whole : Object) : (rv : bool) reads {}  { part.AMFB >= whole.AMFB }


predicate strictlyInside(part : Object, whole : Object) : (rv : bool) reads {}  { part.AMFO > whole.AMFO }

predicate directlyInsideOLD(part : Object, whole : Object) : (rv : bool) { part.AMFX == whole.AMFO }
  //is this one right?  probably?  //see DreddOwner...
  //what if aprt as MORE directly listed owners?
  //what if thwose directly listed onwers are ALSO inside the whole?
  //if you do that, the whole can point DOWN INSIDE them, can't it??     //NEEDS_MORE_THOUGHT 3 Mar 2026

predicate directlyInside(part : Object, whole : Object) : (rv : bool) { whole in part.owner }
  //whole is (one of) part's listed direcly enclosing owners
  //whole has permission to point at part
  //matches current refDI - 3 Mar 2026

predicate onlyInside(part : Object, whole : Object) : (rv : bool) { part.owner == {whole} }
  //whole is the ONLY owner of part - part is only diretly inside whole

predicate directlyBounded(part : Object, bound : Object) : (rv : bool) {  part.AMFB  == bound.AMFO }
//nice idea but nor sure what it wouldu be (or do/)
//perhpas bound should bd an Owner not a Object.
//?yeah - what if there are stack owners around?
// or part.bound == bound ??

predicate outside(part : Object, whole : Object) : (rv : bool) reads {}  { not(inside(part,whole)) }

predicate colinear<T>(a : set<T>, b : set<T>) { (a > b) || (a == b) || (a < b) }



//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
// owner geometery
//
//ARGH -- shioudl thse be "Owners" or rather AMFO (ik.e OWNRs) s???
//answer - OWNR if this code doesnt' flatten - so shudl this flatten??? ARGH?

predicate ownerInsideOwner(partO : Owner, wholeO : Owner) { partO >= wholeO }
predicate ownerStrictlyInsideOwner(partO : Owner, wholeO : Owner) { partO > wholeO }

predicate ownerEquals(partO : Owner, wholeO : Owner) { flatten(partO) == flatten(wholeO) }
predicate ownerInside(partO : Owner, wholeO : Owner) { flatten(partO) >= flatten(wholeO) }

lemma transitiveInsideOwners(a : Owner, b : Owner, c : Owner)
  requires ownerInsideOwner(a,b)
  requires ownerInsideOwner(b,c)
   ensures ownerInsideOwner(a,c)
{}


// odd?

function sub(partO : OWNR, wholeO : OWNR) : OWNR
//the "local" ANFOs in partO  that are not strictly inside wholeO
  { partO - wholeO }

// object vs owner

predicate objectInsideOwner(part : Object, wholeO : Owner)         { part.AMFO >= wholeO }
predicate objectStrictlyInsideOwner(part : Object, wholeO : Owner) { part.AMFO >  wholeO }

lemma transitiveInside(a : Object, b : Object, c : Object)
  //CULL requires a.Ready() && b.Ready() && c.Ready()
  requires inside(a,b)
  requires inside(b,c)
   ensures inside(a,c)
{}

//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//
//interobject references
//
//
//see also R2? - NonCachedDefinitionsForPaper

predicate refBI(f : Object, t : Object) {(f.AMFB > {}) &&  (f.AMFB >=  t.AMFX)}

//predicate refDI(f : Object, t : Object) {f in t.owner}
//predicate refDI(f : Object, t : Object) {{f} == t.owner}

// predicate refDI(f : Object, t : Object) {flatten({f}) == flatten(t.owner)}  //HAK 12 APril 2026
// predicate refDI(f : Object, t : Object)      {f.self == t.owner}  // trial 12 APril 2026  //WRONGO WRONGO WRONGO
predicate refDI(f : Object, t : Object) {{f} == t.owner}  //GRK GKR 12 April 2026
   //annoying but makes the refOK proof fucking trivial...


predicate refDI_seqo(f : Object, t : Object) {f.AMFO == t.AMFX} // prev version
predicate refDI_fint(f : Object, t : Object) {f in t.owner} //AMDI_FINT
predicate refDI_fall(f : Object, t : Object) {t.owner == {f}} //AMDI_FINT

predicate refOK(f : Object, t : Object) {(f==t) || refBI(f,t) || refDI(f,t)}

//older version -- horrible namese so I don't write them by accident!!
predicate r_efOI(f : Object, t : Object) {f.AMFO >= t.AMFX}
predicate r_efOO(f : Object, t : Object) {(f==t) || r_efOI(f,t) || refDI(f,t)}

//
// lemma {:isolate_assertions} PaperVersions(f : Object, t : Object)
//  requires f.Ready() && t.Ready()
//   ensures ownerEquals(f.self, t.owner)  == refDI(f,t)
//   ensures ownerInside(f.self, t.owner)  == refOI(f,t)
//   ensures ownerInside(f.self, t.owner)  == refOI(f,t)
//  { }


lemma {:isolate_assertions} RefOKvsOO(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
    ensures refOK(f,t)  ==> r_efOO(f,t)
  //  ensures not(refOK(f,t) <==  r_efOO(f,t))
{}








//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//flatness
//

function {:isolate_assertions} {:timeLimit 15} flatten(os : Owner) : (fs : Owner)
     reads {}
   ensures os <= fs
    {(set o <- os, oo <- o.AMFO :: oo) + os}

predicate isFlat(os : Owner) {forall o <- os, oo <- o.AMFO :: oo in os}    //seems to work...





//From DAHLIA
predicate OutgoingReferencesAreInTheseObjects(os : set<Object>)
      reads os
      //note that this is within *this objectset
      //see also OutgoingReferencesAreInThisHeap
{
     (forall o <- os :: o.outgoing() <= os)
}


lemma ALLFEWERFIELDS(os : set<Object>)
   requires forall a <- os :: a.Ready()
   ensures  forall a <- os :: mapLEQ(a.fields, old(a.fields))
   ensures  forall a <- os :: a.Ready()
{}





////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//
// threads

predicate isThread(o : Object) reads o`nick { (o.nick != "" ) && (o.nick[0] == 't') }

predicate compatible(a : Object, b : Object)
 reads a`nick, b`nick
{ not( isThread(a) && isThread(b) ) }

predicate allCompatible(os: set<Object>)
  reads os`nick
 { forall a <- os, b <- os :: (a != b) ==> compatible(a,b) }


////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//
// bounds

function collectBounds(os : Owner) : Owner    //TODO old should delete  //THULE
  //  requires isFlat(os)
  reads {}    {set o <- os, oo <- o.AMFB :: oo}

predicate nuBoundsOK(oo : Owner, mb : Owner) {
//arguments are local fields, unflattened...
//&& (flatten(mb) <= flatten(oo))  //bound is a subset of owner
//  && (flatten(oo) >= flatten(mb)) //aka effectiveowner is INSIDE effectivebound
  //  && (forall o <- oo :: ((o.AMFB) >= flatten(mb)))

  && (myBoundsOK(oo,mb))

//  && (forall o <- oo :: ((o.AMFB + {o} ) >= flatten(mb)))

//  && (flatten(mb) <= (set ooo <- oo, omb <- ooo.AMFB :: omb) + oo)
        //AKA (I think) effectivebound is subseteq/surroundingeq the union of owners' bounds.
  }
//
// lemma {:verify false}  OldPolonium(oo : Owner, mb : Owner, m : Klon)
//   requires m.apoCalidse()
//   requires m.SuperCalidFragilistic()
//   requires oo <= m.m.Keys
//   requires mb <= m.m.Keys
//   requires nuBoundsOK(oo, mb)
//   requires flatten(oo) > m.o.AMFO
//   requires flatten(mb) > m.o.AMFO
// //   ensures nuBoundsOK(computeOwnerForClone(oo,m), computeOwnerForClone(mb,m))
//  {
//   assert (flatten(oo) >= flatten(mb));
//   assert (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))));
//
//   // var ro := computeOwnerForClone(oo,m);
//   // var rb := computeOwnerForClone(mb,m);
//
// var ro := mapThruKlon(oo, m);
// var rb := mapThruKlon(mb, m);
//
//   assert (flatten(ro) >= flatten(rb));
// //  assert (forall o <- ro ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(rb))));
//  }

////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
//
// gratuitious stuff for converting allAMFOs vs Flatten //LILLE

lemma {:isolate_assertions}  FLATTEN_ALLAMFOS(oo : Owner)
   requires AllReady(oo)
    ensures flatten(oo) == allAMFOs(oo)
{}


predicate AllReady(os : Owner) {forall oo <- os :: oo.Ready()}

function allAMFOs(oo : Owner) : (r : OWNR)
  ensures AllReady(oo) ==> (oo <= r)
  { set o <- oo, ooo <- o.AMFO :: ooo }


lemma ALLAMFOZZ(oo : Owner, o : Object)
  requires o in oo
   ensures allAMFOs(oo - {o}) + allAMFOs({o}) == allAMFOs(oo)
  {}

lemma {:isolate_assertions} ALLAMFOX(oo : Owner)
  requires AllReady(oo)
   ensures allAMFOs(oo) == allAMFXs(oo) + oo
  {
 calc {
   allAMFOs(oo);
   (set o <- oo, ooo <- o.AMFO :: ooo);
   (set o <- oo, ooo <- (o.AMFX+{o}) :: ooo);
   (set o <- oo, ooo <- (o.AMFX) :: ooo) +  (set o <- oo, ooo <- {o} {:trigger}  :: ooo);
   (set o <- oo, ooo <- (o.AMFX) :: ooo) +  oo;
   allAMFXs(oo) + oo;
  }}

function allAMFXs(oo : OWNR)  : (r : Owner)  { set o <- oo, ooo <- o.AMFX :: ooo }

function allReadyAMFOs(oo : Owner) : (r : OWNR)
    requires AllReady(oo)     { set o <- oo, ooo <- o.AMFO :: ooo }
function allObjectsAndAMFOs(oo : Owner) : (r : OWNR)   { set o <- oo, ooo <- o.AMFO :: ooo }



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

   requires strictlyInside(a, m.o)

   ensures c.owner == mapThruKlon(a.owner, m)
   ensures d.owner == mapThruKlon(b.owner, m)
//
//
//   requires strictlyInside(b,a)
//    ensures strictlyInside(d,c)

  requires inside(b,a)
   ensures inside(d,c)
  {}





lemma {:isolate_assertions} ac(a : Object, c : Object, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)

  requires a.Ready()
  requires c.Ready()
  // requires m.objectInKlown(a)
  // requires m.m[a] == c

  requires strictlyInside(a, m.o)

  requires m.ownersInKlown(a)
  requires c.owner == mapThruKlon(a.owner, m)
   ensures strictlyInside(c, m.c)
  {}



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