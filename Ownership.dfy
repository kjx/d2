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

// predicate refDI(f : Object, t : Object) {f in t.owner}
predicate refDI(f : Object, t : Object)      {f.self == t.owner}  // trial 12 APril 2026

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

predicate isFlat(os : Owner)              {forall o <- os, oo <- o.AMFO :: oo in os}    //seems to work...





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

lemma {:verify false}  OldPolonium(oo : Owner, mb : Owner, m : Klon)
  requires m.apoCalidse()
  requires m.SuperCalidFragilistic()
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
  requires nuBoundsOK(oo, mb)
  requires flatten(oo) > m.o.AMFO
  requires flatten(mb) > m.o.AMFO
//   ensures nuBoundsOK(computeOwnerForClone(oo,m), computeOwnerForClone(mb,m))
 {
  assert (flatten(oo) >= flatten(mb));
  assert (forall o <- oo ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(mb))));

  // var ro := computeOwnerForClone(oo,m);
  // var rb := computeOwnerForClone(mb,m);

var ro := mapThruKlon(oo, m);
var rb := mapThruKlon(mb, m);

  assert (flatten(ro) >= flatten(rb));
//  assert (forall o <- ro ::( (o.AMFX > {}) ==> ((o.AMFB+{o}) >= flatten(rb))));
 }

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
