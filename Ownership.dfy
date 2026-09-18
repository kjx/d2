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
predicate pivotlyOutside(part : Object, whole : Object) : (rv : bool) reads {}  { not(strictlyInside(part,whole)) }


predicate colinear<T>(a : set<T>, b : set<T>) { (a > b) || (a == b) || (a < b) }

predicate offside(part : Object, whole : Object) reads {} { not(colinear(part.AMFO,whole.AMFO)) }

function allInside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | inside(o,whole) }
function allOutside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | outside(o,whole) }
function allOffside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | offside(o,whole) }

function allStrictlyInside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | strictlyInside(o,whole) }
function allPivotlyOutside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | pivotlyOutside(o,whole) }


lemma OffsideIsSideways(part : Object, whole : Object)
 //important bit is that we don't *just want these offsiders*4
 //we *also* want any "outsiders" that are reachable without going through the pivot / the whole
 //see point below
  ensures offside(part, whole) ==  (outside(part,whole) && not(inside(whole,part)))
  ensures offside(part, whole) ==> (outside(part,whole))
{}

lemma STRICTLY_COME_INSIDE(part : Object, whole : Object)
  // requires part.Ready()
  // requires whole.Ready()
   ensures     inside(part, whole)  <==>    (strictlyInside(part, whole) || (part == whole))
   ensures not(inside(part, whole)) <==> not(strictlyInside(part, whole) || (part == whole))

   ensures     strictlyInside(part, whole)  <==>    (inside(part, whole) && (part != whole))
   ensures not(strictlyInside(part, whole)) <==> not(inside(part, whole) && (part != whole))
   ensures not(strictlyInside(part, whole)) <==>   (outside(part, whole) || (part == whole))
   ensures outside(part,whole) != inside(part,whole)
{
  assume part.Ready();
  assume whole.Ready();
}



lemma PIVOTLY_COME_OUTSIDE(part : Object, whole : Object)
  // requires part.Ready()
  // requires whole.Ready()
   ensures     pivotlyOutside(part, whole)  <==>    (outside(part, whole) || (part == whole))
   ensures not(pivotlyOutside(part, whole)) <==> not(outside(part, whole) || (part == whole))

   ensures     outside(part, whole)  <==>    (pivotlyOutside(part, whole) && (part != whole))
   ensures not(outside(part, whole)) <==> not(pivotlyOutside(part, whole) && (part != whole))
   ensures not(outside(part, whole))  <==>   (strictlyInside(part, whole) || (part == whole))
   ensures strictlyInside(part,whole) != pivotlyOutside(part,whole)
{
  assume part.Ready();
  assume whole.Ready();
}


lemma HappyFamilies0(next : Object, whole : Object)
  requires next.Ready()
   ensures (allInside(next.AMFO, whole) + allOutside(next.AMFO, whole)) == next.AMFO
   ensures (allInside({next}, whole) + allOutside({next}, whole)) == {next}

   ensures (allInside(next.AMFO, whole) + allOutside(next.AMFO, whole) + allOffside(next.AMFO, whole)) == next.AMFO
   ensures (allInside({next}, whole) + allOutside({next}, whole) + allOffside({next}, whole)) == {next}
{

}


lemma HappyFamilies(soup : set<Object>, whole : Object, ins: set<Object>, outs: set<Object>, sides: set<Object>)
  requires ins   == allInside(soup, whole)
  requires outs  == allOutside(soup, whole)
  requires sides == allOffside(soup, whole)
   ensures soup  == ins + outs
   ensures soup  == ins + outs + sides  //WHAAAT?
   ensures soup  >= outs >= sides
{}

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

//see also R2? - NonCachedDefinitionsForPaper

predicate refBI(f : Object, t : Object) {(f.AMFB > {}) &&  (f.AMFB >=  t.AMFX)}

//predicate refDI(f : Object, t : Object) {f in t.owner}
//predicate refDI(f : Object, t : Object) {{f} == t.owner}

// predicate refDI(f : Object, t : Object) {flatten({f}) == flatten(t.owner)}  //HAK 12 APril 2026
// predicate refDI(f : Object, t : Object)      {f.self == t.owner}  // trial 12 APril 2026  //WRONGO WRONGO WRONGO
predicate refDI(f : Object, t : Object) {{f} == t.owner}  //GRK GKR 12 April 2026
   //annoying but makes the refOK proof fucking tril...


predicate refDI_seqo(f : Object, t : Object) {f.AMFO == t.AMFX} // prev version
predicate refDI_fint(f : Object, t : Object) {f in t.owner} //AMDI_FINT
predicate refDI_fall(f : Object, t : Object) {t.owner == {f}} //AMDI_FINT

predicate refOK(f : Object, t : Object) {(f==t) || refBI(f,t) || refDI(f,t)}

//older version -- horrible namese so I don't write them by accident!!
predicate r_efOI(f : Object, t : Object) {f.AMFO >= t.AMFX}
predicate r_efOO(f : Object, t : Object) {(f==t) || r_efOI(f,t) || refDI(f,t)}

//
// lemma PaperVersions(f : Object, t : Object)
//  requires f.Ready() && t.Ready()
//   ensures ownerEquals(f.self, t.owner)  == refDI(f,t)
//   ensures ownerInside(f.self, t.owner)  == refOI(f,t)
//   ensures ownerInside(f.self, t.owner)  == refOI(f,t)
//  { }


lemma RefOKvsOO(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
    ensures refOK(f,t)  ==> r_efOO(f,t)
  //  ensures not(refOK(f,t) <==  r_efOO(f,t))
{}








//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//flatness
//


function argh(o : Object) : (rv : Owner)
//clean recursive  alternative definition of AMFO (recAmfo?) // recAllOwners
//but with a really really shitty name!
  decreases o.AMFO
  // requires o.Ready()
 { assume o.Ready();
   {o} + (set oo <- o.owner, ooo <- argh(oo) :: ooo) }


function flatten(os : Owner) : (fs : Owner)
     reads {}
   ensures os <= fs
    {(set o <- os, oo <- o.AMFO :: oo) + os}

predicate isFlat(os : Owner) {forall o <- os, oo <- o.AMFO :: oo in os}    //seems to work...
// or  forall o <- os :: o.AMFO <= os ?

lemma FLAT_EITHER_WAY(os : Owner)
  ensures (forall o <- os, oo <- o.AMFO :: oo in os) == (forall o <- os :: o.AMFO <= os)
  {}

lemma FLATTEN0(o : Object)
 decreases o.AMFO
  requires o.Ready()
   ensures flatten(o.owner) == o.AMFX
   ensures flatten({o}) == o.AMFO
   ensures o.AMFO == argh(o)
   ensures flatten({o}) == argh(o)
{}

lemma FLATTEN1(os : Owner, o : Object, fs : Owner)
 decreases o.AMFO
  requires o.Ready()
  requires os + {o} == fs
   ensures flatten(os) + flatten({o}) == flatten(fs)
   ensures flatten(os) + o.AMFO == flatten(fs)
   ensures flatten(os) + argh(o) == flatten(fs)
  {
    FLATTEN0(o); FLATTEN2(os,{o},fs);
  }

lemma FLATTEN2(os : Owner, ps : Owner, fs : Owner)
  requires os + ps == fs
   ensures flatten(os) + flatten(ps) == flatten(fs)
  {}

lemma FLATTEN9(os : Owner, fs : Owner)
 decreases allAMFOs(os)
  requires fs == flatten(os)
   ensures fs == (set s <- os, f <- s.AMFO :: f) + os
{}


lemma OutySidey(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
   requires outside(o,pivot)
    ensures forall oo <- o.owner :: outside(oo,pivot)
    ensures forall oo <- o.AMFO  :: outside(oo,pivot)
    ensures forall oo <- flatten({o}) :: outside(oo,pivot)
{}

lemma OutiesSidies(soup : Owner, pivot : Object)
  decreases allAMFOs(soup)
   requires pivot.Ready()
   requires forall s <- soup :: s.Ready()
   requires forall s <- soup :: outside(s,pivot)
    ensures forall oo <- soup :: outside(oo,pivot)
    ensures forall s <- soup, oo <- s.AMFO :: outside(oo,pivot)
    ensures forall oo <- flatten(soup) :: outside(oo,pivot)
{}

lemma MaybeOutiesSidies(soup : Owner, pivot : Object)
  decreases allAMFOs(soup)
   requires pivot.Ready()
   requires forall s <- soup :: s.Ready()
    ensures forall s <- soup | outside(s,pivot) :: outside(s,pivot)
    ensures forall s <- soup, oo <- s.AMFO | outside(s,pivot) :: outside(oo,pivot)
////ensures forall oo <- flatten({s}), s <- soup | outside(s,pivot) :: outside(oo,pivot)   ///.EEEVIL
    ensures forall s <- soup, oo <- flatten({s}) | outside(s,pivot) :: outside(oo,pivot)
{}

/////////////////////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////////////////////



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


//
// lemma {:verify false}  OldPolonium(oo : Owner, mb : Owner, m : Klon)
//   requires m.apoCalidse()
//   requires m.SuperCalidFragilistic()
//   requires oo <= m.m.Keys
//   requires mb <= m.m.Keys
//   requires boundsOK(oo, mb)
//   requires flatten(oo) > m.o.AMFO
//   requires flatten(mb) > m.o.AMFO
// //   ensures boundsOK(computeOwnerForClone(oo,m), computeOwnerForClone(mb,m))
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

lemma  FLATTEN_ALLAMFOS(oo : Owner)
   requires AllReady(oo)
    ensures flatten(oo) == allAMFOs(oo)
{}


predicate AllReady(os : Owner) {forall oo <- os :: oo.Ready()}
predicate AllValid(os : Owner) reads os`fields, os`fieldModes {forall oo <- os :: oo.Valid()}

function allAMFOs(oo : Owner) : (r : OWNR)
  ensures AllReady(oo) ==> (oo <= r)
  { set o <- oo, ooo <- o.AMFO :: ooo }


lemma ALLAMFOZZ(oo : Owner, o : Object)
  requires o in oo
   ensures allAMFOs(oo - {o}) + allAMFOs({o}) == allAMFOs(oo)
  {}

lemma ALLAMFOX(oo : Owner)
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


predicate insideAndReady(part : Object, whole : Object)
  requires part.Ready()
  requires whole in part.AMFO
   ensures whole.Ready()
   {
    WHOLE_ENCHILADA(part,whole.AMFO);
    inside(part,whole)
   }




lemma WHOLE_READY(part : Object, whole : Object)
  decreases part.AMFO
   requires part.Ready()
   requires whole in part.AMFO
    ensures inside(part,whole)
    ensures whole.Ready()
  {
   assert whole.AMFO <= part.AMFO;
    AllOwnersFlatAndReady(part);
   }

lemma WHOLE_ENCHILADA(part : Object, random : set<Object>)
  decreases part.AMFO
   requires part.Ready()
   requires random <= part.AMFO
    ensures forall x <- random :: x.Ready()
    ensures forall x <- random :: isFlat(x.AMFO)
    ensures forall x <- random :: x.AMFO <= part.AMFO
    ensures forall x <- random :: inside(part, x)
  {
   AllOwnersFlatAndReady(part);
  }

lemma AllOwnersFlatAndReady(part : Object)
  decreases part.AMFO
   requires part.Ready()
    ensures isFlat(part.AMFO)
    ensures forall x <- part.AMFO :: x.AMFO <= part.AMFO
    ensures forall x <- part.AMFO :: isFlat(x.AMFO)
    ensures forall x <- part.AMFO :: x.Ready()
{}
