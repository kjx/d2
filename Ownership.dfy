include "Library.dfy"
include "Object.dfy"

//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//  core geometry
//
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]





//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//flatness
//
//

function {:isolate_assertions} {:timeLimit 15} flatten(os : Owner) : (fs : Owner)
     reads {}
   ensures os <= fs
    {(set o <- os, oo <- o.AMFO :: oo) + os}




////////////////////////////////////////////////////////////////////////////////
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



//KJXFEARSATAN
predicate isFlat(os : Owner)              {forall o <- os, oo <- o.AMFO :: oo in os}    //seems to work...
predicate isReallyFuckingFlat(os : Owner) {forall o <- os, oo <- o.AMFO :: oo in os}

predicate colinear<T>(a : set<T>, b : set<T>) { (a > b) || (a == b) || (a < b) }
function sub(partO : OWNR, wholeO : OWNR) : OWNR
//the "local" ANFOs in partO  that are not strictly inside wholeO
  { partO - wholeO }
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













lemma {:isolate_assertions} SubObjectsGeqViaOWNRs(p0 : Object, w0 : Object, p1 : Object, w1 : Object, m : Klon)
    requires m.SuperCalidFragilistic()
    requires m.objectReadyInKlown(p0)
    requires m.objectReadyInKlown(w0)
    requires inside3(p0,w0,m.o)
    requires not(inside(w1, w0)) // careful because we want !>= relation, as against < or <=
    requires p1.AMFO == shiftAMFO(p0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
    requires w1.AMFO == shiftAMFO(w0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
     ensures inside3(p1,w1,m.m[m.o])
{}

// lemma {:isolate_assertions} SubObjectsGeqViaOWNRs(p0 : Object, w0 : Object, p1 : Object, w1 : Object, m : Klon)
//     requires m.SuperCalidFragilistic()
//     requires m.objectReadyInKlown(p0)
//     requires m.objectReadyInKlown(w0)
//     requires inside3(p0,w0,m.o)
//     requires not(inside(w1, w0)) // careful because we want !>= relation, as against < or <=
//     requires p1 == shiftObject(p0, m)
//     requires w1 == shiftObject(w0, m)
//      ensures inside3(p1,w1,m.m[m.o])
//      {
//
//      }

lemma {:isolate_assertions} SubAMFOsGeq(p0 : OWNR, w0 : OWNR, p1 : OWNR, w1 : OWNR, m : Klon)
    //p0 and w0 are flattened owners )AMFOs( within pivot x0;  (original)
    //p1 and w1 are flattened owners )AMFOs( within copivot x1;  (clone)
    requires m.SuperCalidFragilistic()
    requires m.m.Keys >= p0 >= w0 >= m.o.AMFO
  //  requires not( w1 >= w0 ) // careful because we want !>= relation, as against < or <=
    requires p1 == shiftAMFO(p0, m.o.AMFO, m.m[m.o].AMFO, m.m)
    requires w1 == shiftAMFO(w0, m.o.AMFO, m.m[m.o].AMFO, m.m)

     ensures m.objectReadyInKlown(m.o)
     ensures m.m[m.o] in m.m.Values
     ensures sub(p0,m.o.AMFO) >= sub(w0,m.o.AMFO)
     ensures sub(p1,m.m[m.o].AMFO) >= sub(w1,m.m[m.o].AMFO)
     ensures p1 >= w1 >= m.m[m.o].AMFO
{
    assert m.SuperCalidFragilistic();
    assert m.objectReadyInKlown(m.o);
    assert m.m.Keys >= m.o.AMFO;
    assert forall oo <- m.o.owner :: (oo in m.m.Keys) && (m.m[oo] in m.m.Values);
    assert forall oo <- m.o.AMFO :: m.m[oo] in m.m.Values;

    assert m.OwnersLineKV(m.o, m.m[m.o]);
    assert mappingOwnersThruKlownKV(m.o, m.m[m.o], m);

    assert m.o.Ready();
    assert forall oo <- m.o.owner :: inside(m.o, oo);
    assert m.m[m.o].Ready();
    assert forall oo <- m.m[m.o].owner :: inside(m.m[m.o], oo);
}

function {:isolate_assertions} shiftObject(i0 : Object, m : Klon) : (i1 : Object)
// see below BETTER version but with stronger preconditions
// kept this one becuase the necessary refactoring needs to come later //JDl
    requires m.apoCalidse()
//    requires m.SuperCalidFragilistic()
//     ensures m.AllLinesCalid()
    requires i0.Ready()
    requires inside(i0, m.o)
    requires m.objectInKlown(i0)

//    ensures inside(i1, m.m[m.o] )
    //    reads m.hns()
    { m.m[i0] }


///MOVED out to M2... for now
//verison verifies in M2 with HighLine as precondition...
// function {:isolate_assertions} shiftObjectBETTER(i0 : Object, m : Klon) : (i1 : Object)
//     requires m.apoCalidse()
//     requires m.SuperCalidFragilistic()
//      ensures m.AllLinesCalid()
//     requires i0.Ready()
//     requires inside(i0, m.o)
//     requires m.objectInKlown(i0)
//      ensures inside(i1, m.m[m.o])
//        reads m.hns()
//     { m.m[i0] }



lemma {:isolate_assertions} {:timeLimit 60} IWannaBeFoolish(i0 : Object, m : Klon, i1 : Object)
  requires m.objectReadyInKlown(i0)
  requires m.SuperCalidFragilistic()
  requires inside(i0, m.o)
  requires m.m[i0] == i1 ///'not strong enough  (6 Oct 2025)
  requires i1.AMFO == shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
  requires forall z <- (m.m.Keys)   :: z.Ready()
  requires forall z <- (m.m.Values) :: z.Ready()
  requires forall z <- (i0.AMFO)    :: z.Ready()
  requires forall z <- (i1.AMFO)    :: z.Ready()
  requires flatten(i0.AMFO) <= m.oHeap
  requires flatten(i1.AMFO) <= m.hns(i1.AMFO)

   ensures i1 == shiftObject(i0, m)
   ensures i1.AMFO == shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m)
   ensures mappingOWNRsThruKlownKV(i0.AMFO, i1.AMFO, m)
   {

   var kk := i0.AMFO;
   var vv := (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO);
   assert vv == i1.AMFO;

var si0 := i0.AMFO;
var sx0 := m.o.AMFO;
var sx1 := m.m[m.o].AMFO;
var slm := m.m;
var si1 := shiftAMFO(i0.AMFO, m.o.AMFO, m.m[m.o].AMFO, m.m);
assert si1 == (set o <- (si0 - sx0) :: slm[o]) + sx1;
assert si1 == (set o <- (i0.AMFO - m.o.AMFO) :: m.m[o]) + m.m[m.o].AMFO;
assert si1 == vv;

assert i1.AMFO == si1;

//assert mappingOWNRsThruKlownKV(i0.AMFO, i1.AMFO, m);
   }

//MORE FOOKING LEMMERS
//
//every AAMFO was an owner somnwbere    ie. go up recursively aND you'll fid in decaredw aws a nao nwer
//we can cu & paste flatteniung trthough shit

// lemma IsFUCKEDREALLY(p : OWNR, w : OWNR)
//    requires AllReady(p)
//    requires AllReady(w)   //force of hobbit?
//    requires p >= w        // p inside w
//
//  {}


//tis lemmer moved to the top of R2.dfy


function {:isolate_assertions} shiftAMFO(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires i0 >= x0
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures i1 >= x1
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }

function {:isolate_assertions} shiftAMFOF(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires flatten(i0) >= x0
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures flatten(i1) >= x1
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }



function {:isolate_assertions} shiftAMFOZ(i0 : OWNR, x0 : OWNR, x1 : OWNR, im : vmap<Object, Object>) : (i1 : OWNR)
 //given i0 insidfe x0, shift it sideways to the same relationship with w1
 //fuck - perhaps this needs a Klon.  probalby does!
 // lemmee guess, this thrns out to b som version of nmapwthKlon.  fucker.  commie FUCK.
 // except coming in as OWNRs not Owners or Objects
 //grrr
 //**wont verify with just apoCalidse..  */
  requires i0 <= im.Keys
     //aka requires im.Keys >= i0 >= x0
   ensures i1 == (set o <- (i0 - x0) :: im[o]) + x1
               { (set o <- (i0 - x0) :: im[o]) + x1 }


// bounds

function collectBounds(os : Owner) : Owner    //TODO old should delete  //THULE
  //  requires isFlat(os)
  reads {}    {set o <- os, oo <- o.AMFB :: oo}

// Owner or OWNR
// needs to be flat?

predicate nuBoundsOK(oo : Owner, mb : Owner) {
//&& (flatten(mb) <= flatten(oo))  //bound is a subset of owner
  && (flatten(oo) >= flatten(mb)) //aka effectiveowner is INSIDE effectivebound
  && (flatten(mb) <= (set ooo <- oo, omb <- ooo.AMFB :: omb) + oo)
      //AKA (I think) effectivebound is subseteq/surroundingeq the union of owners' bounds.
}

lemma {:isolate_assertions} SuicideIsPainless(o : Object, m : Klon, rowner : Owner, rbound : Owner)
//attempt at the FUCKING THING whch of course DOES NOT WORK
  requires o.Ready()

  requires strictlyInside(o, m.o)
  requires m.ownersInKlown(o)
  requires m.SuperCalidFragilistic()
  requires m.apoCalidse()
   ensures flatten(o.owner) >= flatten(o.bound)

  requires rowner == computeOwnerForClone(o.owner, m)
  requires rbound == computeOwnerForClone(o.bound, m)

  //  ensures nuBoundsOK(rowner, rbound)
  //  ensures flatten(rowner) >= flatten(rbound)
  //  ensures flatten(rbound) >= flatten(o.bound)
{}





// definitions of inside

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


lemma DirectlyInside(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires directlyInside(part, whole)
   ensures inside(part,whole)
   ensures strictlyInside(part,whole)
{
  FlattenInsideFlat(whole,flatten(part.owner));
}


lemma OnlyInside(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires onlyInside(part, whole)
   ensures inside(part,whole)
   ensures strictlyInside(part,whole)
{
   FlattenInsideFlat(whole,flatten(part.owner));
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
  FlattenIsFlat(part.owner);
  FlattenInsideFlat(whole,flatten(part.owner));
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



predicate objectInsideOwner(part : Object, wholeO : Owner)         { part.AMFO >= wholeO }
predicate objectStrictlyInsideOwner(part : Object, wholeO : Owner) { part.AMFO >  wholeO }


predicate outside(part : Object, whole : Object) : (rv : bool) reads {}  { not(inside(part,whole)) }

lemma ownerInsideSanity(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
   ensures inside(part, whole)        ==> ownerInside(part.owner, whole.owner)
   ensures inside(part, whole)       <==> ownerInside(part.self , whole.self )
   ensures (part.AMFB >= whole.AMFB) <==> ownerInside(part.bound, whole.bound)
  {}

lemma transitiveInside(a : Object, b : Object, c : Object)
  //CULL requires a.Ready() && b.Ready() && c.Ready()
  requires inside(a,b)
  requires inside(b,c)
   ensures inside(a,c)
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


//interobject references
//see also R2? - NonCachedDefinitionsForPaper

predicate refBI(f : Object, t : Object) {(f.AMFB > {}) &&  (f.AMFB >=  t.AMFX)}  //GREENLAND //AMFB_GEQ_GT  //AMFB-NOT-NULL

predicate refDI(f : Object, t : Object) {f.AMFO == t.AMFX}

predicate refDI_seqo(f : Object, t : Object) {f.AMFO == t.AMFX}
predicate refDI_fint(f : Object, t : Object) {f in t.owner} //AMDI_FINT
predicate refDI_fall(f : Object, t : Object) {t.owner == {f}} //AMDI_FINT

predicate refOK(f : Object, t : Object) {(f==t) || refBI(f,t) || refDI(f,t)}

//older version
predicate refOI(f : Object, t : Object) {f.AMFO >= t.AMFX}
predicate refOO(f : Object, t : Object) {(f==t) || refOI(f,t) || refDI(f,t)}

//{:timeLimit 30}
//{:isolate_assertions}

lemma {:isolate_assertions} PaperVersions(f : Object, t : Object)
 requires f.Ready() && t.Ready()
  ensures ownerEquals(f.self, t.owner)  == refDI(f,t)
  ensures ownerInside(f.self, t.owner)  == refOI(f,t)  //SHIT. f.self of f.owner. which is right, trhis onw or abo evw?
 { }

lemma {:isolate_assertions} RefOKvsOO(f : Object, t : Object)
  requires f.Ready()
  requires t.Ready()
    ensures refOK(f,t)  ==> refOO(f,t)
  //  ensures not(refOK(f,t) <==  refOO(f,t))
{}

//does ths make sense.  dunno?
// lemma {:isolate_assertions} RefOKisInsideOwner(f : Object, t : Object)
//   requires f.Ready()
//   requires t.Ready()
//   requires refOK(f,t)
//    ensures f.AMFO >= t.AMFX   ///classic O-as-D, f->t ==> f inside T.owner
//    {
//     assert  refOK(f,t);
//
//     if (f==t)
//      {
//       assert f.AMFO > f.AMFX == t.AMFX;
//       return;
//      }
//
//     if (refBI(f,t))
//      {
//       assert f.AMFO >= f.AMFB >= t.AMFX;
//       return;
//      }
//
//     if (refDI(f,t))
//      {
//       assert f in t.owner;
//       assert f in flatten(t.owner);
//       assert f in t.AMFX;
//       FlatMeFlatMyOwners(f,t.AMFX);
//
//
// //      assert flatten({f}) >= flatten(t.owner);
//       assert f.AMFO >= t.AMFX;
//       return;
//      }
//
// assert false;
// }




// lemma  {:isolate_assertions} RefOKisRefOK(f' : Object, t' : Object, f : Object, t : Object, m : Klon)
//     //moved out to M2 to get HighLineKV
//  requires …
//  requires refOK(f',t')
//   //i.e thees are ACTUAL CLONES not POTENTIAL CLOINES
//  requires f == m.m[f']
//  requires t == m.m[t']
//
//  ensures refOK(f,t)
//



// lemma {:isolate_assertions} RefBIGoesIn(f' : Object, f : Object, t : Object, m : Klon)
   //cancelled 24 Jan 2024 becaues  **it doesn't "go in"
   //notaby, if refBI(f', t), and  inside(f,f'). well f could be another object that can reach t
   //but equally f could3 be a capsule with NO OUTGOING REFERENFES.
    //OOPS.  so there is luikely some analogue ut I dunno what it is. backwards?
//   requires f'.Ready() && f.Ready() && t.Ready()
//   requires m.SuperCalidOwners()
//   requires refBI(f', t)
//    ensures f'.AMFB >= t.AMFX
//   requires inside(f,f')
//    ensures f.AMFO >= f'.AMFO
//    ensures refBI(f,  t)
//    ensures f'.AMFB >= t.AMFX
// {
//   assert f.AMFO >= f'.AMFO;
//   assert f' in f.AMFO;
//   assert f.AMFO == f.AMFX + {f};
//   assert (f == f') || (f' in f.AMFX);
//
//   if (f == f') { return; }  //HAW HAW HAW
//
//   f.ExtraReady();
//   assert  (f' in f.AMFX);
//   assert  (forall oo <- f.AMFX  :: f.AMFB <= oo.AMFB);
//   assert  f.AMFB <= f'.AMFB;
// }


lemma {:isolate_assertions} RefDIGoesIn(f' : Object, f : Object, t : Object, m : Klon)
  requires f'.Ready() && f.Ready() && t.Ready()
  requires m.SuperCalidOwners()
  requires refDI(f', t)
//  requires inside(f,f')
//   ensures refDI(f, t)
ensures inside(t,f')
{
   assert inside(t,f');
}



// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //
// //  Klon - clone mapping!
// //
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//
//
//
//  thinkgs to add - the two level version?  (PreKlon and Klon?)
//    c - : objecet --=- the top of the clone! hurrah! m.m[m.o]!

datatype Klon = Klon
(
  m : vmap<Object,Object>,    //the  klon map
  o : Object,                 //object being copied
  clowner : Owner,            //owner of the clone
  clbound : Owner,            //bound of the clone
  oHeap : set<Object>,        //heap
  o_amfx : Owner,             //was o. so the AMFX of o
  //  c_amfb : OWNR,              //epected flattened bound of the clone..
  c_amfx : Owner              //epected flattened ownershio of the clone..
)
{
  function  ns(os : set<Object> := {}) : set<Object> { m.Values+os        }
  function hns(os : set<Object> := {}) : set<Object> { oHeap+m.Values+os  }

  predicate from(prev : Klon) : (r : bool)
    ensures r ==> (isFlat(prev.oHeap) ==> isFlat(oHeap))
  {
    && mapGEQ(m,  prev.m)
    && o       == prev.o
    && clowner == prev.clowner
    && clbound == prev.clbound
    && oHeap   == prev.oHeap     //OPTION - considere incorporating ApoCalidseNow...
    && o_amfx  == prev.o_amfx
    && c_amfx  == prev.c_amfx
       //option ie allow heaps to get bigger, so long as all keys are in the heap
  }


  predicate HeapOwnersReady()
    reads {}
  { forall x <- oHeap :: (x.AMFO <= oHeap) }

  predicate ValuesOwnersReady()
    reads {}
  {
   forall x <- m.Values :: (x.AMFO <= hns())
  }

  predicate HeapContextReady()
    reads oHeap
  {///KJX 1 Augu 2025 - not sure this is right cos
   ///do3esentt that contradict the heap p      ointoting to na
   ///i.e. heap ispart of hns isn't it?
   ///answer yes, but that doen't happen during a clone() operation...
    (forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap)))
  }

  predicate ValuesContextReady()
    reads m.Values, oHeap
  {
    //KJX experimental!! 11 aug 2025
   forall x <- m.Values :: x.Context(hns())  ///KJX HACKED 4 Oct 2025    ///shojld this say "READY"
  //or should this be hns too?
//    (forall x <- m.Values :: (x.Ready() && x.Valid() && x.Context(hns())))
  }

predicate ValueInContext(v : Object)
  requires ValuesContextReady()   //WHAT THE FUYCK???
  requires v in hns()
  reads hns(),  m.Values, oHeap
  { (v.Ready() && v.Valid() && v.Context(hns())) }



  ghost predicate {:isolate_assertions}   preCalid() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name
    reads oHeap, m.Values

    // requires HeapContextReady()
    // requires ValuesContextReady()
  {
    //internal consistency
    //note that the pivot object being clone "o"
    //does not hace to be in the map at the start.

    //&& (isFlat(oHeap))  //KJXFEARSATAN

    && HeapContextReady()
    && ValuesContextReady()

    && (o in oHeap)
    && (objectInKlown(o))  //KJXFUCK  do i want this in here? really?   ///Can U do without it??
    && (o.AMFX == o_amfx)
//WTF    && (flatten(clbound) >= o.AMFB)
    && (nuBoundsOK(o.owner, o.bound))
    && (o.AMFO == o_amfx+{o})
   //bound can only move DOWN
    //    && (not(c_amfx > o_amfx)) //HUMBERT HUMBERT
    // important to note that c_amfx can be any distance below o_amfx -
    // or more accurately, any distance below o.bound
    // which may (or may not) be *above*/*outside* o_amfx.
    && (c_amfx >= flatten(clbound) >= flatten(o.bound))
  }



  ghost predicate {:isolate_assertions} preCalid2() : (r : bool)
    //More PreCalid2 Stuff
    // reads oHeap`fields, oHeap`fieldModes
    // reads m.Keys`fields, m.Keys`fieldModes
    // reads m.Values`fields, m.Values`fieldModes
    // reads o`fields, o`fieldModes
    // reads m.Values, oHeap

    reads {}
  {
    //   m : vmap<Object,Object>,    //the  klon map
    //   o : Object,                 //object being copied
    //   clowner : Owner,            //owner of the clone
    //   clbound : Owner,            //bound of the clone
    //   oHeap : set<Object>,        //heap
    //   o_amfx : Owner,             //was o. so the AMFX of o
    // //  c_amfb : OWNR,              //epected flattened bound of the clone..
    //   c_amfx : Owner

    && (c_amfx <= oHeap) //should goto precalid1??
      //Llooks kinda odd...

    && ((o in m.Keys) ==> (
        var c := m[o]; //WE HAS KLONE
         ///&& add in c.Ready()???
          && (c_amfx  == c.AMFX)
          && (clowner == c.owner)
          && (clbound == c.bound)

          && (c  in m.Values)
          && (c !in oHeap)
       ))
  }

  ghost predicate {:isolate_assertions} SuperCalidFragilistic() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name

    reads oHeap, m.Values
///can goto reads {} bia HeapOwnersReady && ValuesOwnersReady…

    // reads oHeap`fields, oHeap`fieldModes
    // reads m.Keys`fields, m.Keys`fieldModes
    // reads m.Values`fields, m.Values`fieldModes
    // reads o`fields, o`fieldModese
    // reads m.Values, oHeap
  {
//    false  //WHAT THE FUCKY FUCK FUCK???4
    && HeapContextReady()
    && ValuesContextReady()
    && Calid()
  }

  //opaque
  ghost predicate {:isolate_assertions} Calid() : (r : bool)
    //Klon mapping is consitent & valid.
    //Calid just seened like a good name

    //dont call this directly - call SuperCalid
    requires  HeapContextReady()
    requires  ValuesContextReady()

    reads oHeap, m.Values
 {
    //internal consistency
    && preCalid()
    && preCalid2()

    //calidObjects - mostly about oHeap and ns and stuff
    && (m.Keys <= oHeap)
    && (forall k <- m.Keys :: (k.Ready() && k.Valid()))   //note no Context

    //this recapitulates ValuesContextReady() but putting it here lets things work
    && (forall v <- m.Values :: (v.Ready() && v.Valid()))    //note no Context

    //the pivot object "o" being cloned
    // && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))
    && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))

    //what's all this SHIT and why is it here and how doe it realte to allLinesCallid etc!
    && (forall k <- m.Keys   :: m[k].AMFO  >= m[k].AMFB  >= k.AMFB)
//      && (forall k <- m.Keys   :: m[k].AMFO  >= m[k].AMFB >= o.AMFB >= k.AMFB)   ///change made then backed out 10Jul 2025 - why wo why oh why ?

    // && (forall k <- m.Keys   :: m[k].owner >= m[k].bound >= k.bound)
    && (forall k <- m.Keys   :: (not(inside(k,o)) ==> (m[k] == k)))
    && (forall k <- m.Keys   :: (   (inside(k,o)) ==> (m[k] !in oHeap)))
    //
    //calidSheep - su WRONGbsumed?
    //12 Jine 2025 clipping this out for now

    //KlonVMqpOK(k, context)
    && (forall k <- m.Keys :: k.AMFO <= m.Keys)
    && (forall k <- m.Keys :: k.AMFB <= m.Keys)

    && (&& (HeapOwnersReady())
        //  && ((forall x <- m.Keys :: x.Ready() && x.Valid() && x.Context(oHeap) && objectInKlown(x)   ))
        && (ValuesOwnersReady())
        && (gettingThere())
        && (AllLinesCalid()))

    //    && (forall k <- m.Keys :: ownersInKlown(k) && checkClownership(k, m[k], this))
  }



//   //removeing the var declaratioon on this end
//   //made things work on the other!
  predicate gettingThere() reads {} {
    // forall k <- m.Keys ::
    //     (var v := m[k];
    //     && (k.Ready())
    //     && (objectInKlown(k))
    //     && (v.Ready())
    //     && (v in hns({v})))
    forall k <- m.Keys :: (
                            && (k.Ready())
                            && (objectInKlown(k))
                            && (m[k].Ready())
                            && (m[k] in hns())
                          )

  }

//
//   //and again --- isses are things like HeapContexReady, ValuesContext, reqs vs conjuncts,
  predicate {:isolate_assertions} AllLinesCalid()
    //all pairs (aka lines) in the overall Klon map are Calid
    requires gettingThere()

    requires o.Ready() && objectInKlown(o)
    requires m.Keys <= oHeap

    //what's left of the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires HeapOwnersReady()
    requires c_amfx <= oHeap
    reads oHeap, m.Values
  {
    (forall k <- m.Keys :: CalidLineKV(k, m[k]))
  }

//
//
//
//
//

  lemma {:isolate_assertions} {:timeLimit 20} CalidLineKVTo(k : Object, v : Object, m1 : Klon)
    requires apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires ownersInKlown(k)
    requires v.Ready()
    requires CalidLineKV(k,v)
    requires m1.from(this)
    requires m1.apoCalidse()
     ensures m1.CalidLineKV(k,v)
{}


  predicate {:isolate_assertions} CalidLineKV(k : Object, v : Object)
    //conditions for individual mappings (pairs aka lines) in the overall Klon map
    //this shoiuld work for lines *already* in the Klon
    //*as well as* for lines that aren't into the Klon
    ///(but it won't tell you if you can add them cos they could be already in there)
    requires apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires ownersInKlown(k)
    requires v.Ready()

    reads oHeap, m.Values
  {

    && (k in oHeap)    //this one is easy - what to do for things like v.AMFO aren't...
    //or perhaps it is - they either ibn the preheap or ns newstuff
        //KJX - 10 Aug 2025

    //the fundamental something-or-other
    && (not(inside(k,o)) ==> (v == k))
    && (   (inside(k,o)) ==> (v !in oHeap))
//    && (   (inside(k,o)) ==> (v.AMFO  >= v.AMFB >= k.AMFB))  //Beady2() GREENLAND
    && (   (inside(k,o)) ==> (k.AMFB <= o.AMFB) )  // GREENLAND
      ////Beady2()  GREENLAND -
  //    && (   (inside(k,o)) ==> (v.owner >= v.bound >= k.bound >= o.bound))

//    && ( (v.AMFO > v.AMFB  >= k.AMFB) )   //GREENLAND

//  && ( (v.owner >= v.bound >= k.bound) )

    && (k.AMFX <= m.Keys)
    && (k.AMFB <= m.Keys)
//    && (k.bound <= k.owner <= m.Keys)
    && (ownersInKlown(k))  //belt and braces--- currently a requirement!
    && (checkOwnershipOfClone(k,v,this))
    && (checkBoundOfClone(k,v,this))

  //MAPPING - KJXFEARSATAN
    && (mappingOwnersThruKlownKV(k,v,this))

///k.fieldModes == v.fieldModes  ///or shoudl otherwise be compatible

  }

lemma MOVIN_ON_MAP(os: Owner, left : vmap<Object,Object>, right : vmap<Object,Object>)
  requires left.Keys >= right.Keys >= os
  requires forall o <- right.Keys :: left[o] == right[o]
  ensures  (set o <- os :: left[o]) == (set o <- os :: right[o])
{}



  predicate objectInKlown(o : Object) : (rv : bool)
    //o and all its owners etc are the Klown m
    //(doesn't extend to fields)
    //BUT should incorproate ready!! like ObjectReadyInKlon - merge these in
    reads {}
    requires o.Ready()

    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.self  <= m.Keys)    //WEESA DONT WANTA REQUIRE this MASSA
  { o.AMFO <= m.Keys }


  predicate ownersInKlown(o : Object) : (rv : bool)
    //o's owners but not o itself is in the Klon
    //(doesn't extend to fields)
    reads {}

    //critical that thes does *not* catch AMFO or self ...
    requires o.Ready()

    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
  { o.AMFX <= m.Keys }

  predicate objectReadyInKlown(o : Object) : (rv : bool)
    //o and all its owners etc are the Klown m
    //(doesn't extend to fields)
    reads {}

    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.self  <= m.Keys)

    ensures (o.Ready() && rv) ==> objectInKlown(o)
    ensures  o.Ready() ==> (rv == objectInKlown(o))

  {
    o.Ready() && (o.AMFO <= m.Keys)
   }

  predicate ownersReadyInKlown(o : Object) : (rv : bool)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.Ready())

    ensures (o.Ready() && rv) ==> ownersInKlown(o)
    ensures  o.Ready() ==> (rv == ownersInKlown(o))

    reads {}
    {
      o.Ready() && (o.AMFX <= m.Keys)
    }

//29 Oct 2025
//I think the quesiton is whether clowner have tio be in values.
//and ... it doesn't!!!
  // lemma ObjectValuesInKlownToo(o : O bject)
  //   requires objectInKlown(o)
  //   requires CalidOwners()
  //    ensures m[o].AMFO <= m.Values
  //       {
  //           assert o.AMFO <= n.Keys; requires f.AMFO >= t.AMFX   ///classic O-as-D, f->t ==> f inside T.owner
  //           assert forall x <- o.AMFO :: CalidLineKV(x, m[x]);
  //       }


    predicate  apoCalidse()
   //the six requirements of preCalid2 / computeOwnerForClone apocalypse
   reads {}
  {
    && (m.Keys <= oHeap)
    && (m.Values <= hns())
    && (objectReadyInKlown(o))   //this was originally two predicates
    && (HeapOwnersReady())  //whatt bno value owners ready??
    && (c_amfx <= oHeap)
  }

//{:timeLimit 60}
  function {:isolate_assertions} {:timeLimit 30} CalidKV(k : Object, v : Object) : (mK : Klon)
    //givne a Calid Klon, add in k:=v to the mapping and get a  Calid result.
    //the heart of the heart of the klon

    requires CKV_preconditions(k,v)
    requires CalidLineKV(k,v)    requires CLKV: CalidLineKV(k,v)

     ensures mK == klonKV(this, k, v)
     ensures mK.from(this)
     ensures mK.HeapContextReady()
     ensures mK.ValuesContextReady()
     ensures mK.m.Keys <= mK.oHeap
     // ensures  unchanged(oHeap`fieldModes)
     // ensures  unchanged(m.Values`fieldModes)
     ensures forall z <- m.Keys :: m[z].fieldModes == mK.m[z].fieldModes

     ensures mK.Calid()
     ensures mK.SuperCalidFragilistic()

     reads oHeap, m.Values, k, v
     reads m.Keys, m.Values
  {
       assert CKV_preconditions(k,v);
    // assert CKV_preconditions(k,v);
    //
    //----------------------------------------------------------------------
    //
    // assert SuperCalidFragilistic();
    // assert k.Ready();
    // assert ownersInKlown(k);
    // assert o.Ready();
    // assert objectInKlown(o);
    // assert CalidCanKey(k);
    // assert k !in m.Keys;
    // assert v !in m.Values;
    // assert HeapContextReady();
    // assert ValuesContextReady();
    // assert Calid();
    // assert k in oHeap;
    // assert (v.Ready() && v.Context(hns({v})));
    // assert this.m.Keys <= this.oHeap;
    // assert klonVMapOK(m);
    // assert klonCanKV(this, k, v);
    // assert CalidLineKV(k,v);
    //
    //
    //     requires SuperCalidFragilistic()
    //
    //     requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    //     requires ownersInKlown(k)   //be nice to get rid of this...
    //     requires o.Ready() //&& o.Valid()
    //     requires objectInKlown(o)
    //
    //     requires CalidCanKey(k)
    //
    //     requires k !in m.Keys
    //     requires v !in m.Values
    //
    //     // requires HeapContextReady()
    //     // requires ValuesContextReady()
    //     // requires Calid()
    //
    //     requires k in oHeap
    //     requires (v.Ready() && v.Context(hns({v})))
    //
    //     requires this.m.Keys <= this.oHeap
    //
    //     requires klonVMapOK(m)
    //     requires klonCanKV(this, k, v)
    //
    //     requires CalidLineKV(k,v)
    //
    //----------------------------------------------------------------------
//
//
//     assert preCalid();
//     assert preCalid2();
//     assert && (c_amfx <= oHeap);
//
//     assert HeapContextReady();
//
//     assert forall x <- m.Keys :: (x.Ready() && objectInKlown(x))
//       by { assert SuperCalidFragilistic(); }        // SuperCalidGetsAllOwnersReadyInKlown();\\
//
//     assert ValuesContextReady();
//     assert AllLinesCalid();
//
//
//     //use kalidLineKV rather than checkOwnershipOfClone(k, m[k], this);
//     //assert forall k <- m.Keys :: checkOwnershipOfClone(k, m[k], this);
//
  (
     var mK := klonKV(this, k, v);
     assert mK.m[k] == v;

     assert mK.m.Keys            == m.Keys+{k};
     assert mKmVmVv: mK.m.Values == m.Values+{v};
     assert          mK.m.Values == m.Values+{v};
     assert mK.from(this);

     assert hns({v}) == mK.hns({});
     assert v.Context(hns({v})) by { assert CKV_preconditions(k,v); }
     assert v.Context(mK.hns({}));

     forall x <- mK.m.Keys ensures {:contradiction} (mK.m.Keys <= oHeap) //by
     {
       if (x == k) { assert {:contradiction} k in oHeap; }
       if (x != k) { assert {:contradiction} x in oHeap; }
       assert {:contradiction} x in oHeap;
     }

     forall y <- mK.m.Values ensures (y.Context(mK.hns())) //by
     {
       if (y == v) { assert v.Context(mK.hns()); }
       if (y != v) {
         assert  {:contradiction} y in m.Values;
         assert  {:contradiction} y.Context(hns());
                                  y.WiderContext(hns(), mK.hns());
         assert  {:contradiction} y.Context(mK.hns()); }

     }

    //  forall y <- mK.m.Values ensures (y.Ready() && y.Valid() ) //by
    //  {
    //    if (y == v) { assert (v.Ready() && v.Valid()); }
    //    if (y != v) {
    //      assert  {:contradiction} y in mK.m.Values;
    //      assert  {:contradiction}  (y.Ready() && y.Valid()); }
    //  }



     assert {:contradiction} mK.HeapContextReady();
     assert ValuesContextReady();

     assert  forall x <- m.Values :: x.OwnersWithin(hns());
         // assert  (forall x <- m.Values :: (x.Ready() && x.Valid() && x.Context(hns())));

     assert v in mK.m.Values;
    //  assert v.Context(hns({v})) by { assert CKV_preconditions(k,v); }
     assert v.Context(mK.hns({}));
     assert mK.m.Values == m.Values + {v};

     assert forall x  : Object <-    m.Values + {v} :: x.OwnersWithin(hns({v}));
     assert forall x  : Object <- mK.m.Values       :: x.OwnersWithin(mK.hns());
//     assert mK.ValuesContextReady();

//      assert objectInKlown(o);
//      assert mK.objectInKlown(o);
//
//      assert CalidCanKey(k); //pro you're like to want to walk.
//      // ^-- no idea what that comment means but…
//   //seems a but fyckiung late for this level of quibling now!
// //     assert forall k <- m.Keys :: CalidLineKV(k,v);
//
//      assert mK.m.Keys == m.Keys + {k};
//     //
//     //  assert forall k <- mK.m.Keys :: mK.objectInKlown(k);
//

     assert CKV_preconditions(k,v);
     assert AllLinesCalid();
     assert forall x <- m.Keys :: CalidLineKV(x,m[x]);
     assert CalidLineKV(k,v); //GNT by { reveal CLKV; }
     assert mK.m[k] == v;
     CalidLineKVTo(k,mK.m[k],mK);
     assert mK.CalidLineKV(k,v);
     assert mK.CalidLineKV(k,mK.m[k]);
//
//      forall x <- m.Keys ensures ( this.CalidLineKV(x,m[x]) && ( mK.CalidLineKV(x,m[x])))
// {
//        assert CalidLineKV(x,m[x]);
//         //CUL  CalidLineKVKV(mK,x,this);  //wasKVDFrom!!!!Q
//
//        // assert x in mK.m.Keys;
//        // assert mK.m[x] == m[x];
//        // assert checkOwnershipOfClone(k,v,this);
//        //      CheckOwnershipOfCloneFrom(k, v, mK, this);
//        //      computeOwnerForCloneFrom(k, mK, th is);
//        // CalidlineFrom(mK,x,this);
//        //      assert checkOwnershipOfClone(k,v,mK);
//        assert mK.CalidLineKV(x,m[x]);
//       //
//       //  assert KCLX: mK.CalidLineKV(x,m[x]);
//       //  assert       mK.CalidLineKV(x,m[x]) by { reveal KCLX; }
//       //  assert (this.CalidLineKV(x,m[x]) && mK.CalidLineKV(x,m[x])) by { reveal TCLX, KCLX; }
// }
//
     forall x <- mK.m.Keys ensures mK.CalidLineKV(x,mK.m[x]) //by
     {
//       assert CalidLineKV(x, mK.  m[x]);   //how long?  whu knows
       if (x in m.Keys) {
         assert mK.m[x] == m[x];
         assert this.CalidLineKV(x,m[x]);
         assert x in mK.m.Keys;
         assert CalidLineKV(x,mK.m[x]);   //how long?  whu knows?
         CalidLineKVTo(x,mK.m[x],mK);
         assert mK.CalidLineKV(x,mK.m[x]);
       } else {
         assert x == k;
         assert mK.m[k] == v;
         assert CalidLineKV(k,v); //GNT by { reveal CLKV; } by { reveal CLKV; }
         assert this.CalidLineKV(x,mK.m[x]);
         assert mK.CalidLineKV(x,mK.m[x]);
       }
     }

//      assert (forall k <- mK.m.Keys ::  (k.Ready()));
//      assert (forall k <- mK.m.Keys ::  (mK.objectInKlown(k)));
//      assert (forall k <- mK.m.Keys ::  (var v := mK.m[k]; (v.Ready())));
//      assert (forall k <- mK.m.Keys ::  (var v := mK.m[k]; (v in mK.hns({v}))));
//
//     //  assert mK.thettinGhere();
//     //  assert mK.gettingThere();
//      assert mK.o.Ready();
//      assert mK.objectInKlown(mK.o);
//      assert mK.m.Keys <= mK.oHeap;
//      assert mK.HeapOwnersReady();
//      assert mK.c_amfx <= mK.oHeap;
//
//      assert   (forall k <- mK.m.Keys ::  mK.CalidLineKV(k,m[k]));
//
//      assert mK.AllLinesCalid();
//
//AND THEN IT ALL GETS SIUPER-WEIrD??
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())));
//
//      assert forall o <- mK.m.Values :: o.Ready() ==> ((o.AMFO >= o.AMFB));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())
//                                    && (v.AMFO >= v.AMFB)
//                ));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                 // && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                                    && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (mK.CalidLineKV(k,v))
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                                    && (not(inside(k,o)) ==> (v.AMFB == k.AMFB))
//                                    && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                ));
//
//
//
//      assert (forall k <- mK.m.Keys  ::
//                (var v := mK.m[k];  var o := mK.o;
//                                    && (v.Ready())
//                                    && (v.AMFO >= v.AMFB)
//                                    && (not(inside(k,o)) ==> (k == mK.m[k] == v))
//                 // && (not(inside(k,o)) ==> (v.AMFO >= v.AMFB == k.AMFB))
//                 // && (   (inside(k,o)) ==> (v.AMFO >= v.AMFB >= k.AMFB >= o.AMFB))   ///from CalidLineKV
//                 // && (   (inside(k,o)) ==> (v.`owner >= v.bound >= k.bound >= o.bound) )
//                 // && (  mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB  )  /// current - early Jun 2025 defiunition from Calid() which soiuld be refacgored
//                ));
//
//      // ///////////////////////////////////////////////////////////////////////////
//
//      // ///////////////////////////////////////////////////////////////////////////
//
//      assert  (forall k <- mK.m.Keys   :: mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB) ;
//
// ///assume  (forall k <- mK.m.Keys   :: mK.m[k].AMFO >= mK.m[k].AMFB >= k.AMFB) ;   //WHAT THE FUCK IS THIS DOING HERE
//
//      assert mK.HeapContextReady();
//      assert mK.ValuesContextReady();
//      // ///////////////////////////////////////////////////////////////////////////
//      //tryna get calid
//      assert (mK.Calid())
//      by {
//        assert      && mK.preCalid()
//                    && mK.preCalid2()
//
//                    //calidObjects - mostly about oHeap and ns and stuff
//                    && (mK.m.Keys <= mK.oHeap)
//                    && (forall k <- mK.m.Keys :: (k.Ready() && k.Valid()))
//
//                    //this recapitulates ValuesContextReady() but putting it here lets things work
//                    && (forall v <- mK.m.Values :: (v.Ready() && v.Valid()))
//
//                    //the pivot object "o" being cloned
//                    // && (o.Ready() && o.Valid() && o.Context(oHeap) && objectInKlown(o))
//                    && (mK.o.Ready() && mK.o.Valid() && mK.o.Context(mK.oHeap) && mK.objectInKlown(mK.o))
//
//                    && (forall k <- mK.m.Keys   :: mK.m[k].AMFO  >= mK.m[k].AMFB  >= k.AMFB)
// //wont veruify     && (forall k <- mK.m.Keys   :: mK.m[k].AMFO  >= mK.m[k].AMFB  >= mK.o.AMFB >= k.AMFB)    ///change made then backed out  10JKul 2025 - why wo why oh why ?
// //  WRONG                 && (forall k <- mK.m.Keys   :: mK.m[k].owner >= mK.m[k].bound >= k.bound)
//
//                    && (forall k <- mK.m.Keys   :: (not(inside(k,mK.o)) ==> (mK.m[k] == k)))
//                    && (forall k <- mK.m.Keys   :: (   (inside(k,mK.o)) ==> (mK.m[k] !in mK.oHeap)))
//                    //
//                    //calidSheep - su WRONGbsumed?
//                    //
//                    //see rant aove...
//                    //
//                    //&& (forall k <- mK.m.Keys :: k.fieldModes == mK.m[k].fieldModes)
//                    //
//                    //
//
//                    //KlonVMqpOK(k, context)
//                    && (forall k <- mK.m.Keys :: k.AMFO <= mK.m.Keys)
//                    && (forall k <- mK.m.Keys :: k.AMFB <= mK.m.Keys)
// //                   && (forall k <- mK.m.Keys :: k.bound <= k.owner <= mK.m.Keys)
//                    // && (forall k <- m.Keys :: //;this is s"gettingThere" so why twice?
//                    //      (var v := m[k];
//                    //         && (k.Ready())
//                    //         && (objectInKlown(k))
//                    //         && (v.Ready())
//                    //         && (v in hns())))
//
//                    && (&& (mK.HeapOwnersReady())
//                        && (mK.ValuesOwnersReady())
//                        && (mK.gettingThere())
//                        && (mK.AllLinesCalid()));
//      } //tryna
//
     assert mK.Calid();
     assert mK.SuperCalidFragilistic();
     mK
  )

}
//end CalidKV




  ghost predicate {:isolate_assertions} CKV_preconditions(k : Object, v : Object)
    //attempt to capture the common preconditions for CalidKV

    reads oHeap, m.Values, k, v
    reads m.Keys, m.Values
  {
    && SuperCalidFragilistic()

    && k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    && ownersInKlown(k)   //be nice to get rid of this...
    && o.Ready() //&& o.Valid()
    && objectInKlown(o)

    && CalidCanKey(k)

    && k !in m.Keys
    && v !in m.Values

    // && HeapContextReady()
    // && ValuesContextReady()
    // && Calid()

    && k in oHeap
    && (v.Ready() && v.Valid() && v.Context(hns({v})))

    && this.m.Keys <= this.oHeap

    && klonVMapOK(m)
    && klonCanKV(this, k, v)

    && CalidLineKV(k,v)
  }







  predicate {:isolate_assertions} CalidCanKey(k : Object)
    //conditions an object to be added as a Key into the Klon map
    //  note this doesn't seem to deal with ougoing field values, but that will get
    //  caught eventually via  HeapContextReady() &  ValueContextReady()
    //doesn't seem to require Calid????
    //isn't this more eor less ownersInKlown>?>
    //izn't thgs being replaced ie. tis dead
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    //requires ownersInKlown(k) ///hmm, req or jsut in body?  Just In BODY!!! 31 Aug 2025

    //pretty sure I want thewe two here to match CalidCanValue
    requires o.Ready() //&& o.Valid()
//    requires objectInKlown(o)  //THAT is clearly FUCKEDy

    reads {}
  {
    && (k in oHeap)
    && (k !in m.Keys)
    && ownersInKlown(k)
  }


  predicate {:isolate_assertions} CalidCanValue(k : Object, v : Object)
    //conditions an object to be added as a Value into the Klon map
    // dunno if I really need this but wrote it anyway as an extenion of CanCalidKey above
    //  note this doesn't seem to deal with ougoing field values, but that will get
    //  caught eventually via  HeapContextReady() &  ValueContextReady()
    //doesn't seem to require Calid????
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    requires v.Ready() //&& v.Valid()
    requires ownersInKlown(k)
    requires o.Ready() //&& o.Valid()
    requires objectInKlown(o)

    requires CalidCanKey(k)

    //the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires k.owner <= m.Keys <= oHeap
    requires m.Values <= hns()
    requires o.Ready()
    requires objectInKlown(o)
    requires HeapOwnersReady()
    requires c_amfx <= oHeap

    reads oHeap, m.Values
  {
    && (v !in m.Values)
    && (v.Ready()) //&& v.Valid() && v.Context(hns({v})))
    && (CalidLineKV(k,v)) //will this do?
  }



  ghost predicate {:isolate_assertions} calidCanKV(k : Object, v : Object)
    requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
    requires v.Ready() //&& v.Valid()
    requires ownersInKlown(k)
    requires o.Ready() //&& o.Valid()
    requires objectInKlown(o)


    reads oHeap, m.Values

    //     reads oHeap`fields, oHeap`fieldModes
    //     reads m.Keys`fields, m.Keys`fieldModes
    //     reads m.Values`fields, m.Values`fieldModes
    //     reads o`fields, o`fieldModes
    //     reads m.Values, oHeap
    //
    //     reads k`fields, k`fieldModes
    //     reads v`fields, v`fieldModes
    //
    //     reads k`fieldModes, k`fields, m.Values`fieldModes, m.Values`fields, o`fields, o`fieldModes

  {
    && SuperCalidFragilistic()
    // && HeapContextReady()
    // && ValuesContextReady()
    // && Calid()
    && CalidCanKey(k)
    && CalidCanValue(k,v)
  }




  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]




  lemma {:isolate_assertions} CalidLineKVReflexive(k : Object, v : Object)
    //speciefic
    requires not(inside(k,o))
    requires k == v

    //generic?
    requires k.Ready()
    requires ownersInKlown(k)
    requires v.Ready()
    requires o.Ready()
    requires objectInKlown(o)

    //the six requirements of preCalid2 / computeOwnerForClone apocalypse
    requires apoCalidse()

    requires k in oHeap
    requires forall x <- m.Keys :: outside(x,o) ==> (m[x] == x)
//    requires forall x <- k.AMFO :: (m[o] == o)

    ensures  checkOwnershipOfClone(k, v, this)
    ensures  checkBoundOfClone(k, v, this)
    ensures  mappingOwnersThruKlownKV(k,v,this)
    ensures  CalidLineKV(k, v)
  {

    assert forall x <- m.Keys :: outside(x,o) ==> (m[x] == x);

    assert not(inside(k,o));
    assert k == v;
    assert k != o;
    assert k.AMFO == v.AMFO;
    assert checkOwnershipOfClone(k, v, this);
    assert k.owner == v.owner;
    assert k.bound == v.bound;

    k.ExtraReady();

    assert m.Keys >= k.AMFX >= k.AMFB >= k.bound;
    assert m.Keys >= k.AMFX >= k.owner;

    assert outside(k,o);
    //    ExternalOwnersAreOutside(k,o);
    assert forall oo <- k.AMFX  :: outside(oo, o);
    assert forall  x <- m.Keys  :: outside(x, o) ==> (m[x] == x);
    assert forall oo <- k.AMFX  :: m[oo] == oo;
    assert forall oo <- k.owner :: m[oo] == oo;

    assert forall oo <- k.AMFB  :: outside(oo, o);
    assert forall  x <- m.Keys  :: outside(x, o) ==> (m[x] == x);
    assert forall oo <- k.AMFB  :: m[oo] == oo;
    assert forall oo <- k.bound :: m[oo] == oo;

assert v == k;
assert v.bound == k.bound;

    // assert (v.bound == mapThruKlon(k.bound, this));
    // assert (v.owner == mapThruKlon(k.owner, this));

    assert mappingOwnersThruKlownKV(k,v,this);

  }

  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

///OwnersLine version


//Need to WORK The FUCK out wwhat to do about THIS
  ghost predicate {:isolate_assertions}   preOwners() : (r : bool)
    reads oHeap, m.Values
  {
    // && HeapOwnersReady()    ///hmm
    // && ValuesOwnersReady()
    && (o.Ready() && (o in oHeap))
    && (objectInKlown(o))  //KJXFUCK  do i want this in here? really?   ///Can U do without it??
    && (o.AMFX == o_amfx)
    && (flatten(clbound) >= o.AMFB)
    && (o.AMFO == o_amfx+{o})
    && (c_amfx >= flatten(clbound) >= flatten(o.bound))
  }



  ghost predicate {:isolate_assertions} preOwners2() : (r : bool)
    reads {}
  {
    && (c_amfx <= oHeap) //should goto precalid1??
    && ((o in m.Keys) ==> (
        var c := m[o]; //WE HAS KLONE
        && (c_amfx  == c.AMFX)
        && (clowner == c.owner)
        && (clbound == c.bound)
       ))
  }

  ghost predicate {:isolate_assertions} SuperCalidOwners() : (r : bool)
    reads oHeap, m.Values
  {
    // && HeapOwnersReady()
    // && ValuesOwnersReady()
    && CalidOwners()
  }

  ghost predicate {:isolate_assertions} CalidOwners() : (r : bool)
    // requires  HeapOwnersReady()
    // requires  ValuesOwnersReady()
    reads oHeap, m.Values
  {
        // && HeapOwnersReady()
        // && ValuesOwnersReady()
    && apoCalidse()
    && preOwners()
    && preOwners2()
    && (m.Keys <= oHeap)
    && objectInKlown(o)
    && (forall k <- m.Keys :: OwnersLineKV(k, m[k]))
  }

//does this mean it MUST be in or it CAN be in
//with objectInKnown(k) this says it MUST ne in,. doesn;t it?
//FUCK FUCK FUCK compare CalidLineKV!!!
//ditto (v in hns({v}))) from earlier plain (v in hns())
 predicate {:isolate_assertions} OwnersLineKV(k : Object, v : Object)
    requires apoCalidse()
    reads oHeap, m.Values
  {
//  && (k.Ready() && (objectInKlown(k)) && k in oHeap)   28 Oct 2025
    && (k.Ready() && (ownersInKlown(k)) && k in oHeap)
    && (v.Ready() && (v in hns({v})))

 //   && (v.AMFO  >= v.AMFB  >= k.AMFB)  //GREENLAND
    && (   (inside(k,o)) ==> (k.AMFB  <= o.AMFB))  //GREENLAND

    && (not(inside(k,o)) ==> (v == k))
    && (   (inside(k,o)) ==> ((v !in oHeap)) )

  //MAPPING - KJXFEARSATAN
    && (mappingOwnersThruKlownKV(k,v,this))
  }


//FROM DAHLIA

lemma {:isolate_assertions} directOwnerInKlownIsEnough(o : Object)
  requires o.Ready()
  requires SuperCalidFragilistic()
  requires o.owner <= m.Keys //note just direct owner
   ensures ownersInKlown(o)
{
  assert forall x <- m.Keys :: objectInKlown(x);
  assert flatten(o.owner) == o.AMFX <= m.Keys;
  assert forall oo <- o.owner :: o.AMFX <= m.Keys;
  assert ownersInKlown(o);
}





  lemma {:isolate_assertions}  FieldFromHeapContext(o : Object, n : string, v : Object)
    //assert a bunch of stuff about a field - could become a function later
    requires HeapContextReady()
    requires o in oHeap
    requires n in o.fields.Keys
    requires v == o.fields[n]

    ensures  v in o.fields.Values
    ensures  v.Ready()
    ensures  v.Valid()
    ensures  v.Context(oHeap)
    ensures  v in oHeap
  {
    assert o.Ready();
    assert o.Valid();
    FieldInFields(o,n,v);
    assert v in o.fields.Values;
    assert o.Context(oHeap);
    assert o.fields.Values <= oHeap;
    assert v in oHeap;
    assert HeapContextReady();
    assert forall x <- oHeap :: (x.Ready() && x.Valid() && x.Context(oHeap));
    assert v.Ready() && v.Valid() && v.Context(oHeap);
  }



}//end datatype Klon


lemma {:isolate_assertions} HNSV(v : Object, m : Klon)
  ensures v in m.hns({v})
  {}



//timelimit 60 BUT IT WORDS - 2 Jan 2026
//but it doesn't 5 Mar 2026
lemma {:isolate_assertions}  {:timeLimit 60} BROKENCalidKVCalid(k : Object, v : Object, m0 : Klon, m1 : Klon)
  //if m0.klonKLV(kv == m1,  and m0 is calid, can m1 pretty please be calid()?
    requires m0.CKV_preconditions(k,v)
    requires m0.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m0.ownersInKlown(k)
    requires v.Ready()
    requires m0.Calid()
    requires m0.CalidLineKV(k,v)
    requires k !in m0.m.Keys
    requires v !in m0.m.Values
    requires v in  m0.hns({v})
    requires m1.from(m0)
    requires m1 == klonKV(m0,k,v)
     ensures m1.m == vmapKV(m0.m,k,v)
     ensures k in m1.m.Keys
     ensures m1.m.Keys   == m0.m.Keys + {k}
     ensures m1.m.Values == m0.m.Values + {v}
     ensures m1.m[k] == v
     ensures m1.objectInKlown(k)
     ensures m1.Calid()
    {
      assert m0.AllLinesCalid();
      assert m0.CalidLineKV(k,v);
        assert m0.gettingThere();
      assert && (k.Ready())
               && (m0.ownersInKlown(k))
               && (v.Ready())
               && (v in m0.hns({v}));

      assert (k.Ready());
      assert (m1.ownersInKlown(k));
      assert (v.Ready());
      assert (v in m1.hns({v}));

      assert k in m1.m.Keys;
      assert m1.objectInKlown(k);

      assert m1.m.Keys == m0.m.Keys + {k};

      forall j <- m1.m.Keys ensures (
                              && (j.Ready())
                              && (m1.objectInKlown(j))
                              && (m1.m[j].Ready())
                              && (m1.m[j] in m1.hns())
                              && (m1.CalidLineKV(j,m1.m[j]))
                                   )
        {
         if (j == k)
           { assert m0.CalidLineKV(j,v);
             m0.CalidLineKVTo(j,v,m1);
             assert m1.CalidLineKV(j,v);
             assert m1.m[j] == v;
             assert m1.CalidLineKV(j,m1.m[j]);
           } else {
             assert j in m0.m.Keys;
             assert m0.m[j] == m1.m[j];
             assert m0.AllLinesCalid();
             assert m0.CalidLineKV(j,m0.m[j]);
             m0.CalidLineKVTo(j,m1.m[j],m1);
             assert m1.CalidLineKV(j,m1.m[j]);
           }
        }

        assert m1.gettingThere();

        assert m0.ValuesContextReady();
        assert m1.m.Values == m0.m.Values + {v};
        assert m1.hns() == m0.hns({v});
          assert v.Context(m0.hns({v}));
        assert v.Context(m1.hns());
//      assert forall x <- m0.m.Values :: x.Context(m0.hns()) && x.Context(m1.hns());
        forall  x <- m0.m.Values ensures (x.Context(m1.hns())) //by
          {
            assert x.Context(m0.hns());
            x.WiderContext(m0.hns(), m1.hns());
            assert x.Context(m1.hns());
          }
        assert forall x <- m1.m.Values ::
           if (x in m0.m.Values)
              then (x.Context(m1.hns()))
              else ((x == v) && (x.Context(m1.hns())));
        assert m1.ValuesContextReady();
  }



lemma {:isolate_assertions} {:timeLimit 0} BETTERCalidKVCalid(k : Object, v : Object, m0 : Klon, m1 : Klon)
  //if m0.klonKLV(kv == m1,  and m0 is calid, can m1 pretty please be calid()?
    requires m0.CKV_preconditions(k,v)
//requires HighCalidFragilistic(m0)
    requires m0.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m0.ownersInKlown(k)
    requires v.Ready()
    requires m0.Calid()
    requires m0.CalidLineKV(k,v)
    requires k !in m0.m.Keys
    requires v !in m0.m.Values
    requires v in  m0.hns({v})
    requires m1.from(m0)
    requires m1 == klonKV(m0,k,v)
     ensures m1.m == vmapKV(m0.m,k,v)
     ensures k in m1.m.Keys
     ensures m1.m.Keys   == m0.m.Keys + {k}
     ensures m1.m.Values == m0.m.Values + {v}
     ensures m1.m[k] == v
     ensures m1.objectInKlown(k)
     ensures m1.Calid()
//ensures HighCalidFragilistic(m1)

{
    assert m1 == m0.CalidKV(k,v);
    assert m1.Calid();
    //assume m1.Calid();  //still crashes
}



  lemma {:isolate_assertions}  FieldInFields(o : Object, n : string, v : Object)
    requires o.Ready()
    requires o.Valid()
    requires n in o.fields.Keys
    requires v == o.fields[n]
    ensures  v in o.fields.Values
  {}


  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

lemma {:isolate_assertions} OwnersFromCalid(m : Klon)
  requires m.SuperCalidFragilistic()
   ensures m.SuperCalidOwners()
   ensures m.CalidOwners()
{
    assert m.preOwners();
    assert m.preOwners2();
    assert (m.m.Keys <= m.oHeap);
    assert m.objectInKlown(m.o);
    assert m.AllLinesCalid();
    assert (forall k <- m.m.Keys :: m.OwnersLineKV(k, m.m[k]));
}


lemma {:isolate_assertions} {:timeLimit 40} CalidFromOwners(m : Klon)
  requires m.CalidOwners()
  requires m.HeapContextReady()
  requires m.ValuesContextReady()
   ensures m.SuperCalidFragilistic()
{
    assert (forall k <- m.m.Keys :: m.OwnersLineKV(k, m.m[k]));
    assert m.preOwners();
    assert m.preOwners2();
    assert (m.m.Keys <= m.oHeap);
    assert m.objectInKlown(m.o);
    assert forall k <- m.m.Keys :: (k.AMFX <= m.m.Keys) && (k.AMFB <= m.m.Keys);

//                assert forall k <- m.m.Keys :: (

  forall k <- m.m.Keys ensures (m.CalidLineKV(k,m.m[k]))
    //by
            {
                      //body of CalidLIneKV as of 25 Jan 2026
                      var v := m.m[k];
 assert               && (k in m.oHeap)
                      && (not(inside(k,m.o)) ==> (v == k))
                      && (   (inside(k,m.o)) ==> (v !in m.oHeap))
                  //    && (   (inside(k,o)) ==> (v.AMFO  >= v.AMFB >= k.AMFB))  //Beady2() GREENLAND
                      && (   (inside(k,m.o)) ==> (k.AMFB <= m.o.AMFB) )  // GREENLAND Beady2()  GREENLAND -
                      && (k.AMFX <= m.m.Keys)
                      && (k.AMFB <= m.m.Keys)
                      && (m.ownersInKlown(k))  //belt and braces--- currently a requirement!
                      && (checkOwnershipOfClone(k,v, m))
                      && (checkBoundOfClone(k,v, m))
                      && (mappingOwnersThruKlownKV(k,v, m))
                   ;
    assert m.AllLinesCalid();
     }
}

lemma {:isolate_assertions} OwnersLineFromCalidLine(k : Object, v : Object, m : Klon)
    requires m.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires m.ownersInKlown(k)
    requires v.Ready()
    requires v in m.hns({v})
    requires m.CalidLineKV(k,v)
     ensures m.OwnersLineKV(k,v)
    {}

lemma {:isolate_assertions} KindaStupid(k : Object, v : Object, m : Klon)
 //if we're OwnersCalid, and k is in m, then we get stuff
  requires m.CalidOwners()
  requires m.HeapOwnersReady() //grrr
  requires k.Ready() && m.objectInKlown(k)
  requires v.Ready() && m.objectInKlown(v)
  requires m.m[k] == v
   ensures m.OwnersLineKV(k,v)
   ensures mapThruKlon({k},m) == {v}
{
  assert  v  == m.m[k];
  assert {v} == {m.m[k]};
  assert {v} == set o <- {k} :: m.m[o];
  assert {v} == mapThruKlon({k},m);
}


lemma  {:isolate_assertions} {:timeLimit 15} MapThruKlonOutsideOwner(k : Object, m : Klon)
  requires m.CalidOwners()
  requires m.HeapOwnersReady() //grrr
  requires k.Ready() && m.objectInKlown(k)
  requires outside(k, m.o)
   ensures mapThruKlon(k.owner, m) == k.owner
   ensures mapThruKlon(k.bound, m) == k.bound
{
  assert outside(k, m.o);
//  assert forall oo <- k.owner ::  inside(m.o, oo);
  assert forall oo <- m.m.Keys | outside(oo, m.o) :: m.m[oo] == oo;
  assert forall oo <- k.owner  | outside(oo, m.o) :: m.m[oo] == oo;
  assert forall oo <- k.owner  :: outside(oo, m.o);
  assert forall oo <- k.owner  :: (m.m[oo] == oo);
  assert (set o <- k.owner :: m.m[o]) == k.owner;
  assert mapThruKlon(k.owner, m) == k.owner;

  assert forall oo <- k.bound  | outside(oo, m.o) :: m.m[oo] == oo;
  assert forall oo <- k.bound  :: outside(oo, m.o);
  assert forall oo <- k.bound  :: (m.m[oo] == oo);
  assert (set o <- k.bound :: m.m[o]) == k.bound;
  assert mapThruKlon(k.bound, m) == k.bound;
}

lemma {:isolate_assertions} NotFromAJedi(k : Object, v : Object, m : Klon)
  requires m.CalidOwners()
  requires m.HeapOwnersReady() //grrr
  requires k.Ready() && m.objectInKlown(k)
  requires v.Ready() && m.objectInKlown(v)
  requires m.m[k] == v

  requires mapThruKlon(k.owner, m) == v.owner
  requires mapThruKlon(k.bound, m) == v.bound

   ensures mapBackKlon(v.owner, m) == k.owner
   ensures mapBackKlon(v.bound, m) == k.bound

  {
    ThereAndKlonAgain1(k.owner, m, v.owner);
    ThereAndKlonAgain1(k.bound, m, v.bound);

   }


lemma {:isolate_assertions} OnlyAMasterOfEvilDarth(k : Object, v : Object, m : Klon)
  //showing how this was previous fucked up
//BUT YOU FUCKED IT UP -- IT CAN'T!!!!!!!!
//NOT WHEN k == mn.o at least?
  requires m.apoCalidse()
  requires m.CalidOwners()
  requires m.HeapOwnersReady() //grrr
  requires k.Ready() && m.objectInKlown(k)
  requires v.Ready() && m.objectInKlown(v) //WTF?? - this FUCKS EVERYTHING, only vadlid if k outside m.o
  requires m.m[k] == v
   ensures m.OwnersLineKV(k,v)
   ensures mapThruKlon({k},m) == {v}

   ensures outside(k, m.o)  //WHOOPS APOCALYPSE!
   {}

lemma {:isolate_assertions} OnlyNowAtTheEndDoYouUnderstand(k : Object, v : Object, m : Klon)
  //wpeoves mapTHruKlon works in all cases of original being inside,outside, eq m.o
//BUT YOU FUCKED IT UP -- IT CAN'T!!!!!!!!
//NOT WHEN k == mn.o at least? --
  requires outside(k, m.o)
  requires m.apoCalidse()
  requires m.CalidOwners()
  requires m.HeapOwnersReady() //grrr
  requires k.Ready() && m.objectInKlown(k)
  requires v.Ready() //&& m.objectInKlown(v) //WTF?? - this FUCKS EVERYTHING, only vadlid if k outside m.o
  requires m.m[k] == v
   ensures m.OwnersLineKV(k,v)
   ensures mapThruKlon({k},m) == {v}
   ensures mapThruKlon(k.owner, m) == v.owner
   ensures mapThruKlon(k.bound, m) == v.bound
  {
    assert m.CalidOwners();
    assert m.apoCalidse();
    assert(forall z <- m.m.Keys :: m. OwnersLineKV(z, m.m[z]));
    assert m.OwnersLineKV(k,v);
    assert mappingOwnersThruKlownKV(k, v, m);

    assert (k == m.o) || (outside(k, m.o)) || strictlyInside(k, m.o);

    assert (k == m.o)  ==>  not((outside(k, m.o)) || strictlyInside(k, m.o));
    assert (outside(k, m.o))  ==>  not((k == m.o) || strictlyInside(k, m.o));
    assert (strictlyInside(k, m.o)) ==> not((outside(k, m.o)) || (k == m.o));

    if (k == m.o) {
        assert m.m[k] == m.m[m.o] == v;
        assert (v.owner == m.clowner);
        assert (v.bound == m.clbound);
        assert m.m[k].owner == v.owner;
        assert m.m[k].bound == v.bound;

        // assert mappingOWNRsThruKlownKV(k.owner, v.owner, m);
        // assert mappingOWNRsThruKlownKV(k.bound, v.bound, m);
        assert mapThruKlon(k.owner, m) == v.owner;
        assert mapThruKlon(k.bound, m) == v.bound;
    }

    if (outside(k, m.o)) {
        assert m.m[k] == v;
        assert k == v;
        assert m.m[k] == k;
        assert k.owner == m.m[k].owner == v.owner;
        assert k.bound == m.m[k].bound == v.bound;

        assert not( mappingOWNRsThruKlownKV(k.owner, v.owner, m) );
        assert not( mappingOWNRsThruKlownKV(k.bound, v.bound, m) );

        MapThruKlonOutsideOwner(k, m);
        assert  mapThruKlon(k.owner, m) == k.owner == v.owner;
        assert  mapThruKlon(k.bound, m) == k.bound == v.bound;
    }

    if (strictlyInside(k, m.o)) {
        assert k != v;
        assert m.m[k] == v;
        assert m.m[k].owner == v.owner;
        assert m.m[k].bound == v.bound;

        assert mappingOWNRsThruKlownKV(k.owner, v.owner, m);
        assert mappingOWNRsThruKlownKV(k.bound, v.bound, m);
        assert mapThruKlon(k.owner, m) == v.owner;
        assert mapThruKlon(k.bound, m) == v.bound;
    }

    assert mapThruKlon(k.owner, m) == v.owner;
    assert mapThruKlon(k.bound, m) == v.bound;

    KindaStupid(k,v,m);
    assert mapThruKlon({k},m) == {v};
}






  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]



lemma {:isolate_assertions} {:timeLimit 15} ClownershipReflexive(k : Object, v : Object, m : Klon)

  requires k == v
  requires outside(k,m.o)

  //   requires m.HeapContextReady()
  //   requires m.ValuesContextReady()
  //   requires m.preCalid()
  //   requires m.preCalid2()
  //
  //   requires k.Ready()
  //   requires m.ownersInKlown(k)
  //   requires v.Ready()
  //
  //   requires m.o.Ready()
  //   requires m.objectInKlown(m.o)

  requires k.Ready()
  requires m.ownersInKlown(k)
  requires v.Ready()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)

  //the six requirements of preCalid2 / computeOwnerForClone apocalypse
  requires k.owner <= m.m.Keys <= m.oHeap
  requires m.m.Values <= m.hns()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap


  // //are these two WRONG or WHAT?
  //   requires k !in m.m.Keys
  //   requires v !in m.m.Values

  //note that I don't require Calid.
  //cos I can't cos I'm tryint to establish that..
  //could use CalidLineKV I guess?

  ensures  checkOwnershipOfClone(k, v, m)
  // ensures  m.calidCanKV(k,v)  --wants CALID but can't haveit...
{
  assert (k.AMFB  <= m.m.Keys);
  assert (k.AMFX  <= m.m.Keys);
  assert (k.bound <= m.m.Keys);
  assert (k.owner <= m.m.Keys);

  if (k == m.o)
  {
    assert                  k == m.o;
    assert {:contradiction} outside(k,m.o);
    assert {:contradiction} false;
    // assert v == m.o == k;
    // assert m.o.owner == v.owner == k.owner; // == m.clowner
    // assert m.o.bound == v.bound == k.bound; // == m.clbound
    // assert m.o.AMFO ==  k.AMFO == v.AMFO;   // m.c_amfx + {m.o} ==
    // assert checkOwnershipOfClone(k, v, m);
  }
  else
  {
    assert k != m.o;
    assert outside(k, m.o);
    assert v.owner == k.owner;
    //        assert computeOwnerForClone(k.owner, m) == computeOwnerForClone(v.owner, m);
    //        assert computeOwnerForClone(k.owner, m) == v.owner;

    //      assert v.AMFB >= m.o.AMFB;  ///alson cannot be possible...
    //    assert flatten(k.bound) >= flatten(m.clbound);  //this CANT BE POSSIBLE cos k could be outside the pivot
    assert checkOwnershipOfClone(k, v, m);

  }
}







lemma ONE_OR_TOTHER<T>(a : T, b : set<T>, c : set<T>)
  requires a !in b
  requires c ==  b + {a}

  ensures a in c
  ensures {a} <= c
  ensures b <= c

  ensures forall y <- c :: (y == a)  ==> (y !in b)
  ensures forall y <- c :: (y == a) <==  (y !in b)
  ensures forall y <- c :: (y == a) <==> (y !in b)
  ensures forall y <- c :: (y == a) <==  (y !in b)

  ensures forall y <- c :: (y != a)  ==> (y in b)
  ensures forall y <- c :: (y != a) <==  (y in b)
  ensures forall y <- c :: (y != a) <==> (y in b)
  ensures forall y <- c :: (y != a) <==  (y in b)

  ensures forall y <- c :: (y == a)  !=  (y in b)
 {}




//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

  function {:isolate_assertions} {:timeLimit 60} klonKV(m' : Klon, k : Object, v : Object) : (m : Klon)   //TIME-3-OCT
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires klonVMapOK(m'.m)
  requires klonCanKV(m', k, v)

  ensures klonVMapOK(m.m)
  ensures klonCanKV(m', k, v)
//  ensures forall x <- m.m.Keys, y <- m.m.Values :: (y == v) ==> (x == k)
  ensures m == m'.(m:=m'.m[k:=v])
  ensures m.from(m')
  ensures m.m.Keys   == m'.m.Keys+{k}
  ensures m.m.Values == m'.m.Values+{v}
  ensures m.o        == m'.o
  ensures m.oHeap    == m'.oHeap
  ensures forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes)

  reads k, v, m'.oHeap, m'.hns(), m'.m.Keys, m'.m.Values

  //   reads k`fields, k`fieldModes
  //   reads v`fields, v`fieldModes
  //
  //   reads m'.oHeap`fields, m'.oHeap`fieldModes
  //   reads m'.ns()`fields,  m'.ns()`fieldModes
    reads m'.m.Keys`fields, m'.m.Keys`fieldModes
    reads m'.m.Values`fields, m'.m.Values`fieldModes

  //reads  m'.m.Values, m'.oHeap  //for ValuesContextReady?
{
  assert klonVMapOK(m'.m);
  assert klonCanKV(m', k, v);
  assert forall x <- m'.m.Keys, y <- m'.m.Values :: (y == v) ==> (x == k);
    // var m'fmodes := map z <- m'.m.Keys :: z := z.fieldModes;
    // assert m'fmodes.Keys == m'.m.Keys;
    // assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);

  var r0 : vmap<Object,Object> := vmapKV(m'.m,k,v); // m'.m[k:=v];
  assert klonVMapOK(r0);
  assert r0 ==  m'.m[k:=v];
// assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);
// assert forall z <- m'.m.Keys :: modesEQ(r0[z].fieldModes, m'fmodes[z]);

  var r1 := m'.(m:=r0);
  assert r1 == m'.(m:=m'.m[k:=v]);

  haventFuckedFieldModes(m',k,v,r1);

//  assert forall z <- m'.m.Keys :: z.fieldModes == r1.m[z].fieldModes;
  r1
  }

//
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//

predicate modesEQ(a : map<string,Mode>, b : map<string,Mode>)
 { (a.Keys == b.Keys) && (forall n <- a.Keys :: a[n] == b[n]) }


  lemma {:isolate_assertions} {:timeLimit 30} haventFuckedFieldModes(m' : Klon, k : Object, v : Object, m : Klon)
    requires k !in m'.m.Keys
    requires v !in m'.m.Values
    requires klonVMapOK(m'.m)
    requires klonCanKV(m', k, v)
    requires m == m'.(m:=m'.m[k:=v])
     ensures forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes)
{
    var m'fmodes := map z <- m'.m.Keys :: z := m'.m[z].fieldModes;
    assert m'fmodes.Keys == m'.m.Keys;
    assert forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m'fmodes[z]);
    assert forall z <- m'.m.Keys :: modesEQ(m. m[z].fieldModes, m'fmodes[z]);
    assert forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes);
}

//
//
//
// //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
//

predicate klonCanKV(m' : Klon, k : Object, v : Object)
  //extending m' with k:=v will be klonVMapOK
  // requires klonVMapOK(m'.m)  //should this be here?  if not, in below!  //BOWIE

  //requires m'.HeapContextReady()     //wuld be nice but fucks callers' read clauses?
  //requires m'.ValuesContextReady()
  //requires Calid() ?????

///does not check ownerhsip!!!

  reads k, v, m'.oHeap, m'.hns(), m'.m.Keys, m'.m.Values
  // reads k`fields, k`fieldModes
  // reads v`fields, v`fieldModes
  //
  // reads m'.oHeap`fields, m'.oHeap`fieldModes
  // reads m'.ns()`fields,  m'.ns()`fieldModes
  // reads m'.m.Keys`fields, m'.m.Keys`fieldModes
  // reads m'.m.Values`fields, m'.m.Values`fieldModes
{
  && klonVMapOK(m'.m) //BOWIE
  && canVMapKV(m'.m, k, v)
  && (k in m'.oHeap)  //KJX do I want this here?
  && (if (v==k) then (v in m'.oHeap) else (v !in m'.oHeap)) //nope - happens after  wards

  //grrr. should refactor this
  && k.Ready() && k.Valid() && k.Context(m'.oHeap)
  && v.Ready() && v.Valid() && v.Context(m'.hns({v}))

  //  && k.Context(m'.m.Keys+{k})  ///what IS this?
  &&  m'.ownersInKlown(k)
  && (k.fieldModes == v.fieldModes)//hhhmm see anbove

  //  && (v.AMFX >= v.AMFB >= k.AMFB) //is this right?   really?
  //17 June 2025 kjx thinks this iswrong & shoud be in CalidLineKV


  //END DOOUBLE BOWIE
}

//

lemma MapThruKlonIsVMap(kk: set<Object>, m : Klon, vv : set<Object>)
  requires kk <= m.m.Keys
  requires mapThruKlon(kk, m) == vv
   ensures mapThruVMap(kk, m.m) == vv
   {}


function mapWithinKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Keys
  ensures  r  <= m.m.Values
  reads {}
{ set o <- os | inside(o, m.o) :: m.m[o] }



function {:isolate_assertions} mapThruKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Keys
   ensures r  <= m.m.Values
   ensures (os > {}) ==> (r > {})
  reads {}
    { assert (os > {}) ==> ( var x :| x in os; {m.m[x]} > {});  //THIS LINE IS OF SATAN. WASBN"T NEEDED PREVIOUSLY.,..
      set o <- os :: m.m[o] }

lemma MapThruKlonFrom(os: set<Object>, m : Klon, m' : Klon)
  requires os <= m'.m.Keys
  requires m.from(m')
  ensures  mapThruKlon(os, m) == mapThruKlon(os, m')
{}

lemma MapThruKlonFUCKED(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os == ot
  ensures  mapThruKlon(os, m) == mapThruKlon(ot, m)
{}

lemma MapThruKlonLEQ(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os <= ot
  ensures  mapThruKlon(os, m) <= mapThruKlon(ot, m)
{}


lemma MapThruKlonGEQ(os: set<Object>, ot : set<Object>,  m : Klon)
  requires os <= m.m.Keys
  requires ot <= m.m.Keys
  requires os >= ot
  ensures  mapThruKlon(os, m) >= mapThruKlon(ot, m)
{}


lemma MapThruKlonID(os: set<Object>, m : Klon)
  requires os <= m.m.Keys
  requires forall x <- os :: m.m[x] == x
  ensures  mapThruKlon(os, m) == os
{}


lemma MapThruKlonIsMapThruVMap(ks: set<Object>, m : Klon, vs : set<Object>)
  requires ks <= m.m.Keys
  requires mapThruKlon(ks, m)   == vs
  ensures  mapThruVMap(ks, m.m) == vs
{}

function mapBackKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under INVERSE klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Values
  ensures  r  <= m.m.Keys
  reads {}
{ mapBackVMap(os,m.m) }


lemma ThereAndKlonAgain1(os: set<Object>, m : Klon, r : set<Object>)
  requires os <= m.m.Keys
  requires r  == mapThruKlon(os,m)
   ensures r  <= m.m.Values
   ensures os == mapBackKlon(r,m)
{
  InversionLove(m.m, invert(m.m));
  assert r  == mapThruKlon(os,m);
  assert os == mapBackKlon(r,m);
}

lemma ThereAndKlonAgain2(os: set<Object>, m : Klon, r : set<Object>)
  requires os <= m.m.Values
  requires r == mapBackKlon(os,m)
   ensures r  <= m.m.Keys
   ensures os  == mapThruKlon(r,m)
 {
    InversionLove(m.m, invert(m.m));
 }




lemma {:isolate_assertions} OwnershipOfCloneGEQ(os: set<Object>, ot : set<Object>,  m : Klon)
//
///kj 7 June 2025 - not claer how this  works if we're comaring owners and bounds?
  requires os <= m.m.Keys <= m.oHeap
  requires ot <= m.m.Keys <= m.oHeap
  requires os >= ot

  requires m.apoCalidse()
  requires m.SuperCalidFragilistic()

  requires m.m.Values <= m.hns()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap  //flattened ownershio of the top of the clone... - 'tis OK cos its the very top
   ensures computeOwnerForClone(os, m) >= computeOwnerForClone(ot, m)
{}





lemma {:isolate_assertions} OwnershipOfCloneGEQ2(os: set<Object>, ot : set<Object>, m : Klon, ro : set<Object>, rt : set<Object>)
  requires os <= m.m.Keys <= m.oHeap
  requires ot <= m.m.Keys <= m.oHeap
  requires os >= ot

  requires m.apoCalidse()
  requires m.SuperCalidFragilistic()

  requires m.m.Values <= m.hns()
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap  //flattened ownershio of the top of the clone... - 'tis OK cos its the very top

   requires ro == computeOwnerForClone(os, m)
   requires rt == computeOwnerForClone(ot, m)

   ensures computeOwnerForClone(os, m) >= computeOwnerForClone(ot, m)
{}






predicate {:isolate_assertions} istKlonnyKlon(os : Owner, ks : set<Object>, m : Klon)
    requires m.o.Ready()
    requires m.objectInKlown(m.o)
    requires os <=  m.m.Keys <= m.oHeap
    requires m.c_amfx <= m.oHeap
    requires m.apoCalidse()
    requires m.SuperCalidFragilistic()

     reads m.oHeap, m.m.Values

    decreases os, 50
{
  && (forall o <- os :: o in m.m.Keys)
  && (m.o in os)
  && (computeOwnerForClone(os, m) == ks)  ///AMOST CERTAINLY WRONG!!!!!  --- should call checkOwnershipOfClone instead
}

predicate istKlonAlleFelder(o : Object, k : Object, m : Klon)
  reads o`fields, o`fieldModes
  reads k`fields, k`fieldModes
{
  && (o.fields.Keys     == k.fields.Keys)
  && (o.fieldModes.Keys == k.fieldModes.Keys)
  && (o.fields.Values     <= m.m.Keys)
  && (forall f <- o.fields.Keys :: (m.m[o.fields[f]]  == k.fields[f]))
//  && ()   //at some point needs to check mapping for fieldModes?
}




function local(o : OWNR, m : Klon) : (r : OWNR)
 //take a "global" original OWNR to a local internal one in the original (should this be global2local)
 //should theyb e differen types? ARGH!
  // //requires isFlat(o)
  // //ARGH.  this is a set of Owners inside the pivotg
  // //but those objects are all fully global AMDOs...?
  // requires m.apoCalidse()
  // requires o >= m.o.AMFO   //o >= or o > ?
   ensures r <= o
   //ensures isFlat(r)
   // { o - m.o.AMFO  }   //shit shit shit
   { o - m.o.AMFO  }

function {:isolate_assertions} global(oo : set<Object>, m : Klon) : (rs : set<Object>)
 //take a "local" OWNR to a global one in the clone (should this be local2global)
   requires m.apoCalidse()
  //  requires forall o <- oo :: inside(o,m.m[m.o])
  //  //ensures  isReallyFuckingFlat(rs)
  // //requires o >= m.o.AMFO
  //  //ensures isFlat(r)
   { oo + m.m[m.o].AMFO  }

function sideways(oo : set<Object>, m : Klon) : (r : set<Object>)
 //take a "local" OWNR to a global one in the clone (should this be local2global)
  //  requires AllReady(oo)
   requires oo <= m.m.Keys
  //  requires m.apoCalidse()
  // //requires isFlat(o)
  // requires oo <= m.o.AMFO
  //  //ensures isFlat(r)
  ensures r ==  mapThruKlon(oo, m) //hmm???
  ensures r <= m.m.Values
   { mapThruKlon(oo, m) }





//---------------------------------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------------
//---------------------------------------------------------------------------------------------------
//Lemmers


lemma AMFOsisAMFOs(o : Object)
  requires o.Ready()
  ensures forall oo <- o.AMFO | oo != o :: (o.AMFO > oo.AMFO)
  ensures forall oo <- o.AMFO | oo != o :: strictlyInside(o, oo)
  ensures forall oo <- o.AMFO           :: inside(o, oo)
{}

//this costs 0.08ms - who knows whw?
lemma OIKsisOIKs(o : Object, m : Klon)
  requires o.Ready()
  requires m.ownersInKlown(o)
  ensures forall oo <- o.AMFO | oo != o :: m.ownersInKlown(oo)
  ensures forall oo <- o.AMFX :: m.ownersInKlown(oo)
{}

// //    //   //   //   //   ///   ///   //   //   //   //     //    //          //
//
predicate klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys
  //klonVMapOK the vmap parts of a klon are OK
  //still need to do something for iHeap and ns etc
  //should probably swizzle this to take a Klon, not a vmap/...
  //KJX AND that shoud something like klonReady
  //meaning that for all targets (m.Keys)
  //the coresponding klon  m[k] is
  // - ready
  // - corresponds to the target
  //structure of this needs TO MATCH THE CALIDs and
  //object invairants ready, valid, calid, etc
  //klonca
  // IDEALLY the "mapThru" features shouldn't be part of
  // the invariuant itself (klonOK) NOR the extension test (klonCanKV)
  // no the extension (klonKV)
  // rather mapThru etc should be post-derivable efrom calid, not wired in...
  //  which hopefully is ONE clause per "field" of Dahlia's "Object" and no more?
  reads m.Values`fieldModes
  reads ks`fieldModes
{
//Readiness???  //KJXFEARSATAN
   && (forall k <- ks :: k.Ready() && m[k].Ready() )

  //AMFO
  && (forall k <- ks :: k.AMFO <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFO, m) == m[k].AMFO)

  //AMFB
  && (forall k <- ks :: k.AMFB <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFB, m) == m[k].AMFB)

  //KJXOWNERS
  //region & owners?
  //  && (forall x <- ks :: x.owaner <= x.AMFO)//KJXOWNERS
//  && (forall x <- ks :: x.bound <= x.owner <= m.Keys) //should that bound be ks?
  //  && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
  //  && (forall k <- ks :: mapThruVMap(k.bound, m) == m[k].bound)

  //field values? //KJX
  //
  //
  //  && (forall k <- ks :: k.fieldModes == m[k].fieldModes)
///
  //see rant above
}




predicate {:isolate_assertions}  checkOwnershipOfClone(k : Object, v : Object, m : Klon)
  //to work, this needs m.o and m.m[m.o] to be set up
  //but does NOT need k in Keys, or v in values!
  //
  // apparently doesn't even need Caliud or precalid let alone supercalid.  HMMM
  requires k.Ready()
  requires m.ownersInKlown(k)
  requires v.Ready()
  requires m.apoCalidse()

  //the six requirements of preCalid2 / computeOwnerForClone apocalypse
  requires k.owner <= m.m.Keys <= m.oHeap
  requires m.m.Values <= flatten( m.hns() )
  requires m.o.Ready()
  ///requires m.objectInKlown(m.o) //// NO NO NO NO NO NO NO NO NO
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap

  reads m.oHeap, m.m.Values
{
  mappingOwnersThruKlownKV(k,v,m)
}


predicate {:isolate_assertions} checkBoundOfClone(k : Object, v : Object, m : Klon)
  //to work, this needs m.o and m.m[m.o] to be set up
  //but does NOT need k in Keys, or v in values!
  //
  // apparently doesn't even need Caliud or precalid let alone supercalid.  HMMM
  requires k.Ready()
  requires m.ownersInKlown(k)
  requires v.Ready()


  //the six requirements of preCalid2 / computeOwnerForClone apocalypse
  requires k.owner <= m.m.Keys <= m.oHeap
  requires m.m.Values <= flatten( m.hns() )
  requires m.o.Ready()
  requires m.objectInKlown(m.o)
  requires m.HeapOwnersReady()
  requires m.c_amfx <= m.oHeap
  reads {}
{
  || (v == k)   //note technically redundant condition...
  || (v.AMFB >=  k.AMFB)  //GREENLAND //Beady2()  //AMFB_GEQ_GT
     //when you clone you can *(either)*
      //move the owner down
      //move the bound down (allowing more pointing but less movement)
      //move the owner up to the bound
       //providing you don't break any other invariant...
      // you do need to be able to "copy out" and "copy in"
}



  predicate {:isolate_assertions} mappingOwnersThruKlownKV(k : Object, v : Object, m : Klon) : (r : bool)
    //KJX FEAR SATAN
    //this vrsion currently matches CalidLineKV, i.e. k and v don't have to be in the klon
    //but that means we can't mapp intl and AMFO  //um,,
    //i think this is th4e INVARIANT
    //Sure seeems to be the  INVARIANT -- 22 Dec 2025

   decreases k.AMFO
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
//    requires v.Ready()
    reads m.oHeap, m.m.Values
    {
      // KJX FEAR SATAN!!

      if (k == m.o) then (
          && (v == m.m[m.o])
          && (v.owner == m.clowner)
          && (v.bound == m.clbound)
        ) else if (outside(k, m.o) )
          then (
            k == v
        ) else (
          assert strictlyInside(k, m.o);
              // && (v.bound == mapThruKlon(k.bound, m))
              // && (v.owner == mapThruKlon(k.owner, m))
              && mappingOWNRsThruKlownKV(k.bound, v.bound, m)
              && mappingOWNRsThruKlownKV(k.owner, v.owner, m)
        )
    }

lemma {:isolate_assertions} SuperDuperOwnerMapperKV(k : Object, v : Object, m : Klon)
  //consistency lemma… or somesthing.
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires k.Ready()
    requires v.Ready()
    requires m.CalidLineKV(k,v)
    requires m.OwnersLineKV(k,v)
//  requires v.owner == computeOwnerForClone(k.owner, m)
//  requires v.bound == computeOwnerForClone(k.bound, m)
     ensures mappingOwnersThruKlownKV(k,v,m)
     ensures (k == m.o) ==> (
          && (v == m.m[m.o])
          && (v.owner == m.clowner)
          && (v.bound == m.clbound))
     ensures (outside(k, m.o)) ==> (v == k)
     ensures (strictlyInside(k, m.o)) ==> (
          && mappingOWNRsThruKlownKV(k.owner,v.owner,m)
          && mappingOWNRsThruKlownKV(k.bound,v.bound,m)
          && v.owner == computeOwnerForClone(k.owner, m)
          && v.bound == computeOwnerForClone(k.bound, m)
         )
{}



lemma {:isolate_assertions} SuperDuperExternalMapperKV(k : Object, v : Object, m : Klon)
  //consistency lemma… or somesthing.
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires v.owner == computeOwnerForClone(k.owner, m)
    requires v.bound == computeOwnerForClone(k.bound, m)
    requires outside(k, m.o)
     ensures mappingOWNRsThruKlownKV(k.owner,v.owner,m)
     ensures mappingOWNRsThruKlownKV(k.bound,v.bound,m)
{}


lemma {:isolate_assertions} SuperDuperPivotMapperKV(k : Object, v : Object, m : Klon)
  //consistency lemma… or somesthing.
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires m.SuperCalidFragilistic()
    requires v.owner == computeOwnerForClone(k.owner, m)
    requires v.bound == computeOwnerForClone(k.bound, m)
    requires k == m.o
     ensures mappingOWNRsThruKlownKV(k.owner,v.owner,m)
     ensures mappingOWNRsThruKlownKV(k.bound,v.bound,m)
{}


lemma {:isolate_assertions} SuperDuperKlonMapperKV(m : Klon)
  //consistency lemma… or somesthing.kkkkk
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(m.o)
    requires m.SuperCalidFragilistic()
// i  ensures mappingOWNRsThruKlownKV(m.o.owner,m.m[m.o].owner,m)
//     ensures mappingOWNRsThruKlownKV(m.o.bound,m.m[m.o].bound,m)
     ensures m.m[m.o].owner == m.clowner
     ensures m.m[m.o].bound == m.clbound
{}

    //our shold this be MAPPING Owners?????
    //note that this is called ONLY strictly wihin the pivot - see the JDVANCE note
    predicate {:isolate_assertions} mappingOWNRsThruKlownKV(kk : OWNR, vv : OWNR, m : Klon) : (r : bool)
      //actual OWNR version of mappingOwnersThruKlownKV
      //within the pivot anyway!
      //KJX FEAR SATAN
          //OK so wher doe this asy "inside the pivot"?   - it DO#ESNT
          //does that matter?  who knows?
      requires m.apoCalidse()
      // requires AllReady(kk)  // 29 Oct 2025
      // requires AllReady(vv)  // 29 Oct 2025
      requires kk <= m.m.Keys
  ////requires vv <= m.m.Values  ///hmm must be trie if kjk,s inside Klon...
  ////requires kk > m.o.AMFO  //gotta be inside kloned bit..  //JDVANCE yeah shoud do that!

        {
//I have NO FUCKING IDEA if this is dong te RIGHT THING or not.
//anin't that great.
//i think its dong CLOSE ENOUGH to the right thing for a paper
//the visualisations all look OK now
//but stil - 21 Sept 2025


        && (vv == (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO))
        && (flatten(kk) <= m.oHeap)
        && (flatten(vv) <= m.hns(vv))

          // var inside1 := kk - m.o.AMFO;
          // var option1 := mapThruKlon(inside1,m) + m.m[m.o].AMFO;
          // (vv == option1)
        }

lemma {:isolate_assertions} ShiftAMFOshiftOWNRs(kk : OWNR, vv : OWNR, m : Klon)
   //establishes that shiftAMFO(Kk) makes a vv that passes mappignOWNRS...
      requires m.apoCalidse()
      requires AllReady(kk)
      requires AllReady(vv)
      requires kk <= m.m.Keys
      requires kk >= m.o.AMFO

      requires flatten(kk) <= m.oHeap
      requires flatten(vv) <= m.hns(vv)  //kind of trivially true though...

      requires vv == shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m)

       //ensures vv == (mapThruKlon(kk - m.o.AMFO, m) + m.m[m.o].AMFO)

       ensures mappingOWNRsThruKlownKV(kk, shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m), m)
      {}


lemma {:isolate_assertions} ShiftOWNRshiftAMFOs(kk : OWNR, vv : OWNR, m : Klon)
    //or this? 0 if mappign OWNRS are OK< then shitAMFO doea the righ tthing
      requires m.apoCalidse()
      requires AllReady(kk)
      requires AllReady(vv)
      requires kk <= m.m.Keys

      requires kk >= m.o.AMFO
      requires mappingOWNRsThruKlownKV(kk, vv, m)
      ensures vv == shiftAMFO(kk, m.o.AMFO, m.m[m.o].AMFO, m.m)
      {}



function {:isolate_assertions} computeOwnerForClone(oo : Owner, m : Klon) : (nuowner : Owner)
  //given some flattened Owner oo, calculate the mapped / cloned version
  //EXCEPT OWNERS SHOULDNT BE FLATTENNED!!!
///TODO//Libertarian  //requires (flatten(oo) >= m.o.AMFO)   //should this be there or not?
  //
  //     7 Aug 2025 - kjx thinks - this doesn't work if we're flatting the bound
  //             I removed the constraint hopijng it doesn't break too  much stuff..
  //
  //  I think this makes sense for owners of subparts being clonedj
///  but not neccessarily for e..g bounds that lie (partially) outside?
///
  //  Ha! remember that in many (if not all) cases. bound == owner
  //    which means that, it pretty much needs to have the same mapping...
  //
///seemss to survive without oo being ready!
///seemss to survive without ANYUTHING being Ready
///KJXA Naa will need Values...
  requires m.apoCalidse()  //note that this requires m.o already in m.m.Keys
  requires oo <= m.m.Keys
//  requires flatten(oo) >= m.o.AMFO //hmmmA
  requires m.SuperCalidFragilistic()
   ensures nuowner <= m.hns()
   ensures flatten(oo) <= m.oHeap //so this MUST be preexisting.
   ensures flatten(nuowner) <= m.hns()
   ensures mappingOWNRsThruKlownKV(oo, nuowner, m)   //rather important
       //yes 'rathr imoportant" infdeed,


   ensures nuowner == global(sideways(local(oo, m),m),m)
   ensures nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.m[m.o].AMFO, m.m)

      //********also important that that's OWNRES NOT Owners **************//
      //***ot is it??
      //JDVANCE -- note that sholdlj constraint oo to be inside(the pivot)
      //so the new owner is strictly inside the blivet..../
 // requires flatten(oo) >= m.o.AMFO           //JDVANCE

 reads m.oHeap, m.m.Values
//  reads {}
{
  assert m.ValuesContextReady();
  var inside1 := oo - m.o.AMFO;
  assert inside1 <= m.oHeap;

  var nuowner := mapThruKlon(inside1,m) + m.m[m.o].AMFO;

  assert nuowner == (set x <- (oo - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
  assert nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.m[m.o].AMFO, m.m);

  assert mapThruKlon(inside1,m) <= m.m.Values <= m.hns();
  assert m.m[m.o] in m.hns();
  assert m.ValueInContext(m.m[m.o]);
  assert m.m[m.o].AMFO <=  m.hns();

  var fuck1 := local(oo, m);
  var fuck2 := sideways(fuck1, m);
  var fuck3 := global(fuck2, m);
  assert fuck3 == nuowner;

  assert fuck3 == global(sideways(local(oo, m),m),m);


//  .AMFO <= m.m.Values <= m.hns();ƒƒ∂çƒ©
  assert nuowner <= m.hns();
  nuowner
}
//really this is to MATCH the checkClownershipINSIDE






lemma {:isolate_assertions}  MappingInsideOwnersThruKlown(k : Object, v : Object, m : Klon)
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    requires strictlyInside(k, m.o)
    requires k in m.m.Keys
    requires m.m[k] == v

      ensures strictlyInside(v, m.m[m.o])

      requires mappingOwnersThruKlownKV(k,v,m)
      requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)
      ensures forall oo <- k.owner | strictlyInside(oo,m.o) :: m.m[oo] in v.owner
      ensures inside(v, m.m[m.o])
  {
    assert v.owner == (set x <- (k.owner - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
  }






lemma {:isolate_assertions} MappedBounds(k : Object, v : Object, m : Klon)
    requires k.Ready()
    requires v.Ready()
    requires m.ownersInKlown(k)
    requires m.SuperCalidFragilistic()

    requires strictlyInside(k, m.o)
     ensures k.AMFO > m.o.AMFO

    // ensures (forall oo <- k.AMFX :: k.AMFB <= oo.AMFB)  //GREENLAND //Beady2()
    ensures nuBoundsOK(k.owner, k.bound)

    requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)
   //  ensures (forall oo <- v.AMFX :: v.AMFB <= oo.AMFB)  //GREENLAND //Beady2()
       ensures nuBoundsOK(v.owner, v.bound)
  {
    k.ExtraReady();  //GREENLAND //Beady2()
    v.ExtraReady();  //GREENLAND //Beady2()
    assert nuBoundsOK(k.owner, k.bound);
    assert nuBoundsOK(v.owner, v.bound);
//    assert (forall oo <- k.AMFX :: k.AMFB <= oo.AMFB + k.owner);   //GREENLAND //Beady2()
//    assert (forall oo <- v.AMFX :: v.AMFB <= oo.AMFB + v.owner);  //GREENLAND //Beady2()

    assert  k.AMFX >= k.AMFB;
    assert  (forall oo <- k.AMFX :: oo in m.m.Keys);
    assert  m.HeapContextReady();
    assert  m.ValuesContextReady();
    assert  AllReady(m.hns());

    var nuowner := computeOwnerForClone(k.owner,m);
    assert nuowner <= m.hns();
    assert  AllReady(nuowner);
    assert  AllReady(flatten(nuowner));
    var nubound := computeOwnerForClone(k.bound,m);
    assert nubound <= m.hns();
    assert  AllReady(nubound);
    assert  AllReady(flatten(nubound));
    var fvbound := flatten(nubound);
    var fvowner := flatten(nuowner);

    assert nuowner == global(sideways(local(k.owner, m),m),m);
    assert nubound == global(sideways(local(k.bound, m),m),m);



    //  assert fvowner >= fvbound;                                  //THULE  //TODO
    //  assert (forall vo <- fvowner :: fvbound <= vo.AMFB);        //THULE  //TODO

//    assert fvbound >= collectBounds(fvowner);  //TODO NUBIOUBNDS...
  }


lemma {:isolate_assertions}  MappingSameObjectIsOutsideThruKlown(k : Object, v : Object, m : Klon)
//wrong turn on the rocky road to dublin…
//answer - it works cos saying  m.m[k] == k == v
// constraints the spec so there are no solutions - except outside?
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.SuperCalidFragilistic()
    requires m.objectReadyInKlown(k)
    requires m.m[k] == k == v

    ensures outside(k, m.o)
{
   assert m.AllLinesCalid();
   assert m.CalidLineKV(k,v);
   assert mappingOwnersThruKlownKV(k, v, m);
}

lemma {:isolate_assertions}  MappingInsideBoundsThruKlown(k : Object, v : Object, m : Klon)
//wrong turn on the rocky road to dublin…
//answer - it works cos saying "outside" overconstraints the spec so there are no solutions
//saying m.m[k] == v gives us outside
   decreases k.AMFO
    requires k.Ready()
    requires v.Ready()
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
    // requires strictlyInside(k, m.o)  //how the hell does it work without this?

    //requires outside(k, m.o)

    requires k in m.m.Keys
    requires m.m[k] == v

    ensures flatten(k.owner) >= flatten(k.bound)
    ensures flatten(v.owner) >= flatten(v.bound)

    ensures strictlyInside(v, m.m[m.o])

    requires mappingOwnersThruKlownKV(k,v,m)
    requires mappingOWNRsThruKlownKV(k.bound, v.bound, m)
    requires mappingOWNRsThruKlownKV(k.owner, v.owner, m)

    ensures forall oo <- k.owner | strictlyInside(oo,m.o) :: m.m[oo] in v.owner
    ensures inside(v, m.m[m.o])
  {
    assert v.owner == (set x <- (k.owner - m.o.AMFO) :: m.m[x]) + m.m[m.o].AMFO;
}



//
// //////////////////////////////////////////////////////////////////////////////

lemma {:isolate_assertions}  SetMinus0<T>(a : set<T>, b : set<T>)
  requires (a - b) == {}
   ensures  a <= b
{
  forall x <- a ensures (x in b) //by
   {
      assert x in a;           //all generated by copilot...
      assert (a - b) == {};
      assert not(x in (a - b));
      assert x in b;
  }
}


lemma {:isolate_assertions}  SetMinus3<T>(a : set<T>, b : set<T>, c : set<T>)
 //a is split between b !! c
  requires a - b == c
  requires a >= b
  requires a >= c
   ensures a - c == b
   ensures b !! c
   ensures a == b + c
{}


lemma {:isolate_assertions}  SetMinus4<T>(a : set<T>, b : set<T>, c : set<T>, d : set<T>)
  requires a == c
  requires b == d
  ensures (a - b) == (c - d)
{}

lemma {:isolate_assertions}  SetMinus6<T>(a : set<T>, b : set<T>, c : set<T>, d : set<T>, e : set<T>, f : set<T>)
  requires a == d
  requires b == e
  requires c == f
  ensures (a - b - c) == (d - e - f)
{}

lemma  Set3Eq3<T>(a : set<T>, b : set<T>, c : set<T>, d : set<T>, e : set<T>, f : set<T>)
  requires a == d
  requires b == e
  requires c == f
  ensures  (a+b+c) == (d+e+f)
{}














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
