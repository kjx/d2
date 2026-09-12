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

function  allInside(soup : set<Object>, whole : Object) : (rv : set<Object>) reads {}  { set o <- soup | inside(o,whole) }
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

//
// lemma AXIOMFFFFF(part : Object, whole : Object)
// // o in AMFO ==> o.AMFO <= AMFO
//    requires part.Ready()
//    requires inside(part,whole)
//     ensures whole in part.AMFO
//     ensures forall o <- part.AMFO :: o.Ready();
//     ensures whole.Ready()
//    {
//     part.RettyBetty({part});
//     }


// lemma OffsideIsSideways0(part : Object, whole : Object, side1 : Object, side2 : Object)
//   requires side1 in whole.owner // side is one of whole's owners
//   requires side2 in whole.owner // side is one of whole's owners
//   requires side1 in part.owner
//   requires {part} !! {whole} !! {side1} !! {side2}
//    ensures outside(side1, whole)
//    ensures outside(side1, part)
//    ensures




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
   ensures soup  == ins + outs + sides
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


///Oh SHIT 0 most of the these are WRONG.

 function flattenInside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: inside(r,pivot)
  ensures forall r <- flatten(soup) :: inside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | inside(x,pivot) }

function flattenOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: outside(r,pivot)
  ensures forall r <- flatten(soup) :: outside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | outside(x,pivot) }

function flattenOffside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: offside(r,pivot)
  ensures forall r <- flatten(soup) :: offside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | offside(x,pivot) }

function flattenStrictlyInside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: strictlyInside(r,pivot)
  ensures forall r <- flatten(soup) :: strictlyInside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | strictlyInside(x,pivot) }

function flattenPivotlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall r <- rv :: pivotlyOutside(r,pivot)
  ensures forall r <- flatten(soup) :: pivotlyOutside(r,pivot) ==> r in rv
{ set x <- flatten(soup) | pivotlyOutside(x,pivot) }

predicate onlyPivot(part : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(part, pivot) && inside(part,owner) &&  inside(pivot, owner) } // aka inside3(part,pivot,owner)
predicate exceptPivot(part : Object, pivot : Object, owner : Object) : (rv : bool) reads {}   { inside(part, pivot) && inside(part,owner) && outside(pivot, owner) }
   //should we explicitly require owner in part.AMFO  aka part inside owner?
   //well apart from the "preconditions to the preconditions" problem

function shortcutOnlyPivot(soup : OWNR, pivot : Object) : (rv : Owner)
  ensures forall p <- pivot.AMFO :: inside(pivot, p)
  ensures forall r <- rv :: inside(pivot, r)
  ensures (rv == {}) != (rv == pivot.AMFO)
  ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
  ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
  ensures forall r <- rv :: inside(pivot, r)
  ensures forall r <- rv :: exists s <- soup :: onlyPivot(s, pivot, r)
  ensures forall r <- rv :: r.Ready()
  { assume forall s <- soup :: s.Ready(); assume pivot.Ready();
    if (exists s <- soup :: inside(s,pivot)) then (pivot.AMFO) else {} }

function flattenOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | onlyPivot(s,pivot,oo) :: oo}

function flattenExceptPivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | exceptPivot(s,pivot,oo) :: oo}




lemma LEMMA_flattenOnlyPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))
   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}

lemma LEMMA_flattenOnlyPivot1(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires forall s <- soup :: outside(s,pivot)
   ensures rv == {}
{}

lemma LEMMA_flattenOnlyPivot2(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires exists s <- soup ::  inside(s,pivot)
   ensures rv <= pivot.AMFO
{
  var s :| s in soup && inside(s,pivot);

  forall r <- rv ensures (r in pivot.AMFO) //by
   {
      assert inside(pivot,r);
      AXIOMAMFOREVERSE(pivot, r);
   }
  assert rv <= pivot.AMFO;
}

lemma LEMMA_flattenOnlyPivot3(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))

  requires exists s <- soup ::  inside(s,pivot)
   ensures rv >= pivot.AMFO
{
   var s :| s in soup && inside(s,pivot);
   assert forall r <- s.AMFO     | onlyPivot(s,pivot,r) :: inside(pivot, r);
   assert forall r <- s.AMFO     | onlyPivot(s,pivot,r) :: r in rv;

   assert rv >= pivot.AMFO;
}

lemma LEMMA_flattenOnlyPivot9(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOnlyPivot(soup, pivot))
   ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
{
  if (forall s <- soup :: outside(s,pivot))
     { LEMMA_flattenOnlyPivot1(soup,pivot,rv); return; }
    else
    { LEMMA_flattenOnlyPivot2(soup,pivot,rv); LEMMA_flattenOnlyPivot3(soup,pivot,rv); }
}

lemma LEMMA_shortcutOnlyPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))

   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: inside(s,r)
   ensures forall r <- rv :: inside(pivot, r) && (exists s <- soup :: inside(s,r))
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}

lemma LEMMA_shortcutOnlyPivot1(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == shortcutOnlyPivot(soup, pivot))
   ensures (forall s <- soup :: outside(s,pivot)) ==> (rv == {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv >  {})
   ensures (exists s <- soup ::  inside(s,pivot)) ==> (rv == pivot.AMFO)
{}

lemma LEMMA_flattenExceptPivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenExceptPivot(soup, pivot))
   ensures forall r <- rv :: outside(pivot,r) && (exists s <- soup :: inside(s,r))
   ensures forall r <- rv :: exists s <- soup :: exceptPivot(s,pivot,r)
   ensures forall r <- rv :: exists s <- soup :: inside(s, pivot) && inside(s,r) && outside(pivot, r)
   //ensures forall r <- rv :: exists s <- soup :: exceptPivot(s,pivot,r) && pivotlyOutside(r,pivot)

   ensures rv <= flatten(soup)
   //  ensures (forall s <- soup :: outside(s,pivot) ==> (s in rv))
  //  ensures (forall s <- soup, oo <- s.AMFO, ooo <- oo.AMFO | outside(ooo,pivot) :: (ooo in rv))
   // ensures (rv == {}) ==> (forall s <- soup, oo <- s.AMFO :: colinear(oo.AMFO,pivot.AMFO))
{
  if (rv == {}) { return; }

  var s :| s in soup && inside(s,pivot);
  assert forall r <- s.AMFO     | exceptPivot(s,pivot,r) :: r in rv;


}

lemma LEMMA_shortcutVSflatten2(soup : OWNR, pivot : Object, shOP : Owner, fOP : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires shOP == shortcutOnlyPivot(soup, pivot)
  requires fOP == flattenOnlyPivot(soup, pivot)
  requires forall r <- shOP :: r.Ready()
  requires forall r <- fOP  :: r.Ready()
   ensures shOP == fOP
   ensures (shOP == fOP == {}) || (shOP == fOP == pivot.AMFO)
{
  if (forall s <- soup :: not(inside(s,pivot)))
    { assert shOP == fOP == {}; return; }

  assert exists s <- soup :: inside(s,pivot);
  LEMMA_flattenOnlyPivot9(soup,pivot,fOP);
  assert shOP == fOP == pivot.AMFO;
}


lemma TRICHOTOMY_ONLY_EXCEPT(part : Object, pivot : Object, owner : Object)
   ensures   onlyPivot(part,pivot,owner) ==> inside(part,pivot)
   ensures exceptPivot(part,pivot,owner) ==> inside(part,pivot)
  //  ensures      inside(part, pivot) ==> (onlyPivot(part,pivot,owner)
  //                exceptPivot(part,pivot,owner))

   ensures     outside(part, pivot) ==> (onlyPivot(part,pivot,owner) == exceptPivot(part,pivot,owner) == false)
{
  assume part.Ready();
  assume pivot.Ready();
  assume owner.Ready();
}


// inside(part, pivot) && inside(part,owner) &&  inside(pivot, owner)
// inside(part, pivot) && inside(part,owner) && outside(pivot, owner)


lemma OWNERZ_OF_PIVOTRY(soup : set<Object>, pivot : Object, fEP : Owner, fOP : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires fEP == flattenExceptPivot(soup,pivot)
 requires fOP == flattenOnlyPivot(soup,pivot)
  ensures forall r <- fEP :: exists s <- soup :: exceptPivot(s,pivot,r)
  ensures forall r <- fOP :: exists s <- soup ::   onlyPivot(s,pivot,r)
  ensures forall r <- fEP :: exists s <- soup :: exceptPivot(s,pivot,r)
  ensures forall r <- fOP :: exists s <- soup ::   onlyPivot(s,pivot,r)
    {}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// pivotlyOutside - pivotlyOutside(x,pivot)
//   onlyPivot -  inside(pivot,owner)
//   exceptPivot -outside(pivot,owner)
lemma FUCKING_WIT_DA_PIVOT(pivot : Object, owner : Object)
  requires pivot.Ready()
  requires owner.Ready()
    ensures pivotlyOutside(owner,pivot) == not(owner.AMFO > pivot.AMFO)
    ensures  inside(pivot,owner) == (pivot.AMFO >= owner.AMFO)
    ensures outside(pivot,owner) == not(pivot.AMFO >= owner.AMFO)

    ensures    (pivot.AMFO >= owner.AMFO) ==> not(owner.AMFO > pivot.AMFO)
    ensures           inside(pivot,owner) ==> pivotlyOutside(owner,pivot)
//    ensures outside(pivot, owner) ==> pivotlyOutside(owner,pivot)
//  ensures not(pivot.AMFO >= owner.AMFO) ==> not(owner.AMFO > pivot.AMFO)
    {}


//////////////////////////////////////////////////////////////////////////////////////////////////////////////////



lemma FUCKING_WIT_pivotlyOutside(a : Object, b : Object)
  requires a.Ready()
  requires b.Ready()
  requires pivotlyOutside(a,b)
   ensures not(a.AMFO > b.AMFO)
   ensures (a.AMFO == b.AMFO) || not(a.AMFO >= b.AMFO)
    {}

lemma FUCKING_WIT_DA_except_PIVOT(a : Object, b : Object, c : Object)
  requires a.Ready()
  requires b.Ready()
  requires c.Ready()

  requires exceptPivot(a,b,c)
    ensures inside(a, b) && inside(a,c) && outside(b, c)
    ensures (a.AMFO >= b.AMFO) && (a.AMFO >= c.AMFO) && not(b.AMFO >= c.AMFO)
    ensures not(c.AMFO > b.AMFO)
  //  ensures pivotlyOutside(c,b)
    {}



lemma TRICHOTOMY_DICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenStrictlyInside(soup,pivot)
 requires left1 == flattenPivotlyOutside(soup,pivot)
 requires right == flatten(soup)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
 {}




lemma DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flattenPivotlyOutside(soup,pivot)

  ensures left0 <= right
  ensures left1 <= right
//  ensures left0 + left1 <= right
  // ensures left0 + left1 >= right
  // ensures left0 + left1 == right

///HERE///

{
}


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
predicate AllValid(os : Owner) reads os`fields, os`fieldModes {forall oo <- os :: oo.Valid()}

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
