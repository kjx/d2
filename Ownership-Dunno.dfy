include "Ownership.dfy"
//include "Ownership-Trilemma.dfy"

function nuke(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}

lemma FLATTEN_NUKE(soup : Owner)
  ensures nuke(soup) == flatten(soup)
{
  assume forall s <- soup :: s.Ready();
  assert forall s <- soup :: s in s.AMFO;
  forall s <- soup ensures (true)
  {
    forall t <- s.AMFO ensures (true)
    {
        assert t in nuke({s});
        assert t in flatten({s});
     }
     assert forall n <-    nuke({s}) :: n in s.AMFO;
     assert forall f <- flatten({s}) :: f in s.AMFO;
     assert s.AMFO == nuke({s}) == flatten({s});
  }
}

function nukeOutside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
//  ensures forall s <- soup, o <- s.AMFO | outside(s,pivot) :: outside(o,pivot)
 requires pivot.Ready()
  ensures forall r <- rv :: outside(r,pivot)
//ensures rv == flatten( (set s <- soup | outside(s,pivot)) )
     {  MaybeOutiesSidies(soup, pivot);
      flatten( set s <- soup | outside(s,pivot) ) }


function nukeInside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
//  ensures forall s <- soup, o <- s.AMFO | outside(s,pivot) :: outside(o,pivot)
 requires pivot.Ready()
     { flatten( set s <- soup | inside(s,pivot) ) }


function nukeStrictlyInside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
     {      flatten( set s <- soup | strictlyInside(s,pivot) ) }


function nukePivotlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
     {      flatten( set s <- soup | pivotlyOutside(s,pivot) ) }




function nukeStrictlyPivot(soup : OWNR, pivot : Object) : (rv : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 ensures (pivot in soup)  <==> (rv == pivot.AMFO)
 ensures (pivot !in soup) <==> (rv == {})
 requires pivot.Ready()
     { flatten( set s <- soup | s == pivot ) }


lemma FLATTEN_SUM4(a : Owner, b : Owner, c : Owner, cc : Owner)
  requires a+b+c == cc
  ensures flatten(a) + flatten(b) + flatten(c) == flatten(cc)
{}


lemma nukeEmAll1(soup : OWNR, pivot : Object)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
{
   assert forall s <- soup ::  outside(s,pivot) != inside(s,pivot);

   assert soup ==
              (set s <- soup | outside(s,pivot) ) +
              (set s <- soup | inside(s,pivot) );

   assert forall s <- soup | inside(s,pivot) :: (s == pivot) != strictlyInside(s,pivot);

   assert (set s <- soup | inside(s,pivot)) ==
              (set s <- soup | (s == pivot) ) +
              (set s <- soup | strictlyInside(s,pivot) );

    assert soup ==
              (set s <- soup | outside(s,pivot) ) +
              (set s <- soup | (s == pivot) ) +
              (set s <- soup | strictlyInside(s,pivot) );

}

lemma nukeEmAll2(soup : OWNR, pivot : Object, sOut : OWNR, sIn : OWNR, sSIn : OWNR, sSPv : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires sOut == (set s <- soup | outside(s,pivot))
   requires sIn  == (set s <- soup | inside(s,pivot))
   requires sSIn == (set s <- soup | strictlyInside(s,pivot) )
   requires sSPv == (set s <- soup | s == pivot )
    ensures sIn  == sSIn + sSPv
    ensures soup == sIn + sOut
    ensures soup == sOut + sSIn + sSPv
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);
}

lemma nukeEmAll3(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
    ensures nOut + nSIn + nSPv == foup
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);

   var sOut := (set s <- soup | outside(s,pivot) );
   var sSIn := (set s <- soup | strictlyInside(s,pivot) );
   var sSPv := (set s <- soup | s == pivot );
   var sIn  := (set s <- soup | inside(s,pivot) );

   nukeEmAll2(soup, pivot, sOut, sIn, sSIn, sSPv);
   assert sIn == sSIn + sSPv;
   assert soup == sIn + sOut;
   assert soup == sOut + sSIn + sSPv;

   assert nOut == flatten( sOut );
   assert nSIn == flatten( sSIn );
   assert nSPv == flatten( sSPv );

   FLATTEN_SUM4(sOut, sSIn, sSPv, soup);

   assert flatten(soup) == foup;
   assert flatten(sOut + sSIn + sSPv) == foup;
   assert flatten(sOut) + flatten(sSIn) + flatten(sSPv) == foup;
   assert nOut + nSIn + nSPv == foup;
}



lemma nukeEmAll3F(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
    ensures nOut + nSIn + nSPv == foup
{
   assert forall s <- soup :: outside(s,pivot) != inside(s,pivot);
   assert forall s <- soup | inside(s,pivot) :: strictlyInside(s,pivot) != (s == pivot);

   var sOut := (set s <- soup | outside(s,pivot) );
   var sSIn := (set s <- soup | strictlyInside(s,pivot) );
   var sSPv := (set s <- soup | s == pivot );
   var sIn  := (set s <- soup | inside(s,pivot) );

   nukeEmAll2(soup, pivot, sOut, sIn, sSIn, sSPv);
   assert sIn == sSIn + sSPv;
   assert soup == sIn + sOut;
   assert soup == sOut + sSIn + sSPv;

   assert nOut == flatten( sOut );
   assert nSIn == flatten( sSIn );
   assert nSPv == flatten( sSPv );

   FLATTEN_SUM4(sOut, sSIn, sSPv, soup);

   assert flatten(soup) == foup;
   assert flatten(sOut + sSIn + sSPv) == foup;
   assert flatten(sOut) + flatten(sSIn) + flatten(sSPv) == foup;
   assert nOut + nSIn + nSPv == foup;
}



lemma nukeEmAll4F(soup : OWNR, pivot : Object, nOut : OWNR, nSIn : OWNR, nSPv : OWNR, foup : OWNR)
 //verifies on the comnmand line subn 13 sep
   requires forall s <- soup :: s.Ready()
   requires pivot.Ready()
   requires nOut == nukeOutside(soup, pivot)
   requires nSIn == nukeStrictlyInside(soup, pivot)
   requires nSPv == nukeStrictlyPivot(soup, pivot)
   requires foup == flatten( soup )
//    ensures (nOut + nSPv) !! nSIn
    {

    }


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


predicate insidePivot(part : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(part, pivot) && inside(part,owner) }
  //part >= pivot is a selecwtion condition for this case
  //part >= owner should be fucken built the fuck in

lemma LEMMA_insidePivot(part : Object, pivot : Object, owner : Object)
   requires inside(part,owner)
    ensures insidePivot(part,pivot,owner) == inside(part,pivot)
{}

predicate onlyPivot(part : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(part, pivot) && inside(part,owner) &&  inside(pivot, owner) }
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

function flatteninsidePivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | insidePivot(s,pivot,oo) :: oo}


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
   ensures   onlyPivot(part,pivot,owner) ==> (inside(part,pivot) && inside(part,owner))
   ensures exceptPivot(part,pivot,owner) ==> (inside(part,pivot) && inside(part,owner))

   ensures outside(part, pivot) ==> (onlyPivot(part,pivot,owner) == exceptPivot(part,pivot,owner) == false)
   ensures (inside(part,pivot) && inside(part,owner))   ==> (onlyPivot(part,pivot,owner) != (exceptPivot(part,pivot,owner)))
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
  //  ensures not(c.AMFO > b.AMFO)
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

//  ensures left0 <= right
  ensures left1 <= right
//  ensures left0 + left1 <= right
  // ensures left0 + left1 >= right
  // ensures left0 + left1 == right
{}

lemma NUKE_TRICHOTOMY_DICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == nukeStrictlyInside(soup,pivot)
 requires left1 == nukePivotlyOutside(soup,pivot)
 requires right == nuke(soup)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
 {}


lemma NUKE_DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flatteninsidePivot(soup,pivot)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
{}





lemma INSIDE_VS_OUTSIDE(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()
  requires inside(part, whole)
  requires whole != part
   ensures outside(whole,part)
{}


lemma AFMO_ALWAYS_INSIDE(part : Object, whole : Object)
  requires part.Ready()
  requires whole.Ready()

  requires whole in part.AMFO
   ensures inside(part, whole)
{}




  // onlyPibot   --  inside(part, pivot) &&  inside(pivot, owner)
  // exceptPivot  -- inside(part, pivot) && outside(pivot, owner)

  //



lemma EXCEPT_EXCEPT_PIVOT(part : Object, pivot : Object, owner : Object)
  requires part.Ready()
  requires owner.Ready()
  requires pivot.Ready()

  requires owner in part.AMFO
   ensures inside(part, owner)
   ensures ( ||  ( inside(part,pivot) &&  inside(owner,pivot))
             ||  ( inside(part,pivot) && outside(owner,pivot))
             ||  (outside(part,pivot) && outside(owner,pivot)) )

   ensures  not( (outside(part,pivot) &&  inside(owner,pivot)) )

   ensures inside(owner,pivot) <==> (strictlyInside(owner,pivot) || (owner == pivot))

   ensures pivotlyOutside(owner,pivot) <==> (outside(owner,pivot) || (owner == pivot))

   ensures inside(pivot, owner) != outside(pivot, owner)
          //onlyPivot (inside) || exceptPivot (outside)

   ensures       ( inside(part,pivot) &&  inside(owner,pivot) ) <==>
           ( ||  ( inside(part,pivot) && strictlyInside(owner,pivot))
             ||  ( inside(part,pivot) && (owner == pivot) ) )


   ensures ( ||  ( inside(part,pivot) && strictlyInside(owner,pivot))  //fully inside
             ||  ( inside(part,pivot) && pivotlyOutside(owner,pivot))
             ||  (outside(part,pivot) && outside(owner,pivot)) )       //fully outside

   ensures ( ||  (     inside(part,pivot)       && strictlyInside(owner,pivot))  //fully inside
             ||  (  onlyPivot(part,pivot,owner) && pivotlyOutside(owner,pivot))  //is the pivot
             ||  (exceptPivot(part,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
             ||  (    outside(part,pivot)       && outside(owner,pivot)) )       //fully outside


ensures (onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner)) ==> inside(part,pivot)
ensures outside(part,pivot) != (inside(part,pivot) || onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner))
ensures strictlyInside(owner,pivot) != pivotlyOutside(owner,pivot)




   ensures  (inside(part,pivot) && pivotlyOutside(owner,pivot)) ==>
                     (onlyPivot(part,pivot,owner) != exceptPivot(part,pivot,owner))

   ensures  (inside(part,pivot) && strictlyInside(owner,pivot)) ==>
                     (onlyPivot(part,pivot,owner) != exceptPivot(part,pivot,owner))

   ensures (insidePivot(part, pivot, owner)) <==>
                     (onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner))

   ensures (inside(part, pivot)) <==>
                     (onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner))

   ensures insidePivot(part,pivot,owner) == (onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner))

   ensures ownerInsidePivot(part,pivot,owner) ==
                             (ownerOnlyPivot(part,pivot,owner) || ownerExceptPivot(part,pivot,owner))

///ensures (inside(part, pivot) && strictlyInside(owner,pivot))  ?


///ensures strictlyInside(owner,pivot)  ==>  inside(pivot, owner)
///ensures strictlyInside(owner,pivot) <==   inside(pivot, owner)

   ensures strictlyInside(owner,pivot)  ==>  not(inside(pivot, owner))
///ensures strictlyInside(owner,pivot) <==   not(inside(pivot, owner))

   ensures strictlyInside(owner,pivot)  ==> outside(pivot, owner)
///   ensures strictlyInside(owner,pivot) <==  outside(pivot, owner)

///ensures strictlyInside(owner,pivot)  ==> not(outside(pivot, owner))
///ensures strictlyInside(owner,pivot) <==  not(outside(pivot, owner))





///ensures pivotlyOutside(owner,pivot)  ==>  inside(pivot, owner)
   ensures pivotlyOutside(owner,pivot) <==   inside(pivot, owner)

///ensures pivotlyOutside(owner,pivot)  ==>  not(inside(pivot, owner))
///ensures pivotlyOutside(owner,pivot) <==   not(inside(pivot, owner))

///ensures pivotlyOutside(owner,pivot)  ==> outside(pivot, owner)
///ensures pivotlyOutside(owner,pivot) <==  outside(pivot, owner)

///ensures pivotlyOutside(owner,pivot)  ==> not(outside(pivot, owner))
   ensures pivotlyOutside(owner,pivot) <==  not(outside(pivot, owner))



ensures (inside(part,pivot) && pivotlyOutside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(part,pivot,owner)
ensures (inside(part,pivot) && pivotlyOutside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(part,pivot,owner)

ensures (inside(part,pivot) && strictlyInside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(part,pivot,owner)
ensures (inside(part,pivot) && strictlyInside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(part,pivot,owner)


ensures (inside(part,pivot)                                &&  inside(pivot, owner)) ==> onlyPivot(part,pivot,owner)
ensures (inside(part,pivot)                                && outside(pivot, owner)) ==> exceptPivot(part,pivot,owner)



ensures  strictlyInside(owner,pivot) ==> inside(part,pivot)
ensures  strictlyInside(owner,pivot) ==> strictlyInside(part,pivot)




////ensures ( inside(part, pivot) && pivotlyOutside(owner,pivot))  ==>  inside(pivot, owner)
//
////ensures (outside(part, pivot) && pivotlyOutside(owner,pivot))  ==>  outside(pivot, owner)

////ensures (onlyPivot(part,pivot,owner) || exceptPivot(part,pivot,owner)) ==> (pivotlyOutside(owner,pivot))


   ensures  inside(part,pivot)  != outside(part,pivot)
   ensures  inside(owner,pivot) != outside(owner,pivot)
{}

lemma FORALL_AMFO_PART_OWNER(soup : OWNR, sludge : Owner, pivot : Object)
  requires AllReady(soup)
  requires pivot.Ready()

   ensures forall part <- soup, owner <- part.AMFO :: (
    && inside(part,owner)
   // && ((inside(part, pivot) &&  inside(pivot, owner))  ==> outside(owner, pivot) )

    )

   ensures nuke(soup) == (set part <- soup,  owner <- part.AMFO :: owner)
{}


  //  ensures ( ||  (     inside(part,pivot)       && strictlyInside(owner,pivot))  //ownerStrictlyInside
  //            ||  (  onlyPivot(part,pivot,owner) && pivotlyOutside(owner,pivot))  //owner
  //            ||  (exceptPivot(part,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
  //            ||  (    outside(part,pivot)       && outside(owner,pivot)) )       //fully outside

predicate ownerStrictlyInside(part : Object, pivot : Object, owner : Object) : (rv : bool)
  requires part.Ready() && pivot.Ready() && owner.Ready()  requires inside(part, owner)  reads {}
    {strictlyInside(owner,pivot)}
predicate ownerFullyOutside(part : Object, pivot : Object, owner : Object) : (rv : bool)
  requires part.Ready() && pivot.Ready() && owner.Ready()  requires inside(part, owner)  reads {}
    {outside(owner,pivot) &&  outside(part,pivot)}

predicate ownerOnlyPivot(part : Object, pivot : Object, owner : Object) : (rv : bool)
  requires part.Ready() && pivot.Ready() && owner.Ready()  requires inside(part, owner)  reads {}
    {pivotlyOutside(owner,pivot) && onlyPivot(part,pivot,owner)}
predicate ownerExceptPivot(part : Object, pivot : Object, owner : Object) : (rv : bool)
  requires part.Ready() && pivot.Ready() && owner.Ready()  requires inside(part, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(part,pivot,owner)}
predicate ownerInsidePivot(part : Object, pivot : Object, owner : Object) : (rv : bool)
  requires part.Ready() && pivot.Ready() && owner.Ready()  requires inside(part, owner)  reads {}
    {pivotlyOutside(owner,pivot) && insidePivot(part,owner,pivot)}



lemma PART_INSIDE_OWNER(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
  ensures forall part <- soup, owner <- part.AMFO :: inside(part, owner)
  ensures forall part <- soup :: part.Ready()
{}

lemma PART_PIVOT_OBJECT(part : Object, pivot : Object, owner : Object)
  ensures part.Ready() && pivot.Ready() && owner.Ready()  //HERE
//and other transgressions...




function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}
  //yes same as nuke() etc...

function flownerStrictlyInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set part <- soup, owner <- part.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyInside(part,pivot,owner) :: owner}
function flownerFullyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set part <- soup, owner <- part.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerFullyOutside(part,pivot,owner) :: owner}

function flownerOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set part <- soup, owner <- part.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOnlyPivot(part,pivot,owner) :: owner}
function flownerExceptPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set part <- soup, owner <- part.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerExceptPivot(part,pivot,owner) :: owner}
function flownerInsidePivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(soup) && pivot.Ready()
 {set part <- soup, owner <- part.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerInsidePivot(part,pivot,owner) :: owner}


lemma FLOWNER_DISJOINT(soup : OWNR, pivot : Object)
  requires AllReady(soup) && pivot.Ready()
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerFullyOutside(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerFullyOutside(soup,pivot))
   ensures (flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot))
{}


lemma FLOWNER_CONJOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires FIO == FOP + FEP
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerInsidePivot(soup,pivot)

   ensures flownerInsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))

{
   forall part <- soup, owner <- part.AMFO ensures (true) //by
     {
      PART_INSIDE_OWNER(soup,pivot);
      assert inside(part, owner);

      assert (owner in FOP) ==>  (owner in FIO);
      assert (owner in FEP) ==>  (owner in FIO);
      assert (owner in FIO) ==> ((owner in FOP) || (owner in FEP));
      assert (owner in FIO) ==> ((owner in FOP) != (owner in FEP));

      assert ownerOnlyPivot(part,pivot,owner)   ==>  pivotlyOutside(owner,pivot) && onlyPivot(part,pivot,owner);
      assert ownerExceptPivot(part,pivot,owner) ==>  pivotlyOutside(owner,pivot) && exceptPivot(part,pivot,owner);

      assert ownerOnlyPivot(part,pivot,owner)   <==  pivotlyOutside(owner,pivot) && onlyPivot(part,pivot,owner);
      assert ownerExceptPivot(part,pivot,owner) <==  pivotlyOutside(owner,pivot) && exceptPivot(part,pivot,owner);

      assert ownerOnlyPivot(part,pivot,owner)   <==> pivotlyOutside(owner,pivot) && onlyPivot(part,pivot,owner);
      assert ownerExceptPivot(part,pivot,owner) <==> pivotlyOutside(owner,pivot) && exceptPivot(part,pivot,owner);

      assert flownerInsidePivot(soup,pivot) >= FIO;
      assert flownerInsidePivot(soup,pivot) <= FIO;  //ERR

//      assert ownerInsidePivot(part,pivot,owner) == insidePivot(part,owner,pivot);

//      assert flownerInsidePivot(soup,pivot) >= FIO;

     }
}





lemma FLOWNER_JOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(soup) && pivot.Ready()
  requires FIO == FOP + FEP
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerInsidePivot(soup,pivot)

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot)
   ensures                     flownerStrictlyInside(soup,pivot) !! (flownerFullyOutside(soup,pivot) + flownerInsidePivot(soup,pivot))
   ensures flownerInsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}







lemma FLOWER_POWER_H(oo : Owner, ob : Bound, pivot : Object)
 //should be xo & xb??
  requires AllReady(oo)
  requires AllReady(ob)
  requires pivot.Ready()
  requires flatten(oo) >= flatten(ob)
   ensures flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
   ensures flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
   ensures flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)
   ensures flownerInsidePivot(oo,pivot) >= flownerInsidePivot(ob,pivot)
// ensures flownerFullyOutside(oo,pivot) >= flownerFullyOutside(ob,pivot)

   ensures (flownerInsidePivot(oo,pivot) + flownerStrictlyInside(oo,pivot) + flownerFullyOutside(oo,pivot))
      >= (flownerInsidePivot(ob,pivot) + flownerStrictlyInside(ob,pivot) + flownerFullyOutside(ob,pivot))

  {
     FLOWNER_DISJOINT(oo, pivot);
     FLOWNER_DISJOINT(ob, pivot);

  //  ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerFullyOutside(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerFullyOutside(soup,pivot))
  //  ensures (flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot))


  }


lemma FLOWER_POWER_V(ox : Owner, cx : Owner, m : Klon)
  requires AllReady(ox)
  requires AllReady(cx)
  requires klonCalid(m)
  requires m.m.Keys >= ox
  requires cx == mapThruKlon(ox, m)
//   ensures forall i <- flownerStrictlyInside(ox,m.o) :: m.m[i] in flownerStrictlyInside(cx,m.c)
//   ensures forall o <- flownerFullyOutside(ox,m.o)   :: (o == m.m[o]) && (m.m[o] in flownerFullyOutside(cx,m.c))

  {
    assert forall i <- flownerStrictlyInside(ox,m.o) :: (i in flownerAll(ox));
    assert forall i <- flownerStrictlyInside(ox,m.o) :: strictlyInside(i,m.o);
    assert forall i <- flownerAll(ox) | strictlyInside(i,m.o) :: i in flownerStrictlyInside(ox,m.o);
    assert forall i <- flownerStrictlyInside(ox,m.o) :: i in m.m.Keys;
    assert forall i <- flownerStrictlyInside(ox,m.o) :: klonLine(i,m.m[i],m);

    forall part <- ox, owner <- part.AMFO | ownerStrictlyInside(part,m.o,owner)
        ensures (true) //by
///        ensures (ownerStrictlyInside(m.m[part],m.c,m.m[owner])) //by
     {
        assert strictlyInside(part,m.o);
        assert strictlyInside(owner,m.o);
        var cart := m.m[part];
        var cowner := m.m[owner];

        assert klonLine(part,cart,m);
        assert klonGeometry(part,cart,m);
        assert klonIdentity(part,cart,m);
        assert (part != m.o) && (not(outside(part,m.o)));
        assert strictlyInside(cart,m.c);
        assert (part != m.o) && (part != cart);
        assert (cart.owner == mapThruKlon(part.owner, m));
        assert (cart.bound == mapThruKlon(part.bound, m));

        assert klonLine(owner,cowner,m);
        assert klonGeometry(owner,cowner,m);
        assert klonIdentity(owner,cowner,m);
        assert (owner != m.o) && (not(outside(owner,m.o)));
        assert strictlyInside(cowner,m.c);
        assert (owner != m.o) && (owner != cowner);
        assert (cowner.owner == mapThruKlon(owner.owner, m));
        assert (cowner.bound == mapThruKlon(owner.bound, m));

        INSIDE_PARALLEL(part,owner,cart,cowner,m);

        assert inside(cart, cowner);
        assert ownerStrictlyInside(cart,m.c,cowner);
        assert m.m[part] == cart; assert m.m[owner] == cowner;
        assert ownerStrictlyInside(m.m[part],m.c,m.m[owner]);
     }

    // assert forall part <- ox, owner <- part.AMFO ::
    //     ownerStrictlyInside(part,m.o,owner) ==> ownerStrictlyInside(m.m[part],m.m[m.o],m.m[owner]);
    // assert forall part <- ox, owner <- part.AMFO ::
    //     ownerStrictlyInside(part,m.o,owner) ==> ownerStrictlyInside(m.m[part],m.c,m.m[owner]);



//    assert mapThruKlon(flownerStrictlyInside(ox,m.o),m) == flownerStrictlyInside(cx,m.c);

  }



lemma INSIDE_PARALLEL(o0 : Object, o1 : Object, c0 : Object, c1 : Object, m : Klon)
 decreases o0.AMFO
  requires o0.Ready()
  requires o1.Ready()
  requires c0.Ready()
  requires c1.Ready()
  requires o0 in m.m.Keys
  requires o1 in m.m.Keys
  requires klonCalid(m)
  requires c0 == m.m[o0]
  requires c1 == m.m[o1]

  requires strictlyInside(o0,m.o)
  requires strictlyInside(o1,m.o)
  requires inside(o0,o1)

   ensures strictlyInside(c0,m.c)
   ensures strictlyInside(c1,m.c)
   ensures inside(c0,c1)

  {
    if (o0 == o1) { assert o0 == o1;           assert inside(o0,o1);
                    assert m.m[o0] == m.m[o1]; assert inside(c0,c1);
                    return;  }

    assert o0 != o1;     assert c0 != c1;

    assert klonLine(o0,c0,m);
    assert klonIdentity(o0,c0,m);
    assert (o0 != m.o) && (not(outside(o0,m.o)));
    assert strictlyInside(c0,m.c);
    assert (o0 != m.o) && (o0 != c0);
    assert c0.owner == mapThruKlon(o0.owner,m);

    if (o1 in o0.owner)
      {
        assert c1 in c0.owner;
        assert inside(c0,c1);
        return;
      }

    assert inside(o0,o1);
    ThereIsALightThatNeverGoesOut(o0,o1);
    var oo := YouCan'tGetThereFromHereBut(o0,o1);
    INSIDE_PARALLEL(oo,o1,m.m[oo],c1,m);
  }















lemma NUKE_MAPPED_GEQ(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
  requires AllReady(oo)
  requires AllReady(ob)
  requires AllReady(co)
  requires AllReady(cb)
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

//requires boundsOK(oo,ob)
  requires flatten(oo) >= flatten(ob)
//requires forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob)

  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

// ensures boundsOK(co,cb)
// ensures flatten(co) >= flatten(cb)
// ensures forall o <- co :: flatten(o.ownerBound()) >= flatten(cb)
{
  var pivot  := m.o;
  var blivet := m.c;

  assert flatten(oo) >= flatten(ob);
//  assert forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob);

  var noo := nuke(oo);
  var nob := nuke(ob);
  var nco := nuke(co);
  var ncb := nuke(cb);

  FLATTEN_NUKE(oo);
  assert noo == nuke(oo) == flatten(oo);
  FLATTEN_NUKE(ob);
  assert nob == nuke(ob) == flatten(ob);


  var out_oo := nukeOutside(oo,pivot);
  var sin_oo := nukeStrictlyInside(oo,pivot);
  var pvt_oo := nukeStrictlyPivot(oo,pivot);
  nukeEmAll3(oo,pivot,out_oo,sin_oo,pvt_oo,noo);
  assert out_oo + sin_oo + pvt_oo == noo;

//assert (out_oo + pvt_oo) !! sin_oo;


  var out_ob := nukeOutside(ob,pivot);
  var sin_ob := nukeStrictlyInside(ob,pivot);
  var pvt_ob := nukeStrictlyPivot(ob,pivot);
  nukeEmAll3(ob,pivot,out_ob,sin_ob,pvt_ob,nob);
  assert out_ob + sin_ob + pvt_ob == nob;





  FLATTEN_NUKE(co);
  assert nco == nuke(co) == flatten(co);
  FLATTEN_NUKE(cb);
  assert ncb == nuke(cb) == flatten(cb);

  // assert flatten(co) >= flatten(cb);
  // assert forall o <- co :: flatten(o.ownerBound()) >= flatten(cb);

}
