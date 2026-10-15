include "Ownership.dfy"
//include "BROWNE.dfy"

//named cos I didn't know whwat else to call it
//perhaps functions wiht the PIVOT stay here ("Onwership-Pivot")
//functions with the KLON goto Klon-Ownership or **Klon-Pivot**
//the NUKE methods I think are all DEAD - now removed
//the ones w'ere running with now are flowner -> flatten owner  flowner(owners,pivot) -> flattened owners :-)



///Oh SHIT 0 most of the these are WRONG. - notably the ones iwth the PIVOT,
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




predicate outsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) }
  //o >= pivot is a selecwtion condition for this case
  //o >= owner should be fucken built the fuck in

lemma LEMMA_outsidePivot(o : Object, pivot : Object, owner : Object)
   requires inside(o,owner)
    ensures outsidePivot(o,pivot,owner) == inside(o,pivot)
{}




predicate onlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)   reads {}   { inside(o, pivot) && inside(o,owner) &&  inside(pivot, owner) }
predicate exceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool) reads {}   { inside(o, pivot) && inside(o,owner) && outside(pivot, owner) }
   //should we explicitly require owner in o.AMFO  aka o inside owner?
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

function flattenOutsidePivot(soup : OWNR, pivot : Object) : (rv : Owner)
 {set s <- soup, oo <- s.AMFO | outsidePivot(s,pivot,oo) :: oo}

lemma LEMMA_flattenOutsudePivot0(soup : OWNR, pivot : Object, rv : Owner)
  requires forall s <- soup :: s.Ready()
  requires pivot.Ready()
  requires (rv == flattenOutsidePivot(soup, pivot))

   ensures forall r <- rv :: inside(pivot, r)
   ensures forall r <- rv :: exists s <- soup :: onlyPivot(s,pivot,r)
{}


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


lemma TRICHOTOMY_ONLY_EXCEPT(o : Object, pivot : Object, owner : Object)
   ensures   onlyPivot(o,pivot,owner) ==> (inside(o,pivot) && inside(o,owner))
   ensures exceptPivot(o,pivot,owner) ==> (inside(o,pivot) && inside(o,owner))

   ensures outside(o, pivot) ==> (onlyPivot(o,pivot,owner) == exceptPivot(o,pivot,owner) == false)
   ensures (inside(o,pivot) && inside(o,owner))   ==> (onlyPivot(o,pivot,owner) != (exceptPivot(o,pivot,owner)))
{
  assume o.Ready();
  assume pivot.Ready();
  assume owner.Ready();
}


// inside(o, pivot) && inside(o,owner) &&  inside(pivot, owner)
// inside(o, pivot) && inside(o,owner) && outside(pivot, owner)


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


lemma NUKE_DICHOTOMY_TRICHOTOMY(soup : Owner, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
 requires forall s <- soup :: s.Ready()
 requires pivot.Ready()
 requires left0 == flattenExceptPivot(soup,pivot)
 requires left1 == flattenOnlyPivot(soup,pivot)
 requires right == flattenOutsidePivot(soup,pivot)

  ensures left0 <= right
  ensures left1 <= right
  ensures left0 + left1 <= right
  ensures left0 + left1 >= right
  ensures left0 + left1 == right
{}





lemma INSIDE_VS_OUTSIDE(o : Object, whole : Object)
  requires o.Ready()
  requires whole.Ready()
  requires inside(o, whole)
  requires whole != o
   ensures outside(whole,o)
{}


lemma AFMO_ALWAYS_INSIDE(o : Object, whole : Object)
  requires o.Ready()
  requires whole.Ready()

  requires whole in o.AMFO
   ensures inside(o, whole)
{}




  // onlyPibot   --  inside(o, pivot) &&  inside(pivot, owner)
  // exceptPivot  -- inside(o, pivot) && outside(pivot, owner)

  //



lemma EXCEPT_EXCEPT_PIVOT(o : Object, pivot : Object, owner : Object)
  requires o.Ready()
  requires owner.Ready()
  requires pivot.Ready()

  requires owner in o.AMFO
   ensures inside(o, owner)
   ensures ( ||  ( inside(o,pivot) &&  inside(owner,pivot))
             ||  ( inside(o,pivot) && outside(owner,pivot))
             ||  (outside(o,pivot) && outside(owner,pivot)) )

   ensures  not( (outside(o,pivot) &&  inside(owner,pivot)) )

   ensures inside(owner,pivot) <==> (strictlyInside(owner,pivot) || (owner == pivot))

   ensures pivotlyOutside(owner,pivot) <==> (outside(owner,pivot) || (owner == pivot))

   ensures inside(pivot, owner) != outside(pivot, owner)
          //onlyPivot (inside) || exceptPivot (outside)

   ensures       ( inside(o,pivot) &&  inside(owner,pivot) ) <==>
           ( ||  ( inside(o,pivot) && strictlyInside(owner,pivot))
             ||  ( inside(o,pivot) && (owner == pivot) ) )


   ensures ( ||  ( inside(o,pivot) && strictlyInside(owner,pivot))  //fully inside
             ||  ( inside(o,pivot) && pivotlyOutside(owner,pivot))
             ||  (outside(o,pivot) && outside(owner,pivot)) )       //fully outside

   ensures ( ||  (     inside(o,pivot)       && strictlyInside(owner,pivot))  //fully inside
             ||  (  onlyPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //is the pivot
             ||  (exceptPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
             ||  (    outside(o,pivot)       && outside(owner,pivot)) )       //fully outside


ensures (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner)) ==> inside(o,pivot)
ensures outside(o,pivot) != (inside(o,pivot) || onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))
ensures strictlyInside(owner,pivot) != pivotlyOutside(owner,pivot)




   ensures  (inside(o,pivot) && pivotlyOutside(owner,pivot)) ==>
                     (onlyPivot(o,pivot,owner) != exceptPivot(o,pivot,owner))

   ensures  (inside(o,pivot) && strictlyInside(owner,pivot)) ==>
                     (onlyPivot(o,pivot,owner) != exceptPivot(o,pivot,owner))

   ensures (outsidePivot(o, pivot, owner)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures (inside(o, pivot)) <==>
                     (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures outsidePivot(o,pivot,owner) == (onlyPivot(o,pivot,owner) || exceptPivot(o,pivot,owner))

   ensures ownerOutsidePivot(o,pivot,owner) ==
                             (ownerOnlyPivot(o,pivot,owner) || ownerExceptPivot(o,pivot,owner))

///ensures (inside(o, pivot) && strictlyInside(owner,pivot))  ?


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



ensures (inside(o,pivot) && pivotlyOutside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot) && pivotlyOutside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)

ensures (inside(o,pivot) && strictlyInside(owner,pivot) &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot) && strictlyInside(owner,pivot) && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)


ensures (inside(o,pivot)                                &&  inside(pivot, owner)) ==> onlyPivot(o,pivot,owner)
ensures (inside(o,pivot)                                && outside(pivot, owner)) ==> exceptPivot(o,pivot,owner)



ensures  strictlyInside(owner,pivot) ==> inside(o,pivot)
ensures  strictlyInside(owner,pivot) ==> strictlyInside(o,pivot)



   ensures  inside(o,pivot)  != outside(o,pivot)
   ensures  inside(owner,pivot) != outside(owner,pivot)
{}


  //  ensures ( ||  (     inside(o,pivot)       && strictlyInside(owner,pivot))  //ownerStrictlyInside
  //            ||  (  onlyPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //owner
  //            ||  (exceptPivot(o,pivot,owner) && pivotlyOutside(owner,pivot))  //insife from outside not  pivot
  //            ||  (    outside(o,pivot)       && outside(owner,pivot)) )       //fully outside

predicate ownerStrictlyInside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {strictlyInside(owner,pivot)}
predicate ownerInside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {inside(owner,pivot)}
predicate ownerPivotlyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot)}

predicate ownerStrictlyOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(owner,pivot) &&  outside(o,pivot)}
predicate ownerOutside(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(owner,pivot)}
predicate ownerOnlyPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner)}
predicate ownerExceptPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  //most likely this is *pivotlyOutside* to match tthe others.  BUT is that right?3
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)}
predicate ownerOutsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && outsidePivot(o,owner,pivot)}



predicate ownerDisjunctPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
    requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
        {ownerStrictlyOutside(o,pivot,owner) || ownerExceptPivot(o,pivot,owner)}

predicate ownerWithoutPivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {outside(pivot,owner)}

        // (outside(owner,pivot) &&   inside(o, pivot)  && outside(pivot, owner))
        // (outside(owner,pivot) &&  outside(o,pivot))

lemma WITHOUT_PIVOT_0(o : Object, pivot : Object, owner : Object)
  requires o.Ready() && pivot.Ready() && owner.Ready()
  requires inside(o, owner)
   ensures ownerDisjunctPivot(o,pivot,owner) <==> (ownerStrictlyOutside(o,pivot,owner)        || ownerExceptPivot(o,pivot,owner))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> (ownerStrictlyOutside(o,pivot,owner)        || (pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> ((outside(owner,pivot) && outside(o,pivot)) || ownerExceptPivot(o,pivot,owner))
   ensures ownerDisjunctPivot(o,pivot,owner) <==> ((outside(owner,pivot) && outside(o,pivot)) || (pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)))

   ensures ownerStrictlyOutside(o,pivot,owner) <==> (outside(owner,pivot) && outside(o,pivot))

   ensures ownerExceptPivot(o,pivot,owner)     <==> (pivotlyOutside(owner,pivot)                  && exceptPivot(o,pivot,owner))
   ensures ownerExceptPivot(o,pivot,owner)     <==> (((outside(owner,pivot) || (owner == pivot))) && exceptPivot(o,pivot,owner))

   ensures exceptPivot(o,pivot,owner) <==>  (inside(o, pivot) && inside(o,owner) && outside(pivot, owner))
   ensures exceptPivot(o,pivot,owner) <==>  (inside(o, pivot) &&                    outside(pivot, owner))

   ensures ownerExceptPivot(o,pivot,owner)     <==> (((outside(owner,pivot) || (owner == pivot))) &&  (inside(o, pivot) && outside(pivot, owner)))

   ensures ownerDisjunctPivot(o,pivot,owner) <==>
          ( ||  (outside(owner,pivot)                      && outside(o,pivot))
            || ((outside(owner,pivot) || (owner == pivot)) && (inside(o,pivot) && outside(pivot,owner))) )
     {}


lemma WITHOUT_PIVOT_1(soup : OWNR, pivot : Object)
    requires AllReady(flatten(soup)) && pivot.Ready()
     ensures flownerDisjunctPivot(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerExceptPivot(soup,pivot)
{}


lemma PART_INSIDE_OWNER(soup : OWNR, pivot : Object)
//sort of an assertion that rememnbers parts are inside their owners
//
// when we iterate throught the "soup"  an the input list of stuff
// we'll nested-co-iterate (or is that cosubiterate? or subcoiterater??)
// therough all the owners of that part
// well this makes it easy to say that in a way that seems to get reliably
// into the middle or rhs of foralls or set comps.
  requires AllReady(flatten(soup)) && pivot.Ready()
  ensures forall o <- soup, owner <- o.AMFO :: inside(o, owner)
  ensures forall o <- soup :: o.Ready()
  ensures forall o <- soup, owner <- o.AMFO :: owner in flownerAll(soup)
{}


//  predicate root(root: Object, soup : Owner)


function flownerAll(soup : Owner) : OWNR {assume forall s <- soup :: s.Ready(); (set o <- soup, oo <- o.AMFO :: oo)}
  //yes same as nuke() etc...

function flownerStrictlyInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyInside(o,pivot,owner) :: owner}
function flownerStrictlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyOutside(o,pivot,owner) :: owner}

function flownerInside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerInside(o,pivot,owner) :: owner}
function flownerOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutside(o,pivot,owner) :: owner}

function flownerOnlyPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOnlyPivot(o,pivot,owner) :: owner}
function flownerExceptPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerExceptPivot(o,pivot,owner) :: owner}
function flownerOutsidePivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutsidePivot(o,pivot,owner) :: owner}


function flownerDisjunctPivot(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerDisjunctPivot(o,pivot,owner) :: owner}





lemma XFLOWNER_STRICTLY_OUTSIDE_THRU_KLON2(soup : Owner, left : Owner, rite : Owner, m : Klon)
//doesn't currently work!!!!!
 ///see MAP_THRU_KLON currently in Klon.dfy
  requires AllReady(flatten(soup))
  requires AllReady(flatten(left))
  requires AllReady(flatten(rite))
  requires klonCalid(m)
  requires soup <= m.m.Keys
  requires left == flownerStrictlyOutside(soup, m.o)
  requires rite == flownerStrictlyOutside(mapThruKlon(soup, m), m.c)
   ensures left == rite //Err

{
  var pivot := m.o;
  assert left == flownerStrictlyOutside(soup, m.o);
  assert left == (set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerOutside(o,pivot,owner) :: owner);
  assert left == (set o <- soup, owner <- o.AMFO | assert inside(o,owner); ownerOutside(o,pivot,owner) :: owner);
//  assert forall o <- soup, owner <- o.AMFO ::inside(o,owner); // Err??
  assert left == (set o <- soup, owner <- o.AMFO | ownerOutside(o,pivot,owner) :: owner);
  assert left == (set o <- soup, owner <- o.AMFO | outside(owner,pivot) :: owner);  //Err
  assert flatten(soup) == (set o <- soup, owner <- o.AMFO :: owner); //Err
  assert left == (set owner <- flatten(soup) | outside(owner,pivot) :: owner); //Err?


  var blivet := m.c;
  var coup := mapThruKlon(soup, m);
  assert rite == flownerStrictlyOutside(coup, m.c);
  assert rite == (set o <- coup, owner <- o.AMFO | PART_INSIDE_OWNER(coup,blivet); ownerOutside(o,blivet,owner) :: owner);   //Err
  assert rite == (set o <- coup, owner <- o.AMFO | assert inside(o,owner); ownerOutside(o,blivet,owner) :: owner);
  assert forall o <- coup, owner <- o.AMFO :: inside(o,owner);
  assert rite == (set o <- coup, owner <- o.AMFO | ownerOutside(o,blivet,owner) :: owner);
  assert rite == (set o <- coup, owner <- o.AMFO | outside(owner,blivet) :: owner);

}


 function flownerEverythingOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
 { flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot) }
 function flownerPivotlyOutside(soup : OWNR, pivot : Object)  : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
   {set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner}

lemma FLOWNER_EVERYTHING_OUTSIDE(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerPivotlyOutside(soup,pivot)
{}
//could merge these two, but thiss lets us be more specific when calling them,
lemma FLOWNER_EVERYTHING_EVERYTHING(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot)
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_EVERYTHING_EVERYWHERE(soup : OWNR, pivot : Object, FEO : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FEO == flownerEverythingOutside(soup,pivot)
  requires FFO == flownerStrictlyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures FEO == FFO + FOP + FEP
   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{}

lemma FLOWNER_ALL_EVERYTHING(soup : OWNR, pivot : Object, ALL : Owner, SIN : Owner, FFO : Owner, FOP : Owner, FEP : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires ALL == flownerAll(soup)
  requires SIN == flownerStrictlyInside(soup,pivot)
  requires FFO == flownerStrictlyOutside(soup,pivot)
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
   ensures ALL == SIN + FFO + FOP + FEP
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
  FLOWNER_ALL_ALL(soup, pivot);
}


lemma FLOWNER_DISJOINT(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOutsidePivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerOutsidePivot(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! flownerStrictlyOutside(soup,pivot)
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerStrictlyOutside(soup,pivot))
   ensures flownerStrictlyInside(soup,pivot) !! (flownerOutsidePivot(soup,pivot) + flownerStrictlyOutside(soup,pivot))
{}


lemma FLOWNER_CONJOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
 //seems to be doing a fuckload of work to get fOutP == fOnlyP + fExceptP
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerOutsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures flownerOutsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
{
   forall o <- soup, owner <- o.AMFO ensures (true) //by
     {
      PART_INSIDE_OWNER(soup,pivot);
      assert inside(o, owner);

      assert (owner in FOP) ==>  (owner in FIO);
      assert (owner in FEP) ==>  (owner in FIO);
      assert (owner in FIO) ==> ((owner in FOP) || (owner in FEP));
      assert (owner in FIO) ==> ((owner in FOP) != (owner in FEP));

      assert ownerOnlyPivot(o,pivot,owner)   ==>  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) ==>  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==  pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==  pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert ownerOnlyPivot(o,pivot,owner)   <==> pivotlyOutside(owner,pivot) && onlyPivot(o,pivot,owner);
      assert ownerExceptPivot(o,pivot,owner) <==> pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner);

      assert flownerOutsidePivot(soup,pivot) >= FIO;
      assert flownerOutsidePivot(soup,pivot) <= FIO;  //ERR

//      assert ownerOutsidePivot(o,pivot,owner) == outsidePivot(o,owner,pivot);

//      assert flownerOutsidePivot(soup,pivot) >= FIO;

     }
}




lemma FLOWNER_JOINT(soup : OWNR, pivot : Object, FIO : Owner, FOP : Owner, FEP : Owner)
 //delete in favour of FLOWNER_ALL_ALL?
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FOP == flownerOnlyPivot(soup,pivot)
  requires FEP == flownerExceptPivot(soup,pivot)
  requires FIO == flownerOutsidePivot(soup,pivot)
   ensures FIO == FOP + FEP
   ensures FOP !! FEP
{}



lemma FLOWNER_JOINT2(soup : OWNR, pivot : Object, FA : Owner, FB : Owner, FC : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires FA == flownerAll(soup)
  requires FB == flownerStrictlyInside(soup,pivot)
  requires FC == flownerPivotlyOutside(soup,pivot)
   ensures FA == FB + FC
   ensures FB !! FC
{}


lemma FLOWNER_JOINT2x2(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerStrictlyInside(soup0,pivot) !! flownerPivotlyOutside(soup0,pivot)
   ensures flownerStrictlyInside(soup1,pivot) !! flownerPivotlyOutside(soup1,pivot)
//   ensures flownerStrictlyInside(soup0,pivot) >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerPivotlyOutside(soup0,pivot) >= flownerPivotlyOutside(soup1,pivot)
//   ensures (flownerStrictlyInside(soup0,pivot) + flownerStrictlyInside(soup1,pivot))
//    !! (flownerStrictlyInside(soup0,pivot) + flownerPivotlyOutside(soup1,pivot))
{}


lemma flownerAll_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //given the input is stupidlyHappy (close to flatten(soup0) >= close to(soup1)
 //then all the "partials" are at MONOTNOIC
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()

//  requires stupidlyHappy(soup0, soup1, pivot)

  requires flownerAll(soup0) >= flownerAll(soup1)
  requires flatten(soup0) >= flatten(soup1)

//requires flownerAll(soup0) >= flownerAll(sup1)
//  requires flatten(soup0) >= flatten(soup1)

   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
   ensures flownerStrictlyOutside(soup0,pivot)   >= flownerStrictlyOutside(soup1,pivot)
   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
   ensures flownerOutsidePivot(soup0,pivot)      >= flownerOutsidePivot(soup1,pivot)
   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)

   ensures flownerDisjunctPivot(soup0,pivot)     >= flownerDisjunctPivot(soup1,pivot)
{
    flownerStrictlyInside_MONOTONIC(soup0, soup1, pivot);
    flownerStrictlyOutside_MONOTONIC(soup0, soup1, pivot);
    flownerOnlyPivot_MONOTONIC(soup0, soup1, pivot);
    flownerExceptPivot_MONOTONIC(soup0, soup1, pivot);
    flownerOutsidePivot_MONOTONIC(soup0, soup1, pivot);
    flownerPivotlyOutside_MONOTONIC(soup0, soup1, pivot);

}





lemma flownerAll_SONOMONIC(xo : Owner, xo_sp : FlownerSplit, xb : Owner, xb_sp : FlownerSplit, pivot : Object)
  requires AllReady(flatten(xo))
  requires AllReady(flatten(xb))
  requires pivot.Ready()
  requires flownerSplitOK(xo,pivot,xo_sp)
  requires flownerSplitOK(xb,pivot,xb_sp)
  requires true  //wjztaever upi wanmt tp wrote  <== obviously too tired to continue

  requires (xb_sp.fSin >= xb_sp.fSin)
  requires (xb_sp.fOut >= xb_sp.fOut)
  requires (xb_sp.fPvt >= xb_sp.fPvt)
  requires (xb_sp.fXpt >= xb_sp.fXpt)

   ensures (xb_sp.fAll >= xb_sp.fAll)
//   ensures stupidlyHappy(xo, xb, pivot)
{
  UNPACK_flownerSplitOK(xo,pivot,xo_sp);
  UNPACK_flownerSplitOK(xb,pivot,xb_sp);
}


lemma flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(xo : Owner, xo_sp : FlownerSplit, xb : Owner, xb_sp : FlownerSplit, pivot : Object)
  requires AllReady(flatten(xo))
  requires AllReady(flatten(xb))
  requires pivot.Ready()
  requires (forall r <- xb | outside(r,pivot) :: exists s <- xo :: outside(s,pivot) && inside(s,r))
  requires (forall o <- xo :: flatten(o.ownerBound()) >= flatten(xb))

  requires flownerSplitOK(xo,pivot,xo_sp)
  requires flownerSplitOK(xb,pivot,xb_sp)
  requires true  //wjztaever upi wanmt tp wrote  <== obviously too tired to continue

  requires (xo_sp.fSin >= xb_sp.fSin)
  requires (xo_sp.fOut >= xb_sp.fOut)
  requires (xo_sp.fPvt >= xb_sp.fPvt)
  requires (xo_sp.fXpt >= xb_sp.fXpt)

   ensures (xo_sp.fAll >= xb_sp.fAll)
   ensures stupidlyHappy(xo, xb, pivot)
{
  UNPACK_flownerSplitOK(xo,pivot,xo_sp);
  UNPACK_flownerSplitOK(xb,pivot,xb_sp);
  assert (forall r <- xb | outside(r,pivot) :: exists s <- xo :: outside(s,pivot) && inside(s,r));
  assert (xo_sp.fAll >= xb_sp.fAll);
  assert (flatten(xo) >= flatten(xb));

  assert stupidlyHappy(xo, xb, pivot);
  assert boundsOK(xo, xb);

}



lemma FLOWNER_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
  //  ensures flownerStrictlyOutside(soup0,pivot)      >= flownerStrictlyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerOutsidePivot(soup0,pivot)       >= flownerOutsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)
{
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)
   == (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); ownerPivotlyOutside(o,pivot,owner) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup1,pivot)
   == (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerAll(soup0) >= flownerAll(soup1);
 assert (set owner <- flownerAll(soup0) | PART_INSIDE_OWNER(soup0,pivot); pivotlyOutside(owner,pivot) :: owner)
     >= (set owner <- flownerAll(soup1) | PART_INSIDE_OWNER(soup1,pivot); pivotlyOutside(owner,pivot) :: owner);
 assert flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot);
}

lemma flownerPivotlyOutside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //why is this here.  didn't have a body :-(
 //verifié 24Sept2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
//   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
//   ensures flownerStrictlyOutside(soup0,pivot)      >= flownerStrictlyOutside(soup1,pivot)
//   ensures flownerOnlyPivot(soup0,pivot)         >= flownerOnlyPivot(soup1,pivot)
//   ensures flownerExceptPivot(soup0,pivot)       >= flownerExceptPivot(soup1,pivot)
//   ensures flownerOutsidePivot(soup0,pivot)       >= flownerOutsidePivot(soup1,pivot)
//   ensures flownerEverythingOutside(soup0,pivot) >= flownerEverythingOutside(soup1,pivot)
   ensures flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot)
{
FLOWNER_MONOTONIC(soup0,soup1,pivot);
}

lemma flownerStrictlyInside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
 //why is this here.  didn't have a body :-(
 //verifié 24Sept2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot)
   {
    FLOWNER_MONOTONIC(soup0,soup1,pivot);
    assert flownerPivotlyOutside(soup0,pivot)    >= flownerPivotlyOutside(soup1,pivot);

    FLOWNER_ALL_ALL(soup0, pivot);
    assert flownerStrictlyInside(soup0,pivot) == flownerAll(soup0) - flownerPivotlyOutside(soup0,pivot);
    FLOWNER_ALL_ALL(soup1, pivot);
    assert flownerStrictlyInside(soup1,pivot) == flownerAll(soup1) - flownerPivotlyOutside(soup1,pivot);

    assert flownerStrictlyInside(soup0,pivot)    >= flownerStrictlyInside(soup1,pivot);
   }

lemma flownerOnlyPivot_RESULT(soup : Owner, pivot : Object, rv : Owner)
//verified 23Sep2026 - compare ONLY_PIVOT
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerOnlyPivot(soup,pivot) == rv
   ensures (pivot  in flownerAll(soup))  ==> (rv == pivot.AMFO)
   ensures (pivot !in flownerAll(soup)) ==> (rv == {})
   {
   assert rv == flownerOnlyPivot(soup, pivot);
FLOWNER_SHORTCUT_OnlyPivot(soup, pivot, rv);
   assert rv == shortcutOnlyPivot(soup, pivot);
 LEMMA_shortcutOnlyPivot1(soup, pivot, rv);
   }

lemma {:timeLimit 120}  flownerExceptPivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
////verified 25Sep2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flatten(soup0) >= flatten(soup1)
//requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerExceptPivot(soup0,pivot)  >= flownerExceptPivot(soup1,pivot)
{
  var rv0 := flownerExceptPivot(soup0,pivot);
  var rv1 := flownerExceptPivot(soup1,pivot);
  assert  flownerAll(soup0) >= flownerAll(soup1);
  assert rv0 == (set o <- soup0, owner <- o.AMFO | PART_INSIDE_OWNER(soup0,pivot); ownerExceptPivot(o,pivot,owner) :: owner);
  assert rv1 == (set o <- soup1, owner <- o.AMFO | PART_INSIDE_OWNER(soup1,pivot); ownerExceptPivot(o,pivot,owner) :: owner);
  assert rv0 >= rv1;
  assert flownerExceptPivot(soup0,pivot)     >= flownerExceptPivot(soup1,pivot);
}



lemma flownerOnlyPivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
////verified 23Sep2026
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerOnlyPivot(soup0,pivot)  >= flownerOnlyPivot(soup1,pivot)
{
  var rv0 := flownerOnlyPivot(soup0,pivot);
  flownerOnlyPivot_RESULT(soup0,pivot,rv0);
  var rv1 := flownerOnlyPivot(soup1,pivot);
  flownerOnlyPivot_RESULT(soup1,pivot,rv1);
  assert flownerOnlyPivot(soup0,pivot)     >= flownerOnlyPivot(soup1,pivot);
}


lemma flownerOutsidePivot_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
//feelin' proovie!
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
   ensures flownerOutsidePivot(soup0,pivot)  >= flownerOutsidePivot(soup1,pivot)
{
  var rv0 := flownerOutsidePivot(soup0,pivot);
  var rv1 := flownerOutsidePivot(soup1,pivot);
  var op0 := flownerOnlyPivot(soup0,pivot);
  var op1 := flownerOnlyPivot(soup1,pivot);
  var ep0 := flownerExceptPivot(soup0,pivot);
  var ep1 := flownerExceptPivot(soup1,pivot);

  flownerOnlyPivot_MONOTONIC(soup0,soup1,pivot);
  flownerExceptPivot_MONOTONIC(soup0,soup1,pivot);
  FLOWNER_CONJOINT(soup0,pivot,rv0,op0,ep0);
  FLOWNER_CONJOINT(soup1,pivot,rv1,op1,ep1);
  assert rv0 >= rv1;
  assert flownerOutsidePivot(soup0,pivot)     >= flownerOutsidePivot(soup1,pivot);
}


lemma EXISTENTIAL_FLATTEN(soup : Owner)
  requires AllReady(soup)
    ensures forall o <- flatten(soup) :: exists s <- soup :: o in s.AMFO
    ensures forall o <- flatten(soup) :: exists s <- soup :: inside(s,o)
{}





function roots(soup0 : Owner, soup1 : Owner) : Owner {soup0 + soup1}

predicate stupidlyHappy(soup0 : Owner, soup1 : Owner, pivot : Object) : (rv : bool)
// owners "outside" the bound must still be "outside" the owner
//
//  this makes it easier to prove preservation of ownership
//  and may make thigns more visible locally, but I think can
//  likely be avoided if we no longer't distinguish between
//  strictlyOutside and
//
// I'm stupidly happy
// With idiot grin
// I'm stupidly happy
// It's surely a sin
// --- Stupidly Happy, XTC
//
 //  requires flatten(soup0) >= flatten(soup1)
   {
      //  && (flatten(soup0) >= flatten(soup1)) //  this clause deleted 13Oct2026
        && (forall r <- soup1 | outside(r,pivot) :: exists s <- soup0 :: outside(s,pivot) && inside(s,r))
   }






//TWO WAYS TO LIVE / DUMB WAYS TO DIE
// a_ - stupidlyBigger - so a version with the extra constraints
// .  a_ almost ertianly theright thing to do IF otherwise esetaboishign boundsOK needs anuythigh other than >=
// b_ - see if I can tweak the definitino of nmonotonicity
//     or rather tweak the underlying deifnfiotns of the things I'm asking are monontonicl
//  so the jhust don't go dowbn - e.,g.
// the proboem (I think) is that the damns things can be reahavle from the soup,
///  ARGH I'm losing it!!!
// the basic problem is that directly inside soup1's "initial soup"
// aren't from soup0's  soup - there's there, and still should be captured.
///
/// perhaps just talk about things reachable from without the pibot
///**WITHOUT HAVIN TO BE IN A DIRECT WSOUP AT ALL/

lemma EXISTENTIAL_FUCKED(soup0 : Owner, soup1 : Owner, s : Object, pivot : Object, owner : Object, o : Object)
 //any ideas about wtf this does?
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flatten(soup0) >= flatten(soup1)


  requires stupidlyHappy(soup0, soup1, pivot)


  requires s in soup1
   ensures s in flatten(soup0)
  requires outside(s,pivot)
   ensures outside(s,pivot)

  requires owner in s.AMFO
   ensures inside(s,owner)
  requires owner in flatten(soup1)
   ensures owner in flatten(soup0)
  requires outside(owner,pivot)
   ensures outside(owner,pivot)

  requires s in o.AMFO

   ensures inside(o,s)
  requires o in soup0
   ensures o in flatten(soup0)
  // requires outside(o,pivot) //needs this to verify! --- either that or stupidlyHappy??
  //  ensures outside(o,pivot)

   requires forall q <- flatten(soup0) :: q.Ready()

  requires ownerStrictlyOutside(s,pivot,owner)
// ensures ownerStrictlyOutside(o,pivot,owner)   //neds o outside pivot to verify
   ensures (exists o <- soup0 :: (outside(o,pivot) && inside(o,s)))
   ensures (exists o <- soup0 |  (outside(o,pivot) && inside(o,s)) :: ownerStrictlyOutside(o,pivot,owner))   //but stupidlyHappy is enough if reframed comme ca


  {
    assert stupidlyHappy(soup0, soup1, pivot);
    assert (forall s <- soup1 | outside(s,pivot) :: exists o <- soup0 :: outside(o,pivot) && inside(o,s));
    assert s in soup1; assert outside(s,pivot);
    assert exists o <- soup0  :: outside(o,pivot) && inside(o,s);
    assert exists o <- soup0  :: (outside(o,pivot) && inside(o,s)) ==> ownerStrictlyOutside(o,pivot,owner);

    assert (forall r <- soup1 | outside(r,pivot) :: exists s <- soup0 :: outside(s,pivot) && inside(s,r));
    assert (exists o <- soup0  :: (outside(o,pivot) && inside(o,s)) ==> ownerStrictlyOutside(o,pivot,owner));
    assert (exists o <- soup0 | (outside(o,pivot) && inside(o,s)) :: ownerStrictlyOutside(o,pivot,owner));

  }




lemma ownerStrictlyOutside_OUTSIDE(o : Object, pivot : Object, owner : Object)
  requires o.Ready() && pivot.Ready() && owner.Ready()
  requires inside(o, owner)
  requires ownerStrictlyOutside(o,pivot,owner)
   ensures outside(owner,pivot)
   ensures outside(o,pivot)
{}



lemma {:timeLimit 120} flownerStrictlyOutside_MONOTONIC(soup0 : OWNR, soup1 : OWNR, pivot : Object)
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready()
  requires flownerAll(soup0) >= flownerAll(soup1)
  requires flatten(soup0) >= flatten(soup1)

  requires stupidlyHappy(soup0, soup1, pivot)


//X   ensures flownerStrictlyOutside(soup0,pivot)  >= flownerStrictlyOutside(soup1,pivot)
{
   var rv0 := flownerStrictlyOutside(soup0,pivot);
   flownerStrictlyOutside_RESULT(soup0,pivot,rv0);
   assert forall owner <- rv0 :: exists o <- soup0 | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup0,pivot);
           && outside(o,pivot)
           && ownerStrictlyOutside(o,pivot,owner));

   var rv1 := flownerStrictlyOutside(soup1,pivot);
   flownerStrictlyOutside_RESULT(soup1,pivot,rv1);
   assert forall owner <- rv1 :: exists s <- soup1 | owner in s.AMFO ::
          (PART_INSIDE_OWNER(soup1,pivot);  ownerStrictlyOutside(s,pivot,owner));

   forall owner <- rv1 ensures (exists o <- soup0 | owner in o.AMFO ::
       (PART_INSIDE_OWNER(soup0,pivot);
          assert o.Ready();
          assert pivot.Ready();
          assert owner.Ready();
          assert inside(o, owner);
         ownerStrictlyOutside(o,pivot,owner)))  //by
     {
        assert exists s <- soup1 | owner in s.AMFO ::
          (PART_INSIDE_OWNER(soup1,pivot);
          && outside(s,pivot)
          && ownerStrictlyOutside(s,pivot,owner));
        var s :| (s in soup1) && (owner in s.AMFO) && outside(s,pivot) && (PART_INSIDE_OWNER(soup1,pivot);  ownerStrictlyOutside(s,pivot,owner));
        assert flatten(soup0) >= flatten(soup1);
        assert exists o <- soup0 :: s in o.AMFO &&
          (PART_INSIDE_OWNER(soup0,pivot);  ownerStrictlyOutside(o,pivot,owner));
        var o :| (o in soup0) && (s in o.AMFO) &&
          (PART_INSIDE_OWNER(soup0,pivot);  ownerStrictlyOutside(o,pivot,owner));
        assert ownerStrictlyOutside(o,pivot,owner);
        assert outside(o,pivot);


  assert AllReady(flatten(soup0)) && AllReady(flatten(soup1)) && pivot.Ready();
  assert flatten(soup0) >= flatten(soup1);
  assert s in soup1;
  assert outside(s,pivot);
  assert owner in s.AMFO;
  assert owner in flatten(soup1);
  assert outside(owner,pivot);
  assert s in o.AMFO;
  assert o in soup0;
  assert outside(o,pivot);
  assert forall q <- flatten(soup0) :: q.Ready();
  assert ownerStrictlyOutside(s,pivot,owner);

           EXISTENTIAL_FUCKED(soup0, soup1, s, pivot, owner, o);
     }
}






function flattenTwiceStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set s <- flatten(soup), t <- flatten(soup) | inside(s,t) && outside(t,pivot) &&  outside(s,pivot) :: t)
  }

//flownerExistentialStictlyOutsiode
function flownerTwiceStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set s <- flownerAll(soup), t <- flownerAll(soup) | inside(s,t) && outside(t,pivot) && outside(s,pivot) :: t)
  }

function flownerExistentialStictlyOutside(soup : OWNR, pivot : Object) : (rv : Owner)
    requires AllReady(flatten(soup)) && pivot.Ready()
  {
    (set t <- flownerAll(soup) | (exists s <- flownerAll(soup) :: inside(s,t) && outside(t,pivot) &&  outside(s,pivot)) :: t)
  }

// lemma flattenExistentialStictlyOutside_RESULT(soup : OWNR, pivot : Object, rv : Owner, foup : Owner, zoup : Owner)
//     requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
//     requires rv == flownerStrictlyOutside(soup, pivot)
//     requires foup == flownerAll(soup)
//     requires zoup == (set o <- soup, owner <- o.AMFO :: o) ////HERE HERE HERE HERE HERE
// //     ensures rv == flattenTwiceStictlyOutside(soup, pivot)
// //     ensures rv == flownerTwiceStictlyOutside(soup, pivot)
//     ensures rv == flownerExistentialStictlyOutside(soup, pivot)
//      {
//
//      }

lemma flownerStrictlyOutside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyOutside(soup,pivot) == rv
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyOutside(o,pivot,owner))
{}



lemma flownerStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!  -- coould tweak to take a split I guess
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv
   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{}



lemma SLUTTY(soup : Owner, pivot : Object, rv : Owner, other : Object, m : Klon)
 //verfies!!!
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
  requires klonCalid(m)
   requires pivot == m.o

   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv

   requires other in flatten(soup)
   requires strictlyInside(other,pivot)
    ensures other in rv

   requires flatten(soup) <= m.m.Keys
{
 flownerStrictlyInside_RESULT(soup,pivot,rv);
 assert forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv;
}


// forall o1 <- soup1, owner1 <- o1.AMFO | outsidePivot(o1,pivot,owner1) ensures owner1 in flownerAll(soup0) {}

// forall s1 <- soup1, owner1 <- s1.AMFO | outsidePivot(s1,pivot,owner1) ensures owner1 in flownerOutsidePivot(soup0,pivot) {}

// assert forall s1 <- soup1,5 owner1 <- s1.AMFO | outsidePivot(s1,pivot,owner1) :: owner1 in flownerOutsidePivot(soup0,pivot);

// assert forall s1 <- soup1, owner1 <- s1.AMFO | ownerPivotlyOutside(s1,pivot,owner1) :: owner1 in flownerPivotlyOutside(soup0,pivot);
//
//
// assert forall o1 <- soup1, owner1 <- o1.AMFO ::
//    exists o0 <- soup0, owner0 <- o0.AMFO |
//    outsidePivot(o1,pivot,owner1) ::  owner1 in flownerAll(soup0);
//

// assert forall owner1 <- flownerAll(soup1) :: exists s0 <- soup0 | owner1 in s0.AMFO ::
//        forall s1 <- soup1 :: (outsidePivot(s1,pivot,owner1) ==> outsidePivot(s0,pivot,owner1));
//
// assert forall s1 <- soup1, owner1 <- s1.AMFO :: owner1 in flownerAll(soup0);
//
// assert forall s1 <- soup1, owner1 <- s1.AMFO :: owner1 in flownerAll(soup0);


// assert exists s <- soup0, owner1 <- s.AMFO ::



//    assert forall o <- flownerAll(soup1) :: (o in flownerOnlyPivot(soup1,pivot))         ==> (o in flownerOnlyPivot(soup0,pivot));
    // // assert forall o <- flownerAll(soup1) :: (o in flownerExceptPivot(soup1,pivot))       ==> (o in flownerExceptPivot(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerOutsidePivot(soup1,pivot))       ==> (o in flownerOutsidePivot(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerEverythingOutside(soup1,pivot)) ==> (o in flownerEverythingOutside(soup0,pivot));
    // assert forall o <- flownerAll(soup1) :: (o in flownerPivotlyOutside(soup1,pivot))    ==> (o in flownerPivotlyOutside(soup0,pivot));



type FlownerSplit = f : preFlownerSplit | f.Valid() witness * //ARGH ARGH can't make a witness with a nonnill Object field in Dafny!


datatype preFlownerSplit = preFlownerSplit(
    soup : Owner,
    pivot : Object,
    fAll : Owner,
    fSin : Owner,
    fOut : Owner,
    fPvt : Owner,
    fXpt : Owner
  ) {
    predicate Valid() {
     && (pivot.Ready())
     && (AllReady(flatten(soup)))
     && (fAll == flownerAll(soup))
     && (fSin == flownerStrictlyInside(soup,pivot))
     && (fOut == flownerStrictlyOutside(soup,pivot))
     && (fPvt == flownerOnlyPivot(soup,pivot))
     && (fXpt == flownerExceptPivot(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerEverythingOutside(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerPivotlyOutside(soup,pivot))
     && (fAll == fSin + fOut + fPvt + fXpt)

     && (fSin !! (fOut + fPvt + fXpt))

    }
  }




predicate flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()
  {
      && (split.soup == soup)
      && (split.pivot == pivot)
      && (split.Valid())
  }


lemma UNPACK_flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires flownerSplitOK(soup,pivot,split)

   ensures (split.fAll == flownerAll(soup))
   ensures (split.fAll == flatten(soup))
   ensures (split.fSin == flownerStrictlyInside(soup,pivot))
   ensures (split.fOut == flownerStrictlyOutside(soup,pivot))
   ensures (split.fPvt == flownerOnlyPivot(soup,pivot))
   ensures (split.fXpt == flownerExceptPivot(soup,pivot))
   ensures ((split.fOut + split.fPvt + split.fXpt) == flownerEverythingOutside(soup,pivot))
   ensures ((split.fOut + split.fPvt + split.fXpt) == flownerPivotlyOutside(soup,pivot))
   ensures (split.fAll == split.fSin + split.fOut + split.fPvt + split.fXpt)
   ensures split.fSin !! (split.fOut + split.fPvt + split.fXpt)

   ensures forall o <- (split.fOut) :: outside(o,pivot)
   ensures forall o <- (split.fXpt) :: outside(o,pivot)
   ensures forall o <- (split.fOut+split.fXpt) :: outside(o,pivot)
{}



lemma FLOWNER_ALL_ALL(soup : OWNR, pivot : Object)
//can be replaced with split.Valid()
 //verified 20 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) + flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot)
   ensures flownerOutsidePivot(soup,pivot) == (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))

   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerStrictlyOutside(soup,pivot) + (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot))
   ensures flownerAll(soup) == flownerStrictlyInside(soup,pivot) +  flownerPivotlyOutside(soup,pivot)

   ensures                     flownerStrictlyInside(soup,pivot) !! (flownerStrictlyOutside(soup,pivot) + flownerOutsidePivot(soup,pivot))
   ensures                     flownerStrictlyInside(soup,pivot) !! flownerPivotlyOutside(soup,pivot)

   ensures flownerEverythingOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
   ensures flownerPivotlyOutside(soup,pivot) == flownerStrictlyOutside(soup,pivot) + flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot)
{}


function flownerSplit(os : Owner,pivot : Object) : (rv : FlownerSplit)
  requires AllReady(flatten(os)) && pivot.Ready()
   ensures flownerSplitOK(os, pivot, rv)
 {
  var fAll := flownerAll(os);
  var fSin := flownerStrictlyInside(os,pivot);
  var fOut := flownerStrictlyOutside(os,pivot);
  var fPvt := flownerOnlyPivot(os,pivot);
  var fXpt := flownerExceptPivot(os,pivot);
  FLOWNER_ALL_ALL(os,pivot);
  var fs := preFlownerSplit(os,pivot,fAll,fSin,fOut,fPvt,fXpt);
  assert fs.Valid();
  fs
 }

// {:timeLimit 30}
function splitThruKlon(soup : OWNR, split : FlownerSplit, m : Klon) : (cc : FlownerSplit)
 //this doesn't acutally jmove the split across the map
 //**it just recaloculates from scratch? */
 //
 //what I think I meant is (Sep 2026 26)
 //that this returns an OK split
 //but that it does not characterize the relationship
 //between the two slides of the split
  requires AllReady(flatten(soup)) && klonCalid(m)
  requires flownerSplitOK(soup,m.o,split)
  requires split.pivot == m.o
  requires split.soup  == soup
  requires m.m.Keys >= soup
   ensures flownerSplitOK(mapThruKlon(soup,m),m.c,cc)
   reads m.hns()
   {
       var coup := mapThruKlon(soup,m);
       var pivot := m.c;


       var cc := preFlownerSplit(coup,pivot,
                    flownerAll(coup),
                    flownerStrictlyInside(coup,pivot),
                    flownerStrictlyOutside(coup,pivot),
                    flownerOnlyPivot(coup,pivot),
                    flownerExceptPivot(coup,pivot));

   assert (cc.soup == coup);
   assert (cc.pivot == m.c);
   assert (cc.fAll == flownerAll(coup));
   assert (cc.fSin == flownerStrictlyInside(coup,pivot));
   assert (cc.fOut == flownerStrictlyOutside(coup,pivot));
   assert (cc.fPvt == flownerOnlyPivot(coup,pivot));
   assert (cc.fXpt == flownerExceptPivot(coup,pivot));


      //  var cc_All : Owner := flownerAll(coup);
      //  var cc_Sin : Owner := flownerStrictlyInside(coup,pivot);
      //  var cc_Out : Owner := flownerStrictlyOutside(coup,pivot);
      //  var cc_Pvt : Owner := flownerOnlyPivot(coup,pivot);
      //  var cc_Xpt : Owner := flownerExceptPivot(coup,pivot);
FLOWNER_ALL_ALL(coup,pivot);

assert flownerEverythingOutside(coup,pivot) == flownerStrictlyOutside(coup,pivot) + flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot);
assert flownerPivotlyOutside(coup,pivot) == flownerStrictlyOutside(coup,pivot) + flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot);

assert (cc.fOut + cc.fPvt + cc.fXpt) == flownerEverythingOutside(coup,pivot);
assert (cc.fOut + cc.fPvt + cc.fXpt) == flownerPivotlyOutside(coup,pivot);
assert cc.fSin !! (cc.fOut + cc.fPvt + cc.fXpt);
// assert cc.fAll == cc.fSin + cc.fOut + cc.fPvt + cc.fXpt by
//  {
//    assert flownerAll(coup) == flownerStrictlyInside(coup,pivot) +  flownerStrictlyOutside(coup,pivot) + (flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot));
//    assert (cc.fAll == flownerAll(coup));
//    assert cc.fAll == flownerStrictlyInside(coup,pivot) +  flownerStrictlyOutside(coup,pivot) + (flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot));
//    assert (cc.fSin == flownerStrictlyInside(coup,pivot));
//    assert cc.fAll == cc.fSin +  flownerStrictlyOutside(coup,pivot) + (flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot));
//    assert (cc.fOut == flownerStrictlyOutside(coup,pivot));
//    assert cc.fAll == cc.fSin + cc.fOut + (flownerOnlyPivot(coup,pivot) + flownerExceptPivot(coup,pivot));
//    assert (cc.fPvt == flownerOnlyPivot(coup,pivot));
//    assert cc.fAll == cc.fSin + cc.fOut + cc.fPvt + flownerExceptPivot(coup,pivot);
//    assert (cc.fXpt == flownerExceptPivot(coup,pivot));
//    assert cc.fAll == cc.fSin + cc.fOut + cc.fPvt + cc.fXpt;
//  }



       var ccFEO := flownerEverythingOutside(coup,pivot);
     var ccOPX := (cc.fOut + cc.fPvt + cc.fXpt);

       assert flownerEverythingOutside(coup,pivot) ==
                    flownerStrictlyOutside(coup,pivot)
                  + flownerOnlyPivot(coup,pivot)
                  + flownerExceptPivot(coup,pivot)
        by { FLOWNER_EVERYTHING_EVERYWHERE(coup,pivot, ccFEO, cc.fOut, cc.fPvt, cc.fXpt); }


       FLOWNER_EVERYTHING_OUTSIDE(coup,pivot);
       assert ccOPX == flownerPivotlyOutside(coup,pivot);

       FLOWNER_ALL_EVERYTHING(coup,pivot,cc.fAll,cc.fSin,cc.fOut,cc.fPvt,cc.fXpt);
       assert (cc.fAll == cc.fSin + cc.fOut + cc.fPvt + cc.fXpt);
       assert cc.fSin !! (cc.fOut + cc.fPvt + cc.fXpt);

       assert (cc.fAll == cc.fSin + cc.fOut + cc.fPvt + cc.fXpt);
       assert cc.fSin !! (cc.fOut + cc.fPvt + cc.fXpt);


assert (cc.soup == coup);
assert (cc.pivot == m.c);
assert cc.Valid();

      assert flownerSplitOK(coup,m.c,cc);
      // assert cc.Valid();
      cc
   }

lemma DOUBLE_SPLIT(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
 {
   assert os_sp.fSin == flownerStrictlyInside(os,m.o);
   assert cs_sp.fSin == flownerStrictlyInside(cs,m.c);
   //FOREST_FOOD(os_sp.fSin, cs_sp.fSin, m);
 }


lemma FLOWNER_FLATTEN_TODO_FOR_ALL(soup : OWNR, pivot : Object)
 //verified 21 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()

   ensures flattenOutside(soup, pivot) == flownerOutside(soup, pivot)
   ensures flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
   ensures flattenPivotlyOutside(soup, pivot) == flownerPivotlyOutside(soup, pivot)
   ensures flatten(soup) == flownerAll(soup)
{}


lemma FLOWNER_FLATTEN_Outside(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flattenOutside(soup, pivot) == flownerOutside(soup, pivot)
{}

lemma {:timeLimit 70} FLOWNER_FLATTEN_Outside_Klon(soup : OWNR, m : Klon)
 //DOESN WOKR LIsKELY FOR THE USUAL OOD REASON OH FUCK
 //that's another day I'll never get back
  requires AllReady(flatten(soup))
  requires klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  // ensures flownerOutside(mtk(soup,m), m.c) == mtk(flownerOutside(soup,m.o), m)
{
  assume forall x : Object :: x.Ready();
  assume forall x : set<Object> :: AllReady(x);


//  var ffOm :=  flownerOutside(mtk(soup,m), m.c);
  var coup := mtk(soup,m);
  assert forall c <- coup | outside(c,m.c)  :: c in soup;
  assert forall s <- soup | outside(s,m.o)  :: s in coup;
  assert   (set c <- coup | outside(c,m.c)) == (set s <- soup | outside(s,m.o));

  var fsoup := flatten(soup);
  var fcoup := mtk(fsoup,m);

  assert forall c <- fcoup | outside(c,m.c)  :: c in fsoup;
  assert forall s <- fsoup | outside(s,m.o)  :: s in fcoup;
  assert   (set c <- fcoup | outside(c,m.c)) == (set s <- fsoup | outside(s,m.o));

  assert flattenOutside(mtk(soup,m), m.c) == flownerOutside(mtk(soup,m), m.c)
    by { FLOWNER_FLATTEN_Outside(mtk(soup,m),m.c); }

  assert forall o <- m.m.Keys | outside(o, m.o) :: m.m[o] == o;

  assert flattenOutside((set s <- soup :: m.m[s]), m.c)                          == flattenOutside(mtk(soup,m), m.c);
  assert flattenOutside((set s <- soup :: m.m[s]), m.c)                          == flattenOutside(mtk(soup,m), m.c);
  assert (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))      == flattenOutside((set s <- soup :: m.m[s]), m.c) by
                                                                                       { var r := flattenOutside((set s <- soup :: m.m[s]), m.c);
                                                                                         FLOWNER_FLATTEN_Outside_Klon_03(soup,m,r); }


   assert (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x) == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c)) by
                                                                                       { var r :=  (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c));
                                                                                         FLOWNER_FLATTEN_Outside_Klon_04(soup,m,r); }


  // assert (set x <- flatten(  (set s <- soup ::     s)   ) | outside(m.m[x],m.c) :: m.m[x]) == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x);

 // assert flattenOutside(mtk(soup,m), m.c) == flownerOutside(mtk(soup,m), m.c);
}

lemma {:timeLimit 7} FLOWNER_FLATTEN_Outside_Klon_03(soup : OWNR, m : Klon, r : Owner)
  requires AllReady(flatten(soup)) && AllReady(flatten(r)) && klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  requires r == flattenOutside((set s <- soup :: m.m[s]), m.c)
   ensures r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))
   {}


lemma {:timeLimit 7} FLOWNER_FLATTEN_Outside_Klon_04(soup : OWNR, m : Klon, r : Owner)
  requires AllReady(flatten(soup)) && AllReady(flatten(r)) && klonCalid(m)
  requires soup <= m.m.Keys
   ensures flatten(soup) <= m.m.Keys
  requires r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c))
   ensures r == (set x <- flatten(  (set s <- soup :: m.m[s])  ) | outside(x,m.c) :: x)
   {}




lemma FUCK_YOU_TORY_CUNT(soup : OWNR, pivot : Object)
   requires AllReady(flatten(soup)) && pivot.Ready()
    ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot)

 {
   LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}


lemma ONLY_PIVOT(soup : OWNR, pivot : Object, rv : Owner)
   requires AllReady(flatten(soup)) && pivot.Ready()

  requires || (flownerOnlyPivot(soup,pivot) == rv)
           || (flattenOnlyPivot(soup,pivot) == rv)
           || (shortcutOnlyPivot(soup,pivot) == rv)

   ensures ((pivot  in flownerAll(soup)) || (pivot  in flatten(soup)))
       ==> (rv == pivot.AMFO)
   ensures ((pivot !in flownerAll(soup)) && (pivot !in flatten(soup)))
       ==> (rv == {})

    ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == flownerOnlyPivot(soup,pivot) == rv
 {
   assume AllReady(flatten(soup));
   assume pivot.Ready();
   LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}


lemma FLOWNER_SHORTCUT_OnlyPivot(soup : OWNR, pivot : Object, rv : Owner)
 //verified 21 Sep 2026
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot)
   ensures (shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == {}) || (shortcutOnlyPivot(soup, pivot) == flattenOnlyPivot(soup, pivot) == pivot.AMFO)

   ensures shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot)
   ensures (shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot) == {}) || (shortcutOnlyPivot(soup, pivot) == flownerOnlyPivot(soup, pivot) == pivot.AMFO)
{
  LEMMA_shortcutVSflatten2(soup, pivot, shortcutOnlyPivot(soup, pivot), flattenOnlyPivot(soup, pivot));
}



lemma  STUPIDLY_HAPPY_To_OnlyPivot(xo : Owner, xb : Owner,
      xo_sp : FlownerSplit, xb_sp : FlownerSplit, pivot : Object)
 //verified 21Sep2026
  requires AllReady(flatten(xo)) && AllReady(flatten(xb))
  requires xo_sp.fAll >= xb_sp.fAll // or should this be stupid happy or something???
//  requires stupidlyHappy(xo,xb,pivot)      //ISNT THIS PRETTY MUCH CIRCULAR:??
  requires pivot.Ready()
  requires flownerSplitOK(xo, pivot, xo_sp)
  requires flownerSplitOK(xb, pivot, xb_sp)

   ensures xo_sp.fAll == flownerAll(xo)
   ensures xb_sp.fAll == flownerAll(xb)
   ensures xo_sp.fPvt == flownerOnlyPivot(xo, pivot)
   ensures xb_sp.fPvt == flownerOnlyPivot(xb, pivot)

   ensures (pivot  in xo_sp.fAll) ==> (xo_sp.fPvt == pivot.AMFO)
   ensures (pivot !in xo_sp.fAll) ==> (xo_sp.fPvt == {})
   ensures (pivot  in xb_sp.fAll) ==> (xb_sp.fPvt == pivot.AMFO)
   ensures (pivot !in xb_sp.fAll) ==> (xb_sp.fPvt == {})
   ensures (pivot  in xb_sp.fAll) ==> (pivot  in xo_sp.fAll)
{
   UNPACK_flownerSplitOK(xo,pivot,xo_sp);
   UNPACK_flownerSplitOK(xb,pivot,xb_sp);

      ONLY_PIVOT(xo,pivot,xo_sp.fPvt);
      ONLY_PIVOT(xb,pivot,xb_sp.fPvt);
}



lemma DOUBLE_SPLIT_OnlyPivot(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
   ensures os_sp.fPvt == flownerOnlyPivot(os, m.o)
   ensures cs_sp.fPvt == flownerOnlyPivot(cs, m.c)

   ensures (m.o  in os_sp.fAll) ==> (os_sp.fPvt == m.o.AMFO)
   ensures (m.o !in os_sp.fAll) ==> (os_sp.fPvt == {})
   ensures (m.o  in os_sp.fAll) ==> (cs_sp.fPvt == m.c.AMFO)
   ensures (m.o !in os_sp.fAll) ==> (cs_sp.fPvt == {})

//   ensures os_sp.fPvt == (if (m.o in os_sp.fAll) then (m.o.AMFO) else {})
 {
   assert os_sp.fPvt == flownerOnlyPivot(os, m.o);
FLOWNER_SHORTCUT_OnlyPivot(os, m.o, os_sp.fPvt);
   assert os_sp.fPvt == shortcutOnlyPivot(os, m.o);
 LEMMA_shortcutOnlyPivot1(os, m.o, os_sp.fPvt);

   assert (m.o  in os_sp.fAll) ==> (os_sp.fPvt == m.o.AMFO);
   assert (m.o !in os_sp.fAll) ==> (os_sp.fPvt == {});
   if (m.o in os_sp.fAll) { assert os_sp.fPvt == m.o.AMFO; } else { assert os_sp.fPvt == {}; }
//   assert os_sp.fPvt == (if (m.o in os_sp.fAll) then (m.o.AMFO) else {});

  assert (m.o in os_sp.fAll) ==> (m.c in cs_sp.fAll);

   assert cs_sp.fPvt == flownerOnlyPivot(cs, m.c);
FLOWNER_SHORTCUT_OnlyPivot(cs, m.c, cs_sp.fPvt);
   assert cs_sp.fPvt == shortcutOnlyPivot(cs, m.c);
 LEMMA_shortcutOnlyPivot1(cs, m.c, cs_sp.fPvt);

 }



lemma SIDEWAYS_StrictlyInside(soup0 : Owner, soup1 : Owner, f0 : Owner, f1 : Owner, m : Klon)
//no ensures...
//one more attempt at the "inside problem"
  requires AllReady(flatten(soup0)) && AllReady(flatten(soup1))
  requires klonCalid(m)
  requires m.m.Keys >= soup0
  requires soup1 == mapThruKlon(soup0, m)
  requires f0 == flownerStrictlyInside(soup0, m.o)
  requires f1 == flownerStrictlyInside(soup1, m.c)
//   ensures forall f <- f0 :: m.m[f] in f1
{
  assert f1 <= flownerAll(soup1);
  assert f1 == flownerStrictlyInside(soup1, m.c);
  FLOWNER_FLATTEN_StrictlyInside(soup1,m.c);
  assert f1 == flattenStrictlyInside(soup1, m.c);
  assert f1 == (set x <- flatten(soup1) | strictlyInside(x,m.c));
  assert forall f <- f1 :: strictlyInside(f,m.c);
  assert f1 == (set x <- flatten(mapThruKlon(soup0, m)) | strictlyInside(x,m.c));
  assert f1 == (set x <- flatten(set s <- soup0 :: m.m[s]) | strictlyInside(x,m.c));
  assert m.c == m.m[m.o];
//  assert f1 == (set x <- flatten(set s <- soup0 | strictlyInside(s,m.o) :: m.m[s]));

  assert forall f <- f0 :: strictlyInside(f,m.o) <==>  strictlyInside(m.m[f],m.m[m.o]);


//   assert f0 == flownerStrictlyInside(soup0, m.o);
//   FLOWNER_FLATTEN_StrictlyInside(soup0,m.o);
//   assert f0 == flattenStrictlyInside(soup0, m.o);
//   assert f0 == (set x <- flatten(soup0) | strictlyInside(x,m.o));
//   assert forall f <- f0 :: strictlyInside(f,m.o);
//
//
//   assert f1 == flattenStrictlyInside(mapThruKlon(soup0, m), m.c);

}


lemma MAP_THRU_KLON_FILTER(soup : Owner, m : Klon)
//one more attempt at the "inside problem"
  requires AllReady(flatten(soup))
  requires klonCalid(m)
  requires m.m.Keys >= soup
  //  ensures (set c <- mapThruKlon(soup,m) | strictlyInside(c,m.c))
  //    == mapThruKlon((set s <- soup | strictlyInside(s,m.o)),m)
   {
    var sf := (set s <- soup | strictlyInside(s,m.o) :: s);
    var f  := mapThruKlon(sf,m);
    assert f == (set s <- sf :: m.m[s]);
    assert f == (set s <- (set s <- soup | strictlyInside(s,m.o) :: s) :: m.m[s]);

    assert f == (set s <- soup | strictlyInside(s,m.o) :: m.m[s]);
    assert f == (set s <- soup | strictlyInside(s,m.o) :: m.m[s]);
//    assert f == (set s <- (set s <- soup :: m.m[s]) | strictlyInside(s,m.o) :: s);
//james wonders if this is the "set comprehension problem"
//and if so, can he find rhe code from TRUMP or LUXON that likely fixes it?
//    assert f == (set c <- (set s <- soup :: m.m[s]) | strictlyInside(c,m.m[m.o]) :: c);


  //  assert f ==  mapThruKlon(  (set s <- soup | strictlyInside(s,m.o) :: s), m);

//    assert f ==  (set s <- mapThruKlon(soup,m) | strictlyInside(s,m.m[m.o]) :: s);
//    assert f ==  (set s <- mapThruKlon(soup,m) | strictlyInside(s,m.c) :: s);
   }

function collectAllStrictlyInside(o : Object, pivot : Object) : (rv : set<Object>)
  // all o's transitive owners that are strictly inside pivot
  // recursive, shortcutting analogue of allInside
  decreases o.AMFO
   requires o.Ready()
    { if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- collectAllStrictlyInside(oo, pivot) :: ooo)
    }


function allCollectAllStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
  decreases allAMFOs(soup)
   requires forall o <- soup :: o.Ready()
    { (set o <- soup, ooo <- collectAllStrictlyInside(o,pivot) :: ooo) }


function collectStrictlyInsideObject(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO, 10
   requires o.Ready()
    { if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }


function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
   requires forall o <- soup :: o.Ready()
      decreases allAMFOs(soup), 20
    { (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }



lemma MORE_SELF_HATRED(o : Object, pivot : Object)
 requires o.Ready()
 requires pivot.Ready()
  ensures collectStrictlyInsideObject(o,pivot) == (set o <- argh(o) | strictlyInside(o, pivot))
{
  if (not(strictlyInside(o,pivot))) {
    assert {} == collectStrictlyInsideObject(o,pivot)  == (set o <- argh(o) | strictlyInside(o, pivot));
  }
}

lemma COLLECT_STRICTLY_INSIDE_DO_NOT_PASS_GO(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires forall o <- soup :: o.Ready()
 //  ensures allCollectAllStrictlyInside(soup, pivot) == collectStrictlyInside(soup, pivot)
 decreases allAMFOs(soup), 3
{
  var left := allCollectAllStrictlyInside(soup, pivot);
  var rite := collectStrictlyInside(soup, pivot);

  if (soup == {}) { assert {} == left == rite; return; }

  forall s <- soup ensures true // (allCollectAllStrictlyInside({s}, pivot) == collectStrictlyInsideObject(s, pivot))
   {
     if (not(strictlyInside(s,pivot)))
          { assert {} == allCollectAllStrictlyInside({s}, pivot) == collectStrictlyInsideObject(s, pivot); }
     else
         {
            assert strictlyInside(s,pivot);
            COLLECT_STRICTLY_INSIDE_DO_NOT_PASS_GO(s.owner,pivot);
            assert allCollectAllStrictlyInside(s.owner, pivot) == collectStrictlyInside(s.owner, pivot);
            // assert allCollectAllStrictlyInside({s}, pivot) == {s} +  allCollectAllStrictlyInside(s.owner, pivot);
            // assert collectStrictlyInside({s}, pivot) == {s} +  collectStrictlyInside(s.owner, pivot);
            assert allCollectAllStrictlyInside({s}, pivot) == collectStrictlyInsideObject(s, pivot);
         }
   }

}


lemma {:timeLimit 30} FUCK_THA_TORIES(s : Object, pivot : Object)
  requires AllReady(flatten({s})) && pivot.Ready()
  requires s.Ready()
  requires strictlyInside(s,pivot)
    ensures allCollectAllStrictlyInside({s}, pivot) == collectAllStrictlyInside(s,pivot)
   ensures collectAllStrictlyInside(s,pivot) ==  ({s} + (set oo <- s.owner, ooo <- collectAllStrictlyInside(oo, pivot) :: ooo))

//  ensures collectAllStrictlyInside(s,pivot) ==
//     if (not(strictlyInside(s,pivot))) then ({})
//           else  {s} + (set oo <- s.owner, ooo <- collectAllStrictlyInside(oo, pivot) :: ooo)

    ensures collectStrictlyInsideObject(s,pivot) == ({s} + collectStrictlyInside(s.owner,pivot))
{}

// lemma {:timeLimit 50} allAMFOs_MONOTONIC(a : Owner, b : Owner)
//    requires a > b
//    requires AllReady(a)
//    requires AllReady(b)
//     ensures flatten(a) >  flatten(b)
//     // ensures allAMFOs(a) > allAMFOs(b)
//     // ensures (allAMFOs(a),3 decreases to allAMFOs(b),3)
// {}

lemma FLOWNER_FLATTEN_StrictlyInside(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flattenStrictlyInside(soup, pivot) == flownerStrictlyInside(soup, pivot)
   ensures flownerStrictlyInside(soup, pivot) <= flownerAll(soup)
   ensures allStrictlyInside(flatten(soup), pivot) == flattenStrictlyInside(soup, pivot)
   ensures allStrictlyInside(flownerAll(soup), pivot) == flattenStrictlyInside(soup, pivot)

  //  ensures flattenStrictlyInside(soup, pivot) == allCollectAllStrictlyInside(soup, pivot)
  //  ensures flattenStrictlyInside(soup, pivot) == collectStrictlyInside(soup, pivot)
{}


lemma MORE_StrictlyInside(soup : OWNR, pivot : Object)
  decreases allAMFOs(soup)
  requires AllReady(flatten(soup)) && pivot.Ready()
//   ensures collectStrictlyInside(soup, pivot) == allStrictlyInside(flatten(soup), pivot)
{
  if (soup == {}) { assert collectStrictlyInside(soup, pivot) == allStrictlyInside(flatten(soup), pivot); return; }

  forall s <- soup ensures (collectStrictlyInside({s}, pivot) == allStrictlyInside(flatten({s}), pivot))  //by
   {
      if (not(strictlyInside(s,pivot)))
           {
             assert {} == collectStrictlyInside({s}, pivot) == collectStrictlyInsideObject(s, pivot) == allStrictlyInside(flatten({s}), pivot);
           }
      else {
            assert collectStrictlyInsideObject(s, pivot)  == {s} + collectStrictlyInside(s.owner, pivot);
            assert allStrictlyInside(flatten({s}), pivot) == {s} + allStrictlyInside(flatten(s.owner), pivot);
            MORE_StrictlyInside(s.owner, pivot);
            assert collectStrictlyInside(s.owner, pivot) == allStrictlyInside(flatten(s.owner), pivot);
            assert ({s} + collectStrictlyInside(s.owner, pivot)) == ({s} + allStrictlyInside(flatten(s.owner), pivot));
            assert (collectStrictlyInside({s}, pivot) == allStrictlyInside(flatten({s}), pivot));
           }
   }
   assert forall s <- soup :: collectStrictlyInside({s}, pivot) == allStrictlyInside(flatten({s}), pivot);

   FUCKED_arghStrictlyInside_LEMMA1b(soup, pivot);
   assert collectStrictlyInside(soup, pivot) == (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) ;
   assert allStrictlyInside(flatten(soup), pivot) == (set s <- soup, ss <- collectStrictlyInside(s.AMFO, pivot) ::  ss);
   assert collectStrictlyInside(soup, pivot) == allStrictlyInside(flatten(soup), pivot);
}


lemma FUCKED_arghStrictlyInside_LEMMA1b(soup : OWNR, pivot : Object)   //WORKS
 //lifts asI==sAi to sets     //this may be the forall -> set magio!
   decreases allAMFOs(soup)
    requires AllReady(soup)
    requires forall s <- soup :: s.Ready()
    requires pivot.Ready()
//    requires strictlyInside(o,pivot)
    requires forall s <- soup :: collectStrictlyInside({s},pivot) == allStrictlyInside(flatten({s}),pivot)
     ensures forall s <- soup :: (set ooo <- collectStrictlyInside({s},pivot) :: ooo) == (set ooo <- allStrictlyInside(flatten({s}),pivot) :: ooo)
     ensures (set s <- soup, ooo <- (set x <- collectStrictlyInside({s},pivot)) :: ooo) == (set s <- soup, ooo <- allStrictlyInside(flatten({s}),pivot) :: ooo)
     ensures (set s <- soup, ooo <- collectStrictlyInside({s},pivot) :: ooo) == (set s <- soup, ooo <- allStrictlyInside(flatten({s}),pivot) :: ooo)
   //  ensures (collectStrictlyInside(soup,pivot) == allStrictlyInside(soup,pivot))
{
   // forall oo <- o.owner ensures (set ooo <- arghStrictlyInside(oo,pivot) :: ooo) == (set ooo <- collectAllStrictlyInside(oo,pivot) :: ooo)
   //    {
   //       assert arghStrictlyInside(oo,pivot) == collectAllStrictlyInside(oo,pivot);
   //    }
}


lemma SELF_HATRED(soup : OWNR, pivot : Object)
   decreases allAMFOs(soup)
    requires AllReady(soup)
    requires forall s <- soup :: s.Ready()
    requires pivot.Ready()

    ensures forall s <- soup :: allStrictlyInside(flatten({s}), pivot) == {s} + allStrictlyInside(flatten(s.owner), pivot)
    {}

lemma {:timeLimit 50} EVEN_MORE_StrictlyInside(soup : OWNR, pivot : Object)
 decreases allAMFOs(soup)
  requires AllReady(flatten(soup))
  requires forall o <- soup :: o.Ready()
  requires pivot.Ready()
   ensures collectStrictlyInside(soup, pivot) == (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo)
{
  if (soup == {})
     { assert collectStrictlyInside(soup, pivot) == (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo);
     }
}


lemma DOUBLE_SPLIT_StrictlyInside(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
  //verifies
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
   ensures os_sp.fSin == flownerStrictlyInside(os, m.o)
   ensures cs_sp.fSin == flownerStrictlyInside(cs, m.c)

  //  ensures forall o <- os_sp.fSin :: (
  //     && (o in m.m.Keys)
  //     && (strictlyInside(o,m.o))
  //     && (klonLine(o,m.m[o],m))
  //     && (m.m[o] in cs_sp.fSin)
  // )

 {
   assert os_sp.fSin == flownerStrictlyInside(os,m.o);
   assert cs_sp.fSin == flownerStrictlyInside(cs,m.c);

   assert m.m.Keys >= os_sp.fSin;

   assert forall o <- os_sp.fSin ::
//    && (exists s <- os :: ownerStrictlyInside(s,m.o,o))
    (var c := m.m[o];
        && (strictlyInside(o,m.o))
    );

   assert forall o <- os_sp.fSin ::
    (var c := m.m[o];
        && (klonLine(o,c,m))
    );

   assert forall o <- os_sp.fSin ::
    (var c := m.m[o];
        && (klonIdentity(o,c,m))
        && (o != c)
        && (strictlyInside(c,m.c))
   );

  assert cs_sp.fSin <= cs_sp.fAll;

  //     assert forall o <- os_sp.fSin :: //Err
  //   (var c := m.m[o];
  //       && (c in cs_sp.fAll)
  //  );

  //     assert forall o <- os_sp.fSin ::   //Err
  //   (var c := m.m[o];
  //       && (c in cs_sp.fSin)
  //  );


 }




lemma ORIGINAL_ALL_OBJECTS_OUTSIDE_MAP(os : Owner, m : Klon)
  requires AllReady(flatten(os))
  requires klonCalid(m)
  requires os <= m.m.Keys
  requires forall o <- os :: outside(o,m.o)

   ensures outside(m.o,m.c)
   ensures forall o <- os :: m.m[o] == o
   ensures forall o <- os :: outside(o,m.c)
   ensures mapThruKlon(os,m) == os
   ensures flownerPivotlyOutside(os,m.o) == flownerAll(os)
   ensures flownerPivotlyOutside(os,m.c) == flownerAll(os)
   ensures flownerPivotlyOutside(mapThruKlon(os,m),m.c) == flownerAll(os)
   ensures flownerPivotlyOutside(os,m.o) == flownerPivotlyOutside(mapThruKlon(os,m),m.c)

   {
    var fPO := flownerPivotlyOutside(os,m.o);

    FLOWNER_FLATTEN_TODO_FOR_ALL(os,m.o);
    FLOWNER_FLATTEN_TODO_FOR_ALL(os,m.c);

    assert flownerPivotlyOutside(os,m.o) == flownerAll(os);
    assert flownerPivotlyOutside(os,m.c) == flownerAll(os);
    assert flownerPivotlyOutside(mapThruKlon(os,m),m.c) == flownerAll(os);


   }

lemma MAP_OBJECTS_OUTSIDE(os : Owner, oos : Owner, m : Klon)
  requires AllReady(flatten(os))
  requires klonCalid(m)
  requires os <= m.m.Keys
  requires oos == (set o <- os | outside(o,m.o))  //<==BINARY VERSION

//  HMM.  grr.
//lthinkg about this through 
//gblahy

///MNOST LIKEKY this shouljd be tqeaked to take an input a soup (or two)
//and then produce the sets of outsidee thingus
//and then dio the analysis on them....
//for flownerPivotlyOutside we can rediret through flowerAll()/flattenX
//hmm. or perhaps that won't relaly work
//in whcih case can we get at the ternary version of the binary version here
//and yet get to the same place...?

///ALSO look hard at FLOWER_SPLIT_H around line 1420
//if I can get flownerStrictlyOutside going  --FLOWER_JOIN_All
//whcih frankly should be more than enuf
//then isn't that IT?
//are we ALREADY FUCKING THERE?????



   ensures outside(m.o,m.c)
   ensures forall o <- oos :: m.m[o] == o
   ensures mapThruKlon(oos,m) == oos
   ensures flownerPivotlyOutside(oos,m.o) == flownerAll(oos)
   ensures flownerPivotlyOutside(oos,m.c) == flownerAll(oos)
   ensures flownerPivotlyOutside(mapThruKlon(oos,m),m.c) == flownerAll(oos)
   {
    var fPO := flownerPivotlyOutside(oos,m.o);

    FLOWNER_FLATTEN_TODO_FOR_ALL(oos,m.o);
    FLOWNER_FLATTEN_TODO_FOR_ALL(oos,m.c);

    assert flownerPivotlyOutside(oos,m.o) == flownerAll(oos);
    assert flownerPivotlyOutside(oos,m.c) == flownerAll(oos);
    assert flownerPivotlyOutside(mapThruKlon(oos,m),m.c) == flownerAll(oos);
   }




lemma ONE_OBJECT_OUTSIDE(o : Object, c : Object, m : Klon)
  //verifies 21Sep2026
  requires o.Ready() && c.Ready()
  requires klonCalid(m)
  requires o in m.m.Keys
  requires m.m[o] == c
  requires outside(o,m.o)

   ensures {c} == mapThruKlon({o},m)
   ensures outside(c,m.c)
   ensures o == c
{
  assert klonLine(o,c,m);
  assert klonIdentity(o,c,m);
  assert outside(o,m.o);

  MAPPEN_ONE(o,m);
}


lemma MAPPEN_ONE(o : Object, m : Klon)
 //took at least an hour trying more sensile versions of the next 12 lines
 //to just copy these ones in from an earlier file because they work.
  requires o.Ready()
  requires o in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
  ensures mtk({o},m) == {m.m[o]}
{
 FLATTEN_ONE(o);
}
lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
{}


lemma flownerStrictlyOutside_OUTSIDE(os : Owner, FFO : Owner, pivot : Object)
//verified 22 sept
  requires AllReady(flatten(os))
  requires AllReady(flatten(FFO))
  requires pivot.Ready()
  requires FFO == flownerStrictlyOutside(os, pivot)
   ensures forall f <- FFO :: outside(f,pivot)
{}

lemma flownerExceptPivot_OUTSIDE(os : Owner, FEP : Owner, pivot : Object)
   //verified 22 sept
  requires AllReady(flatten(os))
  requires AllReady(flatten(FEP))
  requires pivot.Ready()
  requires FEP == flownerExceptPivot(os, pivot)
   ensures forall f <- FEP :: outside(f,pivot)
{}



lemma DOUBLE_SPLIT_Outside(os : Owner, cs : Owner, os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon)
 //verified 21Sep2026  (well; kinda)  --- except the last two crucial ensures below
  requires AllReady(flatten(os)) && AllReady(flatten(cs))
  requires klonCalid(m)
  requires m.m.Keys >= os
  requires cs == mapThruKlon(os,m)
  requires flownerSplitOK(os, m.o, os_sp)
  requires flownerSplitOK(cs, m.c, cs_sp)
   ensures os_sp.fAll == flownerAll(os)
   ensures cs_sp.fAll == flownerAll(cs)
   ensures os_sp.fOut == flownerStrictlyOutside(os, m.o)
   ensures cs_sp.fOut == flownerStrictlyOutside(cs, m.c)
   ensures os_sp.fXpt == flownerExceptPivot(os, m.o)
   ensures cs_sp.fXpt == flownerExceptPivot(cs, m.c)

   ensures os_sp.fOut == cs_sp.fOut   //ERR
   ensures os_sp.fXpt == cs_sp.fXpt   //ERR
{
   assert m.m.Keys >= os_sp.fOut;
   assert m.m.Keys >= os_sp.fXpt;

   flownerStrictlyOutside_OUTSIDE(os, os_sp.fOut, m.o);
   flownerStrictlyOutside_OUTSIDE(cs, cs_sp.fOut, m.c);
   flownerExceptPivot_OUTSIDE(os, os_sp.fXpt, m.o);
   flownerExceptPivot_OUTSIDE(cs, cs_sp.fXpt, m.c);

}


lemma KRX(k : Object, m : Klon)
  requires klonCalid(m)
   ensures outside(m.o,m.c)
   ensures forall x <- m.m.Keys | outside(x,m.o) :: outside(x,m.c)
{}



lemma XLR(x : Owner, l : Owner, r : Owner, m : Klon)
//dpes peove22

//consider a larger hammer??
///see MAP_THRU_KLON currently in Klon.dfy
////see also FLOWNER_STRICTLY_OUTSIDE_THRU_KLON etc
  requires AllReady(flatten(x))
  requires AllReady(flatten(l))
  requires AllReady(flatten(r))
  requires klonCalid(m)
  requires x <= m.m.Keys
  requires l == flownerStrictlyOutside(x, m.o)
  requires r == flownerStrictlyOutside(mapThruKlon(x, m), m.c)

  // ensures outside(m.o,m.c)
  ensures l == r  //Err
  {
   flownerStrictlyOutside_OUTSIDE(x, l, m.o);
   flownerStrictlyOutside_OUTSIDE(mapThruKlon(x, m), r, m.c);

assert l == (set o <- x, owner <- o.AMFO | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: owner);

assert r == (set o <- mapThruKlon(x,m), owner <- o.AMFO | PART_INSIDE_OWNER(x,m.c); ownerStrictlyOutside(o,m.c,owner) :: owner);

// assert forall o <- x, owner <- o.AMFO | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: outside(owner,m.o);

assert forall owner <- l :: outside(owner,m.o);
assert forall owner <- r :: outside(owner,m.o);




 var xx := mapThruKlon(x,m);
MAP_THRU_KLON(x,xx,m);



assert l == r;

  //  assert flownerStrictlyOutside(x, m.o) ==
  //     (set o <- x, owner <- o.AMFO
  //       | PART_INSIDE_OWNER(x,m.o); ownerStrictlyOutside(o,m.o,owner) :: owner);
  }

lemma FLOWER_SPLIT_H(oo : Owner, ob : Bound, pivot : Object)
 //given Foo >= Fob, then the vartious components are >=
 //should be xo & xb??
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires pivot.Ready()
  requires flatten(oo) >= flatten(ob) ///works better than flownerALl. why?
//  requires flownerAll(oo) >= flownerAll(ob)
   ensures flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
   ensures flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  //  ensures flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)
   ensures flownerOutsidePivot(oo,pivot) >= flownerOutsidePivot(ob,pivot)
// ensures flownerStrictlyOutside(oo,pivot) >= flownerStrictlyOutside(ob,pivot)

//    ensures (flownerOutsidePivot(oo,pivot) + flownerStrictlyInside(oo,pivot) + flownerStrictlyOutside(oo,pivot))
//       >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyInside(ob,pivot) + flownerStrictlyOutside(ob,pivot))
//
//    ensures (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot))
//       >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerEverythingOutside(oo,pivot) >= flownerEverythingOutside(ob,pivot)

  {
     FLOWNER_DISJOINT(oo, pivot);
     FLOWNER_DISJOINT(ob, pivot);



  //  ensures flownerStrictlyInside(soup,pivot) !! flownerOnlyPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerExceptPivot(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! flownerStrictlyOutside(soup,pivot)
  //  ensures flownerStrictlyInside(soup,pivot) !! (flownerOnlyPivot(soup,pivot) + flownerExceptPivot(soup,pivot) + flownerStrictlyOutside(soup,pivot))
  //  ensures (flownerOnlyPivot(soup,pivot) !! flownerExceptPivot(soup,pivot))
  }



lemma flownerOutsidePivot_REJOIN(oo : Owner, ob : Bound, pivot : Object)
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires pivot.Ready()

  requires flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  requires flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)

   ensures flownerOutsidePivot(oo,pivot) == flownerOnlyPivot(oo,pivot) + flownerExceptPivot(oo,pivot)
   ensures flownerOutsidePivot(ob,pivot) == flownerOnlyPivot(ob,pivot) + flownerExceptPivot(ob,pivot)
   ensures flownerOutsidePivot(oo,pivot) >= flownerOutsidePivot(ob,pivot)
   {}


lemma FUCKED(o0 : Owner, o1 : Owner, o2 : Owner, b0 : Owner, b1 : Owner, b2 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires o0 >= b0
  requires (o1+o2) >= (b1+b2)
  requires o0 !! (o1+o2)
  requires b0 !! (b1+b2)
   ensures (o0+o1+o2) >= (b0+b1+b2)
   {}


lemma FUCK4D(o0 : Owner, o1 : Owner, o2 : Owner, o3 : Owner, b0 : Owner, b1 : Owner, b2 : Owner, b3 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires o0 >= b0
  requires (o1+o2+o3) >= (b1+b2+b3)
  requires o0 !! (o1+o2+o3)
  requires b0 !! (b1+b2+b3)
   ensures (o0+o1+o2+o3) >= (b0+b1+b2+b3)
   {}

lemma UNFUCK4D(o0 : Owner, o1 : Owner, o2 : Owner, o3 : Owner, b0 : Owner, b1 : Owner, b2 : Owner, b3 : Owner)
  //set >= monotonic over disjoint splts and through joint sum
  requires (o0 + b0) !! ((o1+o2+o3) + (b1+b2+b3))
  requires (o0+o1+o2+o3) >= (b0+b1+b2+b3)
   ensures o0 >= b0
   ensures (o1+o2+o3) >= (b1+b2+b3)
   {
      //SET_DISJOINT_GT(o0, (o1+o2+o3), b0, (b1+b2+b3));
   }


lemma SET_DISJOINT_GT(o0 : Owner, o1 : Owner, b0 : Owner, b1 : Owner)
  //set >= monotonic over disjoint splts
  requires (o0 + b0) !! (o1 + b1)
  //  ensures ((o0+o1) >= (b0+b1))  ==> ((o0 >= b0) && (o1 >= b1))
  //  ensures ((o0+o1) >= (b0+b1)) <==  ((o0 >= b0) && (o1 >= b1))
   ensures ((o0+o1) >= (b0+b1)) <==> ((o0 >= b0) && (o1 >= b1))
   {}



lemma FLOWER_JOIN_All(oo : Owner, ob : Bound, pivot : Object)
 //given the vartious components are >=, conclude Foo >= Fob,
 //just a nice? version of FLOWER_JOIN_H without the typo
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires pivot.Ready()

  requires flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)
  requires (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot)) >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerStrictlyInside(oo,pivot) + (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot)) >=
           flownerStrictlyInside(ob,pivot) + (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot))
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))
   ensures flownerAll(oo) >= flownerAll(ob)
//   ensures stupidlyHappy(oo,ob,pivot)
   {
    FUCKED(flownerStrictlyInside(oo,pivot), flownerOutsidePivot(oo,pivot), flownerStrictlyOutside(oo,pivot),
           flownerStrictlyInside(ob,pivot), flownerOutsidePivot(ob,pivot), flownerStrictlyOutside(ob,pivot)) ;
    FLOWNER_DISJOINT(oo, pivot);
    FLOWNER_DISJOINT(ob, pivot);
    FLOWNER_ALL_ALL(oo,pivot);
    FLOWNER_ALL_ALL(ob,pivot);
   }



lemma FLOWER_JOIN_H(oo : Owner, ob : Bound, pivot : Object)
 //given the vartious components are >=, conclude Foo >= Fob,
 //should be xo & xb??
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires pivot.Ready()

  requires flownerStrictlyInside(oo,pivot) >= flownerStrictlyInside(ob,pivot)

  requires flownerOnlyPivot(oo,pivot) >= flownerOnlyPivot(ob,pivot)
  requires flownerExceptPivot(oo,pivot) >= flownerExceptPivot(ob,pivot)

  requires flownerStrictlyOutside(oo,pivot) >= flownerStrictlyOutside(ob,pivot)

  requires flownerEverythingOutside(oo,pivot) >= flownerEverythingOutside(ob,pivot)

   ensures (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot)) >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerOutsidePivot(oo,pivot) >= flownerOutsidePivot(ob,pivot)


  //  ensures (flownerOutsidePivot(oo,pivot) + flownerStrictlyOutside(oo,pivot))
  //     >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyOutside(ob,pivot))


   ensures (flownerOutsidePivot(oo,pivot) + flownerStrictlyInside(oo,pivot) + flownerStrictlyOutside(oo,pivot))
      >= (flownerOutsidePivot(ob,pivot) + flownerStrictlyInside(ob,pivot) + flownerStrictlyOutside(ob,pivot))

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + flownerEverythingOutside(oo,pivot)
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + flownerEverythingOutside(ob,pivot)

   ensures flownerAll(oo) == flownerStrictlyInside(oo,pivot) + flownerStrictlyOutside(oo,pivot) + flownerOutsidePivot(oo,pivot)
   ensures flownerAll(ob) == flownerStrictlyInside(ob,pivot) + flownerStrictlyOutside(ob,pivot) + flownerOutsidePivot(ob,pivot)
   ensures flownerAll(oo) >= flownerAll(ob)
  {
        FUCKED(flownerStrictlyInside(oo,pivot), flownerOutsidePivot(oo,pivot), flownerStrictlyOutside(oo,pivot),
           flownerStrictlyInside(ob,pivot), flownerOutsidePivot(ob,pivot), flownerStrictlyOutside(ob,pivot)) ;
    FLOWNER_DISJOINT(oo, pivot);
    FLOWNER_DISJOINT(ob, pivot);
    FLOWNER_ALL_ALL(oo,pivot);
    FLOWNER_ALL_ALL(ob,pivot);
  }


//shpudl thje next three be turned into predicates,
//one for each case of klonIdentity?  OH probably but fuck it
lemma WOOD_FOOD(o : Object, c : Object, m : Klon)
 //expands on some consequences of klonLine(o,c) when o is *strictlyInside*
 //that inside objects are 1:1 with the clone
 //and also that their owners are -thus the strictlyInside
 //
 //is the is the point about owners (or boundS) thje important one?
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)


   requires o in m.m.Keys
   requires strictlyInside(o,m.o)
   requires c == m.m[o]

    ensures klonLine(o,c,m)
    ensures klonGeometry(o,c,m)
    ensures klonIdentity(o,c,m)
    ensures (o != m.o) && (not(outside(o,m.o)))
    ensures strictlyInside(c,m.c)
    ensures (o != m.o) && (o != c)
    ensures (c.owner == mapThruKlon(o.owner, m))
    ensures (c.bound == mapThruKlon(o.bound, m))

    ensures woodFood(o,c,m)
{}

predicate woodFood(o : Object, c : Object, m : Klon)
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires strictlyInside(o, m.o)
   requires c == m.m[o]

   reads m.hns()
{
    && klonLine(o,c,m)
    && klonGeometry(o,c,m)
    && klonIdentity(o,c,m)
    && strictlyInside(c,m.c)
    && (o != c)
    && (c.owner == mapThruKlon(o.owner, m))
    && (c.bound == mapThruKlon(o.bound, m))
}



//
//
// lemma WOOD_CRAP(o : Object, c : Object, m : Klon)
//  //expands on some consequences of klonLine(o,c) when o is *pivot*
//  //
//  //is the is the point about owners (or boundS) thje important one?
//    requires o.Ready()
//    requires c.Ready()
//    requires klonCalid(m)
//
//    requires o in m.m.Keys
//    requires o == m.o
//    requires c == m.m[o]
//
//     ensures klonLine(o,c,m)
//     ensures klonGeometry(o,c,m)
//     ensures klonIdentity(o,c,m)
//     ensures c == m.c
//     ensures c.owner == m.c.owner == m.clowner
//     ensures c.bound == m.c.bound == m.clbound
//
//     ensures woodCrap(o,c,m)
// {}
//
//
// predicate woodCrap(o : Object, c : Object, m : Klon)
//    requires o.Ready()
//    requires c.Ready()
//    requires klonCalid(m)
//
//    requires o in m.m.Keys
//    requires o == m.o
//    requires c == m.m[o]
//
//    reads m.hns()
// {
//     && klonLine(o,c,m)
//     && klonGeometry(o,c,m)
//     && klonIdentity(o,c,m)
//     && c == m.c
//     && c.owner == m.c.owner == m.clowner
//     && c.bound == m.c.bound == m.clbound
// }



lemma WOOD_REAL(o : Object, c : Object, m : Klon)
 //expands on some consequences of klonLine(o,c) when o is *outside* the pivot
 //
 //is the is the point about owners (or boundS) thje important one?
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires outside(o, m.o)
   requires c == m.m[o]

    ensures klonLine(o,c,m)
    ensures klonGeometry(o,c,m)
    ensures klonIdentity(o,c,m)
    ensures c == o != m.o
    ensures c.owner == o.owner
    ensures c.bound == o.bound

    ensures woodReal(o,c,m)
{}

predicate woodReal(o : Object, c : Object, m : Klon)
   requires o.Ready()
   requires c.Ready()
   requires klonCalid(m)

   requires o in m.m.Keys
   requires outside(o, m.o)
   requires c == m.m[o]

   reads m.hns()
{
    && klonLine(o,c,m)
    && klonGeometry(o,c,m)
    && klonIdentity(o,c,m)
    && c == o != m.o
    && c.owner == o.owner
    && c.bound == o.bound
}


lemma FOREST_REAL(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
    //wood_read --- outside
   //lifts WOOD_REAL to FOREST - verifies on lately with nothing in the body...? 38s
   requires AllReady(flatten(os))
   requires AllReady(flatten(cs))
   requires klonCalid(m)

   requires os      <= m.m.Keys
   requires os_sp.fOut <= m.m.Keys
   requires os_sp.fXpt <= m.m.Keys
   requires forall o <- os_sp.fOut :: outside(o, m.o)
   requires forall o <- os_sp.fXpt :: outside(o, m.o)
   requires cs == mapThruKlon(os,m)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o <- os_sp.fOut :: m.m[o] == o != m.o
    ensures forall o <- os_sp.fXpt :: m.m[o] == o != m.o

    ensures forall o <- os_sp.fOut :: woodReal(o,m.m[o],m)
    ensures forall o <- os_sp.fXpt :: woodReal(o,m.m[o],m)
{
forall o <- os_sp.fOut ensures (woodReal(o,m.m[o],m)) //by
 {
  WOOD_REAL(o,m.m[o],m);
 }
forall o <- os_sp.fXpt ensures (woodReal(o,m.m[o],m)) //by
 {
  WOOD_REAL(o,m.m[o],m);
 }
}

//DUNNO IF THERE FOREST STUFF is RIGHT
//GRR. should it dwepend on :  cs == mapThruKlon(os,m)
//***or is that what it needs to be finding??***
//      WOOD_FOOD(o,m.m[o],m);

lemma FOREST_FOOD(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
    //wood_food - strictlyInside
   //lifts WOOD_FOOD to FOREST - verifies on lately with nothing in the body...? 38s
   //as far as I can see (4 Oct) this just repeats the same as mapping inside...
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os_sp.fSin :: strictlyInside(o, m.o)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o <- os_sp.fSin :: strictlyInside(m.m[o],m.c) && (o != m.m[o])
    ensures forall o <- os_sp.fSin :: m.m[o].owner == mapThruKlon(o.owner, m)
    ensures forall o <- os_sp.fSin :: m.m[o].bound == mapThruKlon(o.bound, m)

    ensures forall o <- os_sp.fSin :: woodFood(o,m.m[o],m)
{
forall o <- os_sp.fSin ensures (woodFood(o,m.m[o],m)) //by
 {
  WOOD_FOOD(o,m.m[o],m);
 }

}



lemma FLOWER_POWER_V_strictlyInside(ox : Owner, cx : Owner, m : Klon)
 //works but dones't currently conclude much!
  requires AllReady(flatten(ox))
  requires AllReady(flatten(cx))
  requires klonCalid(m)
  requires m.m.Keys >= ox
  requires cx == mapThruKlon(ox, m)
//   ensures forall i <- flownerStrictlyInside(ox,m.o) :: m.m[i] in flownerStrictlyInside(cx,m.c)
//   ensures forall o <- flownerStrictlyOutside(ox,m.o)   :: (o == m.m[o]) && (m.m[o] in flownerStrictlyOutside(cx,m.c))

  {
    assert forall i <- flownerStrictlyInside(ox,m.o) :: (i in flownerAll(ox));
    assert forall i <- flownerStrictlyInside(ox,m.o) :: strictlyInside(i,m.o);
    assert forall i <- flownerAll(ox) | strictlyInside(i,m.o) :: i in flownerStrictlyInside(ox,m.o);
    assert forall i <- flownerStrictlyInside(ox,m.o) :: i in m.m.Keys;
    assert forall i <- flownerStrictlyInside(ox,m.o) :: klonLine(i,m.m[i],m);

    forall o <- ox, owner <- o.AMFO | ownerStrictlyInside(o,m.o,owner)
        ensures (true) //by
///        ensures (ownerStrictlyInside(m.m[o],m.c,m.m[owner])) //by
     {
        assert strictlyInside(o,m.o);
        assert strictlyInside(owner,m.o);
        var c := m.m[o];
        var cowner := m.m[owner];

        WOOD_FOOD(o,c,m);
        // assert klonLine(o,c,m);
        // assert klonGeometry(o,c,m);
        // assert klonIdentity(o,c,m);
        // assert (o != m.o) && (not(outside(o,m.o)));
        // assert strictlyInside(c,m.c);
        // assert (o != m.o) && (o != c);
        // assert (c.owner == mapThruKlon(o.owner, m));
        // assert (c.bound == mapThruKlon(o.bound, m));

        WOOD_FOOD(owner,cowner,m);
        // assert klonLine(owner,cowner,m);
        // assert klonGeometry(owner,cowner,m);
        // assert klonIdentity(owner,cowner,m);
        // assert (owner != m.o) && (not(outside(owner,m.o)));
        // assert strictlyInside(cowner,m.c);
        // assert (owner != m.o) && (owner != cowner);
        // assert (cowner.owner == mapThruKlon(owner.owner, m));
        // assert (cowner.bound == mapThruKlon(owner.bound, m));

        INSIDE_PARALLEL(o,owner,c,cowner,m);

        assert inside(c, cowner);
        assert ownerStrictlyInside(c,m.c,cowner);
        assert m.m[o] == c; assert m.m[owner] == cowner;
        assert ownerStrictlyInside(m.m[o],m.c,m.m[owner]);
     }

    // assert forall o <- ox, owner <- o.AMFO ::
    //     ownerStrictlyInside(o,m.o,owner) ==> ownerStrictlyInside(m.m[o],m.m[m.o],m.m[owner]);
    // assert forall o <- ox, owner <- o.AMFO ::
    //     ownerStrictlyInside(o,m.o,owner) ==> ownerStrictlyInside(m.m[o],m.c,m.m[owner]);


//    assert mapThruKlon(flownerStrictlyInside(ox,m.o),m) == flownerStrictlyInside(cx,m.c);
  }



lemma INSIDE_PARALLEL(o0 : Object, o1 : Object, c0 : Object, c1 : Object, m : Klon)
 // o0 & o1 are inside the pivot; cloned to c0 and c1
 // o0 is inside o1; ensures c0 inside c1...
 //  "CLXNING_PRESERVES_INSIDE"??
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

    //shoudl this also be WOOD_FOOD?  - is the c0.owner conclusion the important one?
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


lemma MAPPING_INSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)
   requires os <= m.m.Keys
   requires AllReady(mapThruKlon(os,m))
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures mapThruKlon(os_sp.fSin, m) == cs_sp.fSin



//{:timeLimit 30}
lemma CLONING_PRESERVES_BOUNDS(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

  requires flatten(oo) >= flatten(ob)
  requires stupidlyHappy(oo,ob,m.o)
  requires boundsOK(oo,ob)

   ensures flatten(co) >= flatten(cb)
   ensures boundsOK(oo,ob)
  //  ensures stupidlyHappy(co,cb,m.c)
{
   CLONING_PRESERVES_OWNERSHIP(oo,ob,co,cb,m);

        // assert (forall r <- ob | outside(r,m.o) :: exists s <- oo :: outside(s,m.o) && inside(s,r));
        // assert flatten(co) >= flatten(cb);
        // assert (forall r <- cb ::  exists o <- ob :: m.m[o] == r);
        // assert (forall r <- co ::  exists o <- oo :: m.m[o] == r);
        // assert (forall r <- cb | outside(r,m.c) :: exists s <- co :: outside(s,m.c) && inside(s,r));

        assert (forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob));

forall o <- oo ensures (flatten(m.m[o].ownerBound()) >= flatten(cb)) //by
   {

// Error: this is the precondition that could not be proved
// Inside strictlyInside(o,m.o)
// Could not prove: part.AMFO > whole.AMFO
// This is the only assertion in batch #360 of 371 in method CLONING_PRESERVES_BOUNDS
// Batch #360 resource usage: 41.9M RU

    CLONING_PRESERVES_OWNERBOUND(o, ob, m.m[o], cb, m);
   }

        assert (forall c <- co :: flatten(c.ownerBound()) >= flatten(cb));
   assert boundsOK(co,cb);
  //  assert stupidlyHappy(co,cb,m.c);

}


lemma CLONING_PRESERVES_OWNERBOUND(o : Object, ob : Owner, c : Object, cb : Owner, m : Klon)
 requires klonCalid(m)
  requires m.objectInKlon(o)
  requires c == m.m[o]
  requires strictlyInside(o,m.o)  ///HHMMMMM

  requires AllReady(flatten(ob))
  requires AllReady(flatten(cb))
  requires m.m.Keys >= ob
  requires cb == mapThruKlon(ob, m)

  requires flatten(o.ownerBound()) >= flatten(ob)

   ensures flatten(c.ownerBound()) >= flatten(cb)
{
//   if (o.owner == o.bound) {
//        assert o.ownerBound() == {o};
//        assert c.ownerBound() == {c};
//        assert c.ownerBound() == mapThruKlon(o.ownerBound(),m);
//        assert flatten(o.ownerBound()) >= flatten(ob);
//        assert flatten(c.ownerBound()) >= flatten(cb);
//        return;kkknnnn
//   }
//
//
//
//
//
//   assert klonLine(o,c,m);   assert klonIdentity(o,c,m);
//   assert strictlyInside(o,m.o);
//   assert o != m.o;
//   assert o != c;
//   assert c.owner == mapThruKlon(o.owner,m);
//   assert c.bound == mapThruKlon(o.bound,m);
//   MAP_THRU_KLON(o.owner,c.owner,m);
//   MAP_THRU_KLON(o.bound,c.bound,m);
//   assert o.owner != o.bound;
//   assert c.owner != c.bound;
//   OWNER_BOUND_BOUND(o);
//   assert o.ownerBound() == o.bound;
//   OWNER_BOUND_BOUND(c);
//   assert c.ownerBound() == c.bound;
//
//   assert c.ownerBound() == mapThruKlon(o.ownerBound(),m);
//        assert flatten(o.ownerBound()) >= flatten(ob);

assume  flatten(o.ownerBound()) <= m.m.Keys;
assume  flatten(ob) <= m.m.Keys;
assume  boundsOK(o.ownerBound(),ob);

MAPPEN_ONE(o,m);

CLONING_PRESERVES_OWNERSHIP(o.ownerBound(),ob, c.ownerBound(),cb , m);

       assert flatten(c.ownerBound()) >= flatten(cb);
}


lemma OWNER_BOUND_BOUND(o : Object)
 requires o.Ready()
  ensures AllReady( o.ownerBound() )
  ensures (o.owner == o.bound) ==> (o.ownerBound() == {o})
  ensures (o.owner != o.bound) ==> (o.ownerBound() == o.bound)
{}



//{:timeLimit 30}
lemma {:timeLimit 30} CLONING_PRESERVES_OWNERSHIP(oo : Owner, ob : Bound, co : Owner, cb : Bound, m : Klon)
 //is this name OVERKILL???
 //should it also do bounds?  --- currentlyt NO!
  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires klonCalid(m)
  requires m.m.Keys >= oo
  requires m.m.Keys >= ob

  requires co == mapThruKlon(oo, m)
  requires cb == mapThruKlon(ob, m)

  requires flatten(oo) >= flatten(ob)
  requires stupidlyHappy(oo,ob,m.o) //GRRRRR do we ereally want / need this?   GRRRRRR
 // requires boundsOK(oo,ob) ////HMM do we *always* need this? or not?
 //problem with keeping boundsOK here is that it means we can' use this to prove boundsOK  properlylater...
  //                          ////I'm not sure we do, e.g. the below :-)
  //                          ///our shoudl we unify this with stupidlyHappy??


   ensures flatten(co) >= flatten(cb)
  //  ensures stupidlyHappy(oo,ob,m.o) ==> stupidlyHappy(co,cb,m.c)
  //  ensures boundsOK(oo,ob) ==> boundsOK(co,cb)
{
//  assert (forall o <- oo :: flatten(o.ownerBound()) >= flatten(ob));
      assert m.o.Ready();      assert m.c.Ready();

     var ooSP := flownerSplit(oo, m.o);
  // UNPACK_flownerSplitOK(oo,m.o,ooSP);

     var coSP := flownerSplit(co, m.c);
  // UNPACK_flownerSplitOK(co,m.c,coSP);

     var obSP := flownerSplit(ob, m.o);
  // UNPACK_flownerSplitOK(ob,m.o,obSP);

     var cbSP := flownerSplit(cb, m.c);
  // UNPACK_flownerSplitOK(cb, m.c, cbSP);

  // flownerAll_MONOTONIC(oo,ob,m.o);
  // flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(oo,ooSP,ob,obSP,m.o);

// ////////////////////////////////////////////////////////////
// //oo to co - inside
//  //  //  //  //  //  //  //  //  //  //  //  //  //  //
  //  assert AllReady(obSP.fAll);
  //  assert AllReady(coSP.fAll);
  //  assert klonCalid(m);
  //  assert oo <= m.m.Keys;
  //  assert AllReady(mapThruKlon(oo,m));
  //  assert co == mapThruKlon(oo,m);
  //  assert flownerSplitOK(oo, m.o,ooSP);
  //  assert flownerSplitOK(co, m.c,coSP);
//  //  //  //  //  //  //  //  //  //  //  //  //  //  //
MAPPING_INSIDE(oo,ooSP,co,coSP,m);
MAPPING_INSIDE(ob,obSP,cb,cbSP,m);
// ////////////////////////////////////////////////////////////
// //outside

MAPPING_OUTSIDE(oo,ooSP,co,coSP,m);
MAPPING_OUTSIDE(ob,obSP,cb,cbSP,m);
//

//////////////////////////////////////////////////////////
// the pivot
  //
  // MAP_THRU_KLON(oo,co,m);
  // MAP_THRU_KLON(ob,cb,m);
  //

  UNPACK_flownerSplitOK(oo,m.o,ooSP);
  UNPACK_flownerSplitOK(ob,m.o,obSP);
  UNPACK_flownerSplitOK(co,m.c,coSP);
  UNPACK_flownerSplitOK(cb,m.c,cbSP);

     MAPPING_PIVOT(oo,ooSP,co,coSP,m);    ///  look  ///
     MAPPING_PIVOT(ob,obSP,cb,cbSP,m);   ///  here  ///

     DOUBLE_SPLIT_OnlyPivot(oo, co, ooSP, coSP, m);
//STUPIDLY_HAPPY_To_OnlyPivot(oo,ob,ooSP,obSP,m.o);
     DOUBLE_SPLIT_OnlyPivot(ob, cb, obSP, cbSP, m);


  assert AllReady(flatten(co)) && AllReady(flatten(cb));

ONLY_PIVOT(oo,m.o,ooSP.fPvt);
ONLY_PIVOT(ob,m.o,obSP.fPvt);
ONLY_PIVOT(co,m.c,coSP.fPvt);
ONLY_PIVOT(cb,m.c,cbSP.fPvt);

// / / / / / / / / / / / / / / / / / / / / / / / / / / / / / / / /


  assert ooSP.fSin >= obSP.fSin;
  M4K(ooSP.fSin, obSP.fSin, coSP.fSin, cbSP.fSin, m);
  assert coSP.fSin >= cbSP.fSin;



  assert coSP.fSin >= cbSP.fSin;
//  assert coSP.fOut >= cbSP.fOut;
  assert coSP.fPvt >= cbSP.fPvt;
//  assert coSP.fXpt >= cbSP.fXpt;
   assert coSP.fOut+coSP.fXpt >= cbSP.fOut+cbSP.fXpt;


  assert flownerStrictlyInside(co,m.c) >= flownerStrictlyInside(cb,m.c);

  assert (flownerOutsidePivot(co,m.c) + flownerStrictlyOutside(co,m.c)) >= (flownerOutsidePivot(cb,m.c) + flownerStrictlyOutside(cb,m.c));


FLOWER_JOIN_All(co,cb,m.c);

assert coSP.fAll >= cbSP.fAll;
assert flatten(co) >= flatten(cb);
// assert (forall o <- co :: flatten(o.ownerBound()) >= flatten(cb));
// assert boundsOK(co,cb);
// assert (forall r <- cb | outside(r,m.c) :: exists s <- co :: outside(s,m.c) && inside(s,r));
//
// assert stupidlyHappy(co,cb, m.o);
// flownerAll_SONOMONIC_AND_HAPPY_AND_BOUNDS(co,coSP,cb,cbSP,m.c);


return;

}

lemma CARREFOUR(
      oo : Owner, oo_sp : FlownerSplit, ob : Bound, ob_sp : FlownerSplit,
      co : Owner, co_sp : FlownerSplit, cb : Bound, cb_sp : FlownerSplit,
      m  : Klon)
  requires klonCalid(m)

  requires flownerAll(oo) >= flownerAll(ob)
  requires stupidlyHappy(oo,ob,m.o)
  requires boundsOK(oo,ob)

  ensures oo_sp.fAll >= ob_sp.fAll
  ensures oo_sp.fSin >= ob_sp.fSin

  requires AllReady(flatten(oo))
  requires AllReady(flatten(ob))
  requires m.o.Ready()
  requires flownerSplitOK(oo,m.o,oo_sp)
  requires flownerSplitOK(ob,m.o,ob_sp)

  requires AllReady(flatten(co))
  requires AllReady(flatten(cb))
  requires m.c.Ready()
  requires flownerSplitOK(co,m.c,co_sp)
  requires flownerSplitOK(cb,m.c,cb_sp)

  requires oo <= m.m.Keys
  requires ob <= m.m.Keys
  requires co == mtk(oo,m)
  requires cb == mtk(ob,m)

  ensures co_sp == splitThruKlon(oo,oo_sp,m)
  ensures cb_sp == splitThruKlon(ob,ob_sp,m)

//  ensures co_sp.fAll >= cb_sp.fAll
  ensures co_sp.fSin >= cb_sp.fSin

  //  ensures stupidlyHappy(co,cb,m.c)
  //  ensures boundsOK(co,cb)

{
  assert co_sp == splitThruKlon(oo,oo_sp,m);
  assert cb_sp == splitThruKlon(ob,ob_sp,m);

  MAP_THRU_KLON(oo,co,m);
  MAP_THRU_KLON(ob,cb,m);

  UNPACK_flownerSplitOK(oo,m.o,oo_sp);
         assert oo_sp.fSin == flownerStrictlyInside(oo,m.o);  //Err
  UNPACK_flownerSplitOK(ob,m.o,ob_sp);
         assert ob_sp.fSin == flownerStrictlyInside(ob,m.o);  //Err
  UNPACK_flownerSplitOK(co,m.c,co_sp);
         assert co_sp.fSin == flownerStrictlyInside(co,m.c);  //Err
  UNPACK_flownerSplitOK(cb,m.c,cb_sp);
         assert cb_sp.fSin == flownerStrictlyInside(cb,m.c);  //Err

  assert oo_sp.fAll >= ob_sp.fAll;
  assert forall o <- ob_sp.fAll :: o in oo_sp.fAll;

  flownerStrictlyInside_MONOTONIC(oo,ob,m.o);
//  flownerStrictlyInside_MONOTONIC(co,cb,m.c);  // flownerAll(co) >= flownerAll(cb)
    //hat's very muc hthe wrong thing - tha's what we're trying to PROVE...

  assert oo_sp.fSin >= ob_sp.fSin;
  assert forall o <- ob_sp.fSin :: o in oo_sp.fSin;



  assert oo_sp.fSin >= ob_sp.fSin;
//   assert forall o <- oo_sp.fSin :: m.m[o] in co_sp.fSin;  //Err
//
//   assert forall o <- ob_sp.fSin :: o in oo_sp.fSin;       //Err
//   assert forall o <- ob_sp.fSin :: m.m[o] in cb_sp.fSin;  //Err
//   assert forall o <- ob_sp.fSin :: m.m[o] in co_sp.fSin;  //Err
//
//   assert forall c <- cb_sp.fSin :: c in cb_sp.fSin;
//   assert forall c <- cb_sp.fSin :: c in co_sp.fSin;  //Err
//
//   assert co_sp.fSin >= cb_sp.fSin;  //Err

/////
//assert co_sp.fAll >= cb_sp.fAll;
}


lemma MTK_SIZE(oo : Owner, rv : Owner, m : Klon)
///unfinished
   decreases allAMFOs(oo)
    requires AllReady(oo) && AllReady(rv)
    requires klonCalid(m)
    requires oo <= m.m.Keys
    requires rv == mapThruKlon(oo, m)
{
    MAP_THRU_KLON(oo,rv,m);

     assert forall o <- oo :: (o in m.m.Keys) && (m.m[o] in rv) && klonLine(o,m.m[o],m);
     assert forall r <- rv :: exists o <- oo :: (m.m[o] == r) && klonLine(o,r,m);

//     assert |oo| == |rv|;

    // var n := superSize(m.m);
    // assert n == |m.m| == |oo| == |rv|;
}

lemma SETTPM(oo : Owner, x : Object, ooo : Owner)
  requires x in oo
  requires oo - {x} == ooo

  ensures ooo + {x} == oo
{}

//lets stop fucking about eh?
//
//
// lemma emteekay(oo : Owner, rv : Owner, m : Klon)
//    decreases allAMFOs(oo)
//     requires AllReady(oo) && AllReady(rv)
//     requires klonCalid(m)
//     requires oo <= m.m.Keys
//     requires rv == mapThruKlon(oo, m)
//
//      ensures forall o <- oo :: var x :| x == m.m[o]; x == m.m[o]
//      ensures forall r <- rv :: exists x <- oo :: m.m[x] == r
//      //opopensures |oo| == |rv|
//      {
//       assert forall x <- oo, y <- oo :: (m.m[x] == m.m[y]) ==> (x == y);
//      }


//
// function MTK_MTK(oo : Owner, rv : Owner, m : Klon) : nat
//    decreases allAMFOs(oo)
//     requires AllReady(oo) && AllReady(rv)
//     requires klonCalid(m)
//     requires oo <= m.m.Keys
//     requires rv == mapThruKlon(oo, m)
//   //   ensures |rv| == |oo|
// {
//   if (oo == {}) then (assert rv == {}; assert |rv| == |oo| == 0; 0)
//   else (
//       assert oo > {};
//       var k : Object :| k in oo;
//       var ooo := oo - {k};
//       var v := m.m[k];
//       var rvv := rv - {v};
//       SETTPM(oo,k,ooo);
//       SETTPM(rv,v,rvv);
//       var ltail := MTK_MTK(ooo,rvv,m);
//       assert |ooo| == |rvv| == ltail;
//       assert |rv| == |oo|== ltail + 1;
//       (ltail + 1)
//   )
// }


function superSize<K,V>(mep : map<K,V>) : (rv : nat)
   ensures rv == |mep.Keys|
  {
      if (mep.Keys == {}) then 0
        else (var x  :| x in mep;
              var nn := mep - {x};
               (1 + (superSize(nn))))
  }



lemma M4K(os : Owner, ob : Owner, cs : Owner, cb : Owner, m : Klon)
 // this is technically *wrong* or rather it's not the whole story
 // you can't make the arguments just the whole lot and call it done!
 // the mainline is flatten(os) >= flatten(ob) for starters
 // but if we can't get this, we can't get the rest.
 // this shoudl work on "inside" which is the one thing currently missing...
 //
 //in spite of that long long rant above - it ran first time 3 Oct 2026
 //
  // requires AllReady(os)  //actually
  // requires AllReady(ob)
  // requires AllReady(cs)
  // requires AllReady(cb)

  requires m.m.Keys >= os
  requires m.m.Keys >= ob

  requires os >= ob
  requires cs == mtk(os,m)  // or should this be woodFood someting-or-othetr
  requires cb == mtk(ob,m)

   ensures cs >= cb
{}




lemma K4M(os : Owner, ob : Owner, cs : Owner, cb : Owner, m : Klon)
  requires AllReady(os)
  requires AllReady(ob)
  requires AllReady(cs)
  requires AllReady(cb)
  requires klonCalid(m)

  requires m.m.Keys >= os
  requires m.m.Keys >= ob

  requires os >= ob
  requires ktm(os,cs,m)
  requires ktm(ob,cb,m)

   ensures cs >= cb
{}

lemma KTM_KTM(os : Owner, rv : Owner, m : Klon)
 requires os <= m.m.Keys
 requires klonCalid(m)
 requires ktm(os,rv,m)
//  ensures ktm1(os,rv,m)
  {
    assert AllMapEntriesAreUnique(m.m);
           AMEAU1(m.m);
    assert AllMapEntriesAreUnique2(m.m);
    reveal UniqueMapEntry();
    assert forall i <- m.m.Keys :: UniqueMapEntry(m.m, i, m.m[i]);
    assert forall k <- m.m.Keys, i <- m.m.Keys :: m.m[i] == m.m[k] ==> (i == k);
    assert forall k <- os,       i <- m.m.Keys :: m.m[i] == m.m[k] ==> (i == k);
    assert ktm(os,rv,m);

    assert (forall o <- os :: m.m[o] in rv)
        && (forall r <- rv :: exists o <- m.m.Keys :: (m.m[o] == r) ==> (o in os));

    assert forall o <- os :: m.m[o] in rv;
//    assert forall r <- rv :: exists o <- m.m.Keys :: (m.m[o] == r);
    assert forall r <- rv :: exists o <- m.m.Keys :: (m.m[o] == r) ==> (o in os);
    assert forall o <- os :: o in m.m.Keys;
    assert forall r <- rv :: forall o <- os :: o in m.m.Keys;

//    assert forall r <- rv :: exists o <- m.m.Keys :: (m.m[o] == r) && (o in os);
    assert forall r <- rv :: exists o <- os :: m.m[o] == r;
  }

predicate ktm(os : Owner, rv : Owner, m : Klon)
 requires os <= m.m.Keys
 requires klonCalid(m)
   reads m.hns()
  {(forall o <- os :: m.m[o] in rv) && (forall r <- rv :: exists o <- m.m.Keys :: (m.m[o] == r) ==> (o in os))}


predicate ktm1(os : Owner, rv : Owner, m : Klon)
 requires os <= m.m.Keys
 requires klonCalid(m)
   reads m.hns()
  {(forall o <- os :: m.m[o] in rv) && (forall r <- rv :: exists o <- os :: m.m[o] == r)}


// function mtk(os : Owner, m : Klon) :  Owner requires os <= m.m.Keys {set o <- os :: m.m[o]}

// lemma INTO_THE_WEST(os : Owner, rv : Owner, m : Klon)

lemma IN_IN(os : Owner, rv : Owner, m : Klon)
 //gets us "ensures forall r <- rv :: exists o <- m.m.Keys :: m.m[o] == r"
 //but it gets it from mapthruklon or the equocalent set compreshension
 //which is alreyad there in mapThrouKlon now. so wghat;s the benefiit of this?

 requires AllReady(os)
 requires AllReady(rv)
 requires os <= m.m.Keys
 requires klonCalid(m)

 //requires rv == mapThruKlon(os,m) /// did I mean to leave this out?
   requires rv == (set o <- os :: m.m[o])  //why doese writing this feel slightly better than the above?
 // requires forall o <- os :: m.m[o] in rv

  ensures forall o <- os :: o in m.m.Keys
  ensures forall o <- os :: klonLine(o,m.m[o],m)
  ensures forall r <- rv :: exists o <- m.m.Keys :: klonLine(o,m.m[o],m)
  ensures forall k <- m.m.Keys, j <- m.m.Keys :: (m.m[k] == m.m[j]) ==> (k == j)
  ensures forall r <- rv :: exists o <- m.m.Keys :: m.m[o] == r
{
  assert forall k <- m.m.Keys, j <- m.m.Keys :: (m.m[k] == m.m[j]) ==> (k == j);

}


lemma klonThruMap(os : Owner, rv : Owner, m : Klon)
  requires os <= m.m.Keys
  requires forall o <- os :: exists r <- rv :: m.m[o] == r
  requires forall r <- rv :: exists o <- os :: m.m[o] == r

   ensures rv == mtk(os,m)
   ensures rv == mapThruKlon(os,m)
   {}

//.predicate isoKlon(os : Owner, rv : Owner, m : Klon)

lemma klonThruMapHacked(os : Owner, rv : Owner, m : Klon)
  requires klonCalid(m)
  requires forall o <- os :: o.Ready()
  requires forall r <- rv :: r.Ready()

  requires os <= m.m.Keys
//  requires forall o <- os :: m.m[o] in rv

  //requires forall o <- os :: exists r <- rv :: m.m[o] == r
//  requires forall r <- rv :: exists o <- os :: m.m[o] == r

    ensures rv == mtk(os,m)
  //  ensures rv == mapThruKlon(os,m)
//   ensures forall r <- rv :: r in mtk(os,m)
   {}


// function doubleStrictlyInsideObject(o : Object, pivot : Object) : (rv : (set<Object>,set<Object>))
//   decreases o.AMFO, 10
//    requires o.Ready()
//     { if (not(strictlyInside(o,pivot))) then ({},{}) else (
//         var (l,r) := doubleStrictlyInside(o.owner,pivot);
//         ({o}+l, {o}+r)) }


function doubleStrictlyInsideObject(o : Object, m : Klon) : (rv : (set<(Object,Object)>))
  decreases o.AMFO, 10
   requires o.Ready()
   // ensures rv == (set x <- collectStrictlyInsideObject(o,m.o) :: (x,x))
    { if (not(strictlyInside(o,m.o))) then ({}) else (
          {(o,o)}+doubleStrictlyInside(o.owner,m) ) }

function doubleStrictlyInside(soup : Owner, m : Klon) : (rv : (set<(Object,Object)>))
  decreases allAMFOs(soup), 20
   requires forall o <- soup :: o.Ready()
//ensures rv == (set x <- collectStrictlyInside(soup,m.o) :: (x,x))
    { (set o <- soup, ooo <- doubleStrictlyInsideObject(o,m) :: ooo) }
















lemma L_doubleStrictlyInsideObject(o : Object, m : Klon, rv : (set<(Object,Object)>))
  decreases o.AMFO, 10
   requires o.Ready()
   requires rv == doubleStrictlyInsideObject(o,m)
//    ensures rv == (set x <- collectStrictlyInsideObject(o,m.o) :: (x,x))
    // ensures p0(rv) == collectStrictlyInsideObject(o,m.o)
    // ensures p1(rv) == collectStrictlyInsideObject(o,m.o)
    {
      if (not(strictlyInside(o,m.o)))
        {
          assert collectStrictlyInsideObject(o,m.o) == {};
          assert p0(rv) == {};
          assert p1(rv) == {};
          assert p0(rv) == collectStrictlyInsideObject(o,m.o);
          assert p1(rv) == collectStrictlyInsideObject(o,m.o);
          return;
        }

      assert strictlyInside(o,m.o);
      assert collectStrictlyInsideObject(o,m.o) == {o}+collectStrictlyInside(o.owner,m.o);

   //   assert rv == (set x <- collectStrictlyInsideObject(o,m.o) :: (x,x));

      // assert p0(rv) == {o}+collectStrictlyInside(o.owner,m.o);
      // assert p1(rv) == {o}+collectStrictlyInside(o.owner,m.o);
      // assert p0(rv) == collectStrictlyInsideObject(o,m.o);
      // assert p1(rv) == collectStrictlyInsideObject(o,m.o);
    }

lemma L_doubleStrictlyInside(soup : Owner, m : Klon, rv : (set<(Object,Object)>))
  decreases allAMFOs(soup), 20
   requires forall o <- soup :: o.Ready()
   requires rv == doubleStrictlyInside(soup,m)
    // ensures rv == (set x <- collectStrictlyInside(soup,m.o) :: (x,x))
    // ensures p0(rv) == collectStrictlyInside(soup,m.o)
    // ensures p1(rv) == collectStrictlyInside(soup,m.o)
  {
  }

function p0(ss : set<(Object,Object)>) : set<Object>  {set s <- ss :: s.0}
function p1(ss : set<(Object,Object)>) : set<Object>  {set s <- ss :: s.1}













































lemma CSItk(soup : Owner, m : Klon)
   requires AllReady(flatten(soup))
   requires flatten(soup) <= m.m.Keys
   requires forall s <- soup :: s.Ready()
   requires klonCalid(m)
  decreases allAMFOs(soup), 25
    ensures mtk(collectStrictlyInside(soup,m.o),m) == collectStrictlyInside(mtk(soup,m),m.c)
{
  if (soup == {}) { assert mtk(collectStrictlyInside(soup,m.o),m) == collectStrictlyInside(mtk(soup,m),m.c) == {};  return; }
  forall o <- soup ensures (true)   //by
    {
       if (soup == {o}) {
           assert allAMFOs(soup) == allAMFOs({o});
           assert allAMFOs({o})  == (set x : Object <- {o}, ooo <- x.AMFO :: ooo);
           assert allAMFOs({o})  == o.AMFO;
           assert 25 > 15;
           assert (allAMFOs(soup), 25 decreases to o.AMFO, 15);
       } else {
           assert allAMFOs(soup) >= o.AMFO;
           assert 25 > 15;
           assert (allAMFOs(soup), 25 decreases to o.AMFO, 15);
       }
       assert (allAMFOs(soup), 25 decreases to o.AMFO, 15);

       CSItkO(o,m);
       assert (mtk(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c));
    }
}


lemma CSItkO(o : Object, m : Klon)
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
  decreases o.AMFO, 15
    ensures mtk(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c)
{
  assert klonCalid(m);
  assert klonHeap(m);
  KLON_HEAP_VALID(m);
  if (not(strictlyInside(o,m.o))) {
    assert collectStrictlyInsideObject(o,m.o) == {};
    assert mtk(collectStrictlyInsideObject(o,m.o),m) == {};
    assert collectStrictlyInsideObject(m.m[o],m.c) == {};
//    assert mtk(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c) == {};
    return;
    }

    CSItk(o.owner, m);
}






lemma MXPPING_XNSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os_sp.fSin :: strictlyInside(o, m.o)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)
//
//     ensures forall o <- os :: klonLine(o,m.m[o],m)
//     ensures forall o <- os :: klonGeometry(o,m.m[o],m)
//     ensures forall o <- os :: klonIdentity(o,m.m[o],m)
//     ensures forall o <- os_sp.fSin :: strictlyInside(m.m[o],m.c) && (o != m.m[o])
//  //   ensures forall o <- os_sp.fSin :: m.m[o].owner == mapThruKlon(o.owner, m)
//  //   ensures forall o <- os_sp.fSin :: m.m[o].bound == mapThruKlon(o.bound, m)
//
//     // ensures forall o <- os_sp.fSin :: woodFood(o,m.m[o],m)

  //love this beautiful symmetrical formulation
    // ensures forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r
    // ensures forall r <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == r

{
     assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,cs_sp.pivot);
     assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,os_sp.pivot);

 flownerStrictlyInside_RESULT(os_sp.soup,os_sp.pivot,os_sp.fSin);
 flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);



}













lemma old_MXPPING_INSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires forall o <- os_sp.fSin :: strictlyInside(o, m.o)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o <- os_sp.fSin :: strictlyInside(m.m[o],m.c) && (o != m.m[o])
 //   ensures forall o <- os_sp.fSin :: m.m[o].owner == mapThruKlon(o.owner, m)
 //   ensures forall o <- os_sp.fSin :: m.m[o].bound == mapThruKlon(o.bound, m)

    // ensures forall o <- os_sp.fSin :: woodFood(o,m.m[o],m)

  //love this beautiful symmetrical formulation
    // ensures forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r
    // ensures forall r <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == r

{

     assert cs_sp == splitThruKlon(os,os_sp,m);
     assert cs_sp.soup == mapThruKlon(os,m) == cs;
     assert cs_sp.pivot == m.c;


     MAP_THRU_KLON(os,cs,m);
    assert forall o <- os :: m.m[o] in cs;
    assert forall o <- os :: exists c <- cs :: m.m[o] == c;
    assert forall c <- cs :: exists o <- os :: m.m[o] == c;
     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);

     assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,cs_sp.pivot);
     assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,os_sp.pivot);
 flownerStrictlyInside_RESULT(os_sp.soup,os_sp.pivot,os_sp.fSin);
 flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);

   assert forall r <- flatten(os_sp.soup) | strictlyInside(r,m.o) :: r in os_sp.fSin;
   assert forall r <- os_sp.fSin :: r in flatten(os_sp.soup);
   assert forall r <- os_sp.fSin :: strictlyInside(r,os_sp.pivot);
   assert forall r <- flatten(cs_sp.soup) | strictlyInside(r,cs_sp.pivot) :: r in cs_sp.fSin;
   assert forall r <- cs_sp.fSin :: r in flatten(cs_sp.soup);
   assert forall r <- cs_sp.fSin :: strictlyInside(r,cs_sp.pivot);

   assert forall o <- os_sp.fSin :: strictlyInside(o,os_sp.pivot);
//X   assert forall o <- os_sp.fSin :: strictlyInside(m.m[o],cs_sp.pivot);
  //X  assert forall c <- cs_sp.fSin :: strictlyInside(c,cs_sp.pivot)
  //X       && (exists o <- m.m.Keys :: ((m.m[o] == c)  && strictlyInside(o,os_sp.pivot)));


//X     assert forall o <- os_sp.fSin :: m.m[o] in cs_sp.fSin;
//X     assert forall c <- cs_sp.fSin :: exists o <- m.m.Keys :: m.m[o] == c;

var rv := cs_sp.fSin;
assert forall o <- os | strictlyInside(o,m.o) :: (o != m.m[o]) && strictlyInside(m.m[o],m.c) && (m.m[o] in rv);  //not reallyu waht we want
//doesn't work // assert forall o <- flatten(os) | strictlyInside(o,m.o) :: (o != m.m[o]) && strictlyInside(m.m[o],m.c) && (m.m[o] in rv);  //but this is ...

assert forall o <- os_sp.fAll | strictlyInside(o,m.o) :: o in os_sp.fSin;
assert forall o <- os_sp.fAll :: strictlyInside(o,m.o)  ==> (o in os_sp.fSin);
assert forall o <- os_sp.fAll :: strictlyInside(o,m.o) <== (o in os_sp.fSin);
//assert forall o <- os_sp.fAll :: strictlyInside(o,m.o) <==> (o in os_sp.fSin);

assert (set o <- os_sp.fAll | strictlyInside(o,m.o)) <=  os_sp.fSin;
assert forall o <- os_sp.fSin :: (o in os_sp.fAll ) && (strictlyInside(o,m.o));
assert (set o <- os_sp.fAll | strictlyInside(o,m.o)) >=  os_sp.fSin;
//assert (set o <- os_sp.fAll | strictlyInside(o,m.o)) ==  os_sp.fSin;







assert forall o <- os | strictlyInside(o,m.o) :: o in os_sp.fSin;

 flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);
   assert forall r <- flatten(cs) | strictlyInside(r,m.c) :: r in rv;
   assert forall r <- rv :: r in flatten(cs);
   assert forall r <- rv :: strictlyInside(r,m.c);
   assert forall r <- rv :: exists c <- cs | r in c.AMFO :: (PART_INSIDE_OWNER(cs,m.c);  ownerStrictlyInside(c,m.c,r));

//DOESNT WORK   assert forall c <- cs :: exists o <- os :: m.m[o] in rv;
//NOR THIS   assert forall c <- flatten(cs) :: exists o <- flatten(os) :: m.m[o] in rv;

//NOR THIS   assert forall c <- flatten(mtk(os,m)) :: exists o <- flatten(os) :: m.m[o] in rv;




//   assert forall o <- flatten(os) | strictlyInside(m.m[o],m.c) :: m.m[o] in rv;


  //  assert forall r <- rv :: exists o <- os_sp.fSin :: m.m[o] == r;


// assert forall o <- flatten(os) | strictlyInside(o,m.o) :: (o != m.m[o]) && strictlyInside(m.m[o],m.c) && (m.m[o] in rv);
//assert forall o <- flownerStrictlyInside(os,m.o) :: (o != m.m[o]) && strictlyInside(m.m[o],m.c) && (m.m[o] in rv);

assert os_sp.fSin <= os_sp.fAll;
assert forall o <- os_sp.fSin :: o.Ready();
assert os_sp.fSin <= m.m.Keys;
assert forall o <- os_sp.fSin :: strictlyInside(o,m.o);
// assert forall o <- os_sp.fSin :: strictlyInside(m.m[o],m.c);   ///works but SLOW






assert forall o <- os_sp.fSin :: (  strictlyInside(o,m.o) && strictlyInside(m.m[o],m.c)  );

// assert forall c <- cs_sp.fSin :: (  strictlyInside(c,m.c) &&  (exists o <- m.m.Keys :: strictlyInside(m.m[o],m.c))  );

//assert forall c <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == c;

assert os_sp.fSin <= m.m.Keys;
//assert forall c <- cs_sp.fSin :: exists o <- m.m.Keys  :: m.m[o] == c;
//assert forall c <- cs_sp.fSin :: exists o <- os_sp.fAll :: m.m[o] == c;
assert forall o <- os_sp.fSin :: (o in m.m.Keys) && (m.m[o] in m.m.Values);
assert forall c <- cs_sp.fSin :: (c in m.m.Values) ==> exists o <- m.m.Keys :: m.m[o] == c;






forall o <- os_sp.fSin ensures (  strictlyInside(o,m.o) && strictlyInside(m.m[o],m.c)  ) // m.m[o] in rv ) ///by
{
  var c := m.m[o];
    assert klonLine(o,c,m);
    assert klonGeometry(o,c,m);
    assert klonIdentity(o,c,m);
    assert strictlyInside(o,m.o);
    assert (o != c);

/// assert c in  cs_sp.fSin;  //grrr doesn't work

     assert (c.owner == mapThruKlon(o.owner,m)) && (c.bound == mapThruKlon(o.bound,m))
      by {
      assert strictlyInside(c,m.c);
      assert klonIdentity(o,c,m);

      var k := o;
      var v := c;
      assert m.m[k] == v;
        assert klonLine(k,v,m);
        assert klonGeometry(k,v,m);
        assert klonIdentity(k,v,m);
          assert strictlyInside(k, m.o);
          assert k != m.o;
          assert (k != v);
          assert (v.bound == mapThruKlon(k.bound, m));
          assert (v.owner == mapThruKlon(k.owner, m));
       }


//  assert exists r <- cs_sp.fSin :: m.m[o] == r;
  assert (c.owner == mapThruKlon(o.owner, m));
  assert (c.bound == mapThruKlon(o.bound, m));
}


//GARGH assert forall o <- os_sp.fSin :: ( m.m[o] in rv );
//GARGH assert forall c <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == c;
//GARGH assert forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r;
//GARGH assert forall r <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == r;


//assert forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r;
//assert forall o <- os_sp.fSin :: m.m[o] in rv;
//assert mtk(os_sp.fSin,m) <= rv;

//assert cs_sp.fSin == mapThruKlon(os_sp.fSin, m);

}



lemma {:timeLimit 15} MAPPING_PIVOT(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(flatten(os))
   requires AllReady(flatten(cs))
   requires m.o.Ready()
   requires m.c.Ready()
   requires klonCalid(m)
   requires flatten(os) <= m.m.Keys
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)

   requires os_sp.fPvt == flownerOnlyPivot(os,m.o)
   requires cs_sp.fPvt == flownerOnlyPivot(cs,m.c)

    ensures forall o <- os_sp.fPvt  :: klonLine(o,m.m[o],m)
    ensures forall o <- os_sp.fPvt  :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os_sp.fPvt  :: klonIdentity(o,m.m[o],m)


    ensures if (m.o in flownerAll(os))
              then ((os_sp.fPvt == m.o.AMFO) && (cs_sp.fPvt == m.c.AMFO))
              else ((os_sp.fPvt == {})       && (cs_sp.fPvt == {}))

//     ensures (os_sp.fPvt == {})  <==> (cs_sp.fPvt == {})
//     ensures (os_sp.fPvt == m.o.AMFO) <==> (cs_sp.fPvt == m.c.AMFO)
    // ensures woodCrap(m.o,m.c,m)
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);
    //  WOOD_CRAP(m.o,m.c,m);

    flownerOnlyPivot_RESULT(os,m.o,os_sp.fPvt);
    flownerOnlyPivot_RESULT(cs,m.c,cs_sp.fPvt);

     ONLY_PIVOT(os,m.o,os_sp.fPvt);
     ONLY_PIVOT(cs,m.c,cs_sp.fPvt);
}

//
// lemma MAPPING_OUTSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
//    requires AllReady(os_sp.fAll)
//    requires AllReady(cs_sp.fAll)
//    requires klonCalid(m)
//
//    requires os <= m.m.Keys
//    requires cs == mapThruKlon(os,m)
//    requires flownerSplitOK(os,m.o,os_sp)
//    requires flownerSplitOK(cs,m.c,cs_sp)
//
//     ensures forall o <- os :: klonLine(o,m.m[o],m)
//     ensures forall o <- os :: klonGeometry(o,m.m[o],m)
//     ensures forall o <- os :: klonIdentity(o,m.m[o],m)
//     ensures forall o : Object <- (os_sp.fOut) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fOut) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fOut) :: o.bound == m.m[o].bound
//     ensures forall o : Object <- (os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.bound == m.m[o].bound
//
//     ensures forall o <- (os_sp.fOut) :: woodReal(o,m.m[o],m)
//     ensures forall o <- (os_sp.fXpt) :: woodReal(o,m.m[o],m)
//     ensures os_sp.fOut == cs_sp.fOut
//     ensures os_sp.fXpt == cs_sp.fXpt
// {
//      assert cs_sp == splitThruKlon(os,os_sp,m);
//      MAP_THRU_KLON(os,cs,m);
//      UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);
//
//      var os_Out := os_sp.fOut;
//      var cs_Out := cs_sp.fOut;
//      assert os_Out == flownerStrictlyOutside(os,m.o);
//      assert cs_Out == flownerStrictlyOutside(cs,m.c);
//
//      var os_Xpt := os_sp.fXpt;
//      var cs_Xpt := cs_sp.fXpt;
//      assert os_Xpt == flownerExceptPivot(os,m.o);
//      assert cs_Xpt == flownerExceptPivot(cs,m.c);
//
//     assert AllReady(os_sp.fAll);
//     assert AllReady(cs_sp.fAll);
//     assert klonCalid(m);
//     assert os <= m.m.Keys;
//
//
//    assert forall o <- os_sp.fOut :: outside(o, m.o);
//    assert forall o <- os_sp.fOut :: m.m[o] == o;
//
//    assert forall o <- cs_sp.fOut :: (outside(o,m.c));
//    assert forall o <- cs_sp.fOut :: m.m[o] == o;
//    assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: klonLine(k,o,m);
//    assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: (m.m[k] == o)  && (outside(k,m.o)) && (k == o);
//
//    assert forall o <- os_sp.fXpt :: outside(o, m.o);
//
//     assert os_sp.fOut >= cs_sp.fOut;
//     assert os_sp.fXpt >= cs_sp.fXpt;
//     assert os_sp.fOut <= cs_sp.fOut;
//     assert os_sp.fXpt <= cs_sp.fXpt;
//
//
//
//
//
//     assert os_sp.fXpt >= cs_sp.fXpt;
//     assert os_sp.fXpt <= cs_sp.fXpt;
//     assert os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt;
//
//
//     FOREST_REAL(os, os_sp,cs,cs_sp,m); //do I even need this?
//
//
// }






lemma MAPPING_OUTSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
//see HACKKING_THRU -
//
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys // requires m.allInKlon(os)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os,m.o,os_sp)
   requires flownerSplitOK(cs,m.c,cs_sp)
   requires forall o <- os_sp.fOut :: outside(o, m.o) //left out & recalcualted below

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)

    ensures forall o <- (os_sp.fOut + os_sp.fXpt) :: woodReal(o,m.m[o],m)
    ensures os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt


//this is the older verison
//
//    requires AllReady(os_sp.fAll)
//    requires AllReady(cs_sp.fAll)
//    requires klonCalid(m)
//
//    requires os <= m.m.Keys
//    requires forall o <- os_sp.fOut :: outside(o, m.o)
//    requires cs == mapThruKlon(os,m)
//    requires flownerSplitOK(os, m.o,os_sp)
//    requires flownerSplitOK(cs, m.c,cs_sp)
//
//
//
//     ensures forall o <- os :: klonLine(o,m.m[o],m)
//     ensures forall o <- os :: klonGeometry(o,m.m[o],m)
//     ensures forall o <- os :: klonIdentity(o,m.m[o],m)
//     ensures forall o : Object <- (os_sp.fOut) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fOut) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fOut) :: o.bound == m.m[o].bound
//     ensures forall o : Object <- (os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.owner == m.m[o].owner
//     // ensures forall o : Object <- (os_sp.fXpt) :: o.bound == m.m[o].bound
//
//     ensures forall o <- (os_sp.fOut) :: woodReal(o,m.m[o],m)
//     ensures forall o <- (os_sp.fXpt) :: woodReal(o,m.m[o],m)
//     ensures os_sp.fOut == cs_sp.fOut
//     ensures os_sp.fXpt == cs_sp.fXpt
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);

     var os_Out := os_sp.fOut;
     var cs_Out := cs_sp.fOut;
     assert os_Out == flownerStrictlyOutside(os,m.o);
     assert cs_Out == flownerStrictlyOutside(cs,m.c);

     var os_Xpt := os_sp.fXpt;
     var cs_Xpt := cs_sp.fXpt;
     assert os_Xpt == flownerExceptPivot(os,m.o);
     assert cs_Xpt == flownerExceptPivot(cs,m.c);

    assert AllReady(os_sp.fAll);
    assert AllReady(cs_sp.fAll);
    assert klonCalid(m);
    assert os <= m.m.Keys;

  //  assert AllReady(flatten(os));
  //  assert AllReady(flatten(cs));
  //  assert AllReady(flatten(os_sp.fOut));
  //  assert AllReady(flatten(cs_sp.fOut));
  //  assert AllReady(flatten(os_sp.fXpt));
  //  assert AllReady(flatten(cs_sp.fXpt));
  //  assert klonCalid(m);
  //  assert os      <= m.m.Keys;
  //  assert os_sp.fOut <= m.m.Keys;
  //  assert os_sp.fXpt <= m.m.Keys;
//
//   MAP_THRU_KLON(os,cs,m);
//   assert forall o <- cs | outside(o,m.c) :: (o == m.m[o]);




   assert forall o <- os_sp.fOut :: outside(o, m.o);


   assert forall o <- cs_sp.fOut :: (outside(o,m.c));
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: klonLine(k,o,m);
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: (m.m[k] == o)  && (outside(k,m.o)) && (k == o);
   assert forall o <- cs_sp.fOut :: m.m[o] == o;




   assert forall o <- os_sp.fXpt :: outside(o, m.o);





    assert os_sp.fOut >= cs_sp.fOut;
    assert os_sp.fXpt >= cs_sp.fXpt;
    assert os_sp.fOut <= cs_sp.fOut;
    assert os_sp.fXpt <= cs_sp.fXpt;




    FOREST_REAL(os, os_sp,cs,cs_sp,m); //do I even need this?


}








lemma HACKING_OUTSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
//see HACKKING_THRU -
//
 ///quick hack at combining fOUT and fXpt - so we don't need to track the outsideness of the soup, or something.
 ///I think the point is that an owner O >= B  should be OK even if  the "strictly ourside" owners in B
 //i.e things reachable from the soup *wihtout8 being inside the pivot
 //well O could be one owner that *is* inside the pivot which is inside Bl..
 //
 //  e.g. bound =   (pivot, someFullyExyernalObject)
 //  intermrdiate has owners =  (pivot, someFullyExyernalObject)
 //  bottom inherits from intermediate  (see notes) 0n
 //

   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires m.allInKlon(os)
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os,m.o,os_sp)
   requires flownerSplitOK(cs,m.c,cs_sp)

    ensures forall o <- os :: klonLine(o,m.m[o],m)
    ensures forall o <- os :: klonGeometry(o,m.m[o],m)
    ensures forall o <- os :: klonIdentity(o,m.m[o],m)
    ensures forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o)

    ensures forall o <- (os_sp.fOut + os_sp.fXpt) :: woodReal(o,m.m[o],m)
    ensures os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt
{
     assert cs_sp == splitThruKlon(os,os_sp,m);
     MAP_THRU_KLON(os,cs,m);
     UNPACK_flownerSplitOK(os,m.o,os_sp);

     assert (os_sp.fOut + os_sp.fXpt) <= os_sp.fAll <= m.m.Keys;

     assert forall o : Object <- (os_sp.fOut + os_sp.fXpt) :: outside(o,m.o) && (o == m.m[o] != m.o);

     UNPACK_flownerSplitOK(mapThruKlon(os,m),m.c,cs_sp);
     var os_Out := os_sp.fOut + os_sp.fXpt;
     var cs_Out := cs_sp.fOut + cs_sp.fXpt;
     assert os_Out == flownerStrictlyOutside(os,m.o) + flownerExceptPivot(os,m.o);
     assert cs_Out == flownerStrictlyOutside(cs,m.c) + flownerExceptPivot(cs,m.c);


    assert AllReady(os_sp.fAll);
    assert AllReady(cs_sp.fAll);
    assert klonCalid(m);
    assert os <= m.m.Keys;


   assert forall o <- os_sp.fOut :: outside(o, m.o);
   assert forall o <- os_sp.fOut :: m.m[o] == o;

   assert forall o <- cs_sp.fOut :: (outside(o,m.c));
   assert forall o <- cs_sp.fOut :: m.m[o] == o;
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: klonLine(k,o,m);
   assert forall o <- cs_sp.fOut :: exists k <- m.m.Keys :: (m.m[k] == o)  && (outside(k,m.o)) && (k == o);

    assert forall o <- os_sp.fXpt :: outside(o, m.o);



    assert os_sp.fOut >= cs_sp.fOut;
    assert os_sp.fXpt >= cs_sp.fXpt;
    assert os_sp.fXpt == cs_sp.fXpt;

    assert os_sp.fOut <= cs_sp.fOut;
    assert os_sp.fXpt <= cs_sp.fXpt;
    assert os_sp.fXpt == cs_sp.fXpt;

    assert os_sp.fOut + os_sp.fXpt >= cs_sp.fOut + cs_sp.fXpt;
    assert os_sp.fOut + os_sp.fXpt <= cs_sp.fOut + cs_sp.fXpt;
    assert os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt;

    FOREST_REAL(os, os_sp,cs,cs_sp,m); //do I even need this?

}

//
//
//
//     assert os_sp.fXpt >= cs_sp.fXpt;
//     assert os_sp.fXpt <= cs_sp.fXpt;
//     assert os_sp.fOut + os_sp.fXpt == cs_sp.fOut + cs_sp.fXpt;






lemma HACKING_THRU(oo : Owner, m : Klon)

 //this versionn adapted from MASTERTY_THRU for some reason1
  decreases allAMFOs(oo), 15
   requires klonCalid(m)
   requires m.allInKlon(oo)
   requires AllReady(oo)
   requires AllReady(mapThruKlon(oo,m))

  //  ensures  (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o)) ==
  //  (flownerStrictlyOutside(mapThruKlon(oo,m),m.c) + flownerExceptPivot(mapThruKlon(oo,m),m.c))
{
  assert oo <= m.m.Keys;
  assert flownerAll(oo) == flatten(oo) <= m.m.Keys;
  var cc := (mapThruKlon(oo,m));
  var fOX := (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o));
  var mOX := (flownerStrictlyOutside(cc,m.c) + flownerExceptPivot(cc,m.c));

  assert flownerStrictlyOutside(oo,m.o) <= flownerAll(oo);
  assert flownerExceptPivot(oo,m.o) <= flownerAll(oo);
  assert fOX <= flownerAll(oo) == flatten(oo) <= m.m.Keys;

  assert forall o <- flownerStrictlyOutside(oo,m.o) :: outside(o,m.o);
  assert forall o <- flownerExceptPivot(oo,m.o) :: outside(o,m.o);
  assert forall o <- fOX :: outside(o,m.o);
  assert forall o <- fOX :: m.m[o] == o;

assert flownerStrictlyOutside(cc,m.c) == mtk(flownerStrictlyOutside(oo,m.o), m);
assert flownerExceptPivot(cc,m.c) == mtk(flownerExceptPivot(oo,m.o), m);

//  assert mOX == mapThruKlon(fOX,m);

//  MAP_KLON_IDENTITY(fOX,mOX,m);
//
//   assert forall o <- flownerStrictlyOutside(oo,m.o) :: o in flownerStrictlyOutside(cc,m.c);
//   assert forall o <- flownerStrictlyOutside(cc,m.c) :: o in flownerStrictlyOutside(oo,m.o);
//   assert flownerStrictlyOutside(oo,m.o) <= flownerStrictlyOutside(cc,m.c);
//   assert flownerStrictlyOutside(oo,m.o) >= flownerStrictlyOutside(cc,m.c);
//   SetLtGtEq(flownerStrictlyOutside(oo,m.o),flownerStrictlyOutside(cc,m.c));
//   assert flownerStrictlyOutside(oo,m.o) == flownerStrictlyOutside(cc,m.c);
//
//
//   assert forall o <- flownerExceptPivot(oo,m.o) :: o in flownerExceptPivot(cc,m.c);
//   assert forall o <- flownerExceptPivot(cc,m.c) :: o in flownerExceptPivot(oo,m.o);
//   assert flownerExceptPivot(oo,m.o) <= flownerExceptPivot(cc,m.c);
//   assert flownerExceptPivot(oo,m.o) >= flownerExceptPivot(cc,m.c);
//   assert flownerExceptPivot(oo,m.o) == flownerExceptPivot(cc,m.c);
//
//   assert forall o <- flownerStrictlyOutside(oo,m.o) :: outside(o,m.o);
//   assert forall o <- flownerExceptPivot(oo,m.o) :: outside(o,m.o);
//   assert forall c <- flownerStrictlyOutside(cc,m.c) :: outside(c,m.c);
//   assert forall c <- flownerExceptPivot(cc,m.c) :: outside(c,m.c);
//
//   forall o <- fOX ensures ((m.m[o] == o) && (m.m[o] in mOX))
//     {
//       var c := m.m[o];
//       assert klonLine(o,c,m);
//       assert klonGeometry(o,c,m);
//       assert klonIdentity(o,c,m);
//       assert outside(o,m.o);
//       assert c == o;
//     }

  // assert fOX == mOX;
  // assert (flownerStrictlyOutside(oo,m.o) + flownerExceptPivot(oo,m.o)) ==
  //    (flownerStrictlyOutside(mapThruKlon(oo,m),m.c) + flownerExceptPivot(mapThruKlon(oo,m),m.c));
//  assert flownerDisjunctPivot(oo,m.o) == flownerDisjunctPivot(cc,m.c);
}






lemma STRICTLY_OUTSIDE_IN_SOUP(soup : Owner, o : Object, pivot : Object, owner : Object)
  requires AllReady(flatten(soup))
  requires o.Ready()
  requires pivot.Ready()
  requires owner.Ready()
  requires owner in flownerStrictlyOutside(soup, pivot)
  requires inside(o, owner)
  requires o in soup

   ensures forall s <- soup | outside(s,pivot) ::
             forall owner <- s.AMFO | outside(owner,pivot) ::
               owner in flownerStrictlyOutside(soup, pivot)

   // ensures forall s <- soup, owner <- flownerStrictlyOutside(soup, pivot) :: outside(owner,pivot) &&  outside(s,pivot) && inside(s,owner)

   ensures forall owner <- flownerStrictlyOutside(soup, pivot) ::
      exists s <- soup :: (
        && (outside(s,pivot))
        && (outside(owner,pivot))
        && (inside(s,owner))
      )


//   ensures forall owner <- flownerAll(soup) :: exists s <- soup ::  &&

   ensures owner in flatten(soup)
   ensures o in soup
   ensures outside(owner,pivot)
   {
     var Out := (set o <- soup, owner <- o.AMFO | PART_INSIDE_OWNER(soup,pivot); ownerStrictlyOutside(o,pivot,owner) :: owner);
     assert owner in Out;
   }
