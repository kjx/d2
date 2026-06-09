//include "Ownership-Recursive.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"

// //////////////////////////////////////////////////////////////////////////////////////////////////////////
//   assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
//   assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));
//   assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
//   assert flat_inside_nopivot == flat_below + flat_above;
//   assert flatten(owners_inside) ==
//   assert flat_above == flatten(whole_f) == flatten(fringe) + flatten(pivot_f)
//   assert flat_below ==
//
//   assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
 //flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot) + pflivot(owner, pivot) //sat 7 Jun
//   assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
//   return;
//////////////////////////////////////////////////////////////////////////////////////////////////////////

lemma VMapEQNEQ<K,V>(a : K, b : K, m : vmap<K,V>)
 requires a in m.Keys
 requires b in m.Keys
  ensures (a == b) <==> (m[a] == m[b])
{}

lemma MTKEQNEQ(a : Owner, b : Owner, m : Klon)
  requires a <= m.m.Keys
  requires b <= m.m.Keys
   ensures (a == b)  ==> (mapThruKlon(a,m) == mapThruKlon(b,m))
   ensures (a == b) <==  (mapThruKlon(a,m) == mapThruKlon(b,m))
   ensures (a == b) <==> (mapThruKlon(a,m) == mapThruKlon(b,m))
{ assert AllMapEntriesAreUnique(m.m);
  if (mapThruKlon(a,m) == mapThruKlon(b,m))
   {
      var mTKa := mapThruKlon(a,m);
      var mBKa := mapBackKlon(mTKa,m);
      var mTKb := mapThruKlon(b,m);
      var mBKb := mapBackKlon(mTKb,m);
      assert mTKa == mTKb;
      assert mBKa == mBKb == a == b;
   }
 }


method {:isolate_assertions} {:verify true} ownerAndBoundViaFringe(k : Object, m' : Klon) returns (rowner : Owner, rbound : Owner)
  requires k !in m'.m.Keys
  requires strictlyInside(k, m'.o)
  requires klonReady(m')
  requires klonCalid(m')
  requires COK(k, m'.oHeap)   requires COKA: COK(k, m'.oHeap)
  requires m'.ownersInKlown(k)
//NOENSURES   ensures myBoundsOK(rowner, rbound)
{
  var owner := k.owner;
  var bound := k.bound;

  assert myBoundsOK(owner, bound);

  var oin, oout, oflatb, ofringe := Zowner(owner, m'.o);
  var bin, bout, bflatb, bfringe := Zowner(bound, m'.c);

  rowner := owner;
  rbound := bound;
}



method {:isolate_assertions} {:verify true} ownerAndBoundForClone(k : Object, m' : Klon) returns (rowner : Owner, rbound : Owner)
  requires k !in m'.m.Keys
  requires strictlyInside(k, m'.o)
  requires klonReady(m')
  requires klonCalid(m')
  requires COK(k, m'.oHeap)   requires COKA: COK(k, m'.oHeap)
  requires m'.ownersInKlown(k)

//NOENSURES   ensures myBoundsOK(rowner, rbound)
{
  assert myBoundsOK(k.owner, k.bound);

  assert forall o <- k.owner :: klonLine(o, m'.m[o], m');

  forall o <- k.owner ensures (true) {
      assert klonLine(o, m'.m[o], m');
      assert klonIdentity(o, m'.m[o], m');
      assert myBoundsOK(o.owner, o.bound);

      if (o == m'.o)
         {
           assert o != m'.m[o];
           assert m'.m[o] == m'.c;
           assert m'.m[o].owner == m'.clowner;
           assert m'.m[o].bound == m'.clbound;

           assert (flatten(m'.m[o].owner) >= flatten(m'.m[o].bound));
           assert ( forall o <- m'.m[o].owner :: flatten(o.ownerBound()) >= flatten(m'.m[o].bound) );
           assert myBoundsOK(m'.m[o].owner, m'.m[o].bound);

          assert mapThruKlon(o.ownerBound(), m') == m'.m[o].ownerBound();
         }
      else if (outside(o, m'.o))
         {
           assert o == m'.m[o];

           assert (flatten(m'.m[o].owner) >= flatten(m'.m[o].bound));
           assert (forall o <- m'.m[o].owner :: flatten(o.ownerBound()) >= flatten(m'.m[o].bound));
           assert myBoundsOK(m'.m[o].owner, m'.m[o].bound);

           assert mapThruKlon(o.ownerBound(), m') == m'.m[o].ownerBound();
         }
      else
        {
          assert strictlyInside(o, m'.o);
          assert o != m'.o;
          assert o != m'.m[o];
          assert mapThruKlon(o.owner,m') == m'.m[o].owner;
          assert mapThruKlon(o.bound,m') == m'.m[o].bound;

          MTKEQNEQ(o.owner, o.bound, m');
          assert (o.owner == o.bound) <==> (mapThruKlon(o.owner,m') == mapThruKlon(o.bound,m'));

          if (o.owner == o.bound) {
              assert (mapThruKlon(o.owner,m') == mapThruKlon(o.bound,m'));
              assert o.ownerBound() == {o};
              assert m'.m[o].ownerBound() == {m'.m[o]};
          } else {
              assert (o.owner != o.bound);
              assert (mapThruKlon(o.owner,m') != mapThruKlon(o.bound,m'));//???
              assert o.ownerBound() == o.bound; //???
              assert m'.m[o].ownerBound() == m'.m[o].ownerBound();
          }

           assert (flatten(m'.m[o].owner) >= flatten(m'.m[o].bound)); //???
           assert (forall o <- m'.m[o].owner :: flatten(o.ownerBound()) >= flatten(m'.m[o].bound));
           assert myBoundsOK(m'.m[o].owner, m'.m[o].bound);

          assert mapThruKlon(o.ownerBound(), m') == m'.m[o].ownerBound();

        } //end if/elseif/else

  } //end forall


return;


  rowner := mapThruKlon(k.owner, m');
  rbound := mapThruKlon(k.bound, m');

  var RSowner := recSplatten(k.owner, m');
  var RSbound := recSplatten(k.bound, m');

  assert RSowner == flatten(rowner);
  assert RSbound == flatten(rbound);

  assert RSowner >= RSbound;

  assert (flatten(rowner) >= flatten(rbound));
  assert (forall o <- rowner :: flatten(o.ownerBound()) >= flatten(rbound));
  assert myBoundsOK(rowner, rbound);


}


//{:timeLimit 30} {:timeLimit 60}
lemma Zowner(owner : Owner, pivot : Object)
//topology?  enfringement?  whatevs?
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)

 requires AllReady(owner)
 requires pivot.Ready()     requires piR: pivot.Ready()

  ensures owners_inside  == set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures fringe     == set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  // ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot) //sat 7 Jun
  // // ensures reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  // // ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot)

  ensures frogbelow(flat_below, owners_inside, pivot)
  ensures reveal frogbelow();  flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot)
  ensures fringe     == set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures flat_below <= flatten(owners_inside)

  ensures froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures reveal froglet(); flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
{
  ReadyFlatten(owner);

  makerfield(owner,pivot);
  owners_inside  := set x <- owner |  inside(x, pivot);
  owners_outside := set x <- owner | outside(x, pivot);
  assert owner == owners_outside + owners_inside;
  assert FLOOI: flatten(owner) == flatten(owners_outside) + flatten(owners_inside);

  if (owners_inside == {})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner;
    assert flatten(owner) == flatten(owners_outside); //8 jun 2026
    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + {} + pflivot(owner, pivot); //sat 8 June 2026
    assert pflinge(owners_inside, pivot) == {};
    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot) + pflivot(owner, pivot); //sat 8 June 2026
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    assert reveal frogbelow(); frogbelow(flat_below, owners_inside, pivot);
    return;
  }

  if (owners_inside == {pivot})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner - {pivot};
    assert owners_inside - {pivot} == {};
    assert flat_below == (set x <- flatten(owners_inside - {pivot}) | inside(x,pivot)) == {};
    assert reveal frogbelow(); frogbelow(flat_below, owners_inside, pivot);

    assert flatten(fringe) == {};
    assert flatten(owner) == flatten(owners_outside) + {} + flatten(pivot.owner) + flatten(pivot.owner) + pflivot(owner, pivot); //mon 9 June 2026
    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot) + pflivot(owner, pivot); //sat 7 Jun 2026
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    return;
  }

  assert owners_inside > {};
  assert exists o <- owners_inside :: strictlyInside(o,pivot);

  flat_below, fringe :=  Zowners_inside(owners_inside, owners_outside, owner, pivot);


  assert fringe     == set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;

  assert flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot);
  assert frogbelow(flat_below, owners_inside, pivot);

  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
      by { reveal froglet(); }


  //assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
 // assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot); //sat 7 Jun

}

  //////////////////////////////////////////////////////////////////////////////

opaque predicate frogbelow(flat_below : Owner, owners_inside : Owner, pivot : Object)
  {  flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot) }

lemma NO_FROG_BELOW(flat_below : Owner, owners_inside : Owner, pivot : Object)
  requires owners_inside <= {pivot}
  requires flat_below == {}
   ensures reveal frogbelow(); frogbelow(flat_below, owners_inside, pivot)
{
  reveal frogbelow();
  assert flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot);
}
  //////////////////////////////////////////////////////////////////////////////


//{:timeLimit 30} {:timeLimit 60}
lemma Zowners_inside(owners_inside : Owner, owners_outside : Owner, owner : Owner, pivot : Object)
//topology?  enfringement?  whatevs?
  returns (flat_below : Owner, fringe : Owner)

 requires AllReady(owner)
 requires pivot.Ready()     requires piR: pivot.Ready()

 requires owners_inside == set x <- owner |  inside(x, pivot)
 requires owners_inside > {}
 requires exists o <- owners_inside :: strictlyInside(o,pivot)

 requires owners_outside == set x <- owner | outside(x, pivot)
 requires FLOOI: flatten(owner) == flatten(owners_outside) + flatten(owners_inside)

  ensures frogbelow(flat_below, owners_inside, pivot)
  ensures reveal frogbelow();  flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot)
  ensures fringe     == set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures flat_below <= flatten(owners_inside)
  ensures reveal frogbelow(); frogbelow(flat_below, owners_inside, pivot)

  ensures froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures reveal froglet(); flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
{
  ReadyFlatten(owner);
  var owners_inside_nopivot := owners_inside - {pivot};
  assert owners_inside_nopivot > {};  //implied by strictlyInside above

  if (pivot in owner) {
    assert pivot in owners_inside;
    assert owners_inside_nopivot + {pivot} == owners_inside;
    FLATTEN_SUM3(owners_inside_nopivot, {pivot}, owners_inside);
    assert flatten(owners_inside_nopivot) + flatten({pivot}) == flatten(owners_inside);
    assert pflivot(owner, pivot) == flatten({pivot});
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }
  else
  {
    assert pivot !in owners_inside;
    assert owners_inside_nopivot == owners_inside;
    assert flatten(owners_inside_nopivot) + {} == flatten(owners_inside);
    assert pflivot(owner, pivot) == {};
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }

    assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);



  var flat_inside_nopivot := flatten(owners_inside_nopivot);
  assert flat_inside_nopivot == flatten(owners_inside - {pivot});
   assert pivot in flat_inside_nopivot;
   FlattenContainsFlatten(owners_inside_nopivot,{pivot});
   assert flatten({pivot}) <= flat_inside_nopivot;    ///yes but htis pivot stems from one of the owners_inside_nopivot --- not pivot itself listed seperately
    assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);


      flat_below := set x <- flat_inside_nopivot | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flat_inside_nopivot | outside(x,pivot);  //do I need this one?
  makerfield(flat_inside_nopivot,pivot);
  assert flat_inside_nopivot == flat_below + flat_above;

  assert flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot);
  assert FROG_BELOW: frogbelow(flat_below, owners_inside, pivot) by { reveal frogbelow(); } //17s to verify on lately.
  // assert FROG_BELOW: frogbelow(flat_below, owners_inside, pivot) by { //this code only makes things worse
  //       assert FB1: flat_below == set x <- flat_inside_nopivot | inside(x,pivot);
  //       assert FB2: flat_inside_nopivot == flatten(owners_inside - {pivot});
  //       assert FB3: flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot) by { reveal FB1, FB2; }
  //       reveal FB3, frogbelow(); assert frogbelow(flat_below, owners_inside, pivot); } // by { reveal FB1, FB1, FB3; } }



//   assert flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot)        //apparently tyhis is 23s to verify??
//      by { }
//   assert FROG_BELOW: frogbelow(flat_below, owners_inside, pivot) by {
//        reveal frogbelow();
//        assert flat_inside_nopivot == flatten(owners_inside - {pivot});
//        reveal FLET_BELOW;
//        assert flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot);
//        }

var whole_f ;
var pivot_f;

//do I ned this call here - or can I just convert the following asserts into assignments?
whole_f,fringe,pivot_f := GordonRamseyThemFringes(owners_inside_nopivot, pivot);
// perhaops better to turn this around, have the definitions here,
//   and the pass them into as lemma, rather than getting them out of the lemma?


//jun05 2026
// assert   whole_f  == set x  <- flat_inside_nopivot, xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x  <- flat_inside_nopivot, xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x  <- flat_inside_nopivot, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
 assert  forall x <- flat_inside_nopivot |  inside(x,pivot)  :: x in flat_below;
assert  forall x <- flat_below :: (x in  flat_inside_nopivot) && inside(x,pivot);

// assert (set x <- flat_below) == (set x <- flat_inside_nopivot |  inside(x,pivot));
//
// assert   whole_f  == set x : Object <- flat_below, xo <- x.owner  |                                     && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x : Object <- flat_below, xo <- x.owner  | (x != pivot)                        && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x : Object <- flat_below, xo <- x.owner  | (x == pivot)                        && (outside(xo,pivot) ) :: xo;

assert pivot_f + fringe == whole_f;
FLATTEN_SUM3(pivot_f,fringe,whole_f);
assert flatten(pivot_f) + flatten(fringe) == flatten(whole_f);
assert pivot_f == pivot.owner;   assert PIVOT_FO: pivot_f == pivot.owner;


// assert flatten(whole_f)  == flat_above;

assert forall w <- whole_f :: outside(w,pivot);

  forall t <- flat_above ensures (t in (flatten(fringe) + flatten(pivot_f)))   // (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- owners_inside_nopivot | (t in flatten({part})) ensures (t in (flatten(fringe) + flatten(pivot_f))) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot)); //ORIG
      assert prev in flatten(owners_inside_nopivot);
      assert next in prev.owner;
      assert prev in flat_below;
      assert (next in flat_above) || (next == pivot);
      assert (next in fringe) || (next == pivot);
      assert t in flatten(owners_inside_nopivot);
      assert t in next.AMFO;
      assert t in flatten({next});
      if (next in fringe) { assert t in flatten(fringe); }
       else { assert next == pivot; assert t in flatten(pivot_f); }
      assert t in (flatten(fringe) + flatten(pivot_f));
    }
  }

  assert forall t <- flat_above ::(t in (flatten(fringe) + flatten(pivot_f)));

  assert ((flatten(fringe) + flatten(pivot_f)) >= flat_above);

  assert FPGE: ((flatten(fringe) + flatten(pivot.owner)) >= flat_above) by { reveal PIVOT_FO; }

  assert forall f <- flatten(fringe) :: f in flat_above;
  assert forall f <- flatten(pivot.owner) :: f in flat_above;
  assert forall f <- (flatten(fringe) + flatten(pivot.owner)) :: f in flat_above;
  SETIN((flatten(fringe) + flatten(pivot.owner)), flat_above);
  assert FPLE: (flatten(fringe) + flatten(pivot.owner)) <= flat_above;

  assert flat_above == (flatten(fringe) + flatten(pivot.owner)) by
   {
    reveal FPGE;  assert (flatten(fringe) + flatten(pivot.owner )) >= flat_above;
    reveal FPLE;  assert (flatten(fringe) + flatten(pivot.owner)) <= flat_above;
    SETLREQ((flatten(fringe) + flatten(pivot.owner)), flat_above);
   }
  assert      flat_above == (flatten(fringe) + flatten(pivot.owner));
  assert FAB: flat_above == (flatten(fringe) + flatten(pivot.owner));

  assert flat_inside_nopivot == flat_below + flat_above;
  assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner))
       by { reveal FAB;
            assert flat_above ==( (flatten(fringe) + flatten(pivot.owner)));
            assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner)); }


//glukk???  assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));

 assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);
 assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below + flat_above) + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below +   (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);

 assert BFPL: flatten(owners_inside) == (flat_below +   (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);

//  assert flatten(owners_inside) == ((set x <- flat_inside_nopivot | inside(x,pivot))  + (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);



  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside) by { reveal FLOOI; }
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
    by {
         reveal FLOOI;
         assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
         reveal BFPL;
         assert flatten(owners_inside) ==                  (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot);
         SATAN(owner, owners_outside, owners_inside, flat_below, fringe, pivot);
         assert flatten(owner) == flatten(owners_outside) + flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot);
        }

//  assert flatten(owner) == flatten(owners_outside) + (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot);
  assert flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot);
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe) by { reveal froglet(); }
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

  assert frogbelow(flat_below, owners_inside, pivot) by { reveal FROG_BELOW; }
  }





































lemma SETIN(left : Owner, right : Owner)
  requires forall f <- left :: f in right
   ensures left <= right
{}

lemma SETLREQ(left : Owner, right : Owner)
  requires left <= right
  requires left >= right
   ensures left == right
{}

//{:timeLimit 30} {:timeLimit 60}
lemma cartography(owner : Owner, pivot : Object)
//topology?  enfringement?  whatevs?
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)

 requires AllReady(flatten(owner))
 requires pivot.Ready()     requires piR: pivot.Ready()

  ensures owners_inside  == set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures flat_below == set x <- flatten(owners_inside) | inside(x,pivot)
  ensures fringe     == set x <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  //orig - 7Jun ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot) //sat 7 Jun
  ensures flat_below <= flatten(owners_inside)

{
  makerfield(owner,pivot);
  owners_inside  := set x <- owner |  inside(x, pivot);
  owners_outside := set x <- owner | outside(x, pivot);
  assert FLOOI: flatten(owner) == flatten(owners_outside) + flatten(owners_inside);

// //////////////////////////////////////////////////////////////////////////////////////////////////////////
//   assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
//   assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));
//   assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
//   assert flat_inside_nopivot == flat_below + flat_above;
//   assert flatten(owners_inside) ==
//   assert flat_above == flatten(whole_f) == flatten(fringe) + flatten(pivot_f)
//   assert flat_below ==
//
//   //OLDassert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
//   assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot); //sat 7 Jun
//   assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
//   return;
//////////////////////////////////////////////////////////////////////////////////////////////////////////



  if (owners_inside == {})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner;

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
    return;
  }


  if (owners_inside == {pivot})
  {
    flat_below := {pivot}; fringe := {};
    assert owners_outside == owner - {pivot};

    assert flat_below == {pivot};
    assert flatten(fringe) == {};
    assert flatten(owner) == flatten(owners_outside) + {pivot} + {} + pflivot(owner, pivot);

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
    return;
  }

//the pivot MAY be within owners_inside - but only if it's in the actual "owner" argument
//otherwise the pivot won't be in owners_inside
//BUT: the pivot (and its flattening) most certainly will be in flatten(owners_inside)
//because every one or the owners_inside is inside the pivot (by definiton)



  assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));

  assert owners_inside > {};

  assert exists o <- owners_inside :: strictlyInside(o,pivot);

  var owners_inside_nopivot := owners_inside - {pivot};
  assert owners_inside_nopivot > {};  //implied by strictlyInside above

  if (pivot in owner) {
    assert pivot in owners_inside;
    assert owners_inside_nopivot + {pivot} == owners_inside;
    FLATTEN_SUM3(owners_inside_nopivot, {pivot}, owners_inside);
    assert flatten(owners_inside_nopivot) + flatten({pivot}) == flatten(owners_inside);
    assert pflivot(owner, pivot) == flatten({pivot});
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }
  else
  {
    assert pivot !in owners_inside;
    assert owners_inside_nopivot == owners_inside;
    assert flatten(owners_inside_nopivot) + {} == flatten(owners_inside);
    assert pflivot(owner, pivot) == {};
    assert flatten(owners_inside_nopivot) + pflivot(owner, pivot) == flatten(owners_inside);
  }

    assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);


  var flat_inside_nopivot := flatten(owners_inside_nopivot);
   assert pivot in flat_inside_nopivot;
   FlattenContainsFlatten(owners_inside_nopivot,{pivot});
   assert flatten({pivot}) <= flat_inside_nopivot;    ///yes but htis pivot stems from one of the owners_inside_nopivot --- not pivot itself listed seperately
    assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);


      flat_below := set x <- flat_inside_nopivot | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flat_inside_nopivot | outside(x,pivot);  //do I need this one?
  makerfield(flat_inside_nopivot,pivot);
  assert flat_inside_nopivot == flat_below + flat_above;


var whole_f;
var pivot_f;

//do I ned this call here - or can I just convert the following asserts into assignments?
whole_f,fringe,pivot_f := GordonRamseyThemFringes(owners_inside_nopivot, pivot);
// perhaops better to turn this around, have the definitions here,
//   and the pass them into as lemma, rather than getting them out of the lemma?


//jun05 2026
// assert   whole_f  == set x  <- flat_inside_nopivot, xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x  <- flat_inside_nopivot, xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x  <- flat_inside_nopivot, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
 assert  forall x <- flat_inside_nopivot |  inside(x,pivot)  :: x in flat_below;
assert  forall x <- flat_below :: (x in  flat_inside_nopivot) && inside(x,pivot);

// assert (set x <- flat_below) == (set x <- flat_inside_nopivot |  inside(x,pivot));
//
// assert   whole_f  == set x : Object <- flat_below, xo <- x.owner  |                                     && (outside(xo,pivot) ) :: xo;
// assert   fringe   == set x : Object <- flat_below, xo <- x.owner  | (x != pivot)                        && (outside(xo,pivot) ) :: xo;
// assert   pivot_f  == set x : Object <- flat_below, xo <- x.owner  | (x == pivot)                        && (outside(xo,pivot) ) :: xo;

assert pivot_f + fringe == whole_f;
FLATTEN_SUM3(pivot_f,fringe,whole_f);
assert flatten(pivot_f) + flatten(fringe) == flatten(whole_f);
assert pivot_f == pivot.owner;   assert PIVOT_FO: pivot_f == pivot.owner;


// assert flatten(whole_f)  == flat_above;

assert forall w <- whole_f :: outside(w,pivot);

  forall t <- flat_above ensures (t in (flatten(fringe) + flatten(pivot_f)))   // (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- owners_inside_nopivot | (t in flatten({part})) ensures (t in (flatten(fringe) + flatten(pivot_f))) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot)); //ORIG
      assert prev in flatten(owners_inside_nopivot);
      assert next in prev.owner;
      assert prev in flat_below;
      assert (next in flat_above) || (next == pivot);
      assert (next in fringe) || (next == pivot);
      assert t in flatten(owners_inside_nopivot);
      assert t in next.AMFO;
      assert t in flatten({next});
      if (next in fringe) { assert t in flatten(fringe); }
       else { assert next == pivot; assert t in flatten(pivot_f); }
      assert t in (flatten(fringe) + flatten(pivot_f));
    }
  }

  assert forall t <- flat_above ::(t in (flatten(fringe) + flatten(pivot_f)));

  assert ((flatten(fringe) + flatten(pivot_f)) >= flat_above);

  assert FPGE: ((flatten(fringe) + flatten(pivot.owner)) >= flat_above) by { reveal PIVOT_FO; }

  assert forall f <- flatten(fringe) :: f in flat_above;
  assert forall f <- flatten(pivot.owner) :: f in flat_above;
  assert forall f <- (flatten(fringe) + flatten(pivot.owner)) :: f in flat_above;
  SETIN((flatten(fringe) + flatten(pivot.owner)), flat_above);
  assert FPLE: (flatten(fringe) + flatten(pivot.owner)) <= flat_above;

  assert flat_above == (flatten(fringe) + flatten(pivot.owner)) by
   {
    reveal FPGE;  assert (flatten(fringe) + flatten(pivot.owner )) >= flat_above;
    reveal FPLE;  assert (flatten(fringe) + flatten(pivot.owner)) <= flat_above;
    SETLREQ((flatten(fringe) + flatten(pivot.owner)), flat_above);
   }
  assert      flat_above == (flatten(fringe) + flatten(pivot.owner));
  assert FAB: flat_above == (flatten(fringe) + flatten(pivot.owner));

  assert flat_inside_nopivot == flat_below + flat_above;
  assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner))
       by { reveal FAB;
            assert flat_above ==( (flatten(fringe) + flatten(pivot.owner)));
            assert flat_inside_nopivot == flat_below +  (flatten(fringe) + flatten(pivot.owner)); }


 assert flatten(owners_outside) == flatten(set x <- owner | outside(x, pivot));

 assert flatten(owners_inside) == flatten(owners_inside_nopivot) + pflivot(owner, pivot);
 assert flatten(owners_inside) == flat_inside_nopivot + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below + flat_above) + pflivot(owner, pivot);
 assert flatten(owners_inside) == (flat_below +   (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);

 assert BFPL: flatten(owners_inside) == (flat_below +   (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);

//  assert flatten(owners_inside) == ((set x <- flat_inside_nopivot | inside(x,pivot))  + (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);



  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside) by { reveal FLOOI; }
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
    by {
         reveal FLOOI;
         assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
         reveal BFPL;
         assert flatten(owners_inside) ==                  (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot);
         SATAN(owner, owners_outside, owners_inside, flat_below, fringe, pivot);
         assert flatten(owner) == flatten(owners_outside) + flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot);
        }

 assert flatten(owner) == flatten(owners_outside) + (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot);
 assert flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot);
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe) by { reveal froglet(); }
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
  }


opaque predicate  froglet(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  { flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot) }
  //flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot) //sat 7 Jun


lemma SATAN(owner : Owner, owners_outside : Owner, owners_inside : Owner, flat_below : Owner, fringe : Owner, pivot : Object)
 requires flatten(owner) == flatten(owners_outside) + flatten(owners_inside)
 requires flatten(owners_inside) == (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
{}


lemma fromTheManyOne(less : seq<nat>, more : seq<nat>)
  requires |less| == |more|
  requires forall x | 0 <= x < |less| :: less[x] <= more[x]
  ensures sum(less) <= sum(more)
{}

function sum(s : seq<int>) : int
{ if (|s| == 0) then 0 else s[0] + sum(s[1..]) }


lemma FLATTEN_OWNER(o : Object)
  requires o.Ready()
   ensures flatten(o.owner) == o.AMFX
   ensures flatten({o}) == o.AMFO  >= flatten(o.owner)
{}


lemma FLATTEN_OWNER2(o : Object, oo : Object)
  requires o.Ready()
  requires oo.Ready()
  requires oo in o.owner
   ensures flatten(o.owner) == o.AMFX
   ensures flatten({o}) == o.AMFO  >= flatten(o.owner) >= flatten({oo})
{}





lemma farage(ownrs : OWNR, aliens : Owner)
  //flattening anuthing within flatten(ownrs) is also in flatten(ownrs)
  requires AllReady((ownrs))
  requires AllReady((aliens))
  requires aliens <= flatten(ownrs)
  ensures forall x : Object <- flatten(ownrs) :: x.AMFO <= flatten(ownrs)
  ensures flatten(aliens) <= flatten(ownrs)
{
  var all := flatten(ownrs);
  assert isFlat(all);
  assert flatten(aliens) <= flatten(ownrs);
}


lemma farage3(ownrs : OWNR, othrs : OWNR, aliens : Owner)
 //given aliaes in flattern(ownrs), faltten(alianes) in flattern(owners
  requires AllReady((ownrs))
  requires AllReady((othrs))
  requires AllReady((aliens))
  requires othrs <= ownrs
  requires aliens <= flatten(ownrs)
  ensures forall x : Object <- flatten(ownrs) :: x.AMFO <= flatten(ownrs)
  ensures flatten(othrs)  <= flatten(ownrs)
  ensures flatten(aliens) <= flatten(ownrs)
{
  var all := flatten(ownrs);
  assert isFlat(all);

  //  assert forall o <- all, oo <- o.AMFO :: oo in all;
  //  assert forall o <- all, oo <- o.AMFO :: oo.AMFO <= all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: oo in all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: oo.AMFO <= all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: ooo in all;
  //  assert forall o <- all, oo <- o.AMFO, ooo <- oo.AMFO :: ooo.AMFO <= all;

  assert forall x : Object <- all :: x.AMFO <= all;

  assert flatten(othrs)  <= flatten(ownrs);
  assert flatten(aliens) <= flatten(ownrs);

}


lemma {:timeLimit 30} makerfield(ownrs : OWNR, pivot : Object)
  requires AllReady(ownrs)   //was   requires AllReady(flatten(ownrs))
  requires pivot.Ready()
   ensures forall x <- ownrs ::    (x.AMFO >= pivot.AMFO) != (not(x.AMFO >= pivot.AMFO))
   ensures forall x <- ownrs :: not(x.AMFO >= pivot.AMFO) != not(not(x.AMFO >= pivot.AMFO))
   ensures forall x <- ownrs ::          outside(x,pivot) != not(outside(x,pivot))
   ensures forall x <- ownrs ::           inside(x,pivot) != not( inside(x,pivot))
   ensures forall x <- ownrs ::
        not(strictlyInside(x,pivot)) == (outside(x,pivot) || (x == pivot))
   ensures ownrs == (set x <- ownrs | inside(x,pivot)) + (set x <- ownrs | outside(x,pivot))
{}

lemma {:timeLimit 30} makerfield3(wholegroup : OWNR, pred : Object -> bool, ingroup : Owner, outgroup: Owner)
  requires AllReady(wholegroup)   //was   requires AllReady(flatten(wholegroup))
  requires ingroup  == set o <- wholegroup | pred(o)
  requires outgroup == set o <- wholegroup | not(pred(o))
  requires forall o <- wholegroup :: pred(o) != not(pred(o))
   ensures ingroup + outgroup == wholegroup
   ensures flatten(ingroup) + flatten(outgroup) == flatten(wholegroup)
{}


//weird pivot
function pflivot(owner : Owner, pivot : Object) : (fp : OWNR)
  { if (pivot in owner) then flatten({pivot}) else {} }

function pflinge(owner : Owner, pivot : Object) : (fp : OWNR)
  { if (owner > {}) then flatten(pivot.owner) else {} }

lemma flatten_monotonic(a : Owner, b : Owner)
  // requires AllReady(a)
  // requires AllReady(b)
   ensures (a == b) ==> flatten(a) == flatten(b)
   ensures (a < b) ==> flatten(a) <= flatten(b)
   ensures (a > b) ==> flatten(a) >= flatten(b)
{}



lemma  FROG_DISJOINT(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 left : Owner, pivot : Object)
                    requires left  == (li + lo + lb + lf + pflivot(left, pivot) )
  requires froglet(left, pivot,li,lo,lb,lf)
  requires frogbelow(lb, li, pivot)
{
  reveal froglet(), frogbelow();

assert lb == set x <- flatten(li - {pivot}) | inside(x,pivot);
assert lf == set x <- flatten(li - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;

assert forall b <- lb :: inside(b,pivot);
assert forall f <- lf :: outside(f,pivot);

  assert lb !! lf;
}


lemma  NAKED_LIBERATION(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
                    requires left  == (li + lo + lb + lf + pflivot(left, pivot) )
                    requires right == (ri + ro + rb + rf + pflivot(right,pivot) )
  requires ((li) >= (ri))
  requires ((lo) >= (ro))
  requires (lb >= rb)
  requires ((lf) >= (rf))
  requires (pflivot(left, pivot) >= pflivot(right,pivot))
   ensures ((left) >= (right))
{}


lemma  FLAT_LIVERATUIB(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
  requires froglet(left, pivot,li,lo,lb,lf)
  requires froglet(right,pivot,ri,ro,rb,rf)
  requires frogbelow(lb, li, pivot)
  requires frogbelow(rb, ri, pivot)

  requires ((li) >= (ri))
  requires ((lo) >= (ro))
  requires (lb >= rb)
  requires ((lf) >= (rf))
  requires (pflivot(left, pivot) >= pflivot(right,pivot))
  requires (pflinge(li, pivot) >= pflinge(ri, pivot))
   ensures (flatten(left) >= (right))
{
  reveal froglet();
  flatten_monotonic(li,ri);
  flatten_monotonic(lo,ro);
  flatten_monotonic(lb,rb);
  flatten_monotonic(lf,rf);
  flatten_monotonic(pflinge(li, pivot),pflinge(ri, pivot));
  flatten_monotonic(pflivot(left, pivot),pflivot(right, pivot));


  assert flatten(li) >= flatten(ri);
  assert flatten(lo) >= flatten(ro);
  assert flatten(lb) >= flatten(rb);
  assert flatten(lf) >= flatten(rf);
  assert (pflinge(li, pivot) >= pflinge(ri, pivot));
  assert (pflivot(left, pivot) >= pflivot(right,pivot));

  assert flatten(left)  == flatten(lo) + lb + flatten(lf) + pflinge(li, pivot) + pflivot(left,  pivot);
  assert flatten(right) == flatten(ro) + rb + flatten(rf) + pflinge(ri, pivot) + pflivot(right, pivot);

   assert (&& (flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf))
          && (pflinge(li, pivot) >= pflinge(ri, pivot)) && (pflivot(left, pivot) >= pflivot(right,pivot)) );
}




lemma LIVE_FLATRATUIB(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
  requires froglet(left, pivot,li,lo,lb,lf)
  requires froglet(right,pivot,ri,ro,rb,rf)
  requires frogbelow(lb, li, pivot)
  requires frogbelow(rb, ri, pivot)

  requires (flatten(left) >= flatten(right))
  //  ensures ((li) >= (ri))
  //  ensures ((lo) >= (ro))
  //  ensures (lb >= rb)
  //  ensures ((lf) >= (rf))
  //  ensures (pflivot(left, pivot) >= pflivot(right,pivot))
  //  ensures (pflinge(li, pivot) >= pflinge(ri, pivot))
{
  reveal froglet(), frogbelow();
  // flatten_monotonic(li,ri);
  // flatten_monotonic(lo,ro);
  // flatten_monotonic(lb,rb);
  // flatten_monotonic(lf,rf);
  // flatten_monotonic(pflinge(li, pivot),pflinge(ri, pivot));
  // flatten_monotonic(pflivot(left, pivot),pflivot(right, pivot));

     assert (flatten(left) >= flatten(right));

  //assert forall x <- flatten(right) :: x in flatten(left);

  assert flatten(left)  == flatten(lo) + lb + flatten(lf) + pflinge(li, pivot) + pflivot(left,  pivot);
  assert flatten(right) == flatten(ro) + rb + flatten(rf) + pflinge(ri, pivot) + pflivot(right, pivot);

  assert flatten(lo) + lb + flatten(lf) + pflinge(li, pivot) + pflivot(left,  pivot) >= flatten(lo) + lb + flatten(lf) + pflinge(li, pivot) + pflivot(left,  pivot);

  var FL := flatten(lo) + lb + flatten(lf) + pflinge(li, pivot) + pflivot(left,  pivot);
  var FR := flatten(ro) + rb + flatten(rf) + pflinge(ri, pivot) + pflivot(right, pivot);

  assert FL == flatten(left);
  assert FR == flatten(right);
  assert FL >= FR;

  // assert forall x <- flatten(right) :: x in flatten(left);
  // assert forall x <- FR :: x in flatten(left);
  // assert forall x <- flatten(right) :: x in FL;
  // assert forall x <- FR :: x in FL;

//
//   assert FL >= FR by
//    {
//      assert FL == flatten(left);
//      assert FR == flatten(right);
//      assert (flatten(left) >= (right));
//      assert FL >= FR;
//    }

  //        (flatten(ro) + rb + flatten(rf) + pflinge(ri, pivot) + pflivot(right, pivot));

  assert flatten(li) >= flatten(ri);
  assert flatten(lo) >= flatten(ro);
  assert flatten(lb) >= flatten(rb);
  assert flatten(lf) >= flatten(rf);
  assert (pflinge(li, pivot) >= pflinge(ri, pivot));
  assert (pflivot(left, pivot) >= pflivot(right,pivot));



  //  assert (|| (flatten(lo) >= flatten(ro)) || (lb >= rb) || (flatten(lf) >= flatten(rf))
  //         || (pflinge(li, pivot) >= pflinge(ri, pivot)) || (pflivot(left, pivot) >= pflivot(right,pivot)) );
}



lemma {:verify false} DaysOfOpenHand2(left : Owner, right : Owner, pivot : Object)
///this is totally brokwn.
///BUT see "FLAT_LIVERATUIB" above. that shows things will all work, doesn't it?
///
        //  li : Owner, lo : Owner, lb : Owner, lf : Owner,
        //  ri : Owner, ro : Owner, rb : Owner, rf : Owner)

  requires AllReady(flatten(left))
  requires AllReady(flatten(right))
  requires pivot.Ready()
  // requires flatten(left) >= pivot.AMFO
  // requires flatten(right) >= pivot.AMFO
  requires exists x <- left :: inside(x, pivot) ///hmmmm
  requires exists x <- right :: inside(x, pivot) ///hmmmm

  // ensures (flatten(left) >= flatten(right)) <== ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)))

  // requires (flatten(lo) >= flatten(ro))
  // requires (lb >= rb)
  // requires (flatten(lf) >= flatten(rf))
  // requires (pflivot(left, pivot) >= pflivot(right,pivot))

  //  ensures (flatten(left) >= flatten(right))
{
  var li,lo,lb,lf := tiredOfSleeping(left, pivot);
  var ri,ro,rb,rf := tiredOfSleeping(right, pivot);

  assert flatten(left)  == flatten(lo) + lb + flatten(lf) + pflivot(left,  pivot);
  assert flatten(right) == flatten(ro) + rb + flatten(rf) + pflivot(right, pivot);

  assert li !! lo;
  assert flatten(li) >= lb;
  assert flatten(left) == flatten(li) + flatten(lo);    //flatten is monotinic

  assert (flatten(left) >= flatten(right)) <== ((flatten(lo) >= flatten(ro)) && (lb >= rb) && (flatten(lf) >= flatten(rf)) && (pflivot(left, pivot) >= pflivot(right,pivot)) );
  assert (flatten(left) >= flatten(right)) ==> ((flatten(lo) >= flatten(ro)) || (lb >= rb) || (flatten(lf) >= flatten(rf)) || (pflivot(left, pivot) >= pflivot(right,pivot)) );


  assert (flatten(lo) >= flatten(ro));
  assert (lb >= rb);
  assert (flatten(lf) >= flatten(rf));
  assert (pflivot(left, pivot) >= pflivot(right,pivot));

  assert (flatten(left) >= flatten(right));
}

//{:timeLimit 30}
lemma {:timeLimit 60}
tiredOfSleeping(owner : Owner, pivot : Object)
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  //FUCK,. shoudl xGG indeed series of functions?
  //pivot or Klon??
//likely needs at least 20s to verify on M2
 requires AllReady(flatten(owner))
 requires pivot.Ready()     requires piR: pivot.Ready()
//requires flatten(owner) >= pivot.AMFO

// requires exists x <- owner :: inside(x, pivot) ///hmmmm

  ensures owners_inside ==  set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures flat_below == set x <- flatten(owners_inside) | inside(x,pivot)
  ensures fringe == set x <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot)

  ensures flat_below <= flatten(owners_inside)

{
  owners_inside, owners_outside := SplitTheDeadOwners(owner, pivot);

  if (owners_inside == {})
  {
    flat_below := {}; fringe := {};
    assert owners_outside == owner;
    // assert flat_below == {};
    assert flatten(owner) == flatten(owners_outside);
    // assert flatten(fringe) == {};

    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    return;
    //a more dedicated model could do more here, but not needed for correctness
  }

  if (owners_inside == {pivot})
  {
    flat_below := {pivot}; fringe := {};
    assert owners_outside == owner - {pivot};
    assert flat_below == {pivot};
    assert flatten(fringe) == {};
    assert flatten(owner) == flatten(owners_outside) + {pivot} + {} + pflivot(owner, pivot);


    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
    assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);

    return;
    //a more dedicated model could do more here, but not needed for correctness
  }
 flat_below := {pivot}; fringe := {};
  return;

  assert owners_inside > {};

  assert pflivot(owner, pivot) == flatten({pivot});

  flat_below := set x <- flatten(owners_inside) | inside(x,pivot);   ///pivot will be inside
  var flat_above := set x <- flatten(owners_inside) | outside(x,pivot);
  assert flatten(owners_inside) == flat_below + flat_above;

var flatI,flatO,fw := FlattenFringeIsAllOutside(owners_inside - {pivot},pivot);
assert flatten(fw) <= flatO;

assert flatI == flat_below;
assert flatO == flat_above;

var whole_f;
var pivot_f;

whole_f,fringe,pivot_f := GordonRamseyThemFringes(owners_inside, pivot);

// //////////////////////////////////////////////////////////////////////////////////////////////////////////
// assume flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflivot(owner, pivot);
//   assert reveal froglet(); froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
//       return;
//////////////////////////////////////////////////////////////////////////////////////////////////////////


assert   fringe   == set x  <- flatten(owners_inside), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
assert   whole_f  == set x  <- flatten(owners_inside), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
assert   pivot_f  == set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;

//jun4 assert fw == whole_f;
//jun4 assert flatten(whole_f) == flat_above;


//
// assert fw == whole_f;
// assert flatten(whole_f) == flat_above;
//
// assert (set x  <- flatten(owners_inside), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));
//
// assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner :: xo)
//           ==
//        (pivot.owner);
//
//
//  assert pivot_f == pvtfrng == pivot.owner;
//
// forall x <- flatten(owners_inside), xo <- x.owner ensures (whole_f == pivot_f + fringe) {
//  if ( (inside(x,pivot) ) && (outside(xo,pivot) ) )
//    {
//     assert xo in whole_f;
//     if (x == pivot)
//       {
//          assert xo in pivot_f;
//          assert xo in pvtfrng;
//          assert xo in pivot.owner;
//          assert pivot_f == pvtfrng == pivot.owner;
//       } else {
//          assert xo in fringe;
//          //assert pivot_f == pvtfrng;
//       }
//       assert (xo in pivot_f) || (xo in fringe);
//       assert whole_f == pivot_f + fringe;
//     //  assert pivot_f == pvtfrng == pivot.owner;
//
//    } //end if
//
//
// }//end foreach
//
//   assert whole_f == fringe + pivot_f;
//   assert whole_f == fringe + pivot.owner;

//jun04  assert flatten(whole_f) == flat_above;
//jun04   assert flatten(fringe + pivot.owner) == flat_above;
//jun04   assert flatten(fringe) + flatten(pivot.owner) == flat_above;
//jun04
//jun04   assert flat_above == flatten(fringe + pivot.owner);
//jun04   assert flat_above == flatten(fringe) + flatten(pivot.owner);
//jun04
//jun04   assert flatten({pivot}) == {pivot} + flatten(pivot.owner);
//jun04   assert flat_above == flatten(fringe) + flatten(pivot.owner);
//jun04   assert flat_above + {pivot} == flatten(fringe) + flatten({pivot});
//jun04
//jun04   assert pivot in flat_below;
//jun04   assert flat_below + flat_above == flat_below + flatten(fringe) + flatten({pivot});


  assert flatten(owners_inside) == flat_below + flat_above;
  assert flatten(owners_inside) == flat_below + flatten(fringe) + flatten({pivot});

  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + flatten({pivot});
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe) by { reveal froglet(); }
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
}




lemma SplitTheDeadOwners(ownrs : OWNR, pivot : Object) returns (onnsiders : Owner, offsiders : Owner)
  requires AllReady(flatten(ownrs))
  requires pivot.Ready()
  ensures onnsiders == set x <- ownrs |  inside(x, pivot)
  ensures offsiders == set x <- ownrs | outside(x, pivot)
  ensures ownrs == offsiders + onnsiders
  ensures ownrs - offsiders == onnsiders
  ensures ownrs - onnsiders == offsiders
  ensures offsiders !! onnsiders
  ensures flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders))
  ensures flatten(ownrs) >=  flatten(offsiders)
  ensures flatten(ownrs) >=  flatten(onnsiders)
{
  onnsiders := set x <- ownrs |  inside(x, pivot);
  offsiders := set x <- ownrs | outside(x, pivot);  //outside df not inside.

  makerfield(ownrs, pivot);

///GOLLUM assert forall x <- ownrs :: (x.AMFO >= pivot.AMFO) != not(x.AMFO >= pivot.AMFO); //ERR
///GOLLUM assert forall x <- ownrs :: (outside(x, pivot) != not(outside(x, pivot)));       //ERR

  assert ownrs == offsiders + onnsiders;
  assert offsiders !! onnsiders;
  assert flatten(ownrs) == (flatten(offsiders) + flatten(onnsiders));
}

lemma FlattenOutsideFlatten(sider : Object, pivot : Object)
  requires sider.Ready()
  requires pivot.Ready()
  requires outside(sider,pivot)
   ensures forall x <- sider.AMFO :: outside(x,pivot)
{}


lemma FlattenContainsFlatten(below : Owner, above : Owner)
  //flattening above within flatten(ownrs) is also in flatten(ownrs)
  //replaces farage
  requires AllReady(below)
  requires AllReady(above)
  requires flatten(below) >= above
   ensures forall x : Object <- above:: x.AMFO <= flatten(below)
   ensures forall x : Object <- flatten(below) :: x.AMFO <= flatten(below)
   ensures flatten(below) >= flatten(above)
{
  //  assert isFlat( flatten(below) );
  //  assert forall o <- flatten(below), oo <- o.AMFO :: oo in flatten(below);
  // assert forall o <- flatten(below) :: o.AMFO <= flatten(below);
  //  assert forall a <- above :: a in flatten(below);
  //   assert forall a <- above :: a.AMFO <= flatten(below);\
}

lemma ReadyFlatten(oo : Owner)
 requires AllReady(oo)
  ensures AllReady(flatten(oo))
{}

//is "inside_pivot" a better name than owners_inside
//{:timeLimit 20}
lemma  GordonPivotFringeInsideFlatternOwner(owners_inside_nopivot : Owner, pivot : Object, whole_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)
 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()
 requires whole_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo
  ensures forall x  <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo in flatten(owners_inside_nopivot)
  // flatten(owners_inside_nopivot) >= (whole_f) //BUT IT's XO X!!!
  ensures flatten(owners_inside_nopivot) >= flatten(whole_f)
{
  forall x : Object <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) ensures ( xo in flatten(owners_inside_nopivot) ) //by
   {
  assert AllReady(flatten(owners_inside_nopivot));
  assert x.Ready() by {
    assert AllReady(flatten(owners_inside_nopivot));
    assert x in flatten(owners_inside_nopivot);
    assert forall q <- flatten(owners_inside_nopivot) :: q.Ready();
    assert x.Ready();
    }
  assert xo.Ready();
  assert x in flatten(owners_inside_nopivot);
  assert xo in x.owner;
    FlattenContainsFlatten(owners_inside_nopivot,x.owner);
    assert flatten(owners_inside_nopivot) >= flatten(x.owner);
    // OwnerInFlatten(owners_inside_nopivot, x, xo);
   }

  forall x <- flatten(owners_inside_nopivot), xo <- x.owner ensures flatten(owners_inside_nopivot) >= flatten({x}) >= flatten(x.owner) >= flatten({xo})
     {
    assert x.Ready() by {
        assert AllReady(flatten(owners_inside_nopivot));
        assert x in flatten(owners_inside_nopivot);
        assert forall q <- flatten(owners_inside_nopivot) :: q.Ready();
        assert x.Ready();
    }
     assert x in flatten(owners_inside_nopivot);
     assert xo in flatten(owners_inside_nopivot);
     OwnerInFlatten(owners_inside_nopivot, x, xo);
     }


 forall x <- whole_f ensures (flatten(owners_inside_nopivot) >= flatten({x}))
  {
    assert x in flatten(owners_inside_nopivot);
    FlattenContainsFlatten(owners_inside_nopivot,{x});
  }


  assert flatten(owners_inside_nopivot) >= flatten(whole_f);
}


lemma  GordonPivotFringeIsPivotOwner(owners_inside_nopivot : Owner, pivot : Object, pivot_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)
 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()

 requires pivot_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == pivot.owner
{
assert (set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);

assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);

assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));

assert inside(pivot,pivot);

assert forall xo <- pivot.owner :: outside(xo,pivot);

assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
          ==
       (set xo <- pivot.owner :: xo);

assert (set xo <- pivot.owner :: xo)
          ==
       (pivot.owner);


}


//is "inside_pivot" a better name than owners_inside
//{:timeLimit 20}
lemma {:timeLimit 20} GordonRamseyThemFringes(owners_inside_nopivot : Owner, pivot : Object) returns (whole_f : Owner, fringe : Owner, pivot_f : Owner)

 requires forall i <- owners_inside_nopivot :: inside(i, pivot)

 requires owners_inside_nopivot > {}
 requires AllReady(owners_inside_nopivot)
 requires pivot.Ready()
  ensures whole_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures fringe  == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
  ensures pivot_f == pivot.owner
  ensures whole_f == pivot_f + fringe
  ensures whole_f == fringe + pivot.owner
  ensures flatten(owners_inside_nopivot) >= flatten(whole_f)
  ensures flatten(owners_inside_nopivot) >= flatten(fringe)
  ensures flatten(owners_inside_nopivot) >= flatten(pivot_f)
  ensures forall f <- whole_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures forall f <- fringe  :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures forall f <- pivot_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot)
  ensures AllReady(flatten(owners_inside_nopivot))
  ensures AllReady(whole_f)
  ensures AllReady(fringe)
  ensures AllReady(pivot_f)
{
          fringe  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
         whole_f  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner |                  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
         pivot_f  := set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
     var pvtfrng  := set xo <- pivot.owner                                   |                                        (outside(xo,pivot) ) :: xo;

//
// assert WHOLEOIN: flatten(owners_inside_nopivot) >= whole_f;
// FlattenContainsFlatten(owners_inside_nopivot, whole_f);
// assert flatten(owners_inside_nopivot) >= flatten(whole_f);
//
// assert FRINFOIN: flatten(owners_inside_nopivot) >= fringe;
// FlattenContainsFlatten(owners_inside_nopivot, fringe);
// assert flatten(owners_inside_nopivot) >= flatten(fringe);


assert AllReady(owners_inside_nopivot);
ReadyFlatten(owners_inside_nopivot);
assert AllReady(flatten(owners_inside_nopivot));
assert forall x <- flatten(owners_inside_nopivot), xo <- x.owner :: x.Ready() && xo.Ready();

forall x  <- flatten(owners_inside_nopivot), xo <- x.owner ensures (whole_f == pivot_f + fringe)  //by
 {
    if (inside(x,pivot) ) && (outside(xo,pivot))
      {
        assert xo in whole_f;
        if (x == pivot) { assert xo in pivot_f;
                          assert xo in pivot.owner; }
        if (x != pivot) { assert xo in fringe; }

        assert x.Ready();
        assert xo.Ready();
        FLATTEN_OWNER2(x,xo);

      }
 }
assert whole_f >= pivot_f + fringe;
assert whole_f <= pivot_f + fringe;

//  assert forall i <- owners_inside_nopivot :: inside(i, pivot);
//  assert owners_inside_nopivot > {};
//  assert AllReady(owners_inside_nopivot);
//  assert pivot.Ready();

GordonPivotFringeIsPivotOwner(owners_inside_nopivot, pivot, set x <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) && (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
);
//
// assert (set x  <- flatten(owners_inside_nopivot), xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert (set x : Object <- {pivot}, xo <- x.owner | (x == pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo);
//
// assert forall xo <- pivot.owner :: (inside(pivot,pivot) ) && (outside(xo,pivot));
//
// assert inside(pivot,pivot);
//
// assert forall xo <- pivot.owner :: outside(xo,pivot);
//
// assert (set xo <- pivot.owner | (inside(pivot,pivot) ) && (outside(xo,pivot) ) :: xo)
//           ==
//        (set xo <- pivot.owner :: xo);
//
// assert (set xo <- pivot.owner :: xo)
//           ==
//        (pivot.owner);
//

 assert pivot_f == pvtfrng == pivot.owner;


  assert pivot_f == pivot.owner;
  assert whole_f == pivot_f + fringe;
  assert whole_f == fringe + pivot.owner;
//whole_f == set x <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo
  GordonPivotFringeInsideFlatternOwner(owners_inside_nopivot, pivot, set x <- flatten(owners_inside_nopivot), xo <- x.owner | (outside(xo,pivot) ) :: xo);

  assert flatten(owners_inside_nopivot) >= flatten(whole_f);
  assert flatten(owners_inside_nopivot) >= flatten(fringe);
  assert flatten(owners_inside_nopivot) >= flatten(pivot_f);
  assert forall f <- whole_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);
  assert forall f <- fringe  :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);
  assert forall f <- pivot_f :: (f in flatten(owners_inside_nopivot)) && outside(f,pivot);





forall x <- flatten(owners_inside_nopivot), xo <- x.owner ensures (whole_f == pivot_f + fringe) {
  assert x.Ready();
  assert xo.Ready();

 if ( (inside(x,pivot) ) && (outside(xo,pivot) ) )
   {
    assert xo in whole_f;
    if (x == pivot)
      {
         assert xo in pivot_f;
         assert xo in pvtfrng;
         assert xo in pivot.owner;
         assert pivot_f == pvtfrng == pivot.owner;
      } else {
         assert xo in fringe;
         //assert pivot_f == pvtfrng;
      }
      assert (xo in pivot_f) || (xo in fringe);
      assert whole_f == pivot_f + fringe;
    //  assert pivot_f == pvtfrng == pivot.owner;

   } //end if


}//end foreach

  assert whole_f == fringe + pivot_f;
  assert whole_f == fringe + pivot.owner;


  // FlattenContainsFlatten(owners_inside_nopivot, fringe) by
  //   { assert fringe <= flatten(owners_inside_nopivot) by { reveal FRINFOIN; } }

}//end GordonRamsey

///FUCK FCUK FUCK
lemma FlattenFringeIsAllOutside(iwnrs : OWNR,  pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
   ///used in tiredOfSleeping... so need to worry
  //ensuress flatten(fringe) == allOutside
  //all iwnrs must all be strictlyInside pivot????
  //pretty much the wrong thing cons iwnrs != owners != ownrs != onnsiders...
  //iwnrs better be equal to owners_Inside???
  //note - works OK if iwners == {}.   just take the pibot out ogf owners_inside before calling this.
 requires forall i <- iwnrs :: strictlyInside(i, pivot)
  //or coudl do it here I gues...

 requires AllReady(flatten(iwnrs))
 requires pivot.Ready()

    ensures allInside  == set x <- flatten(iwnrs) | inside(x, pivot)
    ensures allOutside == set x <- flatten(iwnrs) | outside(x, pivot)
  ensures allInside !! allOutside
  ensures flatten(iwnrs) == (allInside + allOutside)
  //  ensures fringe ==  set x <- allInside, xo <- x¸ | (xo in allOutside)  :: xo

  ensures fringe == set x <- flatten(iwnrs), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures iwnrs <= allInside
  ensures forall o <- allInside  :: o.owner <= (allInside + allOutside)
  ensures forall o <- allOutside :: o.owner <= allOutside
  ensures fringe == set x <- allInside, xo <- x.owner | (x != pivot) &&   (xo in allOutside)  :: xo //original version
//  ensures forall o <- flatten(iwnrs), oo <- o.owner :: (o != pivot) &&  (inside(o,pivot) ) && (outside(oo,pivot) )
  ensures fringe <= allOutside
  ensures flatten(fringe) <= allOutside
  //ensures (flatten(fringe) + flatten({pivot})) == allOutside
{

  allInside  := set x <- flatten(iwnrs) | inside(x, pivot);
  allOutside := set x <- flatten(iwnrs) | outside(x, pivot);

//for nightly?
 forall x <- flatten(iwnrs) ensures flatten(iwnrs) == (allInside + allOutside) //by
  {
    if inside(x, pivot) { assert x in allInside; } else { assert outside(x, pivot); assert x in allOutside; }
  }


 //old fringe := set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;
 //opt fringe := set x <- allInside, xo <- x.owner |  (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
   fringe := set x <- flatten(iwnrs), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
 assert fringe == set x <- allInside, xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  assert fringe <= allOutside;
  OUTSIDE_OUTSIDE(fringe, pivot);
  assert forall f <- flatten(fringe) :: outside(f,pivot);
  assert forall f <- flatten(fringe) :: f in flatten(iwnrs);
  assert flatten(fringe) <= allOutside;

  assert forall t <- allOutside :: t in flatten(iwnrs);


  forall t <- allOutside ensures (t in (flatten(fringe) + flatten({pivot})))   // (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    forall part <- iwnrs | (t in flatten({part})) ensures (t in (flatten(fringe) + flatten({pivot}))) {
      var prev, next := AcrossTheBorder(part, pivot, t);
      assert strictlyInside(prev,t);
      assert not(strictlyInside(next,pivot)); //ORIG
      assert prev in flatten(iwnrs);
      assert next in prev.owner;
      assert prev in allInside;
      assert (next in allOutside) || (next == pivot);
      assert (next in fringe) || (next == pivot);
      assert t in flatten(iwnrs);
      assert t in next.AMFO;
      assert t in flatten({next});
      if (next in fringe) { assert t in flatten(fringe); }
       else { assert next == pivot; assert t in flatten({pivot}); }
      assert t in (flatten(fringe) + flatten({pivot}));
    }
  }

  assert (flatten(fringe) + flatten({pivot})) >= allOutside;
//  assert (flatten(fringe) + flatten({pivot})) == allOutside;

}





lemma Notin(ownrs : OWNR,  pivot : Object, allInside : Owner, allOutside : Owner, fringe : Owner)
  //proof by contradiction
  //pivot is not in rest of fringe
  //was going to extend to an "OnlyTHrough" apparently
  requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  requires allInside  == set x <- flatten(ownrs) | strictlyInside(x, pivot)
  requires allOutside == set x <- flatten(ownrs) | not(strictlyInside(x, pivot))
  // requires allInside !! allOutside
  // requires flatten(ownrs) == (allInside + allOutside)
  requires fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  // requires fringe <= allOutside
  //requires (allInside > {}) ==> (flatten(fringe) == allOutside)
  //requires (allInside > {}) ==> (pivot in fringe)

  ensures pivot !in flatten(fringe - {pivot})
{
  if (pivot in flatten(fringe - {pivot})) {
    assert not(fringe <= allOutside);
    assert false;
  }
}



lemma {:resource_limit 70000000}  {:timeLimit 20} splitOwnersAroundPivot(part : Object, pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
  //splits all into the bits inside pivot,
  //the bits outside pivot,
  //and the fringe (bits outside that are direct owners of an owner inside...)
  //FUCK,. shoudl this be a function?  or indeed series of functions?
  requires part.Ready()
  requires pivot.Ready()
  requires strictlyInside(part, pivot)

  ensures AllReady(allInside)
  ensures AllReady(allOutside)
  ensures AllReady(fringe)

  ensures allInside  == set x <- part.AMFO | strictlyInside(x, pivot)
  ensures allOutside == set x <- part.AMFO | not(strictlyInside(x, pivot))
  ensures allInside !! allOutside
  ensures part.AMFO == (allInside + allOutside)
  ensures fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo
  ensures forall x <- fringe :: x in allOutside
  ensures flatten(fringe) == allOutside
  ensures pivot in fringe
  ensures (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo
  //rensures flatten(fringe) + flatten({pivot}) == allOutside
  //ensures flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside

  //ensures all == recOwners(part)  //can do with Axioms from Ownership-Parallel if necessary...

{
  var all := part.AMFO;

  allInside  := set x <- all | strictlyInside(x, pivot);
  assert part in allInside;

  allOutside := all - allInside;
  assert forall x <- allOutside :: not(strictlyInside(x, pivot));
  assert pivot in allOutside;

  assert forall x <- all :: strictlyInside(x, pivot) != not(strictlyInside(x, pivot));

  assert allInside !! allOutside;
  assert all == (allInside + allOutside);

  fringe := set x <- all, xo <- x.owner | (x in allInside) && (xo in allOutside)  :: xo;
  assert fringe <= allOutside;
  assert fringe == set x <- allInside, xo <- x.owner | (xo in allOutside)  :: xo;

  assert part !in fringe;
  //   assert exists x <- allInside, xo <- x.owner ::  xo == pivot;

  var prev := YouGetThereEventually(part, pivot);
  assert pivot in prev.owner;
  assert strictlyInside(prev,pivot);
  assert prev in all;
  assert inside(part,prev);
  assert prev in allInside;
  assert pivot in allOutside;
  assert pivot in fringe;

  assert flatten(fringe) <= allOutside;


  assert forall t <- allOutside :: inside(part, t);

  forall t <- allOutside ensures (t in flatten(fringe)) //(t in flatten(fringe))  //by
  {
    var prev, next := AcrossTheBorder(part, pivot, t);
    assert strictlyInside(prev,t);
    assert not(strictlyInside(next,pivot));
    assert prev in all;
    assert next in prev.owner;
    assert prev in allInside;
    assert next in allOutside;
    assert next in fringe;
    assert t in all;
    assert t in next.AMFO;
    assert t in flatten({next});
  }

  assert flatten(fringe) >= allOutside;
  assert flatten(fringe) == allOutside;

  var fringeNoPivot:= fringe - {pivot};
  assert pivot !in fringeNoPivot;

  var flatFringeNoPivot := flatten(fringeNoPivot);
  assert pivot !in flatFringeNoPivot;

  assert fringeNoPivot == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;

  assert (fringe - {pivot}) == set x <- allInside, xo <- x.owner | (xo in allOutside) && (xo != pivot) :: xo;
//  assert flatten(fringe - {pivot}) + flatten({pivot}) == flatten(fringe) == allOutside;
//  assert flatten(fringe) + flatten({pivot}) == allOutside;
}




lemma AcrossTheBorder(part : Object,  pivot : Object, whole : Object) returns (prev : Object, next : Object)
  //returns two transitive owners of part that on the way to whole, where prev is inside pivot, and next is outside or == pivot
  decreases part.AMFO
   requires part.Ready()
   requires whole.Ready()
   requires pivot.Ready()
   requires strictlyInside(part, whole)
   requires strictlyInside(part, pivot)
 //requires inside(part, pivot)  //REVERT
   requires not(strictlyInside(whole, pivot))

    ensures part != whole
    ensures prev in part.AMFO
    ensures next in part.AMFO
    ensures inside(part,prev)
    ensures strictlyInside(part,next)
    ensures strictlyInside(prev,pivot)
    ensures strictlyInside(prev,whole)
    ensures next in prev.owner
    ensures not(strictlyInside(next,pivot))
    ensures outside(next,pivot) || (next == pivot)
    ensures prev.Ready()
    ensures next.Ready()
    ensures whole in part.AMFO
    ensures whole in flatten({next})
{
  prev := part;

  if (whole in prev.owner) {
    next := whole;
    return;
  }

  next := YouCan'tGetThereFromHereBut(prev, whole);

  //  assert part != whole;
  //  assert prev in part.AMFO;
  //  assert next in part.AMFO;
  //  assert next in prev.owner;
  //  assert inside(part,prev);
  //  assert strictlyInside(prev,;pivot);
  //  assert inside(next,whole));
  //  assert prev.Ready();
  //  assert next.Ready();

  while (strictlyInside(next,pivot))
    decreases next.AMFO
    invariant part != whole
    invariant prev in part.AMFO
    invariant next in part.AMFO
    invariant next in prev.owner
    invariant inside(part,prev)
    invariant strictlyInside(prev,pivot)
    invariant inside(next,whole)
    invariant prev.Ready()
    invariant next.Ready()
    invariant pivot.Ready()
  {
    prev := next;
    next := YouCan'tGetThereFromHereBut(prev, whole);
  }

  //  assert part != whole;
  //  assert prev in part.AMFO;
  //  assert next in part.AMFO;
  //  assert next in prev.owner;
  //  assert inside(part,prev);
  //  assert strictlyInside(prev,pivot);
  //  assert not(strictlyInside(next,whole));
  //  assert prev.Ready();
  //  assert next.Ready();

//makerfield({next}, pivot);

  assert not(strictlyInside(next,pivot));
  BLAH_BLAH_BLAH(next,pivot);
  assert outside(next,pivot) || (next == pivot);
}

lemma BLAH_BLAH_BLAH(a : Object, b : Object)
 requires a.Ready()
 requires b.Ready()
 requires not(strictlyInside(a,b))
  ensures not(a.AMFO > b.AMFO)
  ensures not( (a.AMFO >= b.AMFO) && not(a.AMFO == b.AMFO) )
  ensures not( (a.AMFO >= b.AMFO) )  ||  (a.AMFO == b.AMFO)
  ensures not( inside(a,b) ) || (a == b)
  ensures outside(a,b)       || (a == b)
{AXIOMAMFOS(a,b);}

lemma OUTSIDE_OUTSIDE(oo : Owner, pivot : Object)
 requires AllReady(oo)
 requires pivot.Ready()
 requires forall o <- oo          :: outside(o, pivot)
  ensures forall o <- flatten(oo) :: outside(o, pivot)
{}



lemma OwnerInFlatten(xwrns : OWNR, x : Object, xo : Object)
  requires AllReady(flatten(xwrns))
  requires x.Ready()
  requires xo.Ready()

  requires x in flatten(xwrns)
  requires xo in x.owner

  ensures xo in flatten(xwrns)
  ensures flatten(xwrns) >= flatten({x})
  ensures flatten(xwrns) >= flatten({xo})
{
FlattenContainsFlatten(xwrns, {x});
}




lemma YouGetThereEventually(part : Object, whole : Object) returns (prev : Object)
  //returns a (transitive) owner of part that is JUST BEFORE whole --- ie of which whole is a direct owner
  decreases part.AMFO
  requires part.Ready()
  requires whole.Ready()
  requires strictlyInside(part, whole)
  ensures part != whole
  ensures prev in part.AMFO
  ensures whole in prev.owner
  ensures strictlyInside(prev,whole)
  ensures inside(part, prev)
{
  if (whole in part.owner) {
    prev := part;
    assert prev in part.AMFO && whole in prev.owner;
    return;
  }
  assert whole !in part.owner;

  ThereIsALightThatNeverGoesOut(part, whole);
  //   assert (exists prev <- part.owner :: inside(prev, whole));

  prev := YouCan'tGetThereFromHereBut(part, whole);
  assert prev in part.owner;   assert whole !in part.owner;     assert prev != whole;
  assert inside(prev,whole);

  if (whole in prev.owner) {
    assert prev in part.AMFO;
    return;
  }
  prev := YouGetThereEventually(prev, whole);
}


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ////
/// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // ///




//
lemma {:timeLimit 30} ThereIsALightThatNeverGoesOut(part : Object, whole : Object)
  //at least one of part's direct owners is on the way to whole.
  requires part.Ready()
  requires whole.Ready()
  requires inside(part,whole)
  ensures (part == whole) || (exists x <- part.owner :: inside(x, whole))
{
  //    InsideRecInside2(part, whole);

  if (part == whole) {
    assert ((part == whole) || (exists x <- part.owner :: inside(x, whole)));
    return; }

  assert part != whole;
  assert (exists x <- part.owner :: inside(x,whole));
}


ghost function {:isolate_assertions} YouCan'tGetThereFromHereBut(part : Object, whole : Object) : (next : Object)
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









lemma FLATTEN_SUBS(a : Owner, b : Owner)
  requires a >= b
  ensures flatten(a - b) + flatten(b) == flatten(a)
{}

lemma FLATTEN_SUM3(a : Owner, b : Owner, c : Owner)
  requires a+b == c
  ensures flatten(a) + flatten(b) == flatten(a+b)
{}

lemma FLATTEN_SUMS(a : Owner, b : Owner, c : Owner, m : Klon)
  requires a+b == c
  // requires forall o <- a :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- b :: o.Ready()  //I'm OH SO TORY
  // requires forall o <- c :: o.Ready()  //TORY TORY TORY
  //  requires AllReady(a)
  //  requires AllReady(b)
  //  requires AllReady(c)
  //  requires klonReady(m)
  //  requires klonCalid(m)
  requires (a+b+c) <= m.m.Keys
  //    ensures recFlatten(a)+recFlatten(b)==recFlatten(a+b)
  ensures flatten(a) + flatten(b) == flatten(a+b)
  ensures mapThruKlon(a,m) + mapThruKlon(b,m) == mapThruKlon(a+b,m)
  ensures flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m)) == flatten(mapThruKlon(a+b,m))
{}

lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
{}


lemma {:timeLimit 20} MAPPEN_ONE(next : Object, m : Klon)
  requires next.Ready()
  requires next in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
  ensures mapThruKlon({next},m) == {m.m[next]}
  //   ensures flatten({next}) == {next} + flatten(next.owner)
  //   ensures flatten(mapThruKlon(done+{next},m)) == flatten(mapThruKlon(done,m)) + flatten(mapThruKlon({next},m))
{
  FLATTEN_ONE(next);
  //  assert mapThruKlon({next},m) == (set o <- {next} :: m.m[o]) == {m.m[next]};
}

lemma {:timeLimit 20} FLATTEN_TWO(done : Owner, next : Object, m : Klon)
  requires AllReady(done)
  requires next.Ready()
  requires klonReady(m)
  requires klonCalid(m)
  requires (done+{next}) <= m.m.Keys
  ensures (done+{next} == done + {next})
  ensures mapThruKlon(done+{next},m) == mapThruKlon(done,m) + mapThruKlon({next},m)
  ensures flatten(done+{next}) == flatten(done) + flatten({next})
  ensures flatten(mapThruKlon(done+{next},m)) == flatten(mapThruKlon(done,m)) + flatten(mapThruKlon({next},m))
{
  FLATTEN_SUMS(done,{next},done+{next},m);
}



lemma {:timeLimit 60} recSplatten(oo : Owner, m : Klon) returns (sp : Owner)
   ///predicts flatten(mapThruKlon(oo, m))

  decreases allAMFOs(oo)
  requires AllReady(oo)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
//requires exists x <- oo :: inside(x, m.o)

  ensures flatten(oo) <= m.m.Keys
  ensures sp == flatten(mapThruKlon(oo, m))
  ensures AllReady(sp)
  ensures (exists x <- oo :: inside(x, m.o)) ==>
     (exists x <- oo :: inside(x, m.o) && (x in m.m.Keys) && (m.m[x] in sp) && inside(m.m[x],m.c))

{
  //     var x :=  {set o : Object <- oo, ooo <- recOwners(o) :: ooo};

  sp := {};

  var todo := oo;
  var done : Owner := {};
  assert AllReady(todo);
  assert oo - todo == {};
  assert oo == done + todo;
  assert mapThruKlon({}, m) == {};
  assert mapThruKlon((oo - todo), m) == {};
  assert flatten({}) == {};
  assert flatten(mapThruKlon((oo - todo), m)) == {};

  assert sp == flatten(mapThruKlon((oo - todo), m));
  assert done == oo - todo == {}; assert done !! todo;
  assert sp == flatten(mapThruKlon((done), m));

  while (todo > {})
    decreases todo
    invariant sp == flatten(mapThruKlon((oo - todo), m))
    invariant done == oo - todo
    invariant sp == flatten(mapThruKlon((done), m))
//invariant exists x <- oo :: inside(x, m.o)
    invariant oo == done + todo
    invariant done !! todo
//invariant exists x <- (done + todo) :: inside(x, m.o)
    invariant forall x <- done | inside(x,m.o) ::  inside(m.m[x],m.c) && (m.m[x] in sp)
  {
    assert sp == flatten(mapThruKlon((oo - todo), m));

    var next :| next in todo;
    assert done == oo - todo;

    var todoHERE := todo;
    assert ttt: next in todo;
    assert nit: next in todoHERE;
    assert done !! todo;
    assert next !in done;
    assert todo == todoHERE;
    assert done == oo - todoHERE;
    assert oo == done + todo == done + todoHERE;

    assert todo decreases to todo - {next} by { reveal ttt; }

    todo := todo - {next};
    assert next !in todo;
    assert next !in done;
    assert done !! {next} !! todo;

    assert next in todoHERE by { reveal nit; }
    assert todo == todoHERE - {next};
    MINUS3(todo,todoHERE,{next});
    assert todoHERE == todo + {next};

    assert oo == done + todoHERE;
    assert done !! {next} !! todo;
    assert oo == done + (todo + {next});

    assert done == oo - todoHERE;
    assert todoHERE == todo + {next};
    assert done == oo - (todo + {next});
    PLUS_MINUS(done,oo,todo,{next});
    assert done == oo - todo - {next};



    var sext := m.m[next];
    assert klonLine(next, sext, m);
    assert klonIdentity(next, sext, m);

    var sowner;   var fowner;

    if (next == m.o)
    {
      assert sext == m.c;
      sowner := m.clowner;
      fowner := flatten(m.clowner);
      assert fowner == flatten(sext.owner);
    }
    else if (outside(next, m.o))
    {
      assert next == sext; assert next.owner == sext.owner;
      sowner := next.owner;
      fowner := flatten(next.owner);
      assert fowner == flatten(sext.owner);
    }
    else
    {
      assert strictlyInside(next, m.o);
      sowner := mapThruKlon(next.owner, m);
      assert sowner == sext.owner;
      fowner := recSplatten(next.owner, m);
      assert fowner == flatten(sext.owner);
    } //end if elseif else

    assert fowner == flatten(sext.owner);
    FLATTEN_ONE(sext);
    assert flatten({sext}) == ({sext} + flatten(sext.owner)) == ({sext} + fowner);
    MAPPEN_ONE(next,m);
    assert mapThruKlon({next}, m) == {m.m[next]} == {sext};
    assert flatten(mapThruKlon({next}, m)) == flatten({sext}) == ({sext} + fowner);
    assert sp == flatten(mapThruKlon((done), m));
    assert (done+{next}) == (done)+({next});    FLATTEN_SUMS(done,{next},done+{next},m);
    assert (mapThruKlon((done+{next}), m)) == (mapThruKlon((done), m)) + (mapThruKlon(({next}), m));
    assert flatten(mapThruKlon((done+{next}), m)) == flatten(mapThruKlon((done), m)) + flatten(mapThruKlon(({next}), m)) == sp + ({sext} + fowner);
    sp := sp + ({sext} + fowner);

    assert oo == done + (todo + {next});
    assert done !! {next} !! todo;
    PLUS4(oo, done, todo, {next});
    assert oo == (done + {next}) + todo;

    done := done + {next};
    assert oo == done + todo;
    assert done == oo - todo;
    assert sp == flatten(mapThruKlon((done), m));
    assert sp == flatten(mapThruKlon((oo - todo), m));
  }//end while


  assert sp == flatten(mapThruKlon((oo - todo), m));
  assert oo == done + todo;
  assert done == oo - todo;
  assert todo == {}; assert done == oo;
  assert sp == flatten(mapThruKlon(oo, m));


//  assert exists x <- oo   | inside(x, m.o) :: inside(m.m[x], m.c);
  assert forall x <- done | inside(x,m.o) ::  inside(m.m[x],m.c) && (m.m[x] in sp);
//  assert exists y <- sp  :: inside(y,m.c) && (y in sp);
  }//end recSplatteno






lemma PLUS_MINUS(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b - (c + d)
   ensures a == b - c - d
{}

lemma MINUS3(a : Owner, b : Owner, c : Owner)
  requires c <= b
  requires a == b - c
   ensures b == a + c
{}

lemma PLUS4(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b + (c + d)
  requires b !! c !! d
   ensures a == (b + d) + c
{}
