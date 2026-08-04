include "Ownership-Recursive.dfy"
include "Set-Lemmata.dfy"
include "Ownership-Parallel.dfy"
include "Context.dfy"

///recSplatten8 - > INNER_LOOP
/// INNER_LOOP ->  CAXE_UALL_PIVOT(
///            ->  CASE_OUTSIDE
///            ->  CASE_INSIDE

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

lemma {:timeLimit 30} MappedInside(part : Object, whole : Object, m : Klon )
 decreases part.AMFO
  requires part.Ready()
  requires whole.Ready()
  requires inside(part,whole)
  requires m.objectInKlown(part)
  requires klonReady(m)
  requires klonCalid(m)

  requires inside(whole,m.o)
  requires part == whole

  ensures inside(m.m[part],m.m[whole])
{
    if (part == whole) {
       assert klonLine(part,m.m[part],m);
       assert klonLine(whole,m.m[whole],m);
       assert inside(m.m[part],m.m[whole]);
       return;
    }

    ThereIsALightThatNeverGoesOut(part,whole);

    var next := YouCan'tGetThereFromHereBut(part, whole);

    MappedInside(next,whole,m);

}



lemma FlattenOutsideIsTheSame(o : Object, m : Klon)
  requires o.Ready()
  requires m.objectInKlown(o)
  requires klonReady(m)
  requires klonCalid(m)

  requires outside(o, m.o)

  ensures o.AMFO == m.m[o].AMFO
  // ensures flatten(mapThruKlon({o},m)) == mapThruKlon(flatten({o}),m)
  {
      assert (o == m.m[o]);
      MAPPEN_ONE(o,m);
      assert NOMAP: ({o} == mapThruKlon({o},m));

assert forall x <- o.AMFO :: outside(x, m.o);
forall (x <- m.m.Keys | outside(x, m.o)) ensures (m.m[x] == x) //by
  {
    assert klonCalid(m);
    assert klonLine(x,m.m[x],m);
    assert klonIdentity(x,m.m[x],m);
    assert m.m[x] == x;
  }
assert forall x <- o.AMFO :: m.m[x] == x;

forall (x <- o.AMFO) ensures ({x} == mapThruKlon({x},m))   //by
  {
    assert m.objectInKlown(o);
    assert x in m.m.Keys;
    assert m.m[x] == x;
    MAPPEN_ONE(x,m);
    assert mapThruKlon({x},m) == {m.m[x]};
    assert {x} == mapThruKlon({x},m);

  }
//
// assert not(o.AMFO >= m.o.AMFO);
//
// assert forall x <- o.AMFO :: (x == m.m[x]) && (flatten({x}) == flatten({m.m[x]}));
//
   //   assert forall x <- o.AMFO :: x.AMFO < m.o.AMFO;  //how thte FUCK does this work????
   //answerr = ot doesn't

//      assert forall x <- o.AMFO :: m.m[x] in m.m[o].AMFO;

//
//       assert flatten(mapThruKlon({o},m)) == flatten({o}) by { reveal NOMAP; }
//       assert flatten({o}) == mapThruKlon(flatten({o}),m) by { reveal NOMAP; }
//      assert flatten({o}) == flatten({o});
    //  assert flatten(mapThruKlon({o},m)) == mapThruKlon(flatten({o}),m);
  }



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


method {:isolate_assertions}  ownerAndBoundViaMeppy(k : Object, m' : Klon) returns (rowner : Owner, rbound : Owner)
 //doesnt work, no surprise :-)
  requires k !in m'.m.Keys
  requires strictlyInside(k, m'.o)
  requires klonReady(m')
  requires klonCalid(m')
  requires COK(k, m'.oHeap)   requires COKA: COK(k, m'.oHeap)
  requires m'.ownersInKlown(k)
//   ensures myBoundsOK(rowner, rbound)
{
  reveal COK();
  assert k.Ready();
  var owner := k.owner;
  var bound := k.bound;

  assert myBoundsOK(owner, bound);
  assert (flatten(owner) >= flatten(bound));
  assert (forall o <- owner :: flatten(o.ownerBound()) >= flatten(bound));

   rowner := mapThruKlon(owner, m');
   rbound := mapThruKlon(bound, m');

//  assert myBoundsOK(rowner, rbound);

}




lemma super_meppy(oo : Owner, mb : Bound, m : Klon, rowner : Owner, rbound : Owner)
//too good to bee true!
//doesnt conclude anything useful
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires AllReady(mb)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
  requires (flatten(oo) >= flatten(mb))

  requires rowner == mapThruKlon(oo, m)
  requires rbound == mapThruKlon(mb, m)

//  ensures (flatten(rowner) >= flatten(rbound))
{
  var foo := flatten(oo);
  var fmb := flatten(mb);




assert m.m.Keys >= foo >= fmb;
var i := invert(m.m);
assert i.Keys == m.m.Values;
assert forall x <- m.m.Keys :: m.m[x] in i.Keys;

//rememebr that (in this version at leat)
//clone cannot (or will not) make new things inside the clone m.c that do not correspond to things in isde the origianl m.o

   assert rowner == mapThruKlon(oo, m);
   assert rbound == mapThruKlon(mb, m);

   var frowner := recSplatten(oo, m);
   var frbound := recSplatten(mb, m);

   assert frowner == flatten(rowner);
   assert frbound == flatten(rbound);

// assert not(frowner >= frbound);

//chop up however FOR today
//HERE HERE HERE HERE HERE
//   chopp up fowner & fbounf
//   comare


//
//
// assert forall x <- foo | inside(x,m.o) :: inside(m.m[x],m.c);
//
// assert forall x <- foo | inside(m.m[x],m.c) :: inside(x,m.o);
//
// //assert forall y <- frowner | inside(y,m.c) ::  y in m.m.Values; // inside(i[x],m.o);
// //
// // var foofrowner := set y <- frowner | y in m.m.Values && i[y] in foo;
// // assert foofrowner == frowner * (set x <- foo ::  m.m[x]);
//
// assert forall x <- foo | strictlyInside(x,m.o) :: strictlyInside(m.m[x],m.c);
//
// assert forall x <- foo | strictlyInside(x,m.o) :: m.m[x] in frowner;
//
// //assert forall x <- foo :: m.m[x] in frowner;
//
//
// assert forall x <- foo | outside(x,m.o) :: m.m[x] == x;
// assert forall x <- foo | outside(x,m.o) :: outside(x,m.c);
// assert forall x <- foo | outside(m.m[x],m.c) :: outside(x,m.o);
//
// // assert forall y <- frowner | outside(y,m.c) && y in i.Keys :: outside(i[y],m.o);
// // assert forall y <- frowner | outside(y,m.c) && y !in i.Keys :: y in m.c.AMFO;
//
//
// assert m.m[m.o] == m.c;
// assert m.c.owner == m.clowner;
// assert m.c.bound == m.clbound;

//assert fOutside(foo,m.o) == fOutside(frowner,m.c);
}



lemma {:timeLimit 60} meppy_meppy(oo : Owner, mb : Bound, m : Klon) returns (rowner : Owner, rbound : Owner)
//too good to bee true!
//does the map but not the flatten
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires AllReady(mb)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
  requires oo >= mb

   ensures rowner == mapThruKlon(oo, m)
   ensures rbound == mapThruKlon(mb, m)

   ensures rowner >= rbound
{
   rowner := mapThruKlon(oo, m);
   rbound := mapThruKlon(mb, m);
}



lemma naive_ne_marche_pas(oo : Owner, mb : Bound, m : Klon) returns (rowner : Owner, rbound : Owner)
//too good to bee true!
 decreases allAMFOs(oo)
  requires AllReady(oo)
  requires AllReady(mb)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
  requires mb <= m.m.Keys
  requires (flatten(oo) >= flatten(mb))

   ensures rowner == mapThruKlon(oo, m)
   ensures rbound == mapThruKlon(mb, m)

  // ensures (flatten(rowner) >= flatten(rbound))
{
   rowner := mapThruKlon(oo, m);
   rbound := mapThruKlon(mb, m);
}



method {:isolate_assertions} {:verify false} ownerAndBoundForClone(k : Object, m' : Klon) returns (rowner : Owner, rbound : Owner)
  requires k !in m'.m.Keys
  requires strictlyInside(k, m'.o)
  requires klonReady(m')
  requires klonCalid(m')
  requires COK(k, m'.oHeap)   requires COKA: COK(k, m'.oHeap)
  requires m'.ownersInKlown(k)

//   ensures myBoundsOK(rowner, rbound)
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
lemma {:timeLimit 60}  Zowner(owner : Owner, pivot : Object)
//topology?  enfringement?  whatevs?
  returns (owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)

 requires AllReady(owner)
 requires pivot.Ready()     requires piR: pivot.Ready()

  ensures owners_inside  == set x <- owner |  inside(x, pivot)
  ensures owners_outside == set x <- owner | outside(x, pivot)
  ensures owner == owners_outside + owners_inside
  ensures flatten(owner) == flatten(owners_inside) + flatten(owners_outside)

  ensures fringe     == set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo

  ensures frogbelow(flat_below, owners_inside, pivot)
  ensures reveal frogbelow();  flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot)
  ensures flat_below <= flatten(owners_inside)

  ensures froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
  ensures reveal froglet(); flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)

  ensures frogdisj(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
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
    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + {} + pflivot(owner, pivot); //mon 8 June 2026
    assert pflinge(owners_inside, pivot) == {};
    assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot) + pflivot(owner, pivot); //mon 8 June 2026
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

predicate frogbelow(flat_below : Owner, owners_inside : Owner, pivot : Object)
  {  flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot) }

lemma NO_FROG_BELOW(flat_below : Owner, owners_inside : Owner, pivot : Object)
  requires owners_inside <= {pivot}
  requires flat_below == {}
   ensures reveal frogbelow(); frogbelow(flat_below, owners_inside, pivot)
{
  reveal frogbelow();
  assert flat_below == set x : Object <- flatten(owners_inside - {pivot}) | inside(x,pivot);
}
  //////////////////////////////////////////////////////////////////////////////



lemma {:timeLimit 30} Zowners_inside(owners_inside : Owner, owners_outside : Owner, owner : Owner, pivot : Object)
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
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)

  ensures frogdisj(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
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
//   and the pass them into aslemma, rather than getting them out of thelemma?


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
// assert flatten(owners_inside) == ((set x <- flat_inside_nopivot | inside(x,pivot))  + (flatten(fringe) + pflinge(owners_inside, pivot) )  ) + pflivot(owner, pivot);



  assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside) by { reveal FLOOI; }
  assert F_ALL: flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
    by {
         reveal FLOOI;
         assert flatten(owner) == flatten(owners_outside) + flatten(owners_inside);
         reveal BFPL;
         assert flatten(owners_inside) ==                  (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot);
         SATAN(owner, owners_outside, owners_inside, flat_below, fringe, pivot);
         assert flatten(owner) == flatten(owners_outside) + flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot);
        }


  assert flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)  by { reveal F_ALL; }
  assert  (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo));
  assert  (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot));

  assert FRG1: (flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot));
  assert FRG2: (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo));
  assert FRG3: (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot));



  assert frogbelow(flat_below, owners_inside, pivot) by { reveal FROG_BELOW; }

  assert forall b <- flat_below :: inside(b,pivot);
  assert forall b <- flat_below-{pivot} :: strictlyInside(b,pivot);

  assert forall f <- fringe                                     :: outside(f,pivot);
  assert forall f <-        owners_outside                      :: outside(f,pivot);
  assert forall f <-                              (pivot.owner) :: outside(f,pivot);

assert pflinge(owner,pivot) <= flatten(pivot.owner);
assert forall x <- pflinge(owner,pivot) :: outside(x,pivot);

  var allOfEm := fringe+owners_outside+pivot.owner;
  OUTSIDE_MY_FRIENDS(fringe, owners_outside,pivot.owner, allOfEm, pivot);



//   assert (owner > {});
//   assert pflinge(owner,pivot) == flatten(pivot.owner);
//   assert forall f <-                       pflinge(owner,pivot) :: outside(f,pivot);
//   // var allOfEm := fringe+owners_outside+pflinge(owner,pivot);
//   forall f <- (fringe+owners_outside+pflinge(owner,pivot)) ensures ( outside(f,pivot)) {
//     if (f in fringe) {
//                      assert forall f <- fringe :: outside(f,pivot);
//                      assert outside(f,pivot); }
//     else if (f in owners_outside) {
//                      assert forall f <- owners_outside :: outside(f,pivot);
//                      assert outside(f,pivot); }
//     else { assert f in pflinge(owner,pivot);
//                       assert forall f <- (pivot.owner) :: outside(f,pivot);
//                       assert outside(f,pivot); }
//     assert outside(f,pivot);
//   FlattenOutsideFlatten(fringe,pivot);
//   assert forall f <- flatten(fringe)                            :: outside(f,pivot);
//   FlattenOutsideFlatten(owners_outside,pivot);
//   assert forall f <-        flatten(owners_outside)             :: outside(f,pivot);
//   FlattenOutsideFlatten(pivot.owner,pivot);
//   assert forall f <-                       flatten(pivot.owner) :: outside(f,pivot);
//   assert  pflinge(owner,pivot) <=  flatten(pivot.owner);
//   assert forall f <-                       pflinge(owner,pivot) :: outside(f,pivot);


  assert (flat_below-{pivot}) !! (fringe+owners_outside+pflinge(owner,pivot));
  assert (flat_below-{pivot}) !! flatten(fringe+owners_outside+pflinge(owner,pivot));

  FLATTEN_SUM4(fringe, owners_outside, pflinge(owner,pivot), fringe+owners_outside+pflinge(owner,pivot));

  // assert flatten(fringe+owners_outside+pflinge(owner,pivot)) ==
  //   ((flatten(owners_outside) + flatten(fringe) + (pflinge(owners_inside, pivot))));
  // assert (flat_below-{pivot}) !! ((flatten(owners_outside) + flatten(fringe) + (pflinge(owners_inside, pivot))) - {pivot});

  assert FRG4: (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe));

  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
     by { reveal froglet(), FRG1, FRG2, FRG3, FRG4;

       assert (flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot));
       assert (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo));
       assert (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot));
       assert (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe));

       assert
         && (flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot))
         && (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo))
         && (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot))
         && (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe))
         ;

      reveal froglet();

       assert  froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
      }
  assert (flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot));
  assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
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

lemma GET_FROGLET(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  requires pivot.Ready()
  requires (flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot))
  requires (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo))
  requires (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot))
  requires (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe))
  ensures froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe)
{
       reveal froglet();
       assert (flatten(owner) == flatten(owners_outside) +  flat_below +  flatten(fringe) + pflinge(owners_inside, pivot)    + pflivot(owner, pivot));
       assert (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo));
       assert (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot));
       assert (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe));

       assert
         && (flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot))
         && (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo))
         && (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot))
         && (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe))
         ;

      reveal froglet();

      if (froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe))
       {
          assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
       }
       else {
        assert froglet(owner, pivot, owners_inside, owners_outside, flat_below, fringe);
        //assert false;
        }
}



predicate
froglet(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
   requires pivot.Ready()
  { && (flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot))
    && (fringe == (set x <- flatten(owners_inside - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo))
    && (flat_below == set x <- flatten(owners_inside - {pivot}) | inside(x,pivot))
    && (frogdisj(owner,pivot,owners_inside,owners_outside,flat_below,fringe))
  }

lemma FROGLET_GETZ_FRINGE(li : Owner, lo : Owner, lb : Owner, lf : Owner, left : Owner, pivot : Object)
  requires pivot.Ready()
  requires froglet(left, pivot,li,lo,lb,lf)
  {
    reveal froglet(left, pivot,li,lo,lb,lf);
    assert froglet(left, pivot,li,lo,lb,lf);

    assert lf == set x <- flatten(li - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo;
  }

opaque predicate old_froglet(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  requires pivot.Ready()
  { flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot) }


lemma SATAN(owner : Owner, owners_outside : Owner, owners_inside : Owner, flat_below : Owner, fringe : Owner, pivot : Object)
 requires pivot.Ready()
 requires flatten(owner) == flatten(owners_outside) + flatten(owners_inside)
 requires flatten(owners_inside) == (flat_below + (flatten(fringe) + pflinge(owners_inside, pivot) )) + pflivot(owner, pivot)
  ensures flatten(owner) == flatten(owners_outside) + flat_below + flatten(fringe) + pflinge(owners_inside, pivot)  + pflivot(owner, pivot)
{}

opaque predicate OOOO(osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner) {osp == obelow + oabove + opivot}

lemma PACK_OOOO(osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner)
  requires osp == obelow + oabove + opivot
   ensures OOOO(osp,obelow,oabove,opivot)
   { reveal OOOO(); }

lemma UNPK_OOOO(osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner)
  requires OOOO(osp,obelow,oabove,opivot)
   ensures osp == obelow + oabove + opivot
   { reveal OOOO(); }


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
  requires pivot.Ready()
   ensures AllReady(fp)
   ensures fp <= flatten(pivot.owner)
  { if (owner > {}) then flatten(pivot.owner) else {} }

lemma flatten_monotonic(a : Owner, b : Owner)
  // requires AllReady(a)
  // requires AllReady(b)
   ensures (a == b) ==> flatten(a) == flatten(b)
   ensures (a < b) ==> flatten(a) <= flatten(b)
   ensures (a > b) ==> flatten(a) >= flatten(b)
{}


predicate frogdisj(owner : Owner, pivot : Object, owners_inside : Owner, owners_outside : Owner, flat_below : Owner, fringe : Owner)
  requires pivot.Ready()
 {
   (flat_below-{pivot}) !! ((flatten(owners_outside) + flatten(fringe) + pflinge(owners_inside, pivot)) - {pivot})
 }

lemma  FROG_DISJOINT(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 left : Owner, pivot : Object)
  requires pivot.Ready()
  requires froglet(left, pivot,li,lo,lb,lf)
  requires frogbelow(lb, li, pivot)
  requires frogdisj(left,pivot,li,lo,lb,lf)
{
  reveal froglet(), frogbelow();
  assert froglet(left, pivot,li,lo,lb,lf);
  assert lb == set x <- flatten(li - {pivot}) | inside(x,pivot);

  assert lf == set x <- flatten(li - {pivot}), xo <- x.owner | (x != pivot) &&  (inside(x,pivot) ) && (outside(xo,pivot) ) :: xo
   by { reveal froglet(left, pivot,li,lo,lb,lf);
        assert froglet(left, pivot,li,lo,lb,lf); }

  assert forall b <- lb ::  inside(b,pivot);
  assert forall f <- lf :: outside(f,pivot);
  assert lb !! lf;
}


lemma  NAKED_LIBERATION(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
                    requires left  == (li + lo + lb + lf + pflivot(left, pivot) )
                    requires right == (ri + ro + rb + rf + pflivot(right,pivot) )
  requires pivot.Ready()

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
  requires pivot.Ready()

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


lemma OUTSIDE_MY_FRIENDS(a : Owner, b : Owner, c : Owner, d : Owner, pivot : Object)
  requires pivot.Ready()
  requires AllReady(a)
  requires AllReady(b)
  requires AllReady(c)

  requires d == a+b+c

  requires forall x <- a :: outside(x,pivot)
  requires forall x <- b :: outside(x,pivot)
  requires forall x <- c :: outside(x,pivot)

  ensures AllReady(d)
  ensures forall x <- d :: outside(x,pivot)
  ensures forall x <- flatten(d) :: outside(x,pivot)


{
    assert forall x <- d :: outside(x,pivot);
    FlattenOutsideFlatten(d,pivot);
    assert forall x <- flatten(d) :: outside(x,pivot);
}



lemma LIVE_FLATRATUIB(li : Owner, lo : Owner, lb : Owner, lf : Owner,
                 ri : Owner, ro : Owner, rb : Owner, rf : Owner,
                 left : Owner, right : Owner, pivot : Object)
  requires pivot.Ready()

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

  // // assert flatten(li) >= flatten(ri);
  // // assert flatten(lo) >= flatten(ro);
  // // assert flatten(lb) >= flatten(rb);
  // // assert flatten(lf) >= flatten(rf);
  // // assert (pflinge(li, pivot) >= pflinge(ri, pivot));
  // // assert (pflivot(left, pivot) >= pflivot(right,pivot));

  //  assert (|| (flatten(lo) >= flatten(ro)) || (lb >= rb) || (flatten(lf) >= flatten(rf))
  //         || (pflinge(li, pivot) >= pflinge(ri, pivot)) || (pflivot(left, pivot) >= pflivot(right,pivot)) );
}


lemma FlattenOutsideFlatten(sider : Owner, pivot : Object)
  requires AllReady(sider)
  requires pivot.Ready()
  requires forall s <- sider :: outside(s,pivot)
   ensures forall s <- sider, x <- s.AMFO :: outside(x,pivot)
   ensures forall x <- flatten(sider) :: outside(x,pivot)
{}



lemma FlattenObjectFlatten(sider : Object, pivot : Object)
  requires sider.Ready()
  requires pivot.Ready()
  requires outside(sider,pivot)
   ensures forall x <- sider.AMFO :: outside(x,pivot)
   ensures forall x <- flatten({sider}) :: outside(x,pivot)
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

lemma {:timeLimit 40} FlattenFringeIsAllOutside(iwnrs : OWNR,  pivot : Object) returns (allInside : Owner, allOutside : Owner, fringe : Owner)
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

lemma FLATTEN_SUM4(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a+b+c == d
  ensures flatten(a) + flatten(b) + flatten(c) == flatten(d)
{}


lemma FLATTEN_SUMS(a : Owner, b : Owner, c : Owner, m : Klon)
  //just say  FLATTEN_SUMS(done,{next},done+{next},m);

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
  ensures mapThruKlon(a+b,m) == mapThruKlon(a,m) + mapThruKlon(b,m)
  ensures flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m)) == flatten(mapThruKlon(a+b,m))
  ensures flatten(mapThruKlon(a+b,m)) == flatten(mapThruKlon(a,m)) + flatten(mapThruKlon(b,m))
{}

lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
{}


lemma MAPPEN_ONE(next : Object, m : Klon)
  requires next.Ready()
  requires next in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
  ensures mapThruKlon({next},m) == {m.m[next]}

{
  FLATTEN_ONE(next);
}

lemma FLATMAP_ONE(next : Object, cext : Object,  m : Klon)
  requires next.Ready()
  requires cext.Ready()
  requires next in m.m.Keys
  requires cext == m.m[next]
  requires klonReady(m)
  requires klonCalid(m)
  ensures mapThruKlon({next},m) == {m.m[next]}
  ensures cext.AMFO == flatten(mapThruKlon({next}, m))
{
      assert cext == m.m[next];
      MAPPEN_ONE(next, m);
      assert mapThruKlon({next},m) == {cext};
      FLATTEN_ONE(cext);
      assert flatten({cext})  == cext.AMFO;
     assert flatten(mapThruKlon({next}, m)) == cext.AMFO;
}

lemma FLAT_DONE_CSP(done : Owner, csp : Owner, m : Klon)
  requires klonReady(m)
  requires klonCalid(m)
  requires AllReady(done)
  requires AllReady(csp)
  requires done <= m.m.Keys
  requires csp == flatten(mapThruKlon((done), m))
//   ensures forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) && (m.m[x] in csp)
{
  assert flatten(done) <= m.m.Keys;

  assert forall x <- flatten(done) ::  klonLine(x,m.m[x],m);

  assert forall x <- done :: x.AMFO <= m.m.Keys;
  assert forall x <- done :: flatten({x}) <= m.m.Keys;
  assert forall x <- done :: x.AMFO <= m.m.Keys;
  assert forall x <- done, y <- x.AMFO | inside(y,m.o) :: inside(m.m[y],m.c);
//
//   assert forall x <- done, y <- collectAllOwners(x) | recInside(y,m.o) :: recInside(m.m[y],m.c);
//
//   assert forall x <- done, y <- collectAllOwners(x) | recInside(y,m.o) :: recInside(m.m[y],m.c);
//
//   assert forall x <- done, y <- x.AMFO | inside(y,m.o) :: m.m[y] in m.m[x].AMFO;



forall x <- done, y <- x.AMFO | inside(y,m.o) ensures (true) {
   assert inside(x,y);
  // assert inside(m.m[x],m.m[y]);
   assert inside(m.m[y],m.c);
InsideRecInside2(x,y);
// zInsideRecInside2(m.m[x],m.m[y]);


}

//   x`  |  inside(x,m.o) ensures  inside(m.m[x],m.c) && (m.m[x] in csp)
//   {
//     assert x in m.m.Keys;
//     assert x.AMFO <= m.m.Keys;
//     assert klonLine(x,m.m[x],m);
//
//     assert inside(m.m[x],m.c);
//     FLATMAP_ONE(x,m.m[x],m);
//   }
}

lemma {:timeLimit 20} FLATTEN_TWO(done : Owner, next : Object, m : Klon)
  requires AllReady(done)
  requires next.Ready()
  requires klonReady(m)
  requires klonCalid(m)
  requires (done+{next}) <= m.m.Keys
  ensures mapThruKlon(done+{next},m) == mapThruKlon(done,m) + mapThruKlon({next},m)
  ensures flatten(done+{next}) == flatten(done) + flatten({next})
  ensures flatten(mapThruKlon(done+{next},m)) == flatten(mapThruKlon(done,m)) + flatten(mapThruKlon({next},m))
{
  FLATTEN_SUMS(done,{next},done+{next},m);
}

function  fOutside(ownrs : OWNR, pivot : Object) : (rv : Owner)
//rename to allLOutside???
//KJX FUCK FUCK FUCK FUCK FUCK FUCK
//returns all flatatnened owners that are outside the pivot...
//YEAH I fear this is still the WRONG THING
//shop;dln't it take in all the *direct* owners
//throw out all that are inside
//and flatten the remainder (outside ONLY)
  // requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  //  ensures AllReady(rv)
  ensures forall r <- rv :: outside(r,pivot)
{ set x <- flatten(ownrs) | outside(x,pivot) } // not(strictlyInside(x, pivot)) }

lemma fOUTSIDE_MONOTONIC(ownrs : OWNR, owmrs : OWNR, pivot : Object)
  // requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  //  ensures AllReady(rv)
  ensures fOutside(ownrs, pivot) + fOutside(owmrs, pivot) == fOutside(ownrs+owmrs, pivot)
   {}

lemma fStrictlyInside_MONOTONIC(ownrs : OWNR, owmrs : OWNR, pivot : Object)
  // requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  //  ensures AllReady(rv)
  ensures fStrictlyInside(ownrs, pivot) + fStrictlyInside(owmrs, pivot) == fStrictlyInside(ownrs+owmrs, pivot)
   {}


lemma FUCKED_SUM3_SUB1(o : Owner, o' : Owner, n : Owner, a : Owner, b : Owner, c : Owner)
  requires o == o' + n
  requires n == a + b + c
   ensures o == o' + a + b + c
{}




lemma DELTA(q : Owner, q' : Owner, q_ : Owner, o : Owner, o' : Owner, o_ : Owner,  pivot : Object,  pred : (Object, Object) -> bool)
     ensures q  == (set x : Object <- o  | pred(x, pivot))

    requires o  == o' + o_
    requires q  == q' + q_
    requires q' == (set x : Object <- o' | pred(x, pivot))
    requires q_ == (set x : Object <- o_ | pred(x, pivot))
{}


lemma DELTA_strictlyInside(q : Owner, q' : Owner, q_ : Owner, o : Owner, o' : Owner, o_ : Owner,  pivot : Object)
     ensures q  == allStrictlyInside(o, pivot)
    requires o  == o' + o_
    requires q  == q' + q_

    requires q' == allStrictlyInside(o', pivot)
    requires q_ == allStrictlyInside(o_, pivot)
    //  ensures q' == allStrictlyInside(o', pivot)
    //  ensures q_ == allStrictlyInside(o_, pivot)
{}

lemma DELTA_objectOutside(q : Owner, q' : Owner, q_ : Owner, d : Owner, d' : Owner,  d_ : Owner,  pivot : Object)
     ensures q  == fOutside(d-{pivot}, pivot)
    requires d  == d' + d_
    requires q  == q' + q_

    requires q' == fOutside(d' -{pivot}, pivot)
    requires q_ == fOutside(d_ -{pivot}, pivot)
    //  ensures q' == fOutside(d' -{pivot}, pivot)
    //  ensures q_ == fOutside(d_ -{pivot}, pivot)
{}

lemma DELTA_cloneOutside(q : Owner, q' : Owner, q_ : Owner, d : Owner, d' : Owner,  d_ : Owner,  m : Klon)
     ensures q  == fOutside(mapThruKlon(d-{m.o}, m), m.c)
    requires m.m.Keys >= d'
    requires m.m.Keys >= d_
    requires d  == d' + d_
    requires q  == q' + q_

    requires q' == fOutside(mapThruKlon(d' -{m.o}, m), m.c)
    requires q_ == fOutside(mapThruKlon(d_ -{m.o}, m), m.c)
     ensures q' == fOutside(mapThruKlon(d' -{m.o}, m), m.c)
     ensures q_ == fOutside(mapThruKlon(d_ -{m.o}, m), m.c)
{}




lemma DELTA_below(q : Owner, q' : Owner, q_ : Owner, o : Owner, o' : Owner, o_ : Owner,  pivot : Object)
     ensures q  == allStrictlyInside(o, pivot)
    requires o  == o' + o_
    requires q  == q' + q_

    requires q' == allStrictlyInside(o', pivot)
    requires q_ == allStrictlyInside(o_, pivot)
    //  ensures q' == allStrictlyInside(o', pivot)
    //  ensures q_ == allStrictlyInside(o_, pivot)
{}



lemma GAMMA_flatten(q : Owner, q' : Owner, q_ : Owner, donePlusNext : Owner, done : Owner, next : Object, m : Klon)
    ensures q  == flatten(donePlusNext)

    requires m.m.Keys >= donePlusNext  == done + {next}

    requires q' == flatten(done)
    requires q_ == flatten({next})
    requires q  == q' + q_
{

      FLATTEN_SUMS(done,{next},done+{next},m);
}







predicate {:timeLimit 15} IN_N_OUT_BURGER(oo : Owner, m : Klon)
  //that original & clones in m.m are either both inside the pivot
  //or outside the pivot and identical :-)
   requires oo <= m.m.Keys
   requires AllReady(oo)
   requires klonReady(m)
   requires klonCalid(m)
      reads m.hns()
  {
    && (forall x <- oo |  inside(x,m.o) ::  inside(m.m[x],m.c))
    && (forall x <- oo | outside(x,m.o) :: (m.m[x] == x) )
    && (forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c))
    && (forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x))
  }

lemma IN_N_OUT_DELTA(o : Owner, o' : Owner, o_  : Owner, m : Klon)
    requires o  == o' + o_
    requires o <= m.m.Keys
    requires AllReady(o)
    requires klonReady(m)
    requires klonCalid(m)
    requires IN_N_OUT_BURGER(o', m)
    requires IN_N_OUT_BURGER(o_, m)
     ensures IN_N_OUT_BURGER(o,  m)
{ FLATTEN_SUMS(o',o_,o,m); }

//
//     invariant  cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//     invariant  opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
//     invariant (cpivot == {}) != (cpivot == m.c.AMFO)
//     invariant (opivot == {}) != (opivot == m.o.AMFO)


lemma IN_N_OUT_LEMMER(oo : Owner, m : Klon)
   requires oo <= m.m.Keys
   requires klonReady(m)
   requires klonCalid(m)

    ensures IN_N_OUT_BURGER(oo,m)
{
    assert m.m.Keys >= flatten(oo);

    assert forall o <- oo :: o.Ready();
    assert forall o <- oo :: m.m[o].Ready();

    assert forall o <- oo :: klonLine(o,m.m[o],m);
    assert forall o <- oo :: klonGeometry(o,m.m[o],m);
    assert forall o <- oo :: m.objectReadyInKlown(o);
    assert forall o <- flatten(oo) :: klonGeometry(o,m.m[o],m);
}
  // {
  //   assert
  //   && (forall x <- oo |  inside(x,m.o) ::  inside(m.m[x],m.c))
  //   && (forall x <- oo | outside(x,m.o) :: (m.m[x] == x) )
  //   && (forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c))
  //   && (forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x))
  //   ;
  // }

predicate triangular(q : Owner, q' : Owner, q_ : Owner)
   //should this be a predicate or alemma??
  { q == q' + q_ }

lemma fOUTSIDE_MINUSONE(o : Object, ownrs : Owner, pivot : Object, rv : Owner)
  requires ownrs == {o}
  requires AllReady(ownrs)
  requires outside(o, pivot)
   ensures forall x <- o.AMFO :: outside(x, pivot)
  requires rv == fOutside(ownrs, pivot)
   ensures rv == set x <- flatten(ownrs) | outside(x,pivot)
   ensures rv == set x <- o.AMFO | outside(x,pivot)
   ensures rv == o.AMFO
  {
//    assert fOutside(ownrs, pivot) == ( set x <- flatten(ownrs) | outside(x,pivot));
    FLATTEN_ONE(o);
    assert flatten({o}) == o.AMFO;
    assert flatten(ownrs) == flatten({o}) == o.AMFO;
}


lemma fOUTSIDE_MINUSTWO(o : Object, pivot : Object, rv : Owner)
  requires AllReady({o})
  requires outside(o, pivot)
   ensures forall x <- o.AMFO :: outside(x, pivot)
  requires rv == fOutside({o}, pivot)
   ensures rv == set x <- flatten({o}) | outside(x,pivot)
   ensures rv == set x <- o.AMFO | outside(x,pivot)
   ensures rv == o.AMFO
  {
//    assert fOutside(ownrs, pivot) == ( set x <- flatten(ownrs) | outside(x,pivot));
    FLATTEN_ONE(o);
    assert flatten({o}) == o.AMFO;
}

lemma fOUTSIDE_ONE(next : Object, pivot : Object, rv : Owner)
  requires next.Ready()
  requires next != pivot
  requires outside(next, pivot)
  requires rv == fOutside({next}-{pivot}, pivot)
   ensures rv == next.AMFO
{
    assert next != pivot;
    assert {next}-{pivot} == {next};
    assert forall x <- next.AMFO :: outside(x,pivot);
    assert (set x <- next.AMFO | outside(x,pivot)) == next.AMFO;
    assert isFlat(next.AMFO);
    assert flatten(next.AMFO) == next.AMFO;
    assert (set x <- flatten(next.AMFO) | outside(x,pivot))
              == (set x <- next.AMFO | outside(x,pivot))
              == next.AMFO;
}


//{:timeLimit 100}
lemma  fOUTSIDE_TWO(next : Object, m : Klon, rv : Owner)
//like outside-ONE but gor the clone side
  requires next.Ready()
  requires next != m.o
  requires m.objectInKlown(next)
  requires outside(next, m.o)
  requires rv == fOutside(mapThruKlon({next}-{m.o},m), m.c)
  requires klonReady(m)
  requires klonCalid(m)
  requires klonLine(next, m.m[next], m)
   ensures rv == m.m[next].AMFO
{
    assert next != m.o;
    assert {next}-{m.o} == {next};
    assert forall x <- next.AMFO :: outside(x,m.o);
    assert klonLine(next, m.m[next], m);
    assert mapThruKlon({next},m) == {m.m[next]};
    assert mapThruKlon({next}-{m.o},m) == {m.m[next]};
    assert outside(m.m[next], m.c);
    assert isFlat(m.m[next].AMFO);
    IS_FLAT_IS_MONOTONIC(m.m[next].AMFO);
 assert flatten(m.m[next].AMFO) == m.m[next].AMFO;
 assert (set x <- flatten(m.m[next].AMFO) | outside(x,m.c)) ==
        (set x <- m.m[next].AMFO | outside(x,m.c));

assert forall x <- m.m[next].AMFO :: outside(x,m.c);

assert
        (fOutside(mapThruKlon({next}-{m.o},m), m.c) ==
        fOutside(mapThruKlon({next},m), m.c)) by
         { assert next != m.o; assert {next}-{m.o} == {next}; }

  assert
        fOutside(mapThruKlon({next},m), m.c) ==  fOutside({m.m[next]}, m.c);



// assert fOutside({m.m[next]}, m.c) ==
//         ( set x <- flatten({m.m[next]}) | outside(x,m.c) ) ==
//         ( set x <- m.m[next].AMFO | outside(x,m.c) ) ==
//         m.m[next].AMFO;
//
//     assert rv == (set x <- m.m[next].AMFO | outside(x,m.c))
//               == m.m[next].AMFO;
//     assert fOutside(mapThruKlon({next}-{m.o},m), m.c) == m.m[next].AMFO;


// assert fOutside({m.m[next]}, m.c)   == m.m[next].AMFO by
assert (set x <- m.m[next].AMFO | outside(x,m.c)) == m.m[next].AMFO by
    {
      forall x <- m.m[next].AMFO ensures (outside(x,m.c))  //by
       {
         var k := invert(m.m)[x];
         assert klonLine(k,x,m);
         assert klonGeometry(k,x,m);
         assert outside(k,m.o);
         assert outside(k,m.c);
         assert k == x;
         assert outside(k, m.o) <==> outside(x, m.c);
         assert outside(x, m.c);
       }
//       var pred := (z requires z in m.m[next].AMFO => outside(z,m.c));
       assert forall x <- m.m[next].AMFO :: outside(x,m.c);
//       assert forall x <- m.m[next].AMFO :: pred(x) <==> outside(x,m.c);
//       assert forall x <- m.m[next].AMFO :: pred(x);
//       SET_SELECT_ALL(m.m[next].AMFO, pred);
      ALL_OWNERS_OUTSIDE(m.m[next].AMFO, m.c);
       assert (set x <- m.m[next].AMFO | outside(x,m.c)) == m.m[next].AMFO;
       }

  fOUTSIDE_MINUSTWO(m.m[next],m.c,fOutside({m.m[next]},m.c));
  assert fOutside({m.m[next]}, m.c) == (set x <- flatten({m.m[next]}) | outside(x,m.c));
  FLATTEN_ONE(m.m[next]);
  assert flatten({m.m[next]}) == m.m[next].AMFO;
  assert fOutside({m.m[next]}, m.c) == (set x <- m.m[next].AMFO | outside(x,m.c));
  assert fOutside({m.m[next]}, m.c) == m.m[next].AMFO;
  assert fOutside(mapThruKlon({next},m), m.c) ==   m.m[next].AMFO;
  assert fOutside(mapThruKlon({next}-{m.o},m), m.c) ==   m.m[next].AMFO;
  assert rv == m.m[next].AMFO;

}



lemma ALL_OWNERS_OUTSIDE(s : Owner, pivot : Object)
// "outside owners outside??""
  requires forall x <- s :: outside(x,pivot)
   ensures (set x <- s | outside(x,pivot)) == s
{}

lemma OUTSIDE_OWNERS_NOTNSIDE(s : Owner, pivot : Object)
  requires forall x <- s :: outside(x,pivot)
   ensures (set x <- s | inside(x,pivot)) == {}
{}

lemma SET_SELECT_MONO2(a : Owner, b : Owner, pivot : Object)
  ensures (set x <- a + b | strictlyInside(x,pivot)) == ((set x <- a | strictlyInside(x,pivot)) + (set x <- b | strictlyInside(x,pivot)))
{}

lemma SET_IGNORE_MONO2(a : Owner, b : Owner, pivot : Object)
 requires forall x <- b :: outside(x, pivot)
  ensures (set x <- a + b | strictlyInside(x,pivot)) == ((set x <- a | strictlyInside(x,pivot)) + (set x <- b | strictlyInside(x,pivot))) == (set x <- a | strictlyInside(x,pivot))
{}


lemma SET_SELECT_ALL<T>(s : set<T>, pred : T --> bool)
  requires forall x <- s :: pred.requires(x)
  requires forall x <- s :: pred(x)
   ensures (set x <- s | pred(x)) == s
{}

lemma SET_SELECT_PRED_MONO2(a : Owner, b : Owner, pred : Object -> bool)
  ensures (set x <- a + b | pred(x)) == ((set x <- a | pred(x)) + (set x <- b | pred(x)))
{}

function fStrictlyInside(ownrs : OWNR, pivot : Object) : (rv : Owner)
///fStrictkylInside
  // requires AllReady(flatten(ownrs))
  // requires pivot.Ready()
  // ensures AllReady(rv)
  ensures forall r <- rv :: strictlyInside(r,pivot)
{ set x <- flatten(ownrs) | strictlyInside(x,pivot) }

lemma LIFT_inside(obelow : OWNR, osp : OWNR, done : Owner, pivot : Object)
  //should be unnecessary.links shit together.
  requires obelow == (set x <- osp | strictlyInside(x,pivot))
  requires osp == flatten(done)
   ensures obelow == (set x <- osp | strictlyInside(x,pivot))
   ensures obelow == fStrictlyInside(done,pivot)
   ensures obelow == allStrictlyInside(flatten(done),pivot)
{}

//lemma HYPERFUCKED_strictlyInside(obelow : OWNR, osp : OWNR, pivot : Object)
//    requires pivot.Ready()
//    requires forall x <- obelow :: strictlyInside(x,pivot)
//     ensures obelow == osp - pivot.AMFO
//    requires obelow == set x <- osp | strictlyInside(x,pivot)
// {}

lemma recSplatten(oo : Owner, m : Klon) returns (sp : Owner)
   ///predicts flatten(mapThruKlon(oo, m))

 decreases allAMFOs(oo), 10
  requires AllReady(oo)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys
//requires exists x <- oo :: inside(x, m.o)

  ensures flatten(oo) <= m.m.Keys
  ensures sp == flatten(mapThruKlon(oo, m))
  ensures AllReady(sp)
  ensures (exists x <- oo :: inside(x, m.o)) ==>
     (exists x <- oo :: inside(x, m.o) && (x in m.m.Keys) && inside(m.m[x],m.c)) //&& (m.m[x] in sp)


  ensures forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in sp)
  ensures forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x) //  (m.m[x] in sp)
{
  var csp, cbelow, cabove, cpivot, osp, obelow, oabove, opivot := recSplatten8(oo, m);

  sp := csp;
}

// opaque predicate VANCE(oo : Owner, todo : Owner, done : Owner)
//  { oo == todo + done }
//
// opaque predicate JAYDEE(oo : Owner, todo : Owner, next : Object, done : Owner)
//  { oo == todo + {next} + done }


///
lemma GET_NEXT_OWNER(oo : Owner, todo' : Owner, done' : Owner, m : Klon) returns (todo : Owner, next : Object, done : Owner)
 decreases allAMFOs(todo'), 5
  // requires AllReady(todo')
  // requires AllReady(done')

  requires todo' !! done'
  requires todo' > {}

 requires oo     == todo' + done'
//  requires todo'   == oo - done'
//  requires done'   == oo - todo'

  ensures todo !! {next} !! done
  ensures todo == todo' - {next}
  ensures done == done'
  ensures todo + {next} + done == (todo' + done') == oo
  ensures done+{next} == oo - todo
  ensures oo == todo + {next} + done

  ensures todo' decreases to todo - {next}
  {
    next :| next in todo';
    todo := todo' - {next};
    done := done';
  }

lemma RET_NEXT_OWNER(oo : Owner, todo' : Owner, next': Object, done' : Owner, m : Klon) returns (todo : Owner,  done : Owner)
 decreases allAMFOs(todo'), 5
  // requi  5res AllReady(todo')
  // requires AllReady(done')
  // requires next'.Ready()

  requires todo' !!  {next'} !! done'
  requires oo == (todo' + {next'} + done')

   ensures todo   !! done
   ensures todo   == todo'
   ensures done   == done' + {next'}
   ensures oo     == (todo' + {next'} + done')

   ensures oo     == todo + done
//   ensures oo     == done + todo
//   ensures todo   == oo - done
//   ensures done   == oo - todo
  {
    todo := todo';
    done := done' + {next'};
  }


lemma FOUR_BY_FOUR(osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner,
                                dbelow : Owner, dabove : Owner, dpivot : Owner)
          returns (rsp : Owner, rbelow : Owner, rabove : Owner, rpivot : Owner)
  requires osp == obelow + oabove + opivot
   ensures rbelow == obelow + dbelow
   ensures rabove == oabove + dabove
   ensures rpivot == opivot + dpivot
   ensures rsp == osp + dbelow + dabove + dpivot
   ensures rsp == rbelow + rabove + rpivot
   ensures (opivot == {}) ==> (rpivot == dpivot)
   ensures (dpivot == {}) ==> (rpivot == opivot)
   ensures (opivot == dpivot) ==> (rpivot == opivot == dpivot)
   ensures (dbelow == dabove == {}) ==> (rsp == osp + dpivot)
   ensures (dbelow == {}) ==> (rbelow == obelow)
   ensures (dabove == {}) ==> (rabove == oabove)
   ensures ((dbelow == {}) && (dpivot == {})) ==> (rsp == osp + dabove)
{
   rbelow := obelow + dbelow;
   rabove := oabove + dabove;
   rpivot := opivot + dpivot;
   rsp    := osp    + dbelow + dabove + dpivot;
}



lemma  SIX_BY_FOUR(osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner,
                                dbelow : Owner, dabove : Owner, dpivot : Owner,
                 rsp : Owner, rbelow : Owner, rabove : Owner, rpivot : Owner)
   requires osp == obelow + oabove + opivot
   requires rbelow == obelow + dbelow
   requires rabove == oabove + dabove
   requires rpivot == opivot + dpivot
    // requires rsp == osp + dbelow + dabove + dpivot  //WORKS
    // ensures rsp == rbelow + rabove + rpivot         //WSORKSa
    // ensures rsp == osp + dbelow + dabove + dpivot  //ALSO WORKS!
    // requires rsp == rbelow + rabove + rpivot         //ALSLO WORKS!
    ensures osp + dbelow + dabove + dpivot == rbelow + rabove + rpivot   //WORKS3
    // ensures (rsp == osp + dbelow + dabove + dpivot) || (rsp == rbelow + rabove + rpivot)   //DOESA NOT WORK  0-- bnot strong enoug hto bind rsp  - could REQUIRE this
    //  ensures (rsp == osp + dbelow + dabove + dpivot)  ==> (rsp == rbelow + rabove + rpivot)  //command line
    //  ensures (rsp == osp + dbelow + dabove + dpivot) <==  (rsp == rbelow + rabove + rpivot)  //command line
    // ensures (rsp == osp + dbelow + dabove + dpivot) == (rsp == rbelow + rabove + rpivot)   ///works but doesnt do what we want
//
  requires (rsp == osp + dbelow + dabove + dpivot) || (rsp == rbelow + rabove + rpivot)  //this pair works
  ensures (rsp == osp + dbelow + dabove + dpivot) && (rsp == rbelow + rabove + rpivot)   //goes either wsay



    ensures (opivot == {}) ==> (rpivot == dpivot)
    ensures (dpivot == {}) ==> (rpivot == opivot)
    ensures (opivot == dpivot) ==> (rpivot == opivot == dpivot)
    ensures (dbelow == dabove == {}) ==> (rsp == osp + dpivot)
    ensures (dbelow == {}) ==> (rbelow == obelow)
    ensures (dabove == {}) ==> (rabove == oabove)
    ensures ((dbelow == {}) && (dpivot == {})) ==> (rsp == osp + dabove)

   ensures OOOO(rsp,rbelow,rabove,rpivot)
   { reveal OOOO(); }

lemma FLATTINGTONS(done : Owner, xxx : Owner)
   requires AllReady(done)
   requires xxx == flatten(done)
    ensures xxx == (set d : Object <- done, dd <- d.AMFO :: dd)
    ensures xxx == (set d : Object <- done, dd <- flatten({d}) :: dd)
{
  forall d : Object <- done, dd <- d.AMFO ensures d.AMFO == flatten({d}) {
    FLATTEN_ONE(d);
  }
}

// {:timeLimit 20}x

lemma recSplatten8(oo : Owner, m : Klon) returns (csp : Owner, cbelow : Owner, cabove : Owner, cpivot : Owner,
                                                  osp : Owner, obelow : Owner, oabove : Owner, opivot : Owner)
  //predicts flatten(mapThruKlon(oo, m)) - o* is *original;  c* is clone
 decreases allAMFOs(oo), 5
  requires AllReady(oo)
  requires klonReady(m)
  requires klonCalid(m)
  requires oo <= m.m.Keys

   ensures flatten(oo) <= m.m.Keys

   ensures osp == flatten(oo)
   ensures osp    == obelow + oabove + opivot
   ensures (set x <- osp | strictlyInside(x,m.o)) == obelow
  //  ensures (set x <- osp |        outside(x,m.o)) == oabove  ///WRONG - see note "FUCK FUCK FUCK FUCK FUCK" above or bnelonw - on fOutside.
  ///    assert oabove == fOutside(done-{m.o}, m.o);
  //  ensures opivot == if (m.o in osp) then (m.o.AMFO) else {}

   ensures csp == flatten(mapThruKlon(oo, m))
   ensures csp    == cbelow + cabove + cpivot
   ensures (set x <- csp | strictlyInside(x,m.c)) == cbelow
  //  assert cabove == fOutside(mapThruKlon(done-{m.o},m), m.c);
  //  ensures (set x <- csp |        outside(x,m.c)) == cabove   //WRONG see note "FUCK FUCK FUCK FUCK FUCK" above or bnelonw - on fOutside.
  //  ensures cpivot == if (m.o in osp) then (m.c.AMFO) else {}

  ensures AllReady(csp)
  ensures (exists x <- oo :: inside(x, m.o)) ==>
     (exists x <- oo :: inside(x, m.o) && (x in m.m.Keys)  && inside(m.m[x],m.c))

  ensures forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp)
  ensures forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x) //  (m.m[x] in csp)
  ensures oabove == cabove
{
  osp := {}; obelow := {}; oabove := {}; opivot := {};
  csp := {}; cbelow := {}; cabove := {}; cpivot := {};

  var todo := oo;
  var todo_at_top := todo;
  var done : Owner := {};

assert obelow == oabove == cbelow == cabove == {};

FLATTINGTONS(done,flatten(done));


assert mapThruKlon({}, m) == {};
assert flatten({}) == {};
assert flatten(mapThruKlon({}, m)) == {};
assert done == {};
assert csp  == {};
assert flatten(mapThruKlon(done, m)) == {};

    assert  cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});  //prewhle
    assert  opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {});  //prewhle
    assert (cpivot == {}) != (cpivot == m.c.AMFO);  //prewhle
    assert (opivot == {}) != (opivot == m.o.AMFO);  //prewhle

    assert done == {}; assert done-{m.o} == {};
    assert mapThruKlon(done-{m.o},m) == {}; assert mapThruKlon({},m) == {};
    assert fOutside(done-{m.o},m.o) == {};  assert fOutside({},m.o) == {};
    assert fOutside(mapThruKlon(done-{m.o},m), m.c) == {};
    assert mapThruKlon({},m) == {}; assert fOutside({},m.o) == {};
    assert oabove == fOutside(done-{m.o}, m.o);
    assert cabove == fOutside(mapThruKlon(done-{m.o},m), m.c);
    assert oabove == cabove;

  while (todo > {})
    decreases todo
    invariant oo     == todo + done
    invariant todo   == oo - done
    invariant todo   !! done
    invariant osp    == obelow + oabove + opivot
    invariant osp == flatten(done)
    invariant csp    == cbelow + cabove + cpivot
    invariant csp    == flatten(mapThruKlon(done, m))

    invariant obelow == (set x <- osp | strictlyInside(x,m.o))
    invariant cbelow == (set x <- csp | strictlyInside(x,m.c))
    invariant oabove == fOutside(done-{m.o}, m.o)
    invariant cabove == fOutside(mapThruKlon(done-{m.o},m), m.c)
    invariant oabove == cabove

    invariant  cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
    invariant  opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    invariant (cpivot == {}) != (cpivot == m.c.AMFO)
    invariant (opivot == {}) != (opivot == m.o.AMFO)

    invariant forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp)
    invariant forall x <- done | outside(x,m.o) ::  (m.m[x] == x)
    invariant forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp)
    invariant forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
  {
    var next;
    var olde_todo := todo;
    todo, next, done := GET_NEXT_OWNER(oo, todo, done, m);
    assert todo_at_top decreases to todo;
    assert todo == olde_todo - {next};
    assert oo == todo + {next} + done;

    // assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
    // assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});


    assert done == oo - (todo + {next});
    PLUS_MINUS(done,oo,todo,{next});
    assert done == oo - todo - {next};

//todo is updated.  done is NOT updated.
//so e.g. flatten(DONE) is correct for other thins NOT updatred
//white flatten(done + {nexdt})  or flatten(oo - todo) is for things AFTER updates

    var cext := m.m[next];
    assert klonLine(next, cext, m);
    assert klonIdentity(next, cext, m);

    assert cbelow == (set x <- csp | strictlyInside(x,m.c));
    assert obelow == (set x <- osp | strictlyInside(x,m.o));
    assert osp == flatten(done);


      osp, obelow, oabove, opivot,
      csp, cbelow, cabove, cpivot
            :=
          INNER_LOOP(oo, m, done, todo, next, cext,
                      osp, obelow, oabove, opivot,
                      csp, cbelow, cabove, cpivot)
            by {
                 assert obelow == (set x <- osp | strictlyInside(x,m.o));
                 assert cbelow == (set x <- csp | strictlyInside(x,m.c));
             }

assert osp    == flatten(done+{next});
assert csp    == flatten(mapThruKlon(done+{next}, m));
assert cbelow == (set x <- csp | strictlyInside(x,m.c));


  assert forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c); //&& (m.m[x] in csp);
  assert forall x <- flatten(done+{next}) | outside(x,m.o) ::  (m.m[x] == x); //(x in csp) &&

  assert oo == todo + {next} + done;
  todo, done := RET_NEXT_OWNER(oo,todo,next,done,m);
  assert   oo == todo + done;

  assert osp == flatten(done);

  }//end while

   assert osp == flatten(done);


  assert todo == {};
  assert   oo == todo + done;
  assert   oo == oo - todo;
  // verifi csp == flatten(mapThruKlon(oo, m));
  // assume osp == flatten(oo);

FLATTINGTONS(done,flatten(done));

// assert forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);

 assert csp == flatten(mapThruKlon((oo - todo), m));
 assert oo == todo + done;
 assert done == oo - todo;
//kjx fuckrfidm  assert todo == {}; assert done == oo;
  assert csp == flatten(mapThruKlon(oo, m));
  assert osp == flatten(oo);

  assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});

  // assert exists x <- oo   | inside(x, m.o) :: inside(m.m[x], m.c);
  assert forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
  assert forall x <- done | outside(x,m.o) :: outside(m.m[x],m.c) && (m.m[x] == x);// && (m.m[x] in csp)

  assert forall x <- flatten(oo) |  inside(x,m.o) ::  inside(m.m[x],m.c); //&& (m.m[x] in csp);
  assert forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x); //(x in csp) &&

  assert osp == flatten(oo);
  }//end recSplatteno








lemma INNER_LOOP(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
//    requires done+{next} == oo - todo
    requires oo     == todo + {next} + done
//    requires todo   == oo - done - {next}
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done     , m))
//    requires csp'    == flatten(mapThruKlon(oo - todo, m))   ///GRRR
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

    //  ensures done+{next} == oo - todo
     ensures oo     == todo + {next} + done
    //  ensures todo   == oo - done - {next}
     ensures todo   !! {next} !! done
     ensures osp    == obelow + oabove + opivot
     ensures osp == flatten(done+{next})
     ensures csp    == cbelow + cabove + cpivot
     ensures csp    == flatten(mapThruKlon(done+{next}, m))
//     ensures csp    == flatten(mapThruKlon(oo - todo,   m))
     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)

     ensures IN_N_OUT_BURGER(oo, m)

     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
     ensures oabove == fOutside(done+{next}-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)
     ensures oabove == cabove
     {
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

       var todo_at_top := todo;

    assert klonLine(next, cext, m);
    assert klonIdentity(next, cext, m);

//  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -

    if (next == m.o)
{

      osp, obelow, oabove, opivot,
      csp, cbelow, cabove, cpivot
            :=
          CAXE_UALL_PIVOT(oo, m, done, todo, next, cext,
                      osp', obelow', oabove', opivot',
                      csp', cbelow', cabove', cpivot');

}
    else if (outside(next, m.o))  //  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
    {

      osp, obelow, oabove, opivot,
      csp, cbelow, cabove, cpivot
            :=
          CASE_OUTSIDE(oo, m, done, todo, next, cext,
                      osp', obelow', oabove', opivot',
                      csp', cbelow', cabove', cpivot');

    }
    else //  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
    {
      assert strictlyInside(next, m.o);
      // assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
      // assert opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {});
      osp, obelow, oabove, opivot,
      csp, cbelow, cabove, cpivot
            :=
          CASE_INSIDE(oo, m, done, todo, next, cext,
                      osp', obelow', oabove', opivot',
                      csp', cbelow', cabove', cpivot');


    assert osp == flatten(done+{next});
    assert csp == flatten(mapThruKlon(done+{next}, m));
    assert OOOO(osp,obelow,oabove,opivot);
    assert OOOO(csp,cbelow,cabove,cpivot);
    }
}

// assert m.m.Keys >= flatten(oo);
// assert IN_N_OUT_BURGER(done+{next}, m);

    // assert  cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
    // assert  opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    // assert (cpivot == {}) != (cpivot == m.c.AMFO);
    // assert (opivot == {}) != (opivot == m.o.AMFO);
     //end if elseif else
// //  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
//
//         UNPK_OOOO(csp,cbelow,cabove,cpivot);
//         UNPK_OOOO(osp,obelow,oabove,opivot);
//         assert osp == obelow + oabove + opivot;  //join
//         assert osp == flatten(done+{next});  //join,
// //assume 2 assert
//     // assert  cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});  //join
//     // assert  opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});  //join
//     // assert (cpivot == {}) != (cpivot == m.c.AMFO); //join
//     // assert (opivot == {}) != (opivot == m.o.AMFO); //join
//
// //     assert osp == obelow + oabove + opivot;
// //     assert csp == cbelow + cabove + cpivot;
// //     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
// //  // older     assert fcowner == flatten(cext.owner);
//   FLATTEN_ONE(cext);
// //  //  assert flatten({cext}) == ({cext} + flatten(cext.owner)) == ({cext} + fcowner);
//     MAPPEN_ONE(next,m);
//     assert mapThruKlon({next}, m) == {m.m[next]} == {cext};
// //  //   assert flatten(mapThruKlon({next}, m)) == flatten({cext}) == ({cext} + fcowner);
//     assert csp == flatten(mapThruKlon(done+{next}, m)); //join OK OK
//     assert (done+{next}) == (done)+({next});    FLATTEN_SUMS(done,{next},done+{next},m);
// //  //   assert flatten(mapThruKlon((done+{next}), m)) == flatten(mapThruKlon((done), m)) + flatten(mapThruKlon(({next}), m)) == csp + ({cext} + fcowner);
// //
// //     assert osp == flatten((done)) + flatten({next});
// //     assert flatten(done+{next}) == flatten(done) + flatten({next});
// //     assert flatten(done+{next}) == osp           + flatten({next});
// //
// //
// //
// //     assert oo == todo + {next} + done;
// //     assert todo !! {next} !! done;
// //     assert oo == todo + {next} + done;
//
// assert forall x <- flatten(done)   |  inside(x,m.o) ::  inside(m.m[x],m.c);//&& (m.m[x] in csp);
// assert forall x <- flatten({next}) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
// assert forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
//
//
//     // assert  cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});  //preret
//     // assert  opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});  //preret
//     // assert (cpivot == {}) != (cpivot == m.c.AMFO); //preret
//     // assert (opivot == {}) != (opivot == m.o.AMFO); //preret
//
//     assert oo == todo + {next} + done;
//
//     todo, done := RET_NEXT_OWNER(oo,todo,next,done,m);
//     assert   oo == todo + done;
//
//     assume obelow == (set x <- osp | strictlyInside(x,m.o));
//     assume cbelow == (set x <- csp | strictlyInside(x,m.c));
//     assume oabove == fOutside(done-{m.o}, m.o);
//     assume cabove == fOutside(mapThruKlon(done-{m.o},m), m.c);
//     assume oabove == cabove;
//
//
//      //kjx    assert   oo == todo + done;








lemma {:verify false} CASE_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    // requires oo     == todo + {next} + done   //doesnt worjk for tge recursive case
    // requires todo !! {next} !! done            //doesnt worjk for tge recursive case
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

    //  ensures oo     == todo + {next} + done            //doesnt worjk for tge recursive casei
    //  ensures todo  !! {next} !! done                   //doesnt worjk for tge recursive case
     ensures osp   == obelow + oabove + opivot
     ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
     ensures csp   == flatten(mapThruKlon(done+{next}, m))
     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
     ensures IN_N_OUT_BURGER(oo, m)
{
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

    osp, obelow, oabove, opivot := osp', obelow', oabove', opivot';
    csp, cbelow, cabove, cpivot := csp', cbelow', cabove', cpivot';
    var todo_at_top := todo;
    var done := done;
    var csp' := csp;
    var osp' := osp;

//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;
    // obelow := obelow';
    // cbelow := cbelow';
    // oabove := oabove';
    // cabove := cabove';
    // opivot := opivot' + next.AMFO;
    // cpivot := cpivot' + cext.AMFO;


      assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
      assert opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {});

      assert cext == m.c;

      assert flatten(m.clowner) == flatten(cext.owner);
      FLATTEN_ONE(next); FLATTEN_ONE(cext);
      assert flatten({next}) == next.AMFO == m.o.AMFO;
      assert flatten({cext}) == cext.AMFO == m.c.AMFO;
      FLATMAP_ONE(next,cext,m);
      assert flatten(mapThruKlon({next}, m)) == flatten({cext}) == cext.AMFO == m.c.AMFO;
      assert flatten(mapThruKlon({next}, m)) == flatten({cext}) == cext.AMFO == m.c.AMFO == m.c.AMFO;
      FLATTEN_ONE(next); FLATTEN_ONE(cext);
      assert flatten({next}) == next.AMFO; //at least aits only short.
      assert m.o in {next};  assert m.o in flatten({next});

    assert csp == flatten(mapThruKlon(done, m));
    assert csp' == csp == flatten(mapThruKlon(done, m));
    assert csp' == cbelow + cabove + cpivot;
    assert osp == flatten(done);
    assert opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {});
    assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});

    osp, obelow,  oabove, opivot := FOUR_BY_FOUR(osp', obelow', oabove', opivot', {}, {}, m.o.AMFO);
    assert opivot == m.o.AMFO;
    csp, cbelow, cabove, cpivot  := FOUR_BY_FOUR(csp', cbelow', cabove', cpivot', {}, {}, m.c.AMFO);
    assert cpivot == m.c.AMFO;

    assert osp == osp' + {} + {} + m.o.AMFO;
    assert csp == csp' + {} + {} + m.c.AMFO;


    assert csp == csp' + {} + {} + m.c.AMFO;
    assert csp == csp' + m.c.AMFO by { assert csp' + {} + {} + m.c.AMFO == csp' + m.c.AMFO; }
    assert csp == flatten(mapThruKlon(done, m)) + m.c.AMFO;
    assert done == done;
    assert m.c.AMFO == flatten({cext}) == flatten(mapThruKlon({next}, m));
    assert csp == flatten(mapThruKlon(done, m))  +  flatten(mapThruKlon({next}, m));



    assert osp == osp' + {} + {} + m.o.AMFO;
    assert osp == osp' + m.o.AMFO by { assert osp' + {} + {} + m.o.AMFO == osp + m.o.AMFO; }
    assert osp == flatten(done) + m.o.AMFO;
    FLATTEN_ONE(next);
    assert m.o.AMFO == next.AMFO == flatten({next});
    assert osp == flatten(done) + flatten({next});

    assert csp == cbelow + cabove + cpivot;
    assert osp == obelow + oabove + opivot;

    assert m.o in {next};  assert m.o in flatten({next});  assert m.o.AMFO <= opivot;
    assert m.o in flatten(done+{next});
    assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
    assert opivot == m.o.AMFO;
    assert cpivot == m.c.AMFO;




  assert done + {next} == done+{next};
    FLATTEN_SUMS(done,{next},done+{next},m);
  assert flatten(done)+flatten({next}) == flatten(done+{next});
  assert (mapThruKlon(done, m)) + mapThruKlon({next}, m) == mapThruKlon(done+{next}, m);
  assert flatten(mapThruKlon(done, m)) + m.c.AMFO == flatten(mapThruKlon(done+{next}, m));
 //    assert done+{next} == (oo - todo);
//    assert csp == flatten(mapThruKlon((oo - todo), m));

    assert osp == flatten(done)+flatten({next});
    assert osp == obelow + oabove + opivot;

//////////////////////////////////////////////
  assert not(strictlyInside(next,m.o));
  assert forall x <- flatten({next}) ::  not(strictlyInside(x,m.o));
  assert   (set x <- flatten({next}) |       strictlyInside(x,m.o)) == {};
  SET_SELECT_MONO2(osp', flatten({next}), m.o);
  assert  flatten({next}) == next.AMFO by { FLATTEN_ONE(next); }
  assert (set x <- next.AMFO | strictlyInside(x,m.o)) == {};
  assert (set x <- osp' + next.AMFO | strictlyInside(x,m.o)) == (set x <- osp' | strictlyInside(x,m.o)) == obelow';
  assert obelow == (set x <- osp | strictlyInside(x,m.o));
///////////////////////////////////////////////
  assert not(strictlyInside(cext,m.c));
  assert forall x <- flatten({cext}) ::  not(strictlyInside(x,m.c));
  assert   (set x <- flatten({cext}) |       strictlyInside(x,m.c)) == {};
  SET_SELECT_MONO2(csp', flatten({cext}), m.c);
  assert  flatten({cext}) == cext.AMFO by { FLATTEN_ONE(cext); }
  assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == {};
  assert (set x <- csp' + cext.AMFO | strictlyInside(x,m.c)) == (set x <- csp' | strictlyInside(x,m.c)) == cbelow';
  assert cbelow == (set x <- csp | strictlyInside(x,m.c));
//////////////////////////////////////////////////
  assert next == m.o;   assert {next}-{m.o} == {};
  assert (done+{next})-{m.o} == (done-{m.o}) by { CORDELIA(done,{next}); }
  assert oabove == fOutside((done+{next})-{m.o}, m.o) == fOutside(done-{m.o}, m.o) == oabove';
  assert cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c) == fOutside(mapThruKlon(done-{m.o},m), m.c) == cabove';
//////////////////////////////////////////////////


//dodgy    assert opivot == (if (m.o in flatten(done)) then (m.o.AMFO) else {});
    assert forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
  assert forall x <- flatten({next}) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
    PACK_OOOO(osp,obelow,oabove,opivot);
    PACK_OOOO(csp,cbelow,cabove,cpivot);
assert OOOO(osp,obelow,oabove,opivot);
assert OOOO(csp,cbelow,cabove,cpivot);

    assert  cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
    assert  opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    assert (cpivot == {}) != (cpivot == m.c.AMFO);
    assert (opivot == {}) != (opivot == m.o.AMFO);

     assert obelow == (set x <- osp | strictlyInside(x,m.o));
     assert cbelow == (set x <- csp | strictlyInside(x,m.c));
     assert oabove == fOutside((done+{next})-{m.o}, m.o);
     assert cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c);
     assert oabove == cabove;

}





lemma {:verify false} CASE_XPIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
     ensures todo  !! {next} !! done
     ensures osp   == obelow + oabove + opivot
      //  ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
      //  ensures csp   == flatten(mapThruKlon(done+{next}, m))
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
    //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//TODO     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
//TODO     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    assert next.AMFO == m.o.AMFO;
    assert osp' == flatten(done);
    assert next.AMFO == flatten({next}) by { FLATTEN_ONE(next); }

FLATTEN_SUMS(done,{next},done+{next},m);
    assert osp   == flatten(done+{next});
    assert csp   == flatten(mapThruKlon(done+{next}, m));

assert forall x <- flatten({next}) :: not(strictlyInside(x, m.o));

    SIX_BY_FOUR(osp', obelow', oabove', opivot',
                      {} , {} , m.o.AMFO,
                osp , obelow , oabove , opivot);

    SIX_BY_FOUR(csp', cbelow', cabove', cpivot',
                      {} , {} , m.c.AMFO,
                csp , cbelow , cabove , cpivot);

}


lemma CASE_Z0_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
   //pivot case, maiintains oo/todo/next/done
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
    {
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;
    }

lemma CASE_Z1_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, osp/csp== below+abov+obapvt
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures osp   == obelow + oabove + opivot
      //  ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
      //  ensures csp   == flatten(mapThruKlon(done+{next}, m))
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
    //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//TODO     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
//TODO     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    SIX_BY_FOUR(osp', obelow', oabove', opivot',
                      {} , {} , m.o.AMFO,
                osp , obelow , oabove , opivot);

    SIX_BY_FOUR(csp', cbelow', cabove', cpivot',
                      {} , {} , m.c.AMFO,
               csp , cbelow , cabove , cpivot);

}

lemma CASE_Z2_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //casa pivot, osp = flattehnthruklon

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})


     ensures osp   == flatten(done+{next})
     ensures csp   == flatten(mapThruKlon(done+{next}, m))
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    assert osp' == obelow' + oabove' + opivot';
    assert csp' == cbelow' + cabove' + cpivot';
    assert obelow == obelow';
    assert cbelow == cbelow';
    assert oabove == oabove';
    assert cabove == cabove';
    assert obelow + oabove == obelow' + oabove';
    assert cbelow + cabove == cbelow' + cabove';
    assert opivot == opivot' + m.o.AMFO;
    assert cpivot == cpivot' + m.c.AMFO;

    var oBA := obelow + oabove;
    assert oBA == (obelow + oabove) == (obelow'+ oabove');
    assert osp == oBA + opivot;
    assert osp == oBA + (opivot' + m.o.AMFO);
    assert osp == (obelow' + oabove') + (opivot' + m.o.AMFO);
    GEFUCKENVANCE(osp, obelow', oabove', opivot', m.o.AMFO);
    assert osp == obelow' + oabove' + opivot' + m.o.AMFO;
    assert osp == (obelow' + oabove' + opivot')  + m.o.AMFO;
    assert osp == osp' + m.o.AMFO;

    assert next.AMFO == m.o.AMFO;
    assert osp' == flatten(done);
    assert next.AMFO == flatten({next}) by { FLATTEN_ONE(next); }
    assert osp == osp' + next.AMFO;


    var cBA := cbelow + cabove;
    assert cBA == (cbelow + cabove) == (cbelow'+ cabove');
    assert csp == cBA + cpivot;
    assert csp == cBA + (cpivot' + m.c.AMFO);
    assert csp == (cbelow' + cabove') + (cpivot' + m.c.AMFO);
    GEFUCKENVANCE(csp, cbelow', cabove', cpivot', m.c.AMFO);
    assert csp == cbelow' + cabove' + cpivot' + m.c.AMFO;
    assert csp == (cbelow' + cabove' + cpivot')  + m.c.AMFO;
    assert  csp  == csp' + m.c.AMFO;


    assert cext.AMFO == m.c.AMFO;
    assert csp' == flatten(mapThruKlon(done,m));
    assert cext.AMFO == flatten(mapThruKlon({next},m))
        by {  assert cext == m.m[next];
              FLATMAP_ONE(next,cext,m);
              assert mapThruKlon({next},m) == {cext};
              assert flatten({cext}) == cext.AMFO; }
    assert csp == csp' + cext.AMFO;

    FLATTEN_SUMS(done,{next},done+{next},m);

    assert osp   == flatten(done+{next});
    assert csp   == flatten(mapThruKlon(done+{next}, m));
}


lemma GEFUCKENVANCE(a : Owner, b : Owner , c : Owner, d : Owner, e : Owner)
  requires a == (b + c) + (d + e)
   ensures a == b + c + d + e
   ensures a == (b + c + d) + e
{}

lemma GEFUCKENHEGSETH(a : Owner, b : Owner , c : Owner, d : Owner, e : Owner)
  requires a == b + (c + d) + e
   ensures a == b + c + d + e
   ensures a == (b + c + e) + d
{}

lemma GEFUCKENRUBIO(a : Owner, b : Owner)
  requires a == (b + b)
   ensures a == b
{}



lemma {:timeLimit 15} CASE_Z3_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, obelow/cbelow
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;
}

lemma CASE_Z4_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, opivot/cabvt-
    // even with the FUCKED vesion of fOutside
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    assert {next} - {m.o} == {};
    assert done+{next}-{m.o} == done-{m.o};
    assert fOutside(done+{next}-{m.o}, m.o) == fOutside(done-{m.o}, m.o);
    assert fOutside(mapThruKlon(done+{next}-{m.o},m), m.c) ==  fOutside(mapThruKlon(done-{m.o},m), m.c);
    assert oabove == cabove;
}


lemma CASE_Z5_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, inside.outside

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
//     requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
//     requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})

    requires opivot' == (if (m.o in osp') then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in osp') then (m.c.AMFO) else {})

     ensures opivot == (if (m.o in osp) then (m.o.AMFO) else {})
     ensures cpivot == (if (m.o in osp) then (m.c.AMFO) else {})


{
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

  assert m.o in opivot;
  assert m.o in osp;

  assert (opivot' == {}) != (opivot' == m.o.AMFO);
  assert (cpivot' == {}) != (cpivot' == m.c.AMFO);

  assert opivot == opivot' + m.o.AMFO;
  assert cpivot == cpivot' + m.c.AMFO;

  if (opivot' == {}) { assert {} + m.o.AMFO == m.o.AMFO; assert opivot ==  m.o.AMFO; }
    else {assert opivot' != {};
          assert opivot' == m.o.AMFO;
          assert opivot  == m.o.AMFO + m.o.AMFO;
          GEFUCKENRUBIO(opivot, m.o.AMFO);
          assert opivot  == m.o.AMFO;
           }

  assert opivot == m.o.AMFO;
  assume cpivot == m.c.AMFO;
}





lemma CASE_Z6_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case,inside/outside
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x)
{
    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

}


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////


lemma CASE_U0_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
   //pivot case, maiintains oo/todo/next/done
    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
    {

    }

lemma {:timeLimit 15} CASE_U1_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot
    //pivot case, osp/csp== below+abov+obapvt
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures osp   == obelow + oabove + opivot
      //  ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
      //  ensures csp   == flatten(mapThruKlon(done+{next}, m))
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
    //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//TODO     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
//TODO     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{



    SIX_BY_FOUR(osp', obelow', oabove', opivot',
                      {} , {} , m.o.AMFO,
                osp , obelow , oabove , opivot);

    SIX_BY_FOUR(csp', cbelow', cabove', cpivot',
                      {} , {} , m.c.AMFO,
               csp , cbelow , cabove , cpivot);

}

lemma CASE_U2_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot
    //casa pivot, osp = flattehnthruklon

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})


     ensures osp   == flatten(done+{next})
     ensures csp   == flatten(mapThruKlon(done+{next}, m))
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;


    // assert osp' == obelow' + oabove' + opivot';
    // assert csp' == cbelow' + cabove' + cpivot';
    // assert obelow == obelow';
    // assert cbelow == cbelow';
    // assert oabove == oabove';
    // assert cabove == cabove';
    // assert obelow + oabove == obelow' + oabove';
    // assert cbelow + cabove == cbelow' + cabove';
    // assert opivot == opivot' + m.o.AMFO;
    // assert cpivot == cpivot' + m.c.AMFO;

    var oBA := obelow + oabove;
    assert oBA == (obelow + oabove) == (obelow'+ oabove');
    assert osp == oBA + opivot;
    assert osp == oBA + (opivot' + m.o.AMFO);
    assert osp == (obelow' + oabove') + (opivot' + m.o.AMFO);
    GEFUCKENVANCE(osp, obelow', oabove', opivot', m.o.AMFO);
    assert osp == obelow' + oabove' + opivot' + m.o.AMFO;
    assert osp == (obelow' + oabove' + opivot')  + m.o.AMFO;
    assert osp == osp' + m.o.AMFO;

    assert next.AMFO == m.o.AMFO;
    assert osp' == flatten(done);
    assert next.AMFO == flatten({next}) by { FLATTEN_ONE(next); }
    assert osp == osp' + next.AMFO;


    var cBA := cbelow + cabove;
    assert cBA == (cbelow + cabove) == (cbelow'+ cabove');
    assert csp == cBA + cpivot;
    assert csp == cBA + (cpivot' + m.c.AMFO);
    assert csp == (cbelow' + cabove') + (cpivot' + m.c.AMFO);
    GEFUCKENVANCE(csp, cbelow', cabove', cpivot', m.c.AMFO);
    assert csp == cbelow' + cabove' + cpivot' + m.c.AMFO;
    assert csp == (cbelow' + cabove' + cpivot')  + m.c.AMFO;
    assert  csp  == csp' + m.c.AMFO;


    assert cext.AMFO == m.c.AMFO;
    assert csp' == flatten(mapThruKlon(done,m));
    assert cext.AMFO == flatten(mapThruKlon({next},m))
        by {  assert cext == m.m[next];
              FLATMAP_ONE(next,cext,m);
              assert mapThruKlon({next},m) == {cext};
              assert flatten({cext}) == cext.AMFO; }
    assert csp == csp' + cext.AMFO;

    FLATTEN_SUMS(done,{next},done+{next},m);

    assert osp   == flatten(done+{next});
    assert csp   == flatten(mapThruKlon(done+{next}, m));
}



lemma {:timeLimit 15} CASE_U3_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, obelow/cbelow

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})


     requires osp   == flatten(done+{next})
     requires csp   == flatten(mapThruKlon(done+{next}, m))
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;

}

lemma CASE_U4_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot
    //pivot case, oabove/cabove
    // even with the FUCKED vesion of fOutside
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{
    assert {next} - {m.o} == {};
    assert done+{next}-{m.o} == done-{m.o};
    assert fOutside(done+{next}-{m.o}, m.o) == fOutside(done-{m.o}, m.o);
    assert fOutside(mapThruKlon(done+{next}-{m.o},m), m.c) ==  fOutside(mapThruKlon(done-{m.o},m), m.c);
    assert oabove == cabove;
}


lemma {:timeLimit 40} CASE_U5_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, opivot/cpivot
    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
//     requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
//     requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})

    requires opivot' == (if (m.o in osp') then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in osp') then (m.c.AMFO) else {})

     ensures opivot == (if (m.o in osp) then (m.o.AMFO) else {})
     ensures cpivot == (if (m.o in osp) then (m.c.AMFO) else {})


{


  assert m.o in opivot;
  assert m.o in osp;

  assert (opivot' == {}) != (opivot' == m.o.AMFO);
  assert (cpivot' == {}) != (cpivot' == m.c.AMFO);

  assert opivot == opivot' + m.o.AMFO;
  assert cpivot == cpivot' + m.c.AMFO;

  if (opivot' == {}) { assert {} + m.o.AMFO == m.o.AMFO; assert opivot ==  m.o.AMFO; }
    else {assert opivot' != {};
          assert opivot' == m.o.AMFO;
          assert opivot  == m.o.AMFO + m.o.AMFO;
          GEFUCKENRUBIO(opivot, m.o.AMFO);
          assert opivot  == m.o.AMFO;
           }

  assert opivot == m.o.AMFO;
  assume cpivot == m.c.AMFO;
}





lemma CASE_U6_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove'
    requires cabove == cabove'
    requires opivot == opivot' + m.o.AMFO
    requires cpivot == cpivot' + m.c.AMFO
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot
    //pivot case,inside/outside -- i.e; IN_N_OUT_BURGER
    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x)
     ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x)
{
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

     assert forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c);
     assert forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x); // && (m.m[x] in csp)
     assert forall x <- flatten(done+{next}) |  inside(x,m.o) :: inside(m.m[x],m.c);
     assert forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x);
}

//////// /////////// /////////// //  /////// //////////// ////// //////  //// ////// ///// // //
//////// /////////// /////////// //  /////// //////////// ////// //////  //// ////// ///// // //


lemma CASE_U0_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
    {

    }


  lemma {:timeLimit 30} CASE_U1_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures osp   == obelow + oabove + opivot
      //  ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
      //  ensures csp   == flatten(mapThruKlon(done+{next}, m))
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
    //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
    //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//TODO     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
//TODO     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{

assert opivot == opivot' == opivot' + {};
assert cpivot == cpivot' == cpivot' + {};

    SIX_BY_FOUR(osp', obelow', oabove', opivot',
                      {}, next.AMFO, {},
                osp , obelow , oabove , opivot);

    SIX_BY_FOUR(csp', cbelow', cabove', cpivot',
                      {}, cext.AMFO, {},
               csp , cbelow , cabove , cpivot);

}

lemma CASE_U2_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})


     ensures osp   == flatten(done+{next})
     ensures csp   == flatten(mapThruKlon(done+{next}, m))
{
//IS THIS REWALLY IT?  HOPEFULLY!!!!!Q
    // osp    := osp'    + m.o.AMFO;
    // csp    := csp'    + m.c.AMFO;


    // assert osp' == obelow' + oabove' + opivot';
    // assert csp' == cbelow' + cabove' + cpivot';
    // assert obelow == obelow';
    // assert cbelow == cbelow';
    // assert oabove == oabove';
    // assert cabove == cabove';
    // assert obelow + oabove == obelow' + oabove';
    // assert cbelow + cabove == cbelow' + cabove';
    // assert opivot == opivot' + m.o.AMFO;
    // assert cpivot == cpivot' + m.c.AMFO;

    assert oabove == oabove' + next.AMFO;
    var oBA := obelow + oabove;
    assert oBA == (obelow + oabove) == (obelow'+ (oabove' + next.AMFO));
    assert osp == oBA + opivot;
    assert osp == oBA + (opivot');
    assert osp == (obelow') + (oabove' + next.AMFO) + (opivot');
    GEFUCKENHEGSETH(osp, obelow', oabove', next.AMFO, opivot');
    assert osp == obelow' + oabove' + next.AMFO + opivot';
    assert osp == (obelow' + oabove' + opivot') + next.AMFO;
    assert osp == osp' + next.AMFO;

    assert osp' == flatten(done);
    assert next.AMFO == flatten({next}) by { FLATTEN_ONE(next); }
    assert osp == osp' + next.AMFO;

    assert cabove == cabove' + cext.AMFO;
    var cBA := cbelow + cabove;
    assert cBA == (cbelow + cabove) == (cbelow'+ (cabove' + cext.AMFO));
    assert csp == cBA + cpivot;
    assert csp == cBA + (cpivot');
    assert csp == (cbelow') + (cabove' + cext.AMFO) + (cpivot');
    GEFUCKENHEGSETH(csp, cbelow', cabove', cext.AMFO, cpivot');
    assert csp == cbelow' + cabove' + cext.AMFO + cpivot';
    assert csp == (cbelow' + cabove' + cpivot') + cext.AMFO;
    assert csp == csp' + cext.AMFO;

// older version from PIVOT - new versiom anove ciut & pasterd.//
//     var cBA := cbelow + cabove;
//     assert cBA == (cbelow + cabove) == (cbelow'+ cabove');
//     assert csp == cBA + cpivot;
//     assert csp == cBA + (cpivot' + m.c.AMFO);
//     assert csp == (cbelow' + cabove') + (cpivot' + m.c.AMFO);
//     GEFUCKENHEGSETH(csp, cbelow', cabove', cpivot', m.c.AMFO);
//     assert csp == cbelow' + cabove' + cpivot' + m.c.AMFO;
//     assert csp == (cbelow' + cabove' + cpivot')  + m.c.AMFO;
//     assert  csp  == csp' + m.c.AMFO;


    assert csp' == flatten(mapThruKlon(done,m));
    assert cext.AMFO == flatten(mapThruKlon({next},m))
        by {  assert cext == m.m[next];
              FLATMAP_ONE(next,cext,m);
              assert mapThruKlon({next},m) == {cext};
              assert flatten({cext}) == cext.AMFO; }
    assert csp == csp' + cext.AMFO;

    FLATTEN_SUMS(done,{next},done+{next},m);

    assert osp   == flatten(done+{next});
    assert csp   == flatten(mapThruKlon(done+{next}, m));
}




lemma {:timeLimit 60} CASE_U3_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     requires osp     == osp' + next.AMFO
     requires csp     == csp' + cext.AMFO
     ensures obelow  == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow  == (set x <- csp | strictlyInside(x,m.c))
{
  assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
  assert cbelow' == (set x <- csp' | strictlyInside(x,m.c));

  assert not(strictlyInside(next,m.o));
  assert not(strictlyInside(cext,m.c));

  assert (set x <- next.AMFO | strictlyInside(x,m.o)) == {};
  assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == {};

  assert obelow' + (set x <- next.AMFO | strictlyInside(x,m.o)) == obelow;
  assert cbelow' + (set x <- cext.AMFO | strictlyInside(x,m.c)) == cbelow;

  assert obelow + (set x <- next.AMFO | strictlyInside(x,m.o)) == obelow;
  assert cbelow + (set x <- cext.AMFO | strictlyInside(x,m.c)) == cbelow;

  assert obelow  == (set x <- osp | strictlyInside(x,m.o));
  assert cbelow  == (set x <- csp | strictlyInside(x,m.c));
}



lemma CASE_U4_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove
{
    assert next != m.o;
    assert {next} - {m.o} == {next};
    assert done+{next}-{m.o} == (done+{next})-{m.o} == (done-{m.o})+{next};
    assert fOutside(done+{next}-{m.o}, m.o) == fOutside(done-{m.o}+{next}, m.o);
    assert fOutside(mapThruKlon(done+{next}-{m.o},m), m.c) ==  fOutside(mapThruKlon(done-{m.o}+{next},m), m.c);
    assert oabove == cabove;
}




lemma {:timeLimit 40} CASE_U5_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //pivot case, opivot/cpivot

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
//     requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
//     requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})

    requires opivot' == (if (m.o in osp') then (m.o.AMFO) else {})





lemma CASE_U6_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner,
                  osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires obelow == obelow'
    requires cbelow == cbelow'
    requires oabove == oabove' + next.AMFO
    requires cabove == cabove' + cext.AMFO
    requires opivot == opivot'
    requires cpivot == cpivot'
    requires osp    == obelow + oabove + opivot
    requires csp    == cbelow + cabove + cpivot

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
     ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x)
{
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);
}


//////// /////////// /////////// //  /////// //////////// ////// //////  //// ////// ///// // //
//////// /////////// /////////// //  /////// //////////// ////// //////  //// ////// ///// // //


//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////

























lemma CASE_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

//we have reached the OUTSIDE directly from the INSIDE - **not** via the pivot (or blivet)

     requires outside(next,m.o)

     requires AllReady(oo)
     requires klonReady(m)
     requires klonCalid(m)
     requires flatten(oo) <= m.m.Keys
     requires next in m.m.Keys
     requires cext == m.m[next]
     requires klonLine(next,cext,m)
     requires oo <= m.m.Keys
    //  requires oo       == todo + {next} + done         //doesnt worjk for tge recursive case
    //  requires todo !! {next} !! done                   //doesnt worjk for tge recursive case
     requires osp'    == obelow' + oabove' + opivot'
     requires osp'    == flatten(done)
     requires csp'    == cbelow' + cabove' + cpivot'
     requires csp'    == flatten(mapThruKlon(done, m))
    //  requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    //  requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    //  requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    //  requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
     requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
requires OB1: obelow' == (set x <- osp' | strictlyInside(x,m.o))
     requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
requires CB1: cbelow' == (set x <- csp' | strictlyInside(x,m.c))
     requires oabove' == fOutside(done-{m.o}, m.o)
     requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
     requires oabove' == cabove'
     requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
     requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})


//the "case outside special conditions?"
     ensures next == cext == m.m[next]
     ensures next.AMFO == cext.AMFO
     ensures forall x <- next.AMFO :: outside(x,m.o)
     ensures forall x <- cext.AMFO :: outside(x,m.c)
     ensures forall x <- next.AMFO :: m.m[x] == x
   //ensures forall x <- cext.AMFO :: (invert(m.m))[x] == x
     ensures forall x <- next.AMFO :: m.m[x] in cext.AMFO
     ensures forall x <- cext.AMFO :: m.m[x] in next.AMFO


     ensures oo     == todo + {next} + done
     ensures todo  !! {next} !! done

     ensures osp    == obelow + oabove + opivot
     ensures osp    == flatten(done+{next})
     ensures csp    == cbelow + cabove + cpivot
     ensures csp    == flatten(mapThruKlon(done+{next}, m))

     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
     ensures oabove == fOutside(done+{next}-{m.o}, m.o)                      ///HHMMM
     ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)        //HHMMM
     ensures oabove == cabove

     ensures IN_N_OUT_BURGER(oo, m)
{
// // // // // // // // // // // // // // // // // // // // // // // // // // // //

    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

  osp, obelow, oabove, opivot := FOUR_BY_FOUR(osp', obelow', oabove', opivot', {}, next.AMFO, {});
assert osp == osp' + next.AMFO; assert obelow == obelow'; assert opivot == opivot';
assert oabove == oabove' + next.AMFO;  assert osp == obelow + oabove + opivot;

  csp, cbelow, cabove, cpivot := FOUR_BY_FOUR(csp', cbelow', cabove', cpivot', {}, cext.AMFO, {});
assert csp == csp' + cext.AMFO; assert cbelow == cbelow'; assert cpivot == cpivot';
assert cabove == cabove' + cext.AMFO;  assert csp == cbelow + cabove + cpivot;

// // // // // // // // // // // // // // // // // // // // // // // // // // // //

    CASE_U3_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot)
        by {
            reveal OB1, CB1;
            assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
            assert cbelow' == (set x <- csp' | strictlyInside(x,m.c));
        }

// // // // // // // // // // // // // // // // // // // // // // // // // // // // //
//   assert (set x <- osp' | strictlyInside(x,m.o)) == obelow';
//   SET_SELECT_MONO2(osp', next.AMFO, m.o);
//   assert (set x <- osp' + next.AMFO | strictlyInside(x,m.o)) == (set x <- osp' | strictlyInside(x,m.o))  + (set x <- next.AMFO | strictlyInside(x,m.o));
//   assert outside(next, m.o); ALL_OWNERS_OUTSIDE(next.AMFO, m.o);
//   SET_IGNORE_MONO2(osp', next.AMFO, m.o);
//   assert (set x <- next.AMFO | strictlyInside(x,m.o)) == {};
//   assert (set x <- osp' + next.AMFO | strictlyInside(x,m.o)) == (set x <- osp' | strictlyInside(x,m.o)) == obelow';
//
// //-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
//   assert (set x <- csp' | strictlyInside(x,m.c)) == cbelow';
//   SET_SELECT_MONO2(csp', cext.AMFO, m.c);
//   assert (set x <- csp' + cext.AMFO | strictlyInside(x,m.c)) == (set x <- csp' | strictlyInside(x,m.c))  + (set x <- cext.AMFO | strictlyInside(x,m.c));
//   assert outside(cext, m.c); ALL_OWNERS_OUTSIDE(cext.AMFO, m.c);
//   SET_IGNORE_MONO2(csp', cext.AMFO, m.c);
//   assert (set x <- cext.AMFO | strictlyInside(x,m.c)) == {};
//   assert (set x <- csp' + cext.AMFO | strictlyInside(x,m.c)) == (set x <- csp' | strictlyInside(x,m.c)) == cbelow';
// // // // // // // // // // // // // // // // // // // // // // // // // // // // //

      assert obelow == (set x <- osp | strictlyInside(x,m.o));
//CANNOT WORK     assert (set x <- osp |        outside(x,m.o)) == oabove;
      assert cbelow == (set x <- csp | strictlyInside(x,m.c));
//CANNOT WRORKA      assert (set x <- csp |        outside(x,m.c)) == cabove;
      assert oabove == cabove;
      assert oabove' == fOutside(done-{m.o}, m.o);
      assert next.AMFO == fOutside({next}-{m.o}, m.o) by
              { fOUTSIDE_ONE(next,m.o,fOutside({next}-{m.o}, m.o)); }
      fOUTSIDE_MONOTONIC(done-{m.o},{next}-{m.o}, m.o);
      PLUS_MINUS3(done,{next},{m.o});
      assert (done-{m.o}) + ({next}-{m.o}) == (done+{next}-{m.o});
      assert oabove == fOutside(done+{next}-{m.o}, m.o);

      assert cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c);
      assert cext.AMFO == fOutside(mapThruKlon({next}-{m.o},m), m.c) by
              { fOUTSIDE_TWO(next,m,fOutside(mapThruKlon({next}-{m.o},m), m.c)); }
      fOUTSIDE_MONOTONIC(mapThruKlon(done-{m.o},m),mapThruKlon({next}-{m.o},m), m.c);
      PLUS_MINUS3(done,{next},{m.o});  assert (done-{m.o})+({next}-{m.o}) == (done+{next}-{m.o});
      FLATTEN_SUMS(done-{m.o},{next}-{m.o},done+{next}-{m.o},m);
      assert (mapThruKlon(done-{m.o},m) + mapThruKlon({next}-{m.o},m)) == mapThruKlon(done+{next}-{m.o},m);
      assert cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c);

    assert opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {});
    assert cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
    assert (m.o !in flatten({next}));
    FLATTEN_SUMS(done,{next},done+{next},m);
    assert (m.o in flatten(done+{next})) == (m.o in flatten(done));
    assert opivot == opivot';   assert cpivot == cpivot';
    assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});

    FLATTEN_SUMS(done,{next},done+{next},m);

    assert csp == csp' + {} + cext.AMFO + {};
    assert csp == csp' + cext.AMFO by {
            FUCKNUFFIN(csp,csp',cext.AMFO);
           }

    assert csp == flatten(mapThruKlon(done, m)) + cext.AMFO;


    // assert old@HERE((set x <- osp | strictlyInside(x,m.o)) == obelow);
    // assert old@HERE((set x <- csp | strictlyInside(x,m.c) )== cbelow);
    // assert old@HERE(obelow) == obelow;
    // assert old@HERE(cbelow) == cbelow;
    // assert old@HERE(oabove) == oabove;
    // assert old@HERE(cabove) == cabove;
    // assert (set x <- osp | strictlyInside(x,m.o)) == obelow;
    // assert (set x <- csp | strictlyInside(x,m.c)) == cbelow;
      assert oabove == fOutside(done+{next}-{m.o}, m.o);                 //HHMM
      assert cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c);  //HHMM

    assert mapThruKlon(done, m) + mapThruKlon({next}, m) == mapThruKlon(done+{next}, m);
    assert flatten(mapThruKlon(done, m)) + flatten(mapThruKlon({next}, m)) == flatten(mapThruKlon(done+{next}, m));
    assert cext.AMFO == flatten(mapThruKlon({next}, m)) by { FLATMAP_ONE(next,cext,m); }
    assert csp == flatten(mapThruKlon(done, m)) + cext.AMFO;
    assert csp == flatten(mapThruKlon(done+{next}, m));
  //    assert done+{next} == (oo - todo);
//    assert csp == flatten(mapThruKlon((oo - todo), m));


    assert osp == osp' + {} + next.AMFO + {};
    assert osp == osp' + next.AMFO by { FUCKNUFFIN(osp,osp',next.AMFO); }
    assert osp == flatten(done) + next.AMFO;  FLATTEN_ONE(next);
    assert osp == flatten(done) + flatten({next});
//assert opivot == (if (m.o in flatten(done)+{next}) then (m.o.AMFO) else {});    //should this have next in it too?
//    assert osp == flatten(done) + flatten({next});

    assert osp == obelow + oabove + opivot;
    PACK_OOOO(osp,obelow,oabove,opivot);
    PACK_OOOO(csp,cbelow,cabove,cpivot);


      assert (set x <- osp | strictlyInside(x,m.o)) == obelow;

      assert (set x <- csp | strictlyInside(x,m.c)) == cbelow;

      assert oabove == cabove;
      assert oabove == fOutside(done+{next}-{m.o}, m.o);
      assert cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c);

    assert forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c);// && (m.m[x] in csp);
assert OOOO(osp,obelow,oabove,opivot);
assert OOOO(csp,cbelow,cabove,cpivot);
    assert  cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
    assert  opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    assert (cpivot == {}) != (cpivot == m.c.AMFO);
    assert (opivot == {}) != (opivot == m.o.AMFO);
}










lemma CASE_INSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires strictlyInside(next, m.o)

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)

    requires next in m.m.Keys
    requires next.Ready()
    requires AllReady(flatten({next}))
    requires m.m.Keys >= oo
    requires m.m.Keys >= flatten(oo) >= flatten({next})
    requires cext     == m.m[next]
    requires klonLine(next,cext,m)
    requires oo       <= m.m.Keys
    requires oo       == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'     == flatten(done)
    requires csp'     == flatten(mapThruKlon(done, m))

    requires IN_N_OUT_BURGER(done, m)
    requires IN_N_OUT_BURGER({next}, m)

    requires osp'     == obelow' + oabove' + opivot'
    requires csp'     == cbelow' + cabove' + cpivot'

    requires obelow'  == allStrictlyInside(osp', m.o)
    requires cbelow'  == allStrictlyInside(csp', m.c)


    requires oabove'  == fOutside(done-{m.o}, m.o)
    requires cabove'  == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove'  == cabove'

    requires opivot'  == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot'  == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
     ensures todo !! {next} !! done
     ensures osp    == obelow + oabove + opivot
     ensures osp    == flatten(done+{next})
     ensures csp    == cbelow + cabove + cpivot
     ensures csp    == flatten(mapThruKlon(done+{next}, m))

     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})

     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
     ensures oabove == fOutside(done+{next}-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)
     ensures oabove == cabove

     ensures IN_N_OUT_BURGER(oo, m)
{
//
    IN_N_OUT_LEMMER(done, m);
    IN_N_OUT_LEMMER({next}, m);
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);
//
    osp, obelow, oabove, opivot := osp', obelow', oabove', opivot';
    csp, cbelow, cabove, cpivot := csp', cbelow', cabove', cpivot';

           osp := osp' + next.AMFO;
           csp := csp' + cext.AMFO;
//
          opaque ensures osp == flatten(done+{next})
            {
              assert osp' == flatten(done);
              FLATTEN_ONE(next);
              assert next.AMFO == flatten({next});
              assert osp' + next.AMFO
                      == flatten(done) +  flatten({next});
              FLATTEN_SUMS(done, {next}, done+{next}, m);
              assert osp == flatten(done+{next});
            }


          opaque ensures csp == flatten(mapThruKlon(done+{next},m))
            {
              MAPPEN_ONE(next,m) by
              {
                assume next.Ready();
                assume next in m.m.Keys;
                assume klonReady(m);
                assume klonCalid(m);
              }

              assert cext == m.m[next];
              FLATMAP_ONE(next,cext,m);
              assert cext.AMFO == flatten(mapThruKlon({next},m));
              assert csp' == flatten(mapThruKlon(done,m));
              assert csp' + cext.AMFO
                      == flatten(mapThruKlon(done,m)) +  flatten(mapThruKlon({next},m));
              FLATTEN_SUMS(done, {next}, done+{next}, m);
              assert csp == flatten(mapThruKlon(done+{next},m));
            }

           var obelow_ := allStrictlyInside(next.AMFO, m.o);
           opaque ensures obelow == allStrictlyInside(osp, m.o)
             {
                assert obelow' == allStrictlyInside(osp', m.o);
                obelow := obelow' + obelow_;
                 DELTA_strictlyInside(obelow, obelow', obelow_, osp, osp', next.AMFO, m.o);
                assert obelow == allStrictlyInside(osp, m.o);
             }

           var cbelow_ := allStrictlyInside(cext.AMFO, m.c);
           opaque ensures cbelow == allStrictlyInside(csp, m.c)
             {
                cbelow := cbelow' + cbelow_;
                DELTA_strictlyInside(cbelow, cbelow', cbelow_, csp, csp', cext.AMFO, m.c);
                assert cbelow == allStrictlyInside(csp, m.c);
             }


    assert m.o in flatten(done+{next}) by {
        assert m.o in flatten({next});
        assert strictlyInside(next, m.o);
    }

    opivot := m.o.AMFO; cpivot := m.c.AMFO;
    assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
    assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});





      var oabove_ := fOutside({next}-{m.o}, m.o);
      opaque ensures oabove == fOutside((done+{next})-{m.o}, m.o)
        {
          oabove := oabove' + oabove_;
          DELTA_objectOutside(oabove, oabove', oabove_, done+{next}, done, {next}, m.o);
          assert oabove == fOutside((done+{next})-{m.o}, m.o);
        }

      var cabove_ := fOutside(mapThruKlon({next}-{m.o},m), m.c);
      opaque ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
        {
          cabove := cabove' + cabove_;
          DELTA_cloneOutside(cabove, cabove', cabove_, done+{next}, done, {next}, m);
          assert cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c);
        }

    assert osp == flatten(done+{next});
   assert osp == obelow + oabove + opivot;
    assert csp == flatten(mapThruKlon(done+{next}, m));
   assert csp == cbelow + cabove + cpivot;

    PACK_OOOO(osp,obelow,oabove,opivot);
    PACK_OOOO(csp,cbelow,cabove,cpivot);
}





















lemma CASE_RECURSIVE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
  decreases next.AMFO

// // requires strictlyInside(next, m.o)

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)

    requires next in m.m.Keys
    requires next.Ready()
    requires AllReady(flatten({next}))
    requires m.m.Keys >= oo
    requires m.m.Keys >= done
    requires m.m.Keys >= todo
    requires next in m.m.Keys

     requires m.m.Keys >= flatten(oo) >= flatten({next})
     requires cext     == m.m[next]
//    requires klonLine(next,cext,m)

      requires oo       <= m.m.Keys
      requires done     <= m.m.Keys
      requires osp'     == flatten(done)
      requires csp'     == flatten(mapThruKlon(done, m))
// //
// //     requires IN_N_OUT_BURGER(done, m)
// //     requires IN_N_OUT_BURGER({next}, m)

    requires osp'     == obelow' + oabove' + opivot'
    requires csp'     == cbelow' + cabove' + cpivot'

    requires obelow'  == allStrictlyInside(osp', m.o)
    requires cbelow'  == allStrictlyInside(csp', m.c)


    requires oabove'  == fOutside(done-{m.o}, m.o)
    requires cabove'  == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove'  == cabove'

    requires opivot'  == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot'  == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//
//      ensures osp    == obelow + oabove + opivot
//      ensures osp    == flatten(done+{next})
//      ensures csp    == cbelow + cabove + cpivot
//      ensures csp    == flatten(mapThruKlon(done+{next}, m))
//
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
//
//     //  ensures OOOO(osp,obelow,oabove,opivot)
//     //  ensures OOOO(csp,cbelow,cabove,cpivot)
//     //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
//     //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//     //  ensures oabove == fOutside(done+{next}-{m.o}, m.o)
//     //  ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)
//     //  ensures oabove == cabove
//
//      ensures m.m.Keys >= next.AMFO
//      ensures IN_N_OUT_BURGER(oo, m)
{
    //   IN_N_OUT_LEMMER(oo, m);
    // assert IN_N_OUT_BURGER(oo, m);


      osp, obelow, oabove, opivot,
      csp, cbelow, cabove, cpivot
            :=
      osp', obelow', oabove', opivot',
      csp', cbelow', cabove', cpivot';

//  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
//
//     if (next == m.o)
// {
// //GOD KNOWS IF THIS IS DOING THE RIGHT THING HERE!
//       osp, obelow, oabove, opivot,
//       csp, cbelow, cabove, cpivot
//             :=
//           CAXE_UALL_PIVOT(oo, m, done, todo, next, cext,
//                       osp', obelow', oabove', opivot',
//                       csp', cbelow', cabove', cpivot');
// }// end pivot
//     else if (outside(next, m.o))  //  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
//     {
//     // //GOD KNOWS IF THIS IS DOING THE RIGHT THING HERE!
//         osp, obelow, oabove, opivot,
//         csp, cbelow, cabove, cpivot
//             :=
//           CASE_OUTSIDE(oo, m, done, todo, next, cext,
//                       osp', obelow', oabove', opivot',
//                       csp', cbelow', cabove', cpivot');
//     }//end outside case
// //  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -  -
//    else {
// //       assert strictlyInside(next, m.o);
// // assert SINM: strictlyInside(next, m.o);

  // 1. - add in just the "next" object itslf

    //  assert m.m[next] == cext;

//      osp := osp' + {next};
//      csp := csp' + {cext};
//
//     obelow := obelow' + {next};
//     cbelow := cbelow' + {cext};
//     oabove := oabove';
//     cabove := cabove';
//     opivot := opivot';
//     cpivot := cpivot';

        // //whatevs. are these here for anuy actual reason?
        // assert forall x <- osp | strictlyInside(x, m.o) ::  (m.m[x] in csp);
        // assert forall x <- csp | strictlyInside(x, m.c) ::  ((invert(m.m))[x] in osp);
  // 2. - recurse on each owner

  var owner := next.owner;
  while owner != {}
    decreases owner

  {
    var o : Object;
    o :| o in owner;
    var c := m.m[o];



//////////////////////////////////////////////////////////////////////////////////////////////
//
//
//
//     assert AllReady(oo);
//     assert klonReady(m);
//     assert klonCalid(m);
//
//     assert next in m.m.Keys;
//     assert next.Ready();
//     assert AllReady(flatten({next}));
//     assert m.m.Keys >= oo;
//     assert m.m.Keys >= done;
//     assert m.m.Keys >= todo;
//     assert next in m.m.Keys;
//     assert m.m.Keys >= flatten(oo) >= flatten({next});
//     assert cext     == m.m[next];
//     assert klonLine(next,cext,m);
//     assert oo       <= m.m.Keys;
//     assert done     <= m.m.Keys;
//     assert osp'     == flatten(done);
//     assert csp'     == flatten(mapThruKlon(done, m));
//     assert osp'     == obelow' + oabove' + opivot';
//     assert csp'     == cbelow' + cabove' + cpivot';
//
//     assert obelow'  == allStrictlyInside(osp', m.o);
//     assert cbelow'  == allStrictlyInside(csp', m.c);
//
//     assert oabove'  == fOutside(done-{m.o}, m.o);
//     assert cabove'  == fOutside(mapThruKlon(done-{m.o},m), m.c);
//     assert oabove'  == cabove';
//
//     assert opivot'  == (if (m.o in flatten(done)) then (m.o.AMFO) else {});
//     assert cpivot'  == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
//
//
//
/////////////////////////////////////////////////////////////////////////////////////////////./



    // assert AllReady(oo);
    // assert klonReady(m);
    // assert klonCalid(m);
    // assert m.m.Keys >= flatten(oo) >= flatten({next});
    // assert cext     == m.m[next];
    // assert c        == m.m[o];

    osp, obelow, oabove, opivot,
    csp, cbelow, cabove, cpivot
        :=
      CASE_RECURSIVE(oo, m, done, todo, o, c,                      //ERR
                  osp', obelow', oabove', opivot',
                  csp', cbelow', cabove', cpivot');

    owner := owner - {o};
  }//end while recurse on owner



    // assert m.o in flatten(done+{next})
    //     by {
    //       assert strictlyInside(next, m.o) by { reveal SINM; }
    //       assert flatten(done+{next}) == flatten(done) + flatten({next}) by { FLATTEN_SUMS(done,{next},done+{next},m); }
    //       assert m.o in flatten({next});
    //       assert m.o in flatten(done+{next});
    //     }

//  }//end else strictlyInside() case




//     opivot := m.o.AMFO; cpivot := m.c.AMFO;
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
//
//
//     assert osp == flatten(done+{next});
//    assert osp == obelow + oabove + opivot;
//     assert csp == flatten(mapThruKlon(done+{next}, m));
//    assert csp == cbelow + cabove + cpivot;

    // PACK_OOOO(osp,obelow,oabove,opivot);
    // PACK_OOOO(csp,cbelow,cabove,cpivot);
}//end CASE_RECURSIVE











// H#ERE - NEXST BIT
//
//        osp, obelow, oabove, opivot,
//        csp, cbelow, cabove, cpivot
//             :=
//           DO_LOOP(oo, m, done, todo, next, cext,
//                       osp, obelow, oabove, opivot,
//                       csp, cbelow, cabove, cpivot);
//                             return;
//
//lemma CASE_RECURSIVE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
//                   osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
//                   csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
//          returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
//                   csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)


//GOD KNOWS IF THIS IS DOING THE RIGHT THING HERE!

    // IN_N_OUT_LEMMER(done, m);
    // IN_N_OUT_LEMMER({next}, m);
    // IN_N_OUT_LEMMER(oo, m);


// //
//           opaque ensures osp == flatten(done+{next})
//             {
//               assert osp' == flatten(done);
//               FLATTEN_ONE(next);
//               assert next.AMFO == flatten({next});
//               assert osp' + next.AMFO
//                       == flatten(done) +  flatten({next});
//               FLATTEN_SUMS(done, {next}, done+{next}, m);
//               assert osp == flatten(done+{next});
//             }
//
//
//           opaque ensures csp == flatten(mapThruKlon(done+{next},m))
//             {
//               MAPPEN_ONE(next,m) by
//               {
//                 assume next.Ready();
//                 assume next in m.m.Keys;
//                 assume klonReady(m);
//                 assume klonCalid(m);
//               }
//
//               assert cext == m.m[next];
//               FLATMAP_ONE(next,cext,m);
//               assert cext.AMFO == flatten(mapThruKlon({next},m));
//               assert csp' == flatten(mapThruKlon(done,m));
//               assert csp' + cext.AMFO
//                       == flatten(mapThruKlon(done,m)) +  flatten(mapThruKlon({next},m));
//               FLATTEN_SUMS(done, {next}, done+{next}, m);
//               assert csp == flatten(mapThruKlon(done+{next},m));
//             }
//
//            var obelow_ := allStrictlyInside(next.AMFO, m.o);
//            opaque ensures obelow == allStrictlyInside(osp, m.o)
//              {
//                 assert obelow' == allStrictlyInside(osp', m.o);
//                 obelow := obelow' + obelow_;
//                  DELTA_strictlyInside(obelow, obelow', obelow_, osp, osp', next.AMFO, m.o);
//                 assert obelow == allStrictlyInside(osp, m.o);
//              }
//
//            var cbelow_ := allStrictlyInside(cext.AMFO, m.c);
//            opaque ensures cbelow == allStrictlyInside(csp, m.c)
//              {
//                 cbelow := cbelow' + cbelow_;
//                 DELTA_strictlyInside(cbelow, cbelow', cbelow_, csp, csp', cext.AMFO, m.c);
//                 assert cbelow == allStrictlyInside(csp, m.c);
//              }
//
//
//     assert m.o in flatten(done+{next}) by {
//         assert m.o in flatten({next});
//         assert strictlyInside(next, m.o);
//     }
//
//     opivot := m.o.AMFO; cpivot := m.c.AMFO;
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
//
//
//
//
//
//       var oabove_ := fOutside({next}-{m.o}, m.o);
//       opaque ensures oabove == fOutside((done+{next})-{m.o}, m.o)
//         {
//           oabove := oabove' + oabove_;
//           DELTA_objectOutside(oabove, oabove', oabove_, done+{next}, done, {next}, m.o);
//           assert oabove == fOutside((done+{next})-{m.o}, m.o);
//         }
//
//       var cabove_ := fOutside(mapThruKlon({next}-{m.o},m), m.c);
//       opaque ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
//         {
//           cabove := cabove' + cabove_;
//           DELTA_cloneOutside(cabove, cabove', cabove_, done+{next}, done, {next}, m);
//           assert cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c);
//         }
//
    // assert osp == flatten(done+{next});
//    assert osp == obelow + oabove + opivot;
    // assert csp == flatten(mapThruKlon(done+{next}, m));
//    assert csp == cbelow + cabove + cpivot;
//
//     PACK_OOOO(osp,obelow,oabove,opivot);
//     PACK_OOOO(csp,cbelow,cabove,cpivot);









//
// lemma CASE_LIGHTWEIGHT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
//                   osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
//                   csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
//          returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
//                   csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
//
//     requires strictlyInside(next, m.o)
//
//     requires AllReady(oo)
//     requires klonReady(m)
//     requires klonCalid(m)
//
//     requires next in m.m.Keys
//     requires next.Ready()
//     requires AllReady(flatten({next}))
//     requires m.m.Keys >= oo
//     requires m.m.Keys >= flatten(oo) >= flatten({next})
//     requires cext     == m.m[next]
//     requires klonLine(next,cext,m)
//     requires oo       <= m.m.Keys
//     requires oo       == todo + {next} + done
//     requires todo !! {next} !! done
//     requires osp'     == flatten(done)
//     requires csp'     == flatten(mapThruKlon(done, m))
//
//     // requires IN_N_OUT_BURGER(done, m)
//     // requires IN_N_OUT_BURGER({next}, m)
// //
// //     requires osp'     == obelow' + oabove' + opivot'
// //     requires csp'     == cbelow' + cabove' + cpivot'
//
//     requires obelow'  == allStrictlyInside(osp', m.o)
//     requires cbelow'  == allStrictlyInside(csp', m.c)
//
// //
// //     requires oabove'  == fOutside(done-{m.o}, m.o)
// //     requires cabove'  == fOutside(mapThruKlon(done-{m.o},m), m.c)
// //     requires oabove'  == cabove'
// //
//     requires opivot'  == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
//     requires cpivot'  == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//
//     ensures oo     == todo + {next} + done
//     ensures todo !! {next} !! done
//     //  ensures osp    == obelow + oabove + opivot
//     ensures osp    == flatten(done+{next})
// //      ensures csp    == cbelow + cabove + cpivot
//      ensures csp    == flatten(mapThruKlon(done+{next}, m))
// //
//      ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
//      ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})
// //
// //      ensures OOOO(osp,obelow,oabove,opivot)
// //      ensures OOOO(csp,cbelow,cabove,cpivot)
//      ensures obelow == allStrictlyInside(osp, m.o)
//      ensures cbelow == allStrictlyInside(csp, m.c)
//     //  ensures obelow == (set x <- osp | strictlyInside(x,m.o))
//     //  ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
//
//      ensures oabove == fOutside(done+{next}-{m.o}, m.o)
//      ensures cabove == fOutside(mapThruKlon(done+{next}-{m.o},m),m.c)
//      ensures oabove == cabove
//
//     ensures IN_N_OUT_BURGER(oo, m)
// {
//     osp, obelow, oabove, opivot := osp', obelow', oabove', opivot';
//     csp, cbelow, cabove, cpivot := csp', cbelow', cabove', cpivot';
//
// // // // // // // // // // // // // // // // // // // // // // // // // // //
//     osp := flatten(done+{next});
//     csp := flatten(mapThruKlon(done+{next},m));
// // // // // // // // // // // // // // // // // // // // // // // // // // //
//     obelow := allStrictlyInside(osp, m.o);
//     cbelow := allStrictlyInside(csp, m.c);
//
//
// //    assert forall x <- obelow :: m.m[x] in cbelow;
//
// // // // // // // // // // // // // // // // // // // // // // // // // // //
//
//     oabove := allOutside(osp, m.o);
//     cabove := allOutside(csp, m.c);
//
//     IN_N_OUT_LEMMER(oo, m);
//
//     assert forall x <- oabove |  outside(x,m.o) ::  (m.m[x] == x);
//     assert forall x <- oabove :: outside(x,m.o);
//     assert forall x <- oabove :: m.m[x] == x;
//
// /// // // // // // // // // // // // // // // // // // // // // // // // // //
//
//
// assert m.m[next] == cext;
// assert klonLine(next,cext,m);
// FLATTEN_ONE(next); assert flatten({next}) == next.AMFO;
// FLATTEN_ONE(cext); assert flatten({cext}) == cext.AMFO;
//
// assert forall n <- next.AMFO | strictlyInside(n, m.o) ::
//   && (n in m.m.Keys)
//   && inside(m.m[n], m.c)
//   && (m.m[n] in cext.AMFO);
//
// /// <<<THURS 16 July>>>   make a recusrive split ,lemma to do thais>>>
// //
// //
// //lemma next / cext, M
// // ensures
// //  if inside
// //   owner => owner;    bound => Bound
// //  if outside
// //     objects are a==
// //
// // argue up from owner fields to AMDOs???
// /// // // // // // // // // // // // // // // // // // // // // // // // // //
//     assert m.o in flatten(done+{next});
//
//     opivot := m.o.AMFO; cpivot := m.c.AMFO;
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
// // // // // // // // // // // // // // // // // // // // // // // // // // //
//
// }
//
// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// //     var D_N_P := (done+{next})-{m.o};
// //     oabove := fOutside(D_N_P, m.o);
// //     cabove := fOutside(mapThruKlon(D_N_P,m), m.c);
// //     IN_N_OUT_LEMMER(oo, m);
// //     assert (forall x <- flatten(oo) | outside(x,m.o) ::  (m.m[x] == x));
// //
// //     assert oabove == set x <- flatten(D_N_P) | outside(x,m.o);
// //
// //     assert oabove == cabove;
// // // // // // // // // // // // // // // // // // // // // // // // // // // //


lemma CASE_NEXT_STRICTLY_INSIDE_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

   //demonstrates that ANFO of stricktlyinside(pivot) is a strict superset of the AMFO of the pivot

    requires strictlyInside(next, m.o)

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)

    requires m.m.Keys >= oo
    requires m.m.Keys >= flatten(oo) >= flatten({next})
    requires cext     == m.m[next]
    requires klonLine(next,cext,m)
    requires oo       <= m.m.Keys
    requires oo       == todo + {next} + done
    requires todo !! {next} !! done

    ensures m.o.AMFO <= next.AMFO
    ensures m.c.AMFO <= cext.AMFO
    ensures oo     == todo + {next} + done
    ensures todo !! {next} !! done
//     //  ensures osp    == obelow + oabove + opivot
//     ensures osp    == flatten(done+{next})
// //      ensures csp    == cbelow + cabove + cpivot
//      ensures csp    == flatten(mapThruKlon(done+{next}, m))
{
    osp, obelow, oabove, opivot := osp', obelow', oabove', opivot';
    csp, cbelow, cabove, cpivot := csp', cbelow', cabove', cpivot';

    // oabove := fOutside(D_N_P, m.o);
    // cabove := fOutside(mapThruKlon(D_N_P,m), m.c);


    //what should come first, tje FLATTEN or the OUTSIDE?
    //nmeedsxs to be flattern?
     //cos next within CASE_INSIDE is always strictlyInside m.o
     //so if we select first, we'd only ever get NOTHING.
     //so we flatten, and then select!
     //but I fear this is wront.  we know next != m.o. so not cleawr suybvracting m.o does the righ tthing.
     //perhaps we should just take the AMFO, then remove the m.o.AMFO from that, then remoive all the inside ones.
    ////hmmm.
     //REALLY need to THINK MORE

    assert m.o.AMFO <= next.AMFO;
    assert m.c.AMFO <= cext.AMFO;

}


//OFFCUTS fronm CASE_INSIDE
//
//
//
// var oInside := obelow_;
// var oOffside := (set x <- next.AMFO | offside(x,m.o));
//
//          SLICE_N_DICE(next.AMFO, m.o, oInside, oOffside);
//          assert        next.AMFO == m.o.AMFO + oInside + oOffside;
//          assert NAMFO: next.AMFO == m.o.AMFO + oInside + oOffside;
//
//     assert osp' == flatten(done);
//     assert osp  == osp' + next.AMFO;
//     FUCKED_SUM3_SUB1(osp, osp', next.AMFO, m.o.AMFO, oInside, oOffside) by { reveal NAMFO; }
//     assert osp  == osp' + m.o.AMFO + oInside + oOffside by { reveal NAMFO; }
//
//
// var cInside  := (set x <- cext.AMFO | strictlyInside(x, m.c));
// var cOffside := (set x <- cext.AMFO | offside(x, m.c));
//
//          SLICE_N_DICE(cext.AMFO, m.c, cInside, cOffside);
//          assert        cext.AMFO == m.c.AMFO + cInside + cOffside;
//          assert CAMFO: cext.AMFO == m.c.AMFO + cInside + cOffside;
//          FLATTEN_ONE(cext);
//          assert flatten({cext}) == m.c.AMFO + cInside + cOffside;
//
//
//     assert csp' == flatten(mapThruKlon(done, m));
//     assert csp  == csp' + cext.AMFO;
//     FUCKED_SUM3_SUB1(csp, csp', cext.AMFO, m.c.AMFO, cInside, cOffside) by { reveal CAMFO; }
//     assert csp  == csp' + m.c.AMFO + cInside + cOffside by { reveal CAMFO; }
//
//     assert osp' == obelow' + oabove' + opivot';
//     assert csp' == cbelow' + cabove' + cpivot';
//
//     assert strictlyInside(next, m.o);
//     assert m.o in flatten({next});
//     assert m.o in flatten(done+{next});
//
//     opivot := m.o.AMFO; cpivot := m.c.AMFO;
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
//
//         opaque
//           ensures obelow' == (set x <- osp' | strictlyInside(x,m.o))
//           ensures oInside == (set x <- next.AMFO | strictlyInside(x, m.o))
//          {
//          assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
//           assert oInside == (set x <- next.AMFO | strictlyInside(x, m.o));
//         }
//
//
//
//     assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
//         assert oInside == (set x <- next.AMFO | strictlyInside(x, m.o));
//
//
//     obelow := obelow' + oInside;
//     DELTA_strictlyInside(obelow, obelow', oInside, osp, osp', next.AMFO, m.o)
//       by
//         {
//           assume obelow' == (set x <- osp' | strictlyInside(x,m.o));
//           assume oInside == (set x <- next.AMFO | strictlyInside(x, m.o));
//         }
//
// return;
//
//
//
//       assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
//       var cpivot_before := cpivot;
//       assert taxi: cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {});
//
//       assert strictlyInside(next, m.o);
// assert cext == m.m[next];
// assert cext.owner ==  mapThruKlon(next.owner, m);
//       assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//                by { reveal taxi; assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {}); }
//
//
//
//      assert cpivot == cpivot_before;
//
//      assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//                by { reveal taxi; assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {}); }
//
//
//
//       assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//                by { reveal taxi; assert cpivot_before == (if (m.o in flatten(done)) then (m.c.AMFO) else {}); }
//       assert cpivot_before == cpivot;
//       assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {})
//          by { reveal taxi; assert cpivot == (if (m.o in flatten(done)) then (m.c.AMFO) else {}); }
//       assert inside(next, m.o);
//       assert m.o in flatten({next});
//       assert m.o in flatten(done+{next});
//
//     assert flatten(mapThruKlon({next}, m)) == m.c.AMFO + cInside + cOffside;
//
//     // FLATTEN_SUMS(done,{next},done+{next},m);
//     // assert csp == flatten(mapThruKlon(done+{next}, m));
//
//
//
//     assert flatten(mapThruKlon(done, m)) + flatten(mapThruKlon({next}, m)) == flatten(mapThruKlon(done+{next}, m));
//     assert flatten(mapThruKlon(done+{next}, m)) == flatten(mapThruKlon(done, m)) + flatten(mapThruKlon({next}, m));
//     assert flatten(mapThruKlon(done, m))   == csp' == cbelow' + cabove' + cpivot';
//     assert      flatten(mapThruKlon({next}, m)) == m.c.AMFO + cInside + cOffside;
//     assert NCM: flatten(mapThruKlon({next}, m)) == m.c.AMFO + cInside + cOffside;
//     assert MCN: (m.c.AMFO + cInside + cOffside) == flatten(mapThruKlon({next}, m));
//
//     osp, obelow, oabove, opivot := FOUR_BY_FOUR(osp', obelow', oabove', opivot', oInside, oOffside, m.o.AMFO);
//     csp, cbelow, cabove, cpivot := FOUR_BY_FOUR(csp', cbelow', cabove', cpivot', cInside, oOffside, m.c.AMFO);
//     assert osp == obelow + oabove + opivot;
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//
//     assert csp == cbelow + cabove + cpivot;
//     assert cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {});
//
//     assert csp == csp' + cInside + cOffside + m.c.AMFO;
//    // assert csp == csp' + cInside + cOffside + m.c.AMFO by { FUCKNUTTIN(csp,csp',cInside,m.c.AMFO); }
//     assert csp == flatten(mapThruKlon(done, m)) + cInside + cOffside + m.c.AMFO;
//     assert done == done;
//     assert csp == flatten(mapThruKlon(done, m))  + cInside + cOffside + m.c.AMFO;
//     assert FNN: flatten(mapThruKlon({next}, m)) == cInside + cOffside + m.c.AMFO by { reveal NCM; }
//
//     FARKWUFFUN(csp, flatten(mapThruKlon(done, m)), cInside+cOffside, m.c.AMFO, flatten(mapThruKlon({next}, m)));
//
//     assert csp == flatten(mapThruKlon(done, m)) + flatten(mapThruKlon({next}, m)) by { reveal FNN, NCM; }
//     assert mapThruKlon(done, m) + mapThruKlon({next}, m) == mapThruKlon(done+{next}, m)
//       by {   FLATTEN_SUMS(done,{next},done+{next},m); }
//        FLATMAP_ONE(next,cext,m);
//     assert flatten(mapThruKlon(done, m)) + flatten(mapThruKlon({next}, m)) == flatten(mapThruKlon(done+{next}, m));
//
//     assert csp == flatten(mapThruKlon(done+{next}, m));
// //    assert done+{next} == (oo - todo);
// //    assert csp == flatten(mapThruKlon((oo - todo), m));
//
//     assert osp' == flatten(done);
//     assert osp == osp' + oInside + m.o.AMFO by { FUCKNUTTIN(osp,osp',oInside,m.o.AMFO); }
//     assert osp == flatten(done) + oInside + oOffside + m.o.AMFO;
//     assert next.AMFO == oInside + oInside + m.o.AMFO by { FLATTEN_ONE(next); }
//     assert osp == flatten(done) + oInside + oOffside + m.o.AMFO;
//     assert oInside + oOffside + m.o.AMFO == flatten({next});
//     FARKWUFFUN(osp, flatten(done), oInside + oOffside, m.o.AMFO, flatten({next}) );
//
//
//
// assert osp  == flatten(done+{next});
// fStrictlyInside_MONOTONIC(done,{next},m.o);
// LIFT_inside(obelow, osp, done+{next}, m.o);
//
// assert osp  == flatten(done) + flatten({next});
// LIFT_inside(obelow', osp', done, m.o);
//
//
//
// assert osp' == flatten(done);
// assert osp  == osp' + flatten({next});
//
// assert obelow' == (set x <- osp' | strictlyInside(x,m.o));
// assert obelow' == (set x <- flatten(done) | strictlyInside(x,m.o));
//
// assert obelow  == (set x <- osp  | strictlyInside(x,m.o));
// assert obelow  == (set x <- flatten(done+{next})  | strictlyInside(x,m.o));
// assert obelow  == (set x <- flatten(done) | strictlyInside(x,m.o))
//                 + (set x <- flatten({next}) | strictlyInside(x,m.o));
// assert obelow  == (set x <- flatten(done) | strictlyInside(x,m.o))
//                 + (set x <- next.AMFO| strictlyInside(x,m.o));
//
// return;
//
// assert obelow ==  fStrictlyInside(done+{next},m.o);
// assert obelow ==  fStrictlyInside(done,m.o) + fStrictlyInside({next},m.o);
// assert obelow ==  obelow' + fStrictlyInside({next},m.o);
//
// FLATTEN_ONE(next);
// assert flatten({next}) == next.AMFO;
// assert oInside == (set x <- flatten({next}) | strictlyInside(x,m.o));
// assert oInside == fStrictlyInside({next},m.o);
// assert obelow ==  obelow' + oInside;
//
//
//
//     assert osp == flatten(done) + flatten({next});
//     assert opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {});
//     assert osp == obelow + oabove + opivot;
//     PACK_OOOO(osp,obelow,oabove,opivot);
//     PACK_OOOO(csp,cbelow,cabove,cpivot);
//
//
//
//     assert obelow == obelow' + oInside;
//     assert cbelow == cbelow' + cInside;
//
//     assert oabove == oabove';
//     assert cabove == cabove';
//
//      assert obelow == (set x <- osp | strictlyInside(x,m.o));
//      assert cbelow == (set x <- csp | strictlyInside(x,m.c));
//
//











































lemma FUCKNUFFIN(x : Owner, y : Owner, z : Owner)
  requires x == y + {} + z + {}
   ensures x == y + z
   {}


lemma FUCKNUTTIN(w : Owner, x : Owner, y : Owner, z : Owner)
  requires w == x + y + {} + z
   ensures  w == x + y + z
   {}

lemma FARKWUFFUN(a : Owner, b : Owner, c : Owner, d : Owner, e : Owner)
  requires a == b + c + d
  requires c + d == e
   ensures a == b + e
   {}




lemma CFTO(o : Object)
  requires o.Ready()
   ensures flatten({o}) == o.AMFO
   {}

lemma SLICE_N_DICE(amfo : OWNR, pivot : Object, below : OWNR, aside : OWNR)
    //give that below == amfo - pivot.AMFO,
    //then below + pivot.AMFO == amfo
  requires AllReady(amfo)
  requires pivot.Ready()
  requires AllReady(below)
  requires AllReady(aside)
  requires amfo > pivot.AMFO
   ensures forall x <- pivot.AMFO :: (x in amfo) //&& inside(x,pivot)
   ensures (set x <- amfo | x in pivot.AMFO) == pivot.AMFO

//nope requires forall x <- below :: x.AMFO > pivot.AMFO    //stops ""side loadung"""
//  requires below == amfo - pivot.AMFO
  requires below == (set x <- amfo | strictlyInside(x,pivot))
  requires aside == (set x <- amfo |        offside(x,pivot))
   ensures amfo == pivot.AMFO + below + aside
   ensures forall x <- below :: (x in amfo) //&& (strictlyInside(x, pivot))
   ensures forall x <- below :: x !in pivot.AMFO
   ensures forall x <- aside :: (x in amfo) //&& (strictlyInside(x, pivot))
   ensures forall x <- aside :: x !in pivot.AMFO
  //nope ensures forall x <- below :: (strictlyInside(x, pivot))
   ensures below >= (set x <- amfo | strictlyInside(x, pivot))
  //nope ensures below <= (set x <- amfo | strictlyInside(x, pivot))
  {}


lemma PLUS_MINUS(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b - (c + d)
   ensures a == b - c - d
{}


lemma PLUS_MINUS3(b : Owner, c : Owner, d : Owner)
   ensures (b - d) + (c - d) == (b + c - d)
{}

lemma CORDELIA(a : Owner, b : Owner)
   ensures (a - b) == ((a + b) - b)
{}

lemma MINUS3(a : Owner, b : Owner, c : Owner)
  requires c <= b
  requires a == b - c
   ensures b == a + c
{}

lemma PLUS4(a : Owner, b : Owner, c : Owner, d : Owner)
  requires a == b + c + d
  requires b !! c !! d
   ensures a == (b + d) + c
   ensures a == b + c + d
   ensures a == d + c + b
{}

























































lemma CAXE_UALL_PIVOT(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)
    //casa pivot, osp = flattehnthruklon

    requires next == m.o

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
     ensures todo  !! {next} !! done
     ensures osp   == obelow + oabove + opivot
     ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
     ensures csp   == flatten(mapThruKlon(done+{next}, m))

     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})

    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)
     ensures obelow == (set x <- osp | strictlyInside(x,m.o))
     ensures cbelow == (set x <- csp | strictlyInside(x,m.c))
     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove

    //  ensures osp   == flatten(done+{next})
    //  ensures csp   == flatten(mapThruKlon(done+{next}, m))

     ensures IN_N_OUT_BURGER(oo, m)

{
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove';
    cabove := cabove';
    opivot := opivot' + m.o.AMFO;
    cpivot := cpivot' + m.c.AMFO;
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    CASE_U0_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U1_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U2_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U3_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U4_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U5_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U6_PIVOT(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
}



lemma CAXE_UALL_OUTSIDE(oo : Owner, m : Klon, done : Owner, todo : Owner, next : Object, cext : Object,
                  osp' : Owner, obelow' : Owner, oabove' : Owner, opivot' : Owner,
                  csp' : Owner, cbelow' : Owner, cabove' : Owner, cpivot' : Owner)
         returns (osp  : Owner, obelow  : Owner, oabove  : Owner, opivot  : Owner,
                  csp  : Owner, cbelow  : Owner, cabove  : Owner, cpivot  : Owner)

    requires outside(next,m.o)

    requires AllReady(oo)
    requires klonReady(m)
    requires klonCalid(m)
    requires flatten(oo) <= m.m.Keys
    requires next in m.m.Keys
    requires cext == m.m[next]
    requires klonLine(next,cext,m)
    requires oo <= m.m.Keys
    requires oo     == todo + {next} + done
    requires todo !! {next} !! done
    requires osp'    == obelow' + oabove' + opivot'
    requires osp' == flatten(done)// == (set d : Object <- done, dd <- flatten({d}) :: dd)
    requires csp'    == cbelow' + cabove' + cpivot'
    requires csp'    == flatten(mapThruKlon(done, m))
    // requires forall x <- done |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- done | outside(x,m.o) :: (m.m[x] == x) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) |  inside(x,m.o) ::  inside(m.m[x],m.c) //&& (m.m[x] in csp')
    // requires forall x <- flatten(done) | outside(x,m.o) ::  (m.m[x] == x) //&& (m.m[x] in csp)
    requires obelow' == (set x <- osp' | strictlyInside(x,m.o))
    requires cbelow' == (set x <- csp' | strictlyInside(x,m.c))
    requires oabove' == fOutside(done-{m.o}, m.o)
    requires cabove' == fOutside(mapThruKlon(done-{m.o},m), m.c)
    requires oabove' == cabove'
    requires opivot' == (if (m.o in flatten(done)) then (m.o.AMFO) else {})
    requires cpivot' == (if (m.o in flatten(done)) then (m.c.AMFO) else {})

     ensures oo     == todo + {next} + done
     ensures todo  !! {next} !! done

     ensures osp   == obelow + oabove + opivot
     ensures osp   == flatten(done+{next})
     ensures csp   == cbelow + cabove + cpivot
     ensures csp   == flatten(mapThruKlon(done+{next}, m))

     ensures cpivot == (if (m.o in flatten(done+{next})) then (m.c.AMFO) else {})
     ensures opivot == (if (m.o in flatten(done+{next})) then (m.o.AMFO) else {})

    //  ensures forall x <- done+{next} |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- done+{next} | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
    //  ensures forall x <- flatten(done+{next}) |  inside(x,m.o) ::  inside(m.m[x],m.c)
    //  ensures forall x <- flatten(done+{next}) | outside(x,m.o) :: (m.m[x] == x) // && (m.m[x] in csp)
     ensures OOOO(osp,obelow,oabove,opivot)
     ensures OOOO(csp,cbelow,cabove,cpivot)

     ensures oabove == fOutside((done+{next})-{m.o}, m.o)
     ensures cabove == fOutside(mapThruKlon((done+{next})-{m.o},m), m.c)
     ensures oabove == cabove

    //  ensures osp   == flatten(done+{next})
    //  ensures csp   == flatten(mapThruKlon(done+{next}, m))

     ensures IN_N_OUT_BURGER(oo, m)
{
    IN_N_OUT_LEMMER(oo, m);
    assert IN_N_OUT_BURGER(oo, m);

    obelow := obelow';
    cbelow := cbelow';
    oabove := oabove' + next.AMFO;
    cabove := cabove' + cext.AMFO;
    opivot := opivot';
    cpivot := cpivot';
    osp    := obelow + oabove + opivot;
    csp    := cbelow + cabove + cpivot;

    GEFUCKENHEGSETH(osp, obelow', oabove', next.AMFO, opivot');
    GEFUCKENHEGSETH(csp, cbelow', cabove', cext.AMFO, cpivot');

    assert osp == osp' + next.AMFO;
    assert csp == csp' + cext.AMFO;

    CASE_U0_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U1_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U2_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U3_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U4_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U5_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
    CASE_U6_OUTSIDE(oo, m, done, todo, next, cext,
                  osp', obelow', oabove', opivot', csp', cbelow', cabove', cpivot',
                  osp , obelow , oabove , opivot , csp , cbelow , cabove , cpivot);
}















































// hacetor srt out where thislog goes
//
// function recOwners(o : Object) : (rv : Owner)
//   decreases o.AMFO
//     ensures o.AMFO >= rv
//    requires o.Ready()
//     { {o} + (set xo <- o.owner, co <- recOwners(xo) :: co) }
//
// function recFlatten(oo : Owner) : (rv : Owner)
//   //set version of recOwners --- all the owners of oo including oo
//   requires AllReady(oo)
//   requires forall o <- oo :: o.Ready()
//  decreases allAMFOs(oo)
// //ensures isFlat(rv)
// //  ensures isRecFlat(rv)
//    {set o : Object <- oo, ooo <- recOwners(o) :: ooo}
//

function recOutsideNotViaPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (outside(o,pivot)) then (o.AMFO)
        else (if (o == pivot) then {}
          else (set oo <- o.owner, ooo <- recOutsideNotViaPivot(oo, pivot) :: ooo))
    }

//
// lemma FIAHF(o : Object, pivot : Object)
//   requires o.Ready()
//    ensures recOwners(o) >= recOutsideNotViaPivot(o, pivot)
// {}




lemma COLLECT_ALL_REC_OWNERS(o : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   o.AMFO == recOwners(o)
  ensures   o.AMFO == collectAllOwners(o)
  {}

lemma {:verify false} COLLECT_ALL_REC_INSIDE(o : Object, pivot : Object)
  decreases o.AMFO
  requires  o.Ready()
  ensures   (set oo <- recOwners(o) | recInside(oo,pivot)) == allInside(recOwners(o),pivot)
  {
    COLLECT_ALL_REC_OWNERS(o);
  }

function recBelow(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
    ensures forall oo <- rv :: inside(oo, pivot)
   requires o.Ready()
    {
      if (inside(o,pivot))
        then ({o} + (set xo <- o.owner, co <- recBelow(xo, pivot) :: co))
        else {}
     }

function walkOwners(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
   requires o.Ready()
    {
      (  if (true) then ({o}) else ({})  )
      +
      (  set xo <- o.owner, co <- walkOwners(xo, pivot) :: co  )
    }

function walk0wners(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    {
      assume forall oo <- o.owner ::  o.AMFO decreases to oo.AMFO;

      (  if (true) then ({o}) else ({})  )
      +
      (  set xo <- o.owner, co <- walk0wners(xo, pivot) :: co  )
    }


lemma {:verify false} REC_WALK_OWNERS(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures walkOwners(o,pivot) == recOwners(o)
{
   if (o.owner == {})
    { assert walkOwners(o,pivot) == {o};
      assert recOwners(o) == {o};
      assert walkOwners(o,pivot) == recOwners(o);
      return; }

   forall oo <- o.owner ensures (walkOwners(oo,pivot) == recOwners(oo)) //by
     {
      REC_WALK_OWNERS(oo, pivot);
     }
}



predicate outsideOrPivot(p : Object, w : Object) : (rv : bool)
   //see pivotlyOutside
   reads {}
    {(p == w) || outside(p,w)}

function walkStrictlyInside(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
    ensures forall r <- rv :: strictlyInside(r, pivot)
      reads {}
   requires o.Ready()
  //  ensures forall r <- walkOwners(o,pivot) | strictlyInside(r, pivot) :: r in rv
    //see recBelow
    {
      (  if (strictlyInside(o,pivot)) then ({o}) else ({})  )
      +
      (  set xo <- o.owner, co <- walkStrictlyInside(xo, pivot) :: co  )
    }


function wasm0(o : Object, pivot : Object) : (rv : Owner)
    reads {}
{ (set r <- walk0wners(o,pivot) | strictlyInside(r, pivot)) }



function wasm(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
   requires o.Ready()
    ensures o.AMFO >= rv
    ensures forall r <- rv :: strictlyInside(r, pivot)
    reads {}
{ (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)) }

lemma W0SM_W0SM(o : Object, pivot : Object, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires rv == wasm0(o,pivot)
 //   ensures o.AMFO >= rv
    ensures forall r <- rv :: strictlyInside(r, pivot)
    ensures rv == wasm0(o,pivot)
    ensures rv == (set r <- walk0wners(o,pivot) | strictlyInside(r, pivot))
   {}

lemma WASM_WASM(o : Object, pivot : Object, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires rv == wasm(o,pivot)
    ensures o.AMFO >= rv
    ensures forall r <- rv :: strictlyInside(r, pivot)
    ensures rv == wasm(o,pivot)
    ensures rv == (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot))
   {}

lemma WALK_STRICTLY_INSIDE(o : Object, pivot : Object, rv : Owner)
  decreases o.AMFO
   requires o.Ready()
   requires rv == walkStrictlyInside(o,pivot)
    ensures o.AMFO >= rv
    ensures forall r <- rv :: strictlyInside(r, pivot)
    ensures rv == wasm(o, pivot)
//    ensures forall r <- walkOwners(o,pivot) | strictlyInside(r, pivot) :: r in rv
    ensures (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)) == walkStrictlyInside(o,pivot)
   requires o.Ready()
{
  var theObjectWhatIsStrictlyInside : set<Object> := {};   //really an option!

  if (strictlyInside(o, pivot)) {
    assert o in walkOwners(o,pivot);
    assert o in (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot));
    assert o in rv;
    assert o in walkStrictlyInside(o,pivot);

    theObjectWhatIsStrictlyInside := {o};
     assert && (o  in walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)))
               && (theObjectWhatIsStrictlyInside <= rv)
               && (theObjectWhatIsStrictlyInside <= walkStrictlyInside(o,pivot));
  } else {
    assert not(strictlyInside(o, pivot));

    assert o  in walkOwners(o,pivot);
    assert o !in (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot));
    assert o !in rv;
    assert o !in walkStrictlyInside(o,pivot);

    theObjectWhatIsStrictlyInside := {};
     assert && (o  in walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)))
               && (theObjectWhatIsStrictlyInside <= rv)
               && (theObjectWhatIsStrictlyInside <= walkStrictlyInside(o,pivot));

    }

     assert && (o  in walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside <= (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)))
               && (theObjectWhatIsStrictlyInside <= rv)
               && (theObjectWhatIsStrictlyInside <= walkStrictlyInside(o,pivot));

   if (o.owner == {})
    {
        assert && (o  in walkOwners(o,pivot))
               && (theObjectWhatIsStrictlyInside == (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot)))
               && (theObjectWhatIsStrictlyInside == rv)
               && (theObjectWhatIsStrictlyInside == walkStrictlyInside(o,pivot));

      return; }

   forall oo <- o.owner //ensures (forall r <- walkOwners(oo,pivot) | strictlyInside(r, pivot) :: r in rv)
     ensures (set r <- walkOwners(oo,pivot) | strictlyInside(r, pivot)) == walkStrictlyInside(oo,pivot)
     {
      WALK_STRICTLY_INSIDE(oo, pivot, walkStrictlyInside(oo,pivot));
      assert (set r <- walkOwners(oo,pivot) | strictlyInside(r, pivot)) == walkStrictlyInside(oo,pivot);
     }

assert forall oo <- o.owner :: (set r <- walkOwners(oo,pivot) | strictlyInside(r, pivot)) == walkStrictlyInside(oo,pivot);

var wosi := set oo <- o.owner, r <- walkOwners(oo,pivot) | strictlyInside(r, pivot) :: r;
var wsi  := set oo <- o.owner, r <- walkStrictlyInside(oo,pivot)  :: r;

assert wosi == set oo <- o.owner, r <- wasm(oo,pivot)  :: r;
assert wosi == wsi;


//   assert walkOwners(o,pivot) == theObjectWhatIsStrictlyInside +
//
//       (set r <- walkOwners(o,pivot) | strictlyInside(r, pivot))
//
//
//
//   assert walkStrictlyInside(o,pivot) == theObjectWhatIsStrictlyInside +
//         walkStrictlyInside(o,pivot);
//

 }

lemma gefucked(o : Object, pivot : Object, a : (Object, Object) -> Owner, b : (Object, Object) -> Owner)
  requires o.Ready()
  requires forall oo <- o.owner :: a(oo,pivot) == b(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  a(oo,pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  b(oo,pivot) :: r )
{}


lemma gefucked2(o : Object, pivot : Object, a : (Object, Object) --> Owner, b : (Object, Object) --> Owner)
  requires o.Ready()
  requires forall oo <- o.owner ::
     && a.requires(oo,pivot)
     && b.requires(oo,pivot)
     && a(oo,pivot) == b(oo,pivot)

  // requires forall oo <- o.owner :: a.requires(oo,pivot)
  // requires forall oo <- o.owner :: b.requires(oo,pivot)
  // requires forall oo <- o.owner :: a(oo,pivot) == b(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  a(oo,pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  b(oo,pivot) :: r )
{}

lemma COMBINE(o : Object, pivot : Object)
  requires o.Ready()
  requires forall oo <- o.owner ::
   && wasm.requires(oo,pivot)
   && walkStrictlyInside.requires(oo,pivot)
   && wasm(oo, pivot)  ==  walkStrictlyInside(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  wasm(oo, pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  walkStrictlyInside(oo, pivot) :: r )
{
  gefucked2(o, pivot, wasm, walkStrictlyInside);
}

lemma C0MBINE(o : Object, pivot : Object)
  requires o.Ready()
  requires forall oo <- o.owner ::
     wasm0(oo, pivot)  ==  walkStrictlyInside(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  wasm(oo, pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  walkStrictlyInside(oo, pivot) :: r )
{
  assert forall oo <- o.owner :: wasm0(oo, pivot)  ==  walkStrictlyInside(oo,pivot);
  gefucked(o, pivot, wasm0, walkStrictlyInside);
  assert
     ( set oo <- o.owner, r <-  wasm(oo, pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  walkStrictlyInside(oo, pivot) :: r );
}

lemma combine(o : Object, pivot : Object)
  requires o.Ready()
  requires forall oo <- o.owner ::
   wasm(oo, pivot)  ==  walkStrictlyInside(oo,pivot)
  ensures
   ( set oo <- o.owner, r <-  wasm(oo, pivot) :: r )
    ==
   ( set oo <- o.owner, r <-  walkStrictlyInside(oo, pivot) :: r )
{}

function walkOutsideOrPivot(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
   requires o.Ready()
      reads {}
    {
      (  if (outsideOrPivot(o,pivot)) then ({o}) else ({})  )
      +
      (  set xo <- o.owner, co <- walkOutsideOrPivot(xo, pivot) :: co  )
    }


// lemma REC_WALK_INSIDE_OUTSIDE(o : Object, pivot : Object)
//   decreases o.AMFO
//    requires o.Ready()
//    requires pivot.Ready()
//     ensures walkOwners(o,pivot) == walkStrictlyInside(o,pivot) + walkOutsideOrPivot(o,pivot)
// {
//    if (o.owner == {})
//     {
//       assert walkOwners(o,pivot) == {o};
//       if (strictlyInside(o,pivot))
//        {
//          assert walkStrictlyInside(o,pivot) == {o};
//          assert walkOutsideOrPivot(o,pivot) == {};
//          assert walkOwners(o,pivot) == walkStrictlyInside(o,pivot) + walkOutsideOrPivot(o,pivot);
//          return;
//        }
//       assert outsideOrPivot(o,pivot);
//
//          assert walkStrictlyInside(o,pivot) == {};
//          assert walkOutsideOrPivot(o,pivot) == {o};
//          assert walkOwners(o,pivot) == walkStrictlyInside(o,pivot) + walkOutsideOrPivot(o,pivot);
//          return;
//      }
//
//   //  forall oo <- o.owner
//   //    ensures (walkOwners(oo,pivot) == walkStrictlyInside(oo,pivot) + walkOutsideOrPivot(oo,pivot)) //by
//   //    {
//   //     REC_WALK_INSIDE_OUTSIDE(oo, pivot);
//   //     assert walkOwners(oo,pivot) == walkStrictlyInside(oo,pivot) + walkOutsideOrPivot(oo,pivot);
//   //    }
//
// var wo  : Owner := {}; //(set oo <- o.owner :: walkOwners(oo,pivot));
// var wsi : Owner := {}; //(set oo <- o.owner :: walkStrictlyInside(oo,pivot));
// var wop : Owner := {}; //(set oo <- o.owner :: walkOutsideOrPivot(oo,pivot));
//
//  var t := o.owner;
//  var d := {};
//   while t != {}
//     decreases t
//     invariant wo  == set oo <- d, ooo <- walkOwners(oo,pivot) :: ooo
//     invariant wsi == set oo <- d, ooo <- walkStrictlyInside(oo,pivot) :: ooo
//     invariant wop == set oo <- d, ooo <- walkOutsideOrPivot(oo,pivot) :: ooo
//     invariant wo  == wsi + wop
//     invariant o.owner  == t + d
//   {
//     var oo: Object;
//     oo :| oo in t;
//
//     t := t - {oo};
//
//     assert walkOwners(oo,pivot) == walkStrictlyInside(oo,pivot) + walkOutsideOrPivot(oo,pivot);
//
//     assert wo == set xo <- d, xoo <- walkOwners(xo,pivot) :: xoo;
//     assert (set xo <- d, xoo <- walkOwners(xo,pivot) :: xoo) + walkOwners(oo,pivot)
//         == (set xo <- d+{oo}, xoo <- walkOwners(xo,pivot) :: xoo);
//
//     assert wsi == set oo <- d, ooo <- walkStrictlyInside(oo,pivot) :: ooo;
//         assert (set xo <- d, xoo <- walkStrictlyInside(xo,pivot) :: xoo) + walkStrictlyInside(oo,pivot)
//         == (set xo <- d+{oo}, xoo <- walkStrictlyInside(xo,pivot) :: xoo);
//
//     assert wop == set oo <- d, ooo <- walkOutsideOrPivot(oo,pivot) :: ooo;
//     assert (set xo <- d, xoo <- walkOutsideOrPivot(xo,pivot) :: xoo) + walkOutsideOrPivot(oo,pivot)
//         == (set xo <- d+{oo}, xoo <- walkOutsideOrPivot(xo,pivot) :: xoo);
//
//     wo  := wo  + walkOwners(oo,pivot);
//     wsi := wsi + walkStrictlyInside(oo,pivot);
//     wop := wop + walkOutsideOrPivot(oo,pivot);
//
//     d := d + {oo};
//     assert wo  == set xo <- d, ooo <- walkOwners(xo,pivot) :: ooo;
//     assert wsi == set xo <- d, ooo <- walkStrictlyInside(xo,pivot) :: ooo;
//     assert wop == set xo <- d, ooo <- walkOutsideOrPivot(xo,pivot) :: ooo;
//
//     REC_WALK_INSIDE_OUTSIDE(oo, pivot);
//     assert wo == wsi + wop;
//
//   }
//
//
//
// assert t == {};
//
// assert d == o.owner;
//
//
//
//   // assert (set oo <- o.owner :: walkOwners(oo,pivot))
//   //      == (set oo <- o.owner :: walkStrictlyInside(oo,pivot))
//   //       + (set oo <- o.owner :: walkOutsideOrPivot(oo,pivot));
//
// // assert wo == wsi+wop;  COLLAPSE3(wo,wsi,wop);
// // assert collapse(wo) == collapse(wsi)+collapse(wop);
//
// assert walkOwners(o,pivot) == walkStrictlyInside(o,pivot) + walkOutsideOrPivot(o,pivot);
// }

//
// function skipOutsidePivotAndNotPivot(o : Object, pivot : Object) : (rv : (Owner, Owner))
//    decreases o.AMFO
//    requires o.Ready()
//    {
//      if (outside(o, pivot)) { assert pivot.AMFO <= rv)
//         then {}
//         else {}
// HERE HERE HERE HERE HERE
//         && (o == pivot)) then (recOwners(o))
//    }

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma SKIP_ALL_OUTSIDE_FROM_INSIDE_REACHES_PIVOT(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires inside(o,pivot)
   requires pivot in o.AMFO //hhmm
    ensures pivot.AMFO <= skipAllOutside'(o, pivot)
{
    WHOLE_ENCHILADA(o,pivot.AMFO);
    if (o == pivot) {
      assert pivot.AMFO <=  skipAllOutside'(o, pivot);
      return;
    }
    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
}

function skipAllOutside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures (o == pivot) || not(inside(o,pivot)) ==> (rv == o.AMFO)
    {
      if (not(strictlyInside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo)
    }

function skipAllOutside'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures (o == pivot) ==> (rv == pivot.AMFO)
    ensures not(inside(o,pivot)) ==> (rv == o.AMFO)
//see _LEMMA3 = rv >= pivot.AMFO
//    ensures not( strictlyInside(o,pivot) || (o == pivot) ) ==> (rv == o.AMFO)
    {
      STRICTLY_COME_INSIDE(o,pivot);

      if (o == pivot) then (pivot.AMFO) //==pivot.amfo
        else if (not(inside(o,pivot))) then (o.AMFO)
          else
           (assert strictlyInside(o,pivot);
           (set oo <- o.owner, ooo <- skipAllOutside'(oo, pivot) :: ooo))

      // if (not(strictlyInside(o,pivot))) then (o.AMFO)
      //     else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo)

    }


function skipAllInside(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(strictlyInside(o,pivot))) then ({})
          else  {o} + (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo)
    }

function skipOutsideOnlyPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures strictlyInside(o,pivot)                      ==> (rv == pivot.AMFO)
    ensures (o == pivot)                                 ==> (rv == pivot.AMFO)
    ensures (strictlyInside(o,pivot) || (o == pivot))    ==> (rv == pivot.AMFO)
//  ensures (inside(o,pivot))                            ==> (rv == pivot.AMFO)

    ensures not(strictlyInside(o,pivot) || (o == pivot)) ==> (rv == {})
 // ensures (outside(o,pivot))                           ==> (rv == {})

    ensures (if (strictlyInside(o,pivot) || (o == pivot)) then (rv == pivot.AMFO) else (rv == {}))
    ensures rv == if (strictlyInside(o,pivot) || (o == pivot)) then (pivot.AMFO) else ({})
 // ensures (if (inside(o,pivot)) then (rv == pivot.AMFO) else (rv == {}))
 // ensures rv == if (inside(o,pivot)) then (pivot.AMFO) else ({}))
    {
//      if (inside(o,pivot)) then (pivot.AMFO) else ({})
     if (strictlyInside(o,pivot)) then (pivot.AMFO)
      else if (o == pivot) then (pivot.AMFO)
        else ({})
    }

function skipOutsideOnlyPivot'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    ensures strictlyInside(o,pivot)                      ==> (rv == pivot.AMFO)
    ensures (o == pivot)                                 ==> (rv == pivot.AMFO)
    ensures (strictlyInside(o,pivot) || (o == pivot))    ==> (rv == pivot.AMFO)
//  ensures (inside(o,pivot))                            ==> (rv == pivot.AMFO)

    ensures not(strictlyInside(o,pivot) || (o == pivot)) ==> (rv == {})
 // ensures (outside(o,pivot))                           ==> (rv == {})

    ensures (if (strictlyInside(o,pivot) || (o == pivot)) then (rv == pivot.AMFO) else (rv == {}))
    ensures rv == if (strictlyInside(o,pivot) || (o == pivot)) then (pivot.AMFO) else ({})
 // ensures (if (inside(o,pivot)) then (rv == pivot.AMFO) else (rv == {}))
 // ensures rv == if (inside(o,pivot)) then (pivot.AMFO) else ({}))
    {
     if (o == pivot) then (pivot.AMFO)
      else if (strictlyInside(o,pivot)) then (pivot.AMFO)
        else ({})
    }

function skipOutsideExceptPivot(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (not(inside(o,pivot))) then (o.AMFO)
        else if (o == pivot) then ({})
          else (set oo <- o.owner, ooo <- skipOutsideExceptPivot(oo, pivot) :: ooo)
    }



function skipOutsideExceptPivot'(o : Object, pivot : Object) : (rv : set<Object>)
  decreases o.AMFO
   requires o.Ready()
    {
      if (o == pivot) then ({})
        else if (not(inside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- skipOutsideExceptPivot'(oo, pivot) :: ooo)
    }


function skipAllBoth(oo : Object, pivot : Object) : (rv : set<Object>)
  decreases oo.AMFO
   requires oo.Ready()
     { skipAllOutside(oo,pivot) + skipAllInside(oo,pivot) }

function amfoBinary(oo : Object, pivot : Object) : (rv : Owner)
  decreases oo.AMFO
   requires oo.Ready()
     { oo.AMFO }


function id(o : Object) : Object {o}
function rd(o : Object) : Object requires o.Ready() {o}


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //

lemma ANTI_TRUMP(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
//    requires strictlyInside(o,pivot)  --- org outside more likely?  - do we know any?
//    ensures skipAllOutside(o,pivot) == skipOutsideExceptPivot(o,pivot) + skipOutsideExceptPivot(o,pivot)
    {
      assert skipAllOutside(o,pivot) ==
        if (not(strictlyInside(o,pivot))) then (o.AMFO)
          else (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo);

      assert skipOutsideOnlyPivot(o, pivot) ==
          if (strictlyInside(o,pivot)) then (pivot.AMFO)
            else if (o == pivot) then (pivot.AMFO)
              else ({});


      assert skipOutsideExceptPivot(o, pivot) ==
          ( if (not(inside(o,pivot))) then (o.AMFO)
              else if (o == pivot) then ({})
                else (set oo <- o.owner, ooo <- skipOutsideExceptPivot(oo, pivot) :: ooo) );

    }



lemma skipOutsideOnlyPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipOutsideOnlyPivot(o,pivot) == skipOutsideOnlyPivot'(o,pivot)
{}

lemma skipOutsideExceptPivot_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipOutsideExceptPivot(o,pivot) == skipOutsideExceptPivot'(o,pivot)
{
//   if (o == pivot) {
//     assert skipOutsideExceptPivot(o,pivot)  == ;
//     assert skipOutsideExceptPivot(o,pivot)' == ;
//
//     assert skipOutsideExceptPivot(o,pivot) == skipOutsideExceptPivot'(o,pivot);
//     return;
}

lemma skipAllOutside_LEMMA0(o : Object, pivot : Object)
 //version equals prime
   decreases o.AMFO
    requires o.Ready()
     ensures skipAllOutside(o,pivot) == skipAllOutside'(o,pivot)
{
    if (o == pivot) {
      assert skipAllOutside(o,pivot)  == o.AMFO;
      assert skipAllOutside'(o,pivot) == o.AMFO;
      assert skipAllOutside(o,pivot) == skipAllOutside'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);
      assert skipAllOutside(o,pivot)  == o.AMFO;
      assert skipAllOutside'(o,pivot) == o.AMFO;
      assert skipAllOutside(o,pivot) == skipAllOutside'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
}

lemma skipAllOutside_LEMMA1(o : Object, pivot : Object)
  //includes outside except pivot
   decreases o.AMFO
    requires o.Ready()
     ensures skipAllOutside'(o,pivot) >= skipOutsideExceptPivot'(o,pivot)
{}

lemma skipAllOutside_LEMMA2(o : Object, pivot : Object)  //broken
//includes outside only pivot
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()
     ensures skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot)
{
    if (o == pivot) {
      assert skipAllOutside'(o,pivot)  == o.AMFO;
      assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
      return;
    }
    if (not(strictlyInside(o,pivot))) {
      STRICTLY_COME_INSIDE(o,pivot);    // isn't this FUCKED??
      assert skipAllOutside'(o,pivot)  == o.AMFO;
      assert skipOutsideOnlyPivot'(o,pivot) == {};
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
      return;
    }

    assert strictlyInside(o,pivot);
    assert o.AMFO >= pivot.AMFO;
    assert pivot.Ready();
    assert pivot in pivot.AMFO;
    assert pivot in o.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      skipAllOutside_LEMMA3(o,pivot,skipAllOutside'(o,pivot));
      // assert skipAllOutside'(o,pivot)  == (set oo <- o.owner, ooo <- skipAllOutside'(oo, pivot) :: ooo);
      assert skipAllOutside'(o,pivot)  >= pivot.AMFO;
      STRICTLY_COME_INSIDE(o,pivot);
      assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
      assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot); //ERR
}



lemma skipAllOutside_LEMMA3(o : Object, pivot : Object, rv : Owner)
//skipAllOutside prime alqays inclues pivot...
   decreases o.AMFO
    requires o.Ready()
    requires pivot in o.AMFO
    requires rv == skipAllOutside'(o,pivot)
     ensures rv >= pivot.AMFO
   {
    STRICTLY_COME_INSIDE(o,pivot);
    WHOLE_ENCHILADA(o,pivot.AMFO);   //I don't expect to do this routinely...
    WHOLE_READY(o,pivot);

      if (o == pivot) {
        assert skipAllOutside'(o,pivot)  == pivot.AMFO;
        assert skipOutsideOnlyPivot'(o,pivot) == pivot.AMFO;
        assert skipAllOutside'(o,pivot) >= skipOutsideOnlyPivot'(o,pivot);
        return;
      }

    assert (inside(o,pivot) && (o != pivot)) ==> strictlyInside(o,pivot);
    assert strictlyInside(o,pivot);

    ThereIsALightThatNeverGoesOut(o,pivot);
    var next := YouCan'tGetThereFromHereBut(o,pivot);
    var nrv := skipAllOutside'(next,pivot);
    skipAllOutside_LEMMA3(next,pivot,nrv);
//
//       var po : Owner := (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  );
//       var no : Owner := (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  );
//
//       var rec : set<(Owner, Owner)> :=
//          (  set xo <- o.owner :: walkOutsidePivotAndNotPivot(xo, pivot)  );
//
//       compress(po,no,rec);
    }


// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //


lemma skipAllBoth_LEMMA0(soup : set<Object>,  pivot : Object) // left0 : set<Object>, left1 : set<Object>, right : set<Object>)
 //establishes skipAllBoth == skipAllInside + skipAllOutside based solely on definitions
 //then 'upscales' that to sets etc

  requires forall o <- soup :: o.Ready()

   ensures forall o <- soup :: skipAllBoth(o,pivot) == skipAllInside(o, pivot) + skipAllOutside(o, pivot)

   ensures forall o <- soup :: skipAllBoth(o,pivot) >= skipAllInside(o, pivot)
   ensures forall o <- soup :: skipAllBoth(o,pivot) >= skipAllOutside(o, pivot)

   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) ::  oo in (skipAllInside(o, pivot) +         skipAllOutside(o, pivot))
   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) :: (oo in skipAllInside(o, pivot)) || (oo in skipAllOutside(o, pivot))
//LUXON   ensures forall o <- soup, oo <- skipAllBoth(o,pivot) :: (oo in skipAllInside(o, pivot)) != (oo in skipAllOutside(o, pivot))

   ensures (set o <- soup, oo <- skipAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- (skipAllInside(o, pivot) + skipAllOutside(o, pivot)) :: oo)
   ensures (set o <- soup, oo <- skipAllBoth(o,pivot) :: oo) == (set o <- soup, oo <- skipAllInside(o, pivot) :: oo) + (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo)

  //  ensures  ((set o <- soup, oo <- skipAllInside(o, pivot) :: oo) + (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo))
  //         == (set o <- soup, oo <- amfoBinary(o, pivot) :: oo)

   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in skipAllInside(oo, pivot)) || (ooo in skipAllOutside(oo,pivot))
   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)))
   ensures forall oo <- soup, ooo <- skipAllBoth(oo,pivot) :: (ooo in (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)))
  {}



lemma letsDoIt(soup : set<Object>,  pivot : Object, left0 : set<Object>, left1 : set<Object>, right : set<Object>)
  requires AllReady(soup)
   ensures forall o <- soup :: o.Ready()
   ensures forall o <- soup :: id(o).Ready()
   ensures forall o <- soup :: rd(o).Ready()
  requires forall o <- soup :: o.Ready()
  requires forall o <- soup :: id(o).Ready()
  requires forall o <- soup :: rd(o).Ready()
  requires (left0 + left1) == right
  requires left0 == (set o <- soup, oo <-  skipAllInside(o, pivot) :: oo)
  requires left1 == (set o <- soup, oo <- skipAllOutside(o, pivot) :: oo)
  requires right == (set o <- soup, oo <-    skipAllBoth(o, pivot) :: oo)
   ensures left0 + left1 == right
  {
    //  assert forall o <- soup :: o.Ready();
    //  forall (o <- soup) ensures (o.Ready())
    //   {
    //     o.ExtraReady(); 4trrr
    //   }
  }


lemma skipAllBoth_LEMMA1(seed : Object,  pivot : Object, left0 : set<Object>, left1 : set<Object>, right : set<Object>)
  requires seed.Ready()
  requires left0 == (set o <- seed.owner, oo <-  skipAllInside(o, pivot) :: oo)
  requires left1 == (set o <- seed.owner, oo <- skipAllOutside(o, pivot) :: oo)
  requires right == (set o <- seed.owner, oo <-    skipAllBoth(o, pivot) :: oo)
//LUXON
// ensures left0 + left1 == right  //Err
  {
    assert AllReady(seed.owner);
//  assert forall o <- seed.owner :: skipAllInside(o, pivot)  !! skipAllOutside(o, pivot);
    assert forall o <- seed.owner :: skipAllInside(o, pivot)  <= skipAllBoth(o, pivot);
    assert forall o <- seed.owner :: skipAllOutside(o, pivot) <= skipAllBoth(o, pivot);
  }

lemma BLANCHE(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: amfoBinary(oo,pivot) == skipAllBoth(oo,pivot)
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
    //  requires forall oo <- o.owner :: (set ooo <- oo.AMFO :: ooo) == (set ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
    //   ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)

{
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    // assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
  //  forall oo <- o.owner ensures (skipAllBoth(oo,pivot) == amfoBinary(oo,pivot)) { gefucked(o,pivot,skipAllBoth,amfoBinary); }
}

lemma LANCHIN(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: oo.AMFO              == (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot))
     ensures forall oo <- o.owner :: amfoBinary(oo,pivot) == skipAllBoth(oo,pivot)
{
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    // assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // forall oo <- o.owner ensures
}

lemma LANCHOUT(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
//   ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo)              == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)\
{
    assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
    // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
    assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
    // assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT1(o : Object, pivot : Object)  //WORKS!!
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO
     ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo)
{
//     assert forall oo <- o.owner ::  amfoBinary(oo,pivot) == oo.AMFO;
//     assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
//     assert (set oo <- o.owner, ooo <- amfoBinary(oo,pivot)  :: ooo) == (set oo <- o.owner, ooo <- oo.AMFO :: ooo);
//     assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT2(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)
     ensures (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
{
      gefucked2(o, pivot, skipAllBoth, (x,y)=> (skipAllOutside(x,y) + skipAllInside(x,y)) );
      // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
      // assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma NCHOUT3(o : Object, pivot : Object, left0 : Owner, left1 : Owner, right : Owner)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot) //WHY? - cos if nothing's strictlyInside the pivot, who gives a FUCK
    requires left0 == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo)
    requires left1 == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo)
    requires right == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
    // requires forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) >= (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) <= (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot)) :: ooo) + (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot)) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
{
    assert left0 + left1 >= right;
    assert right == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
    assert forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
    assert right == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: ooo);
    assert forall oo <- o.owner :: skipAllInside(oo,pivot) <= skipAllInside(oo,pivot) + skipAllOutside(oo,pivot);
assert    forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
assert    forall oo <- o.owner, ooo <-  skipAllInside(oo,pivot) :: ooo in right;
assert    forall oo <- o.owner, ooo <-  skipAllInside(oo,pivot) + skipAllOutside(oo,pivot) :: ooo in right;


    assert left0         <= right;
    assert         left1 <= right;
    assert left0 + left1 <= right;

//      gefucked2(o, pivot, skipAllBoth, (x,y)=> (skipAllOutside(x,y) + skipAllInside(x,y)) );
      // assert forall oo <- o.owner :: skipAllBoth(oo,pivot) == skipAllOutside(oo,pivot) + skipAllInside(oo,pivot);
      // assert (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
}

lemma skipAllBoth_LEMMA2(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
{

///WORKS -->
assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllOutside(oo,pivot)) :: y);

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- skipAllOutside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- skipAllInside(oo,pivot)  :: y) );

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (
               (set oo <- o.owner, y <- skipAllInside(oo,pivot) :: y)
             + (set oo <- o.owner, y <- skipAllOutside(oo,pivot)  :: y) );

assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in skipAllBoth(oo,pivot);

////DOESNT WORK:

//LUXON
// assert forall oo <- o.owner, x <- skipAllBoth(oo,pivot) ::
//          x in ((set oo <- o.owner, y <- skipAllInside(oo,pivot) :: y)
//              + (set oo <- o.owner, y <- skipAllOutside(oo,pivot):: y));
//LUXON
// assert forall oo <- o.owner, x <- skipAllBoth(oo,pivot) ::
//          (x in (set oo <- o.owner, y <- skipAllInside(oo,pivot)  :: y))
//       != (x in (set oo <- o.owner, y <- skipAllOutside(oo,pivot) :: y));
//
//LUXON
// assert forall oo <- o.owner :: skipAllInside(oo,pivot) !! skipAllOutside(oo,pivot);

////DOESNT WORK:

//    var right := (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);

// assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: y);
// assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in (set oo <- o.owner, y <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: y);

    // assert forall oo <- o.owner, x <- skipAllOutside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- skipAllInside(oo,pivot) :: x in right;
    // assert forall oo <- o.owner, x <- right :: (x in skipAllOutside(oo,pivot)) || (x in skipAllInside(oo,pivot));

    // assert right == (set oo <- o.owner, ooo <- (skipAllInside(oo,pivot) + skipAllOutside(oo,pivot)) :: ooo);
    // assert forall oo <- o.owner, ooo <- skipAllOutside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner, ooo <- skipAllInside(oo,pivot) :: ooo in right;
    // assert forall oo <- o.owner :: skipAllInside(oo,pivot) <= skipAllInside(oo,pivot) + skipAllOutside(oo,pivot);
}

lemma ANCHE(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires strictlyInside(o,pivot)
    requires forall oo <- o.owner :: oo.AMFO == (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot))
    // requires forall oo <- o.owner :: amfoBinary(oo,pivot) == skipAllBoth(oo,pivot)
    //  ensures (set oo <- o.owner, ooo <- amfoBinary(oo,pivot) :: ooo) == (set oo <- o.owner, ooo <- skipAllBoth(oo,pivot) :: ooo)
   // requires forall oo <- o.owner :: (set ooo <- oo.AMFO :: ooo) == (set ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)
     ensures (set oo <- o.owner, ooo <- oo.AMFO :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo)

{
    LANCHIN(o,pivot);
    BLANCHE(o,pivot);
    LANCHOUT(o,pivot);
}



lemma INSIDE_OUTSIDE2(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()

     ensures skipAllOutside(o,pivot) + skipAllInside(o,pivot) == o.AMFO
{
  ANCHE(o,pivot);
}


lemma INSIDE_OUTSIDE(o : Object, pivot : Object)
   decreases o.AMFO
    requires o.Ready()
    requires pivot.Ready()

     ensures skipAllOutside(o,pivot) + skipAllInside(o,pivot) == o.AMFO
{
  if (not(strictlyInside(o,pivot)))
    {
      assert skipAllOutside(o, pivot) == o.AMFO;
      assert skipAllInside(o, pivot) == {};
      assert o.AMFO + {} == o.AMFO;
      assert skipAllOutside(o,pivot) + skipAllInside(o,pivot) == o.AMFO;
      return;
    }

assert (strictlyInside(o,pivot));

assert forall oo <- o.owner :: skipAllOutside(oo,pivot) + skipAllInside(oo,pivot) == oo.AMFO;

assert forall oo <- o.owner :: (set ooo <- oo.AMFO :: ooo) == (set ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);
BLANCHE(o,pivot);
assert (set oo <- o.owner, ooo <- oo.AMFO :: ooo) == (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);

assert o.AMFO == {o} + (set oo <- o.owner, ooo <- oo.AMFO :: ooo);

assert o.AMFO == {o} + (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);

      // assert skipAllOutside(o, pivot) == o.AMFO;
      // assert skipAllInside(o, pivot) == {};
      // assert o.AMFO + {} == o.AMFO;
      // assert skipAllOutside(o,pivot) + skipAllInside(o,pivot) == o.AMFO;


// umm  assert o.AMFO == {o} + (set oo <- o.owner, ooo <- (skipAllOutside(oo,pivot) + skipAllInside(oo,pivot)) :: ooo);


// assert skipAllOutside(o, pivot) == (set oo <- o.owner, ooo <- skipAllOutside(oo, pivot) :: ooo);
// assert skipAllInside(o, pivot) == {o} + (set oo <- o.owner, ooo <- skipAllInside(oo, pivot) :: ooo);
// assert skipAllOutside(o,pivot) + skipAllInside(o,pivot) == o.AMFO;


///HERW HERE HERW HERE HERW HERE HERW HERE HERW HERE HERW HERE HERW HERE HERW HERE HERW HERE
}

// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // // //




lemma REC_WALK_INSIDE(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures walkStrictlyInside(o,pivot) == recOwnersInside(o,pivot)
{
   if (o.owner == {})
    {
      if (strictlyInside(o,pivot))
       {
         assert walkStrictlyInside(o,pivot) == {o};
         assert recOwnersInside(o,pivot) == {o};
         assert walkStrictlyInside(o,pivot) == recOwnersInside(o,pivot);
         return;
       }
      assert outsideOrPivot(o,pivot);

         assert walkStrictlyInside(o,pivot) == {};
         assert recOwnersInside(o,pivot) == {};
         assert walkStrictlyInside(o,pivot) == recOwnersInside(o,pivot);
         return;
     }


   forall oo <- o.owner
     ensures (walkStrictlyInside(oo,pivot) == recOwnersInside(oo,pivot)) //by
     {
      REC_WALK_INSIDE(oo, pivot);
      assert walkStrictlyInside(oo,pivot) == recOwnersInside(oo,pivot);
     }

var wsi := (set oo <- o.owner :: walkStrictlyInside(oo,pivot));
var roi := (set oo <- o.owner :: recOwnersInside(oo,pivot));

  assert (set oo <- o.owner :: walkStrictlyInside(oo,pivot))
       == (set oo <- o.owner :: recOwnersInside(oo,pivot));

assert wsi == roi;  COLLAPSE(wsi,roi);
assert collapse(wsi) == collapse(roi);

}







function walkPivot(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
   requires o.Ready()
    {
      (  if (o == pivot) then (recOwners(pivot)) else ({})  )
      +
      (  set xo <- o.owner, co <- walkPivot(xo, pivot) :: co  )
    }

function walkOutsidePivot(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
   requires o.Ready()
    {
      (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  )
      +
      (  set xo <- o.owner, co <- walkPivot(xo, pivot) :: co  )
    }

function walkOutsideNotPivot(o : Object, pivot : Object) : (rv : Owner)
  decreases o.AMFO
    ensures o.AMFO >= rv
   requires o.Ready()
    {
      (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  )
      +
      (  set xo <- o.owner, co <- walkOutsideNotPivot(xo, pivot) :: co  )
    }



function walkOutsidePivotAndNotPivot(o : Object, pivot : Object) : (rv : (Owner, Owner))
  decreases o.AMFO
   requires o.Ready()
    // ensures rv.0 == walkOutsidePivot(o, pivot)
    // ensures rv.1 == walkOutsideNotPivot(o, pivot)
    // ensures rv.0 + rv.1 == walkOutsideOrPivot(o, pivot)
    {
      var po : Owner := (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  );
      var no : Owner := (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  );

      var rec : set<(Owner, Owner)> :=
         (  set xo <- o.owner :: walkOutsidePivotAndNotPivot(xo, pivot)  );

      compress(po,no,rec)
    }



/////

lemma WALK_OUTSIDE_PIVOT_AND_NOT_PIVOT(o : Object, pivot : Object, rv : (Owner, Owner))
    decreases o.AMFO
   requires o.Ready()
   requires rv == walkOutsidePivotAndNotPivot(o, pivot)
    ensures rv.0 == walkOutsidePivot(o, pivot)
    ensures rv.1 == walkOutsideNotPivot(o, pivot)
    ensures rv.0 + rv.1 == recOwners(o)
   {
      var po : Owner := {};
      var no : Owner := {};

      po := (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  );
      no := (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  );

      if (outside(o, pivot)) { assert po + no == recOwners(o); }

      if (outside(o, pivot) && (o == pivot)) {
        assert walkOutsidePivot(o, pivot) == po;
      }

      if (outside(o, pivot) && (o != pivot)) {
        assert walkOutsideNotPivot(o, pivot) >= no;
      }

      var rec : set<(Owner, Owner)> :=
         (  set xo <- o.owner :: walkOutsidePivotAndNotPivot(xo, pivot)  );

     forall xo <- o.owner ensures (true) {
         var rrv :=  walkOutsidePivotAndNotPivot(xo, pivot);
         WALK_OUTSIDE_PIVOT_AND_NOT_PIVOT(xo, pivot, rrv);
         assert rrv.0 == walkOutsidePivot(xo, pivot);
         assert rrv.1 == walkOutsideNotPivot(xo, pivot);
         assert rrv.0 + rrv.1 == recOwners(xo);
        }

     assert rv ==  compress(po,no,rec);

     assert rv.0 == walkOutsidePivot(o, pivot);
     assert rv.1 == walkOutsideNotPivot(o, pivot);
     assert rv.0 + rv.1 == recOwners(o);
   }

//
// lemma WALK_OUTSIDE_PIVOT_AND_NOT_PIVOT(o : Object, pivot : Object, rv : (Owner, Owner))
//     decreases o.AMFO
//    requires o.Ready()
//    requires rv == walkOutsidePivotAndNotPivot(o, pivot)
//     ensures rv.0 == walkOutsidePivot(o, pivot)
//     ensures rv.1 == walkOutsideNotPivot(o, pivot)
//     ensures rv.0 + rv.1 == recOwners(o)
//    {
//       var po : Owner := {};
//       var no : Owner := {};
//
//       po := (  if (outside(o, pivot) && (o == pivot)) then (recOwners(o)) else ({})  );
//       no := (  if (outside(o, pivot) && (o != pivot)) then (recOwners(o)) else ({})  );
//
//       if (outside(o, pivot)) { assert po + no == recOwners(o); }
//
//       if (outside(o, pivot) && (o == pivot)) {
//         assert walkOutsidePivot(o, pivot) == po;
//       }
//
//       if (outside(o, pivot) && (o != pivot)) {
//         assert walkOutsideNotPivot(o, pivot) >= no;
//       }
//
//       var rec : set<(Owner, Owner)> :=
//          (  set xo <- o.owner :: walkOutsidePivotAndNotPivot(xo, pivot)  );
//
//      forall xo <- o.owner ensures (true) {
//          var rrv :=  walkOutsidePivotAndNotPivot(xo, pivot);
//          WALK_OUTSIDE_PIVOT_AND_NOT_PIVOT(xo, pivot, rrv);
//          assert rrv.0 == walkOutsidePivot(xo, pivot);
//          assert rrv.1 == walkOutsideNotPivot(xo, pivot);
//          assert rrv.0 + rrv.1 == recOwners(xo);
//         }
//
//      assert rv ==  compress(po,no,rec);
//
//      assert rv.0 == walkOutsidePivot(o, pivot);
//      assert rv.1 == walkOutsideNotPivot(o, pivot);
//      assert rv.0 + rv.1 == recOwners(o);
//
//     }



lemma WALK_PIVOT_OUTSIDE_PIVOT(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
    ensures walkOutsidePivot(o,pivot) == walkPivot(o,pivot)
    {
      assert (o == pivot) <==> ((outside(o, pivot) && (o == pivot)));
    }


lemma WALK_REC_PIVOT(o : Object, pivot : Object)
   decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures walkPivot(o,pivot) == recOwnersPivot(o,pivot)
{
  if (o.owner == {})
   {
     if (o == pivot)
      {
        assert inside(o,pivot);
        assert recOwnersPivot(o,pivot) == recOwners(pivot);
        assert walkPivot(o, pivot)     == recOwners(pivot);
        return;
      }
     if (o != pivot)
      {
        assert not(inside(o,pivot));
        assert recOwnersPivot(o,pivot) == {};
        assert walkPivot(o, pivot)     == {};
        return;
      }
   }

   forall oo <- o.owner
     ensures (recOwnersPivot(oo,pivot) == walkPivot(oo,pivot)) //by
     {
      WALK_REC_PIVOT(oo, pivot);
      assert recOwnersPivot(oo,pivot) == walkPivot(oo,pivot);
     }



assert (set oo <- o.owner :: recOwnersPivot(oo,pivot))
       == (set oo <- o.owner :: walkPivot(oo,pivot));

// assert (set oo <- o.owner, ooo <- recOwnersPivot(oo,pivot) :: ooo)
//     == (set oo <- o.owner, ooo <- walkPivot(oo,pivot) :: ooo);

assert recOwnersPivot(o,pivot) == walkPivot(o,pivot);
}





lemma RecBelow_AllInside(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
    // ensures recBelow(o,pivot) == allInside(o.AMFO, pivot)
    // ensures recBelow(o,pivot) == allInside(recOwners(o), pivot)
{
  ////HERE
}


lemma precessionOfOwners(o : Object, pivot : Object)
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()
    ensures (o == pivot)     ==> forall oo <- o.owner :: outside(oo,pivot)
    ensures outside(o,pivot) ==> forall oo <- o.owner :: outside(oo,pivot)
    ensures strictlyInside(o,pivot)  ==> forall oo <- o.owner :: inside(oo,pivot) || outside(oo,pivot)
    ensures forall oo <- o.owner ::  inside(oo,pivot) <==> (strictlyInside(oo,pivot) || (oo == pivot))
    ensures strictlyInside(o,pivot)  ==> forall oo <- o.owner :: strictlyInside(oo,pivot) || (oo == pivot) || outside(oo,pivot)
    ensures strictlyInside(o,pivot)  ==> forall oo <- o.owner | outside(oo,pivot) && outside(pivot,oo) :: offside(oo,pivot)
{
  forall oo <- o.owner ensures (inside(oo,pivot) <==> (strictlyInside(oo,pivot) || (oo == pivot)))  //by
    { STRICTLY_COME_INSIDE(oo,pivot); }
}

function collapse(a : set<Owner>) : set<Object>
 {set oo <- a, o <- oo :: o}


lemma COLLAPSE(a : set<Owner>, b : set<Owner>)
   requires a == b
    ensures collapse(a) == collapse(b)
    ensures flatten(collapse(a)) == flatten(collapse(b))
{}


lemma COLLAPSE3(a : set<Owner>, b : set<Owner>, c : set<Owner>)
   requires a == b + c
    ensures collapse(a) == collapse(b) + collapse(c)
    ensures flatten(collapse(a)) == flatten(collapse(b)) + flatten(collapse(c))
{}

function compress(a : Owner, b : Owner, cc : set<(Owner,Owner)>) : (Owner, Owner)
  {
    var ra := a + (set c <- cc, z <- c.0 :: z );
    var rb := b + (set c <- cc, z <- c.1 :: z );
    (ra,rb)
  }