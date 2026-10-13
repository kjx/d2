include "Ownership.dfy"






lemma klon3StrictlyInsideObject(o : Object, pivot : Object) returns (rv : set<Object>)
  decreases o.AMFO, 12
   requires o.Ready()
   requires pivot.Ready()
    ensures rv == collectStrictlyInsideObject(o, pivot)
    { rv := {};
      if strictlyInside(o,pivot) {
        var klect := klon3StrictlyInside(o.owner,pivot);
        rv := {o} + klect;
      }
    }

lemma klon3StrictlyInside(soup : Owner, pivot : Object) returns (rv : set<Object>)
  decreases allAMFOs(soup), 22
   requires pivot.Ready()
    ensures rv == collectStrictlyInside(soup, pivot)
    {  assert pivot.Ready();  assert KCLD: pivot.Ready();
       assume forall o <- soup :: o.Ready();  //  && m.m[o].Ready();
       rv := {};
      var done := {};
      assert collectStrictlyInside(done, pivot) == rv;
      var todo := soup;
      while todo > {}
        decreases todo
        invariant forall o <- soup :: o.Ready()  // && m.m[o].Ready()
        invariant done <= soup
        invariant collectStrictlyInside(done, pivot) == rv
        invariant soup == (todo + done)
        invariant todo !! done
      {
        assert soup >= todo > {};
        todo, done, rv := klon3LOOPY_LOOP(soup, todo, done, rv, pivot)  by { DOWNY_DOWN_DOWN(soup,todo,15); }
        assert (collectStrictlyInside(done, pivot) == rv) by { DOWNY_DOWN_DOWN(soup,todo,20); }
     }
      assert done == soup;
      assert collectStrictlyInside(soup, pivot) == rv;
       }



lemma klon3LOOPY_LOOP(soup : Owner, todo' : Owner, done' : Owner, rv' : Owner, pivot : Object)
                      returns (todo : Owner,  done : Owner,  rv : Owner)
  decreases allAMFOs(todo'), 15
   requires todo' > {}
   requires todo' !! done'
   requires forall o <- soup :: o.Ready() // && m.m[o].Ready()
   requires done' <= soup
   requires collectStrictlyInside(done', pivot) == rv'
   requires soup == (todo' + done')
   requires pivot.Ready()
   ensures done <= soup
   ensures collectStrictlyInside(done, pivot) == rv
   ensures soup == (todo + done)
   ensures todo !! done
   ensures todo < todo'
      {
        assert soup == (todo' + done');
        todo := todo';
        done := done';
        assert soup == (todo + done);
        rv := rv';
        var y :| y in todo';
        assert y in todo'; assert y in soup;
        DOWNY_DOWN(todo',y);
        var ksio := klon3StrictlyInsideObject(y,pivot);
        assert ksio == collectStrictlyInsideObject(y,pivot);
        assert collectStrictlyInside(done, pivot) == rv;
        KLONECT_ONE_MORE(done,y,rv,ksio,pivot);
        assert collectStrictlyInside(done+{y}, pivot) == rv+ksio;
        assert soup == (todo' + done');
        rv := rv + ksio;
        todo, done := UPPY_UPP(soup, y, todo', done') by
           {
            assert allAMFOs(todo') == allAMFOs(todo');
            assert allAMFOs(todo') nonincreases to allAMFOs(todo');
            assert 15 > 5;
            assert 15 decreases to 5;
            assert (allAMFOs(todo'), 15 decreases to allAMFOs(todo'), 5 );
           }

        assert collectStrictlyInside(done, pivot) == rv;
      }






// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //




lemma klon2StrictlyInsideObject(o : Object, m : Klon) returns (rv_o : Owner, rv_c : Owner)
  decreases o.AMFO, 12
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
//    ensures (rv_o, rv_c) == tandemCollectStrictlyInsideObject(o, m)
    ensures rv_o == collectStrictlyInsideObject(o, m.o)
    ensures rv_c == collectStrictlyInsideObject(m.m[o], m.c)
    { rv_o := {}; rv_c := {};
      if strictlyInside(o,m.o) {
        assert strictlyInside(m.m[o],m.c);
        var owner_o, owner_c := klon2StrictlyInside(o.owner,m);
        rv_o := {o} + owner_o;
        rv_c := {m.m[o]} + owner_c;
//        assert (rv_o, rv_c) == tandemCollectStrictlyInsideObject(o, m);
        assert rv_o == collectStrictlyInsideObject(o, m.o);
        assert rv_c == collectStrictlyInsideObject(m.m[o], m.c);
      }
    }


function tandemCollectStrictlyInsideObject(o : Object, m : Klon) : (rr : (Owner, Owner))
  decreases o.AMFO, 11
   requires klonCalid(m)
  //  requires o.Ready()
   requires m.objectInKlon(o)
  //  requires m.m[o].Ready()
    ensures rr.0 == collectStrictlyInsideObject(o, m.o)
    ensures rr.1 == collectStrictlyInsideObject(m.m[o], m.c)
      reads m.hns()
 { assume o.Ready() && m.m[o].Ready();
    (collectStrictlyInsideObject(o, m.o), collectStrictlyInsideObject(m.m[o], m.c))
 }


lemma klon2StrictlyInside(soup : Owner, m : Klon) returns (rv_o : Owner, rv_c : Owner)
  decreases allAMFOs(soup), 22
   requires m.allInKlon(soup)
   requires klonCalid(m)
    ensures rv_o == collectStrictlyInside(soup, m.o)
    ensures rv_c == collectStrictlyInside(mapThruKlon(soup,m), m.c)
    {  assert klonCalid(m);  assert KCLD: klonCalid(m);
       assume forall o <- soup :: o.Ready() && m.m[o].Ready();
       rv_o := {}; rv_c := {};
      var done := {};
      assert collectStrictlyInside(done, m.o) == rv_o;
      assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
      var todo := soup;
      while todo > {}
        decreases todo
        invariant forall o <- soup :: o.Ready() && m.m[o].Ready()
        invariant done <= soup
        invariant collectStrictlyInside(done, m.o) == rv_o
        invariant collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c
        invariant soup == (todo + done)
        invariant todo !! done
      {
        assert soup >= todo > {};
        todo, done, rv_o, rv_c := LOOPY2LOOP(soup, todo, done, rv_o, rv_c, m)  by { DOWNY_DOWN_DOWN(soup,todo,15); }
        assert (collectStrictlyInside(done, m.o) == rv_o) by { DOWNY_DOWN_DOWN(soup,todo,20); }
        assert (collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c) by { DOWNY_DOWN_DOWN(soup,todo,20); }
     }
      assert done == soup;
      assert collectStrictlyInside(soup, m.o) == rv_o;
      assert collectStrictlyInside(mapThruKlon(soup,m), m.c) == rv_c;
       }

lemma LOOPY2LOOP(soup : Owner, todo' : Owner, done' : Owner, rv'o : Owner, rv'c : Owner, m: Klon)
                      returns (todo : Owner,  done : Owner,  rv_o : Owner, rv_c : Owner)
  decreases allAMFOs(todo'), 15
   requires todo' > {}
   requires todo' !! done'
   requires forall o <- soup :: o.Ready() && m.m[o].Ready()
   requires done' <= soup
   requires m.allInKlon(soup)
   requires collectStrictlyInside(done', m.o) == rv'o
   requires collectStrictlyInside(mapThruKlon(done',m), m.c) == rv'c
   requires soup == (todo' + done')
   requires klonCalid(m)
   ensures done <= soup
   ensures collectStrictlyInside(done, m.o) == rv_o
   ensures collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c
   ensures soup == (todo + done)
   ensures todo !! done
   ensures todo < todo'
      {
        assert soup == (todo' + done');
        todo := todo';
        done := done';
        assert soup == (todo + done);
        rv_o, rv_c := rv'o, rv'c;
        var y :| y in todo';
        assert y in todo'; assert y in soup;
        DOWNY_DOWN(todo',y);
        var rv_oo_o, rv_oo_c := klon2StrictlyInsideObject(y,m);
        assert rv_oo_o == collectStrictlyInsideObject(y,m.o);
        assert rv_oo_c == collectStrictlyInsideObject(m.m[y],m.c);
        assert collectStrictlyInside(done, m.o) == rv_o;
        assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
        KLONECT_ONE_MORE(done,y,rv_o,rv_oo_o,m.o);
        assert collectStrictlyInside(done+{y}, m.o) == rv_o+rv_oo_o;
        KLONECT_ONE_MORE(done,m.m[y],rv_c,rv_oo_c,m.c);
        assert collectStrictlyInside(mapThruKlon(done,m)+{m.m[y]}, m.c) == rv_c+rv_oo_c;
        assert soup == (todo' + done');
        rv_o := rv_o + rv_oo_o;
        rv_c := rv_c + rv_oo_c;
        todo := todo' - {y};
        done := done' + {y};
        // todo, done := UPPY_UPP(soup, y, todo', done') by
        //    {
        //     assert allAMFOs(todo') == allAMFOs(todo');
        //     assert allAMFOs(todo') nonincreases to allAMFOs(todo');
        //     assert 15 > 5;
        //     assert 15 decreases to 5;
        //     assert (allAMFOs(todo'), 15 decreases to allAMFOs(todo'), 5 );
        //    }
        assert collectStrictlyInside(done, m.o) == rv_o;
        assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
      }





























lemma klon222StrictlyInsideObject(o : Object, m : Klon) returns (rv_o : Owner, rv_c : Owner)
  decreases o.AMFO, 12
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
//    ensures (rv_o, rv_c) == tandemCollectStrictlyInsideObject(o, m)
    ensures rv_o == collectStrictlyInsideObject(o, m.o)
//    ensures rv_c == collectStrictlyInsideObject(m.m[o], m.c)
    { rv_o := {}; rv_c := {};
      if strictlyInside(o,m.o) {
        assert strictlyInside(m.m[o],m.c);
        var owner_o, owner_c := klon222StrictlyInside(o.owner,m);
        rv_o := {o} + owner_o;
//      rv_c := {m.m[o]} + owner_c;
//        assert (rv_o, rv_c) == tandemCollectStrictlyInsideObject(o, m);
        assert rv_o == collectStrictlyInsideObject(o, m.o);
//        assert rv_c == collectStrictlyInsideObject(m.m[o], m.c);
      }
    }
lemma klon222StrictlyInside(soup : Owner, m : Klon) returns (rv_o : Owner, rv_c : Owner)
  decreases allAMFOs(soup), 22
   requires m.allInKlon(soup)
   requires klonCalid(m)
    ensures rv_o == collectStrictlyInside(soup, m.o)
//    ensures rv_c == collectStrictlyInside(mapThruKlon(soup,m), m.c)
    {  assert klonCalid(m);  assert KCLD: klonCalid(m);
       assume forall o <- soup :: o.Ready() && m.m[o].Ready();
       rv_o := {}; rv_c := {};
      var done := {};
      assert collectStrictlyInside(done, m.o) == rv_o;
//      assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
      var todo := soup;
      while todo > {}
        decreases todo
        invariant forall o <- soup :: o.Ready() && m.m[o].Ready()
        invariant done <= soup
        invariant collectStrictlyInside(done, m.o) == rv_o
//      invariant collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c
        invariant soup == (todo + done)
        invariant todo !! done
      {
        assert soup >= todo > {};
        todo, done, rv_o, rv_c := LOOPY222LOOP(soup, todo, done, rv_o, rv_c, m)  by { DOWNY_DOWN_DOWN(soup,todo,15); }
        assert (collectStrictlyInside(done, m.o) == rv_o) by { DOWNY_DOWN_DOWN(soup,todo,20); }
//        assert (collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c) by { DOWNY_DOWN_DOWN(soup,todo,20); }
     }
      assert done == soup;
      assert collectStrictlyInside(soup, m.o) == rv_o;
//      assert collectStrictlyInside(mapThruKlon(soup,m), m.c) == rv_c;
       }
lemma LOOPY222LOOP(soup : Owner, todo' : Owner, done' : Owner, rv'o : Owner, rv'c : Owner, m: Klon)
                      returns (todo : Owner,  done : Owner,  rv_o : Owner, rv_c : Owner)
  decreases allAMFOs(todo'), 15
   requires todo' > {}
   requires todo' !! done'
   requires forall o <- soup :: o.Ready() ///&& m.m[o].Ready()   //HMMN KJX
   requires done' <= soup
   requires m.allInKlon(soup)
   requires collectStrictlyInside(done', m.o) == rv'o
//   requires collectStrictlyInside(mapThruKlon(done',m), m.c) == rv'c
   requires soup == (todo' + done')
   requires klonCalid(m)
   ensures done <= soup
   ensures collectStrictlyInside(done, m.o) == rv_o
//   ensures collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c
   ensures soup == (todo + done)
   ensures todo !! done
   ensures todo < todo'
      {
        assume forall o <- soup :: o.Ready() && m.m[o].Ready();
        assert soup == (todo' + done');
        todo := todo';
        done := done';
        assert soup == (todo + done);
        rv_o, rv_c := rv'o, rv'c;
        var y :| y in todo';
        assert y in todo'; assert y in soup;
        DOWNY_DOWN(todo',y);
        var rv_oo_o, rv_oo_c := klon222StrictlyInsideObject(y,m);
        assert rv_oo_o == collectStrictlyInsideObject(y,m.o);
//        assert rv_oo_c == collectStrictlyInsideObject(m.m[y],m.c);
        assert collectStrictlyInside(done, m.o) == rv_o;
//        assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
        KLONECT_ONE_MORE(done,y,rv_o,rv_oo_o,m.o);
        assert collectStrictlyInside(done+{y}, m.o) == rv_o+rv_oo_o;
//      KLONECT_ONE_MORE(done,m.m[y],rv_c,rv_oo_c,m.c);
//      assert collectStrictlyInside(mapThruKlon(done,m)+{m.m[y]}, m.c) == rv_c+rv_oo_c;
        assert soup == (todo' + done');
        rv_o := rv_o + rv_oo_o;
        // rv_c := rv_c + rv_oo_c;
        // todo := todo' - {y};
        // done := done' + {y};
        todo, done := UPPY_UPP(soup, y, todo', done') by
           {
            assert allAMFOs(todo') == allAMFOs(todo');
            assert allAMFOs(todo') nonincreases to allAMFOs(todo');
            assert 15 > 5;
            assert 15 decreases to 5;
            assert (allAMFOs(todo'), 15 decreases to allAMFOs(todo'), 5 );
           }
        assert collectStrictlyInside(done, m.o) == rv_o;
//        assert collectStrictlyInside(mapThruKlon(done,m), m.c) == rv_c;
      }








// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //






lemma klonectStrictlyInsideObject(o : Object, m : Klon) returns (rv : set<Object>)
  decreases o.AMFO, 12
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
    ensures rv == collectStrictlyInsideObject(o, m.o)
    { rv := {};
      if strictlyInside(o,m.o) {
        var klect := klonectStrictlyInside(o.owner,m);
        rv := {o} + klect;
      }
    }

lemma klonectStrictlyInside(soup : Owner, m : Klon) returns (rv : set<Object>)
  decreases allAMFOs(soup), 22
   requires m.allInKlon(soup)
   requires klonCalid(m)
    ensures rv == collectStrictlyInside(soup, m.o)
    {  assert klonCalid(m);  assert KCLD: klonCalid(m);
       assume forall o <- soup :: o.Ready();
       rv := {};
      var done := {};
      assert collectStrictlyInside(done, m.o) == rv;
      var todo := soup;
      while todo > {}
        decreases todo
        invariant forall o <- soup :: o.Ready()
        invariant done <= soup
        invariant collectStrictlyInside(done, m.o) == rv
        invariant soup == (todo + done)
        invariant todo !! done
      {
        assert soup >= todo > {};
        todo, done, rv := LOOPY_LOOP(soup, todo, done, rv, m)  by { DOWNY_DOWN_DOWN(soup,todo,15); }
        assert (collectStrictlyInside(done, m.o) == rv) by { DOWNY_DOWN_DOWN(soup,todo,20); }
     }
      assert done == soup;
      assert collectStrictlyInside(soup, m.o) == rv;
       }



lemma LOOPY_LOOP(soup : Owner, todo' : Owner, done' : Owner, rv' : Owner, m: Klon)
                      returns (todo : Owner,  done : Owner,  rv : Owner)
  decreases allAMFOs(todo'), 15
   requires todo' > {}
   requires todo' !! done'
   requires forall o <- soup :: o.Ready()
   requires done' <= soup
   requires collectStrictlyInside(done', m.o) == rv'
   requires soup == (todo' + done')
   requires m.allInKlon(soup)
   requires klonCalid(m)
   ensures done <= soup
   ensures collectStrictlyInside(done, m.o) == rv
   ensures soup == (todo + done)
   ensures todo !! done
   ensures todo < todo'
      {
        assert soup == (todo' + done');
        todo := todo';
        done := done';
        assert soup == (todo + done);
        rv := rv';
        var y :| y in todo';
        assert y in todo'; assert y in soup;
        DOWNY_DOWN(todo',y);
        var ksio := klonectStrictlyInsideObject(y,m);
        assert ksio == collectStrictlyInsideObject(y,m.o);
        assert collectStrictlyInside(done, m.o) == rv;
        KLONECT_ONE_MORE(done,y,rv,ksio,m.o);
        assert collectStrictlyInside(done+{y}, m.o) == rv+ksio;
        assert soup == (todo' + done');
        rv := rv + ksio;
        todo, done := UPPY_UPP(soup, y, todo', done') by
           {
            assert allAMFOs(todo') == allAMFOs(todo');
            assert allAMFOs(todo') nonincreases to allAMFOs(todo');
            assert 15 > 5;
            assert 15 decreases to 5;
            assert (allAMFOs(todo'), 15 decreases to allAMFOs(todo'), 5 );
           }

        assert collectStrictlyInside(done, m.o) == rv;
      }




// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //














lemma KLONECT_ONE_MORE(done : Owner, y : Object, rv : Owner, ksio : Owner, pivot : Object)
   requires forall o <- done :: o.Ready()
   requires y.Ready()
   requires rv   == collectStrictlyInside(done, pivot)
   requires ksio == collectStrictlyInsideObject(y, pivot)
    ensures collectStrictlyInside(done+{y}, pivot) == rv+ksio
{}


lemma GOING_DOWN(oo : Owner, o : Object)
    requires oo > {}
    requires o in oo
     ensures allAMFOs(oo) >= o.AMFO
     ensures allAMFOs(oo) nonincreases to o.AMFO
     ensures 15 decreases to 14
     ensures (allAMFOs(oo), 15 decreases to o.AMFO, 14)
{}

lemma DOWNY_DOWN(todo : Owner, y : Object)
    requires todo > {}
    requires y in todo
     ensures allAMFOs(todo) >= y.AMFO
     ensures allAMFOs(todo) nonincreases to y.AMFO
     ensures 22 decreases to 12
     ensures (allAMFOs(todo), 22 decreases to y.AMFO, 12)
{}

lemma DOWNY_DOWN_DOWN(soup : Owner, todo : Owner, other : nat)
    requires soup >= todo
    requires other < 22

     ensures allAMFOs(soup) >= allAMFOs(todo)
     ensures allAMFOs(soup) nonincreases to allAMFOs(todo)
     ensures 22 >= other
     ensures 22 decreases to other
     ensures (allAMFOs(soup), 22 decreases to allAMFOs(todo), other)
{}


lemma UPPY_UPP(soup : Owner, y : Object, todo' : Owner, done' : Owner)
      returns (todo : Owner, done : Owner)
    decreases allAMFOs(todo'), 5
    requires soup > {}
    requires y in soup
    requires y in todo'
    requires todo' !! done'
    requires soup == todo' + done'

     ensures todo == todo' - {y}
     ensures done == done' + {y}
     ensures todo !! done
     ensures soup == todo + done
     ensures todo <  todo'
{
  todo := todo' - {y};
  done := done' + {y};
}







































lemma P_K_Inside(oo : Object, ob : Object, co : Object, cb : Object, m : Klon)
 //if oo >= ob then clonews co >= cb
 //currently requires inside, but should generalse nicely I think! non urgent.
 decreases oo.AMFO
  requires klonReady(m)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo.Ready() && ob.Ready() && co.Ready() && cb.Ready()

  requires strictlyInside(co,m.o)
  requires strictlyInside(cb,m.o)

  requires oo in m.m.Keys
  requires ob in m.m.Keys
  requires klonLine(oo,co,m)
  requires klonLine(ob,cb,m)
  requires m.m[oo] == co
//  requires m.m[ob] == cb

   ensures m.m[ob] == cb
   ensures inside(oo,ob)
  requires inside(co,cb)
{}




lemma K_P_Inside(oo : Object, ob : Object, co : Object, cb : Object, m : Klon)
 //if oo >= ob then clonews co >= cb
 //currently requires inside, but should generalse nicely I think! non urgent.
 decreases oo.AMFO
  requires klonReady(m)
  requires klonPivot(m)
  requires klonAllLines(m)
  requires oo.Ready() && ob.Ready() && co.Ready() && cb.Ready()

  requires strictlyInside(oo,m.o)
  requires strictlyInside(ob,m.o)

  requires oo in m.m.Keys
  requires ob in m.m.Keys
  requires klonLine(oo,co,m)
  requires klonLine(ob,cb,m)
  requires m.m[oo] == co
  requires m.m[ob] == cb

  requires inside(oo,ob)
   ensures inside(co,cb)
{
forall o <- m.m.Keys | strictlyInside(o,m.o) ensures(m.m[o].owner == mapThruKlon(o.owner,m)) {
  assert klonLine(o,m.m[o],m);
  assert klonGeometry(o,m.m[o],m);
  assert klonIdentity(o,m.m[o],m);
  assert m.m[o].owner == mapThruKlon(o.owner,m);
  }

if (oo == ob) { assert co == cb; assert inside(co,cb); return; }

ThereIsALightThatNeverGoesOut(oo,ob);
var next :=  YouCan'tGetThereFromHereBut(oo,ob);
assert next in oo.owner;
assert inside(oo, next);
assert inside(next,ob);

if (next == ob) {
  assert ob in oo.owner;
  assert co.owner == mapThruKlon(oo.owner,m);
  assert cb in co.owner;
  assert inside(co,cb);
  return;
}

assert strictlyInside(ob,m.o);
assert strictlyInside(next,m.o);

//
var mext := m.m[next];

assert co.owner == mapThruKlon(oo.owner,m);
assert mext in co.owner;


K_P_Inside(next,ob,mext,cb,m);

assert inside(co,cb);
}






predicate splitCalidOK(os_sp : FlownerSplit, cs_sp : FlownerSplit, m : Klon) : (rv : bool)
  ensures rv ==> (AllReady(os_sp.fAll) && AllReady(cs_sp.fAll))
    reads m.hns()
    {
   && AllReady(os_sp.soup)
   && AllReady(cs_sp.soup)
   && klonCalid(m)
   && flownerSplitOK(os_sp.soup, m.o,os_sp)
   && flownerSplitOK(cs_sp.soup, m.c,cs_sp)
    }





lemma TRUMPY_TRUMPFY(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

//    ensures forall v <- cs_sp.fSin :: (exists k <- os_sp.fSin :: m.m[k] == v)
   {
    DRACULA_DRACULA(os,os_sp,cs,cs_sp,m);
    assert forall k <- os_sp.fSin :: (m.m[k] in cs_sp.fSin);


  flownerStrictlyInside_RESULT(os_sp.soup,os_sp.pivot,os_sp.fSin);
      assert forall o <- os_sp.fAll | strictlyInside(o,os_sp.pivot) :: o in os_sp.fSin;
      assert forall o <- os_sp.fSin :: o in os_sp.fAll;
      assert forall o <- os_sp.fSin :: strictlyInside(o,os_sp.pivot);
      assert forall o <- os_sp.fSin :: exists s <- os_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(os_sp.soup,os_sp.pivot);  ownerStrictlyInside(s,os_sp.pivot,o));

  flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);
      assert forall o <- cs_sp.fAll | strictlyInside(o,cs_sp.pivot) :: o in cs_sp.fSin;
      assert forall o <- cs_sp.fSin :: o in cs_sp.fAll;
      assert forall o <- cs_sp.fSin :: strictlyInside(o,cs_sp.pivot);
      assert forall o <- cs_sp.fSin :: exists s <- cs_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(cs_sp.soup,cs_sp.pivot);  ownerStrictlyInside(s,cs_sp.pivot,o));


    assert forall k <- os_sp.fSin :: exists v <- cs_sp.fSin :: m.m[k] == v;
    assert forall k <- os_sp.fSin :: (m.m[k] in cs_sp.fSin) && klonLine(k, m.m[k], m);
    assert os_sp.fAll <= m.m.Keys;

//ERR    assert cs_sp.fAll <= m.m.Values;
//ERR    assert forall v <- cs_sp.fSin :: exists k <- os_sp.fSin :: m.m[k] == v;
//ERR    assert forall v <- cs_sp.fSin :: (var k :| k in os_sp.fSin && (m.m[k] == v); klonLine(k, m.m[k], m) );
   }




lemma ZOMBIE_ZOMBIE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures forall v <- cs_sp.fSin :: (exists k <- os_sp.fSin :: m.m[k] == v)
   {
      forall v <- cs_sp.fSin ensures (true) {        //  forall v <- cs_sp.fSin ensures (exists k <- os_sp.fSin :: m.m[k] == v) {

          assert exists t <- cs_sp.soup :: v in t.AMFO;
          var t :| t in cs_sp.soup && v in t.AMFO;
          transitiveStrictlyInside(t,v,cs_sp.pivot);

          var s :| s in os_sp.soup && (m.m[s] == t);
          assert m.objectInKlon(s);
          m.UPSCALE_KLONISHMENT({s});
          assert exists k <- s.AMFO :: (m.m[k] == v);



          var k :| k in s.AMFO &&  (m.m[k] == v);  //    (inside(s,k) && strictlyInside(k,m.o))

        }

   }


lemma DRACULA_DRACULA(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)

    ensures forall k <- os_sp.fSin :: (m.m[k] in cs_sp.fSin)
  {
    forall k <- os_sp.fSin ensures (m.m[k] in cs_sp.fSin) {

      assert strictlyInside(k,m.o);
      var v := m.m[k];
      assert klonLine(k,v,m);

      assert exists s <- os_sp.soup :: inside(s,k);
      var s :| s in os_sp.soup && inside(s,k);
      transitiveStrictlyInside(s,k,os_sp.pivot);
      assert cs_sp.soup == mapThruKlon(os_sp.soup,m);
      var t :| t in cs_sp.soup && (m.m[s] == t);

      K_P_Inside(s,k,t,v,m);

      assert v in cs_sp.fSin;
    }
  }















// lemma {:timeLimit 10} MASTERY_THRU(oo : Owner, m : Klon)
//   decreases allAMFOs(oo), 15
//    requires klonCalid(m)
//    requires m.allInKlon(oo)
//    requires AllReady(oo)
//    requires AllReady(mapThruKlon(oo,m))
//    requires collectStrictlyInside(oo,m.o) <= m.m.Keys
//
//     ensures mapThruKlon(collectStrictlyInside(oo,m.o),m) == collectStrictlyInside(mapThruKlon(oo,m),m.c)

lemma FNARG(os : Owner, m : Klon)
   requires klonCalid(m)
   requires os <= m.m.Keys
    ensures collectStrictlyInside(os,m.o) <= m.m.Keys
{}

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

{
  assert collectStrictlyInside(os,m.o) <= m.m.Keys;

  assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,m.o);
  assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,m.c);

  assert os_sp.fSin == flownerStrictlyInside(os,m.o);
  assert cs_sp.fSin == flownerStrictlyInside(mapThruKlon(os,m),m.c);

FLOWNER_ALL_COLLECT_StrictlyInside(os_sp.soup,m.o);
assert collectStrictlyInside(os_sp.soup,m.o) == flownerStrictlyInside(os_sp.soup,m.o) == os_sp.fSin;
FLOWNER_ALL_COLLECT_StrictlyInside(cs_sp.soup,m.c);
assert collectStrictlyInside(cs_sp.soup,m.c) == flownerStrictlyInside(cs_sp.soup,m.c) == cs_sp.fSin;

MASTERY_THRU(os_sp.soup,m);

 assert mapThruKlon(collectStrictlyInside(os,m.o),m) == collectStrictlyInside(mapThruKlon(os,m),m.c);
 assert mapThruKlon(os_sp.fSin, m) == mapThruKlon(collectStrictlyInside(os,m.o),m);
 assert cs_sp.fSin == flownerStrictlyInside(mapThruKlon(os,m),m.c);
 assert mapThruKlon(os_sp.fSin, m) == cs_sp.fSin;

//HERE! //HERE //HERE
}



//{:timeLimit 60}
lemma  FLOWNER_ALL_COLLECT_StrictlyInside(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
   ensures flownerStrictlyInside(soup,pivot) <= flownerAll(soup)
   ensures allStrictlyInside(flatten(soup),pivot) == flownerStrictlyInside(soup,pivot)
   ensures allStrictlyInside(flownerAll(soup),pivot) == flownerStrictlyInside(soup,pivot)

   ensures collectStrictlyInside(soup,pivot) == flownerStrictlyInside(soup,pivot)
{

 forall o <- soup
    ensures (flownerStrictlyInside({o},pivot) == collectStrictlyInsideObject(o, pivot)) //by
    { collectStrictlyInsideObject_LEMMA1z_noall(o,pivot); }

 assert forall o <- soup :: collectStrictlyInsideObject(o,pivot) <= collectStrictlyInside(soup,pivot);


 assert forall o <- collectStrictlyInside(soup,pivot) ::
    exists s <- soup :: o in s.AMFO;
 assert forall o <- collectStrictlyInside(soup,pivot) ::
    exists s <- soup :: o in collectStrictlyInsideObject(s,pivot);
//  assert forall o <- collectStrictlyInside(soup,pivot) ::
//     o in (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss);

}


///the magic lines?
// assert forall oo <- soup :: (set ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- (set x <- collectStrictlyInside({oo},pivot)) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
//

// ///the magic lines?
// assert forall oo <- soup :: (set ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- (set x <- collectStrictlyInside({oo},pivot)) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);

  //  assert collectStrictlyInside(soup,pivot) == flownerStrictlyInside(soup,pivot);


lemma LETS_BE_SUBSET(less : Owner, more : Owner)
  requires forall o <- less :: o in more
   ensures less <= more
{}

lemma IS_FUCKED(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
//   ensures collectStrictlyInside(soup,pivot) == (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
 {
    IS2FUCKED(soup,pivot);
//    assert forall o <- collectStrictlyInside(soup,pivot) :: o in (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss);
//    IS0FUCKED(soup,pivot);
    IS1FUCKED(soup,pivot);
 }

lemma IS0FUCKED(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
  requires forall o <- collectStrictlyInside(soup,pivot) :: o in (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss)
//   ensures collectStrictlyInside(soup,pivot) <=                  (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
//   ensures collectStrictlyInside(soup,pivot) >= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
//   ensures collectStrictlyInside(soup,pivot) == (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
{
  IS2FUCKED(soup,pivot);
  LETS_BE_SUBSET(collectStrictlyInside(soup,pivot), (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss));
}

lemma IS1FUCKED(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
//   ensures collectStrictlyInside(soup,pivot) <= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
   ensures collectStrictlyInside(soup,pivot) >= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
//   ensures collectStrictlyInside(soup,pivot) == (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
{}


lemma IS2FUCKED(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
  //  ensures forall o <- collectStrictlyInside(soup,pivot) :: exists s <- soup :: o in s.AMFO
  //  ensures forall o <- collectStrictlyInside(soup,pivot) :: exists s <- soup :: o in collectStrictlyInsideObject(s,pivot)
  //  ensures forall o <- collectStrictlyInside(soup,pivot) :: o in (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss)
//   ensures collectStrictlyInside(soup,pivot) <= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
{
   assert forall o <- collectStrictlyInside(soup,pivot) :: exists s <- soup :: o in s.AMFO;
   assert forall o <- collectStrictlyInside(soup,pivot) :: exists s <- soup :: o in collectStrictlyInsideObject(s,pivot);
   // assert forall o <- collectStrictlyInside(soup,pivot) :: o in (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss);

 var less := collectStrictlyInside(soup,pivot);
 var more := (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss);
 assert forall o <- less :: o in more;
 LETS_BE_SUBSET(less, more);
//    LETS_BE_SUBSET(collectStrictlyInside(soup,pivot), (set s <- soup, ss <- collectStrictlyInsideObject(s,pivot) :: ss));
  //  assert collectStrictlyInside(soup,pivot) <= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo);
}

lemma IS3FUCKED(soup : OWNR, pivot : Object)
  requires AllReady(flatten(soup)) && pivot.Ready()
//   ensures collectStrictlyInside(soup,pivot) <= (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
   ensures forall o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo in collectStrictlyInside(soup,pivot)
//   ensures collectStrictlyInside(soup,pivot) == (set o <- soup, oo <- collectStrictlyInsideObject(o,pivot) :: oo)
{}



lemma collectStrictlyInsideObject_LEMMA1z_noall(o : Object, pivot : Object)
  //if I'm inside I should be in collectStrictlyInsideObject
  //given this one, why do I need all the other shit I'm doing
  //to prove shit?
  //see eg  argh_LEMMA13_noall
  decreases o.AMFO
   requires o.Ready()
   requires pivot.Ready()

    ensures allStrictlyInside(o.AMFO,pivot) <= collectStrictlyInsideObject(o,pivot)
    ensures allStrictlyInside(o.AMFO,pivot) >= collectStrictlyInsideObject(o,pivot)
    ensures allStrictlyInside(o.AMFO,pivot) == collectStrictlyInsideObject(o,pivot)

    ensures allStrictlyInside(o.AMFO,pivot) <= flownerStrictlyInside({o},pivot)
    ensures allStrictlyInside(o.AMFO,pivot) >= flownerStrictlyInside({o},pivot)
    ensures allStrictlyInside(o.AMFO,pivot) == flownerStrictlyInside({o},pivot)

    ensures flownerStrictlyInside({o},pivot) <= collectStrictlyInsideObject(o,pivot)
    ensures flownerStrictlyInside({o},pivot) >= collectStrictlyInsideObject(o,pivot)
    ensures flownerStrictlyInside({o},pivot) == collectStrictlyInsideObject(o,pivot)

   {
    forall oo <- o.AMFO | strictlyInside(oo,pivot) ensures ( oo in collectStrictlyInsideObject(o,pivot) )  {
       assert o.Ready();
       assert oo in o.AMFO;
       assert strictlyInside(oo,pivot);
       collectStrictlyInsideObject_LEMMA1o_noall(o,pivot,oo);
       assert oo in collectStrictlyInsideObject(o,pivot);
      }

   forall  oo <- collectStrictlyInsideObject(o,pivot) ensures (oo in allStrictlyInside(o.AMFO,pivot)) {
      assert o.Ready();
      assume oo.Ready();
      assert oo in o.AMFO;
      assert strictlyInside(oo,pivot);
      assert oo in allStrictlyInside(o.AMFO,pivot);

      collectStrictlyInsideObject_LEMMA1o_noall(o,pivot,oo);
      // assert oo in collectStrictlyInsideObject(o,pivot);

      }

    }



lemma collectStrictlyInsideObject_LEMMA1o_noall(o : Object, pivot : Object, x : Object)
  //if x is inside x should be in collectStrictlyInsideObject
  decreases o.AMFO
   requires o.Ready()
   requires x in o.AMFO
   requires strictlyInside(x,pivot)
    ensures x in collectStrictlyInsideObject(o, pivot)
   {
      if (x == o) {assert x in collectStrictlyInsideObject(o, pivot); return;}
      assert x != o;
      assert exists oo <- o.owner, xx <- oo.AMFO :: x == xx;
      assert exists oo <- o.owner :: x in collectStrictlyInsideObject(oo, pivot);
    }


















lemma orig_MxPPING_xNSIDE(os : Owner, os_sp : FlownerSplit, cs : Owner, cs_sp : FlownerSplit, m : Klon)
   requires AllReady(os_sp.fAll)
   requires AllReady(cs_sp.fAll)
   requires klonCalid(m)

   requires os <= m.m.Keys
   requires cs == mapThruKlon(os,m)
   requires flownerSplitOK(os, m.o,os_sp)
   requires flownerSplitOK(cs, m.c,cs_sp)
//   requires forall o <- os_sp.fSin :: strictlyInside(o, m.o)


//ensures mapThruKlon(os_sp.fSin, m) == cs_sp.fSin

  //love this beautiful symmetrical formulation
    // ensures forall o <- os_sp.fSin :: exists r <- cs_sp.fSin :: m.m[o] == r
    // ensures forall r <- cs_sp.fSin :: exists o <- os_sp.fSin :: m.m[o] == r
{
      assert os_sp.fSin == flownerStrictlyInside(os_sp.soup,os_sp.pivot);
      assert cs_sp.fSin == flownerStrictlyInside(cs_sp.soup,cs_sp.pivot);

  flownerStrictlyInside_RESULT(os_sp.soup,os_sp.pivot,os_sp.fSin);
      assert forall o <- os_sp.fAll | strictlyInside(o,os_sp.pivot) :: o in os_sp.fSin;
      assert forall o <- os_sp.fSin :: o in os_sp.fAll;
      assert forall o <- os_sp.fSin :: strictlyInside(o,os_sp.pivot);
      assert forall o <- os_sp.fSin :: exists s <- os_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(os_sp.soup,os_sp.pivot);  ownerStrictlyInside(s,os_sp.pivot,o));

  flownerStrictlyInside_RESULT(cs_sp.soup,cs_sp.pivot,cs_sp.fSin);
      assert forall o <- cs_sp.fAll | strictlyInside(o,cs_sp.pivot) :: o in cs_sp.fSin;
      assert forall o <- cs_sp.fSin :: o in cs_sp.fAll;
      assert forall o <- cs_sp.fSin :: strictlyInside(o,cs_sp.pivot);
      assert forall o <- cs_sp.fSin :: exists s <- cs_sp.soup | o in s.AMFO :: (PART_INSIDE_OWNER(cs_sp.soup,cs_sp.pivot);  ownerStrictlyInside(s,cs_sp.pivot,o));

  forall k <- os_sp.fSin ensures (m.m[k] in cs_sp.fSin) {

      assert strictlyInside(k,m.o);
      var v := m.m[k];
      assert klonLine(k,v,m);

      assert exists s <- os_sp.soup :: inside(s,k);
      var s :| s in os_sp.soup && inside(s,k);
      transitiveStrictlyInside(s,k,os_sp.pivot);
      assert cs_sp.soup == mapThruKlon(os_sp.soup,m);
      var t :| t in cs_sp.soup && (m.m[s] == t);

      K_P_Inside(s,k,t,v,m);

      assert v in cs_sp.fSin;
   }
assert os_sp.fSin <= m.m.Keys;          // assert forall o <- os_sp.fSin ::

  forall v <- cs_sp.fSin ensures (true) {

//  forall v <- cs_sp.fSin ensures (exists k <- os_sp.fSin :: m.m[k] == v) {

      assert exists t <- cs_sp.soup :: v in t.AMFO;
      var t :| t in cs_sp.soup && v in t.AMFO;
      transitiveStrictlyInside(t,v,cs_sp.pivot);

      var s :| s in os_sp.soup && (m.m[s] == t);
//
//       forall x <- t.AMFO ensures ( strictlyInside(x,cs_sp.pivot) <==> (x in cs_sp.fSin) )
//         {
//           assert strictlyInside(x,cs_sp.pivot)  ==> (x in cs_sp.fSin);
//           assert strictlyInside(x,cs_sp.pivot) <==  (x in cs_sp.fSin);
//           BOOLEAN_SPOOLEAN( strictlyInside(x,cs_sp.pivot) , (x in cs_sp.fSin) );
//           assume strictlyInside(x,cs_sp.pivot) <==> (x in cs_sp.fSin);   ///cos assert doesnt work,
//        }
//
//
//       forall y <- s.AMFO ensures ( strictlyInside(y,os_sp.pivot) <==> (y in os_sp.fSin) )
//         {
//           assert strictlyInside(y,os_sp.pivot)  ==> (y in os_sp.fSin);
//           assert strictlyInside(y,os_sp.pivot) <==  (y in os_sp.fSin);
//           BOOLEAN_SPOOLEAN( strictlyInside(y,os_sp.pivot) , (y in os_sp.fSin) );
//           assume strictlyInside(y,os_sp.pivot) <==> (y in os_sp.fSin);   ///cos assert doesnt work,
//        }
//


      assert m.objectInKlon(s);
      m.UPSCALE_KLONISHMENT({s});
      assert exists k <- s.AMFO :: (m.m[k] == v);
      var k :| k in s.AMFO &&  (m.m[k] == v);  //    (inside(s,k) && strictlyInside(k,m.o))


      // assert forall x <- os_sp.soup :: (x in m.m.Keys) && (exists y : Object :: m.m[x] == y);

//
//       assert s in m.m.Keys; assert t in m.m.Values;
//       assert os_sp.fAll == flatten(os) <= m.m.Keys;
// //      var k :| k in m.m.Keys && (m.m[k] == v);




  }



  assert mapThruKlon(os_sp.fSin, m) <= cs_sp.fSin;
  assert mapThruKlon(os_sp.fSin, m) >= cs_sp.fSin;
  }


lemma BOOLEAN_SPOOLEAN(a : bool, b : bool)
  requires a  ==> b
  requires a <==  b
   ensures a <==> b
{}






























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
    predicate {:timeLimit 60} Valid() {
      assume AllReady(flatten(soup));
      assume pivot.Ready();
    //  && AllReady(flatten(soup))   //should do better than that…
    //  && pivot.Ready() //…ditto
     && (fAll == flownerAll(soup) == flatten(soup))
     && (fSin == flownerStrictlyInside(soup,pivot))
     && (fOut == flownerStrictlyOutside(soup,pivot))
     && (fPvt == flownerOnlyPivot(soup,pivot))
     && (fXpt == flownerExceptPivot(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerEverythingOutside(soup,pivot))
     && ((fOut + fPvt + fXpt) == flownerPivotlyOutside(soup,pivot))
     && (fAll == fSin + fOut + fPvt + fXpt)

     && fSin !! (fOut + fPvt + fXpt)
    }
  }




predicate flownerSplitOK(soup : OWNR, pivot : Object, split : FlownerSplit)
 // requires AllReady(soup) && pivot.Ready()
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
  {}



































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
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && exceptPivot(o,pivot,owner)}
predicate ownerOutsidePivot(o : Object, pivot : Object, owner : Object) : (rv : bool)
  requires o.Ready() && pivot.Ready() && owner.Ready()  requires inside(o, owner)  reads {}
    {pivotlyOutside(owner,pivot) && outsidePivot(o,owner,pivot)}




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
  //yes same as flatten() etc...

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









lemma flownerStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 //verfies!!!
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires flownerStrictlyInside(soup,pivot) == rv
   ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv
   ensures forall r <- rv :: r in flatten(soup)
   ensures forall r <- rv :: strictlyInside(r,pivot)
   ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
          (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{}


lemma {:timeLimit 30} collectStrictlyInside_RESULT(soup : Owner, pivot : Object, rv : Owner)
 decreases allAMFOs(soup)
  requires AllReady(flatten(soup)) && pivot.Ready() && AllReady(flatten(rv))
  requires collectStrictlyInside(soup,pivot) == rv
   //ensures forall r <- flatten(soup) | strictlyInside(r,pivot) :: r in rv //err
   ensures forall r <- rv :: r in flatten(soup)
  ensures forall r <- rv :: strictlyInside(r,pivot)  //err
  //  ensures forall owner <- rv :: exists o <- soup | owner in o.AMFO ::
  //         (PART_INSIDE_OWNER(soup,pivot);  ownerStrictlyInside(o,pivot,owner))
{
  if (soup == {}) {return;}

  forall oo <- soup ensures (true) {
    var rs := collectStrictlyInsideObject(oo, pivot);
    assert (oo in rs) ==> strictlyInside(oo,pivot);
    collectStrictlyInside_RESULT(oo.owner,pivot, collectStrictlyInside(oo.owner,pivot) );
   assert rs == if (strictlyInside(oo,pivot)) then {oo} + collectStrictlyInside(oo.owner, pivot) else {};
   assert forall r <- rs :: strictlyInside(r,pivot);
    assert rs <= flatten(soup);
  }
}


function collectStrictlyInsideObject(o : Object, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases o.AMFO, 1
   requires o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in o.AMFO
    { if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }


function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
///version from BROWNE
  decreases allAMFOs(soup), 2
   requires forall o <- soup :: o.Ready()
    ensures forall r <- rv :: strictlyInside(r,pivot)
    ensures forall r <- rv :: r in flatten(soup)
    { (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }


//
// function collectStrictlyInsideObject(o : Object, pivot : Object) : (rv : set<Object>)
//   decreases o.AMFO, 10
// //   requires o.Ready()
//    ensures rv <= o.AMFO
//     { assume o.Ready(); if (not(strictlyInside(o,pivot))) then ({}) else ({o}+collectStrictlyInside(o.owner,pivot)) }
//
//
// function collectStrictlyInside(soup : Owner, pivot : Object) : (rv : set<Object>)
//   // requires forall o <- soup :: o.Ready()
//       decreases allAMFOs(soup), 20
//         ensures rv <= flatten(soup)
//     { assume forall o <- soup :: o.Ready(); (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }
//


function rorschach(soup : Owner, pivot : Object) : (rv : set<Object>)
    decreases allAMFOs(soup), 20
    { (set o <- soup, ooo <- collectStrictlyInsideObject(o,pivot) :: ooo) }




lemma {:timeLimit 20} MASTERY_OBJECT(o : Object, m : Klon)
  decreases o.AMFO, 14
   requires o.Ready()
   requires klonCalid(m)
   requires m.objectInKlon(o)
   requires collectStrictlyInsideObject(o,m.o) <= m.m.Keys

    ensures mapThruKlon(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c)
{
   var c  := m.m[o];
   var mc := mapThruKlon(collectStrictlyInsideObject(o,m.o),m);
   var cm := collectStrictlyInsideObject(c,m.c);

  if (not(strictlyInside(o,m.o)))
    {
      assert (not(strictlyInside(c,m.c)));
      assert collectStrictlyInsideObject(o,m.o) == {};
      assert mapThruKlon(collectStrictlyInsideObject(o,m.o),m) == {};
      assert collectStrictlyInsideObject(c,m.c) == {};
      assert {} == mc == cm;
      return;
    }

  assert (strictlyInside(o,m.o));
  assert (strictlyInside(c,m.c));

  assert collectStrictlyInsideObject(o,m.o) == {o} + collectStrictlyInside(o.owner,m.o)
      by {
        assert collectStrictlyInsideObject(o,m.o) == (if (not(strictlyInside(o,m.o))) then ({}) else ({o}+collectStrictlyInside(o.owner,m.o)));
        assert (strictlyInside(o,m.o));
        assert collectStrictlyInsideObject(o,m.o) == {o} + collectStrictlyInside(o.owner,m.o);
      }

  assert collectStrictlyInsideObject(c,m.c) == {c} + collectStrictlyInside(c.owner,m.c);
  assert cm == {c} + collectStrictlyInside(c.owner,m.c);

  assert mapThruKlon(collectStrictlyInsideObject(o,m.o),m)
     == mapThruKlon({o}  + collectStrictlyInside(o.owner,m.o),m)
     == mapThruKlon({o},m) + mapThruKlon(collectStrictlyInside(o.owner,m.o),m)
     == {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m)
       by {
            FLATTEN_SUMS(
              {o},  collectStrictlyInside(o.owner,m.o),
             ({o} + collectStrictlyInside(o.owner,m.o)),
              m);
            MAPPEN_ONE(o,m);
       }

  assert mc == {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m);

  assert c.owner == mapThruKlon(o.owner, m) by
    { assert klonLine(o,c,m);
      assert klonIdentity(o,c,m);
      assert strictlyInside(o,m.o);
      assert o != m.o;
      assert c.owner == mapThruKlon(o.owner, m);
    }

  assert cm == {c} + collectStrictlyInside(mapThruKlon(o.owner, m),m.c);

  MASTERY_THRU(o.owner, m);

  assert       mapThruKlon(collectStrictlyInside(o.owner,m.o),m) ==       collectStrictlyInside(mapThruKlon(o.owner, m),m.c);
  assert {c} + mapThruKlon(collectStrictlyInside(o.owner,m.o),m) == {c} + collectStrictlyInside(mapThruKlon(o.owner, m),m.c);

  assert mc == cm;
  assert mapThruKlon(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c);
}




lemma {:timeLimit 10} MASTERY_THRU(oo : Owner, m : Klon)
  decreases allAMFOs(oo), 15
   requires klonCalid(m)
   requires m.allInKlon(oo)
   requires AllReady(oo)
   requires AllReady(mapThruKlon(oo,m))
   requires oo <= m.m.Keys

    ensures mapThruKlon(collectStrictlyInside(oo,m.o),m) == collectStrictlyInside(mapThruKlon(oo,m),m.c)
{
   assert collectStrictlyInside(oo,m.o) <= m.m.Keys;

  var mc := mapThruKlon(collectStrictlyInside(oo,m.o),m);
  var cm := collectStrictlyInside(mapThruKlon(oo,m),m.c);

  forall o <- oo ensures (mapThruKlon(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c))
      {
      var c := m.m[o];
      var omc := mapThruKlon(collectStrictlyInsideObject(o,m.o),m);
      var ocm := collectStrictlyInsideObject(m.m[o],m.c);
      assert o.Ready();
      assert klonCalid(m);
      assert m.objectInKlon(o);
      assert c == m.m[o];
      assert collectStrictlyInsideObject(o,m.o) <= m.m.Keys;



      MASTERY_OBJECT(o, m) by {
                                GOING_DOWN(oo,o);
                                assert (allAMFOs(oo),15 decreases to o.AMFO,14);
                              }
      assert (mapThruKlon(collectStrictlyInsideObject(o,m.o),m) == collectStrictlyInsideObject(m.m[o],m.c));
      }

   assert mc == cm;
   assert mapThruKlon(collectStrictlyInside(oo,m.o),m) == collectStrictlyInside(mapThruKlon(oo,m),m.c);

}


//forall x <- flatten(soup) && strictlyInside(x,pivot) ::  m.m[x] in flatten(coup) && strictlyInside(m.m[x], other-pivot))
//forall x <- flatten(coup) && strictlyInside(x,pivot) ::  unm(x) in flatten(soup) && strictlyInside(unm(x) , other-pivot))


lemma MAPPEN_ONE(o : Object, m : Klon)
 //shitteth has been throwth at the wallth and it sticketh
  requires o.Ready()
  requires o in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
   ensures (set x <- {o} :: m.m[x]) == {m.m[o]}
   ensures mtk({o},m) == {m.m[o]}
   ensures mapThruKlon({o},m) == {m.m[o]}
{
  LemmaSingletonSize({o},o);
  assert IsSingleton({o});
  var z := ExtractFromSingleton({o});
  assert z == o;
  assert {z} == {o};
  assert (set x <- {o} :: m.m[x]) == {m.m[o]};
  assert forall x <- {o} :: x == o;
  assert o in m.m.Keys;
  assert {m.m[o]} == (set x <- {o} :: m.m[x]);
  assert mtk({o},m) == {m.m[o]};
  var os := {o};
  MTK_THRU_KLON(os,m);
  assert mapThruKlon(os,m) == mtk(os,m);

}


lemma OLD_MAPPEN_ONE(o : Object, m : Klon)
 //took at least an hour trying more sensile versions of the next 12 lines
 //to just copy these ones in from an earlier file because they work.
  requires o.Ready()
  requires o in m.m.Keys
  requires klonReady(m)
  requires klonCalid(m)
   ensures mapThruKlon({o},m) == {m.m[o]}
{
  // assert mapThruKlon({o},m) ==
  //     (var os := {o}; assert (os > {}) ==> ( var o :| o in os; {m.m[o]} > {});  //THIS LINE IS OF SATAN. WASN'T NEEDED PREVIOUSLY.,..
  //     set o <- os :: m.m[o] );

  forall x <- m.m.Keys ensures (mtk({x},m) == {m.m[x]})
   {
    assert x in m.m.Keys;
    assert mapThruKlon({x},m) == (set o <- {x} :: m.m[o]);
    assert (set o <- {x} :: m.m[o]) == {m.m[x]};
    assert mapThruKlon({x},m) == {m.m[x]};
   }

}
  // var os := {o};
  // var rv := {m.m[o]};
  // assert os <= m.m.Keys;
  // assert (os > {});
  // assert (os > {}) ==> (rv > {});
  // assert (os > {}) ==> (var o :| o in os; (os == {o}) ==> ( mapThruKlon({o},m))     == {m.m[o]}) ;
  // assert os > {};
  // assert os == {o};
  // assert rv == {m.m[o]};



lemma FLATTEN_ONE(o : Object)
  requires o.Ready()
  ensures flatten({o}) == {o} + flatten(o.owner) == o.AMFO
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
