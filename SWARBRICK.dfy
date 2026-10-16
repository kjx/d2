include "Ownership.dfy"
include "Ownership-Split.dfy"
include "Klon-Preserve.dfy"
include "Ownership-Flatten.dfy"



//SWARBICK - preliminary work on core ownershiup vhecs kept ariound for later...





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




lemma KLONECT_ONE_MORE(done : Owner, y : Object, rv : Owner, ksio : Owner, pivot : Object)
   requires forall o <- done :: o.Ready()
   requires y.Ready()
   requires rv   == collectStrictlyInside(done, pivot)
   requires ksio == collectStrictlyInsideObject(y, pivot)
    ensures collectStrictlyInside(done+{y}, pivot) == rv+ksio
{}


// lemma GOING_DOWN(oo : Owner, o : Object)
//     requires oo > {}
//     requires o in oo
//      ensures allAMFOs(oo) >= o.AMFO
//      ensures allAMFOs(oo) nonincreases to o.AMFO
//      ensures 15 decreases to 14
//      ensures (allAMFOs(oo), 15 decreases to o.AMFO, 14)
// {}

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

// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //
// // // // // // // // // // // // // // // // // // // // // // // // // // // //



lemma P_K_Inside(oo : Object, ob : Object, co : Object, cb : Object, m : Klon)
 //if oo >= ob then clonews co >= cb
 //currently requires inside, but should generalse nicely I think! non urgent.
 // abandoned for other approaches
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
  // abandoned for other approaches

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











///the magic lines?
// assert forall oo <- soup :: (set ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- (set x <- collectStrictlyInside({oo},pivot)) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
// assert (set oo <- soup, ooo <- collectStrictlyInside({oo},pivot) :: ooo) == (set oo <- soup, ooo <- flownerStrictlyInside({oo},pivot) :: ooo);
//




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


lemma LETS_BE_SUBSET(less : Owner, more : Owner)
  requires forall o <- less :: o in more
     ensures less <= more
{}
























































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






lemma EXISTENTIAL_FLATTEN(soup : Owner)
  requires AllReady(soup)
    ensures forall o <- flatten(soup) :: exists s <- soup :: o in s.AMFO
    ensures forall o <- flatten(soup) :: exists s <- soup :: inside(s,o)
{}

function roots(soup0 : Owner, soup1 : Owner) : Owner {soup0 + soup1}






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

  assert forall f <- f0 :: strictlyInside(f,m.o) <==>  strictlyInside(m.m[f],m.m[m.o]);

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









///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////
/////
///// all the WOOD shit
/////
/////



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







function superSize<K,V>(mep : map<K,V>) : (rv : nat)
   ensures rv == |mep.Keys|
  {
      if (mep.Keys == {}) then 0
        else (var x  :| x in mep;
              var nn := mep - {x};
               (1 + (superSize(nn))))
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
