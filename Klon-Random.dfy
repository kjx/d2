include "Klon-Lemmata.dfy"

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















predicate {:isolate_assertions} OLDcheckBoundOfClone(k : Object, v : Object, m : Klon)
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
