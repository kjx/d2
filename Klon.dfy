include "Ownership.dfy"
include "Bound.dfy"
include "Klon-KlonLine.dfy"

//HACK - temporary patch, should be removed once wardisation is done

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
//    c - : objecet --=- the top of the clone! hurrah! m.c!

datatype Klon = Klon
(
  m : vmap<Object,Object>,    //the  klon map
  o : Object,                 //"pivot" object being copied
  c : Object,                 //"trivet" object being built
  clowner : Owner,            //owner of the clone
  clbound : Owner,            //bound of the clone
  oHeap : set<Object>,        //heap
  o_amfx : OWNR,              //the AMFX of o
  c_amfx : OWNR,              //epected flattened ownershio of the clone..
  c_amfb : OWNR              //expected flattened bound of the clone..
)
{
  function  ns(os : set<Object> := {}) : set<Object>
    ensures ns(os) >= ns()
       { m.Values+os }
  function hns(os : set<Object> := {}) : set<Object>
    ensures ns(os) <= hns(os)
    ensures hns() <= hns(os)
    ensures m.Values <= hns()
    ensures oHeap <= hns()
    ensures os <= hns(os)
       { oHeap+m.Values+os }

  predicate   from(prev : Klon) : (r : bool)
    ensures r ==> (isFlat(prev.oHeap) ==> isFlat(oHeap))
    ensures r ==> m.Keys >= prev.m.Keys
  {
    && mapGEQ(m,  prev.m)
    && o       == prev.o
    && c       == prev.c
    && clowner == prev.clowner
    && clbound == prev.clbound
    && oHeap   == prev.oHeap     //OPTION - considere incorporating ApoCalidseNow...
    && o_amfx  == prev.o_amfx
    && c_amfx  == prev.c_amfx
    && c_amfb  == prev.c_amfb
       //option ie allow heaps to get bigger, so long as all keys are in the heap
  }

  predicate HeapOwnersReady()
    reads {}
  { true } //HACK

  predicate ValuesOwnersReady()
    reads {}
  { true } //HACK

  predicate HeapContextReady()
//    requires klonReady(this)
    reads hns()
   { klonReady(this) && klonHeap(this) }

  predicate ValuesContextReady()
//    requires klonReady(this)
    reads hns()
   { klonReady(this) && klonHeap(this) }


  predicate {:isolate_assertions} preCalid() : (r : bool)   //HACK
//    requires klonReady(this)
    reads hns()
  { klonCalid(this) }

  predicate {:isolate_assertions} preCalid2() : (r : bool)  //HACK
//    requires klonReady(this)
    reads hns()
  { klonCalid(this) }

  predicate {:isolate_assertions} SuperCalidFragilistic() : (r : bool)  //HACK
//    requires klonReady(this)
    reads hns()
  { klonCalid(this) }

  predicate {:isolate_assertions} Calid() : (r : bool)  //HACK
//    requires klonReady(this)
    reads hns()
  { klonCalid(this) }

  predicate gettingThere() reads {}   //HACK
//    requires klonReady(this)
    reads hns()
  { klonCalid(this) }

  predicate {:isolate_assertions} AllLinesCalid()  //HACK
//    requires klonReady(this)
    reads hns()
  { klonReady(this) && klonAllLines(this) }   // or klonCalid??


  lemma {:isolate_assertions} {:timeLimit 20} CalidLineKVTo(k : Object, v : Object, m1 : Klon)
    requires apoCalidse()
    requires k.Ready()
    requires ownersInKlown(k)
    requires v.Ready()
        requires CalidLineKV(k,v)
    requires m1.from(this)
    requires m1.apoCalidse()
     ensures m1.CalidLineKV(k,v)
{}


  lemma {:isolate_assertions} {:timeLimit 20} CalidLineKVFrom(k : Object, v : Object, prev : Klon)
    requires prev.apoCalidse()
    requires k.Ready()// && k.Valid() // should context go in here too? probasbly?
    requires prev.ownersInKlown(k)
    requires v.Ready()
    requires prev.CalidLineKV(k,v)
    requires from(prev)
    requires apoCalidse()
     ensures CalidLineKV(k,v)
{}



  predicate {:isolate_assertions} CalidLineKV(k : Object, v : Object)
    requires apoCalidse()
     ensures klonReady(this)
      reads hns(), k, v
    { klonLine(k, v, this) }


lemma MOVIN_ON_MAP(os: Owner, left : vmap<Object,Object>, right : vmap<Object,Object>)
  //some kind of map thing. but it's a lemma
  requires left.Keys >= right.Keys >= os
  requires forall o <- right.Keys :: left[o] == right[o]
  ensures  (set o <- os :: left[o]) == (set o <- os :: right[o])
{}



  predicate objectInKlown(o : Object) : (rv : bool)  //body replace with obejctReadtyInKlon
    //o and all its owners etc are the Klown m
    //(doesn't extend to fields)
    //NOTE critical that this does NOT dpend on klonReady() etc
    ///because i5t supprots that definition
    reads {}

    ensures rv ==> (o in m.Keys)
    ensures rv ==> (o.AMFB <= m.Keys)
    ensures rv ==> (o.AMFX <= m.Keys)
    ensures rv ==> (o.AMFO <= m.Keys)
    ensures rv ==> (o.bound <= m.Keys)
    ensures rv ==> (o.owner <= m.Keys)
    ensures rv ==> (o.self  <= m.Keys)

    // ensures (o.Ready() && rv) ==> objectInKlown(o)
    // ensures  o.Ready() ==> (rv == objectInKlown(o))
  {
    o.Ready() && (o.AMFO <= m.Keys)
   }



  predicate ownersInKlown(o : Object) : (rv : bool) //body replace with owners    ReadtyInKlon
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
      o.Ready() && (o.AMFX <= m.Keys) //&& (k in m.oHeap)
    }

//29 Oct 2025
//I think the quesiton is whether clowner have tio be in values.
//and ... it doesn't!!!
// -- 19 Apr 2026 - no idea wht that means...



predicate apoCalidse()
   //the six requirements of preCalid2 / computeOwnerForClone apocalypse
   reads {}
  {
    klonReady(this)
    // && (m.Keys <= oHeap)
    // && (m.Values <= hns())
    // && (objectReadyInKlown(o))   //this was originally two predicates
    // && (HeapOwnersReady())  //whatt bno value owners ready??
    // && (c_amfx <= oHeap)
  }

lemma APOCAKLON()
  requires klonReady(this)
   ensures apoCalidse()
 {}




//{:timeLimit 60} {:timeLimit 30}
  function {:isolate_assertions} {:timeLimit 20} CalidKV(k : Object, v : Object) : (mK : Klon)
   //shojld be calidKV, shouldn't it. GRRRR
    //givne a Calid Klon, add in k:=v to the mapping and get a  Calid result.
    //the heart of the heart of the klon
    requires klonReady(this)
    requires klonCalid(this)

    requires CKV_preconditions(k,v)
 // requires CalidLineKV(k,v)
    requires klonLine(k,v,this)

     ensures mK == klonKV(this, k, v)
     ensures mK.from(this)
    //  ensures mK.HeapContextReady()
    //  ensures mK.ValuesContextReady()
    //  ensures mK.m.Keys <= mK.oHeap
     // ensures  unchanged(oHeap`fieldModes)
     // ensures  unchanged(m.Values`fieldModes)
      // ensures forall z <- m.Keys :: m[z].fieldModes == mK.m[z].fieldModes

ensures klonReady(mK)
ensures klonCalid(mK)

// Inside klonHeap(m)
// Could not prove: forall x <- m.m.Values :: x.Context(m.hns())
// This is the only assertion in batch #1227 of 1227 in function CalidKV
// Batch #1227 resource usage: 36.8M RU
//
// Error: a postcondition could not be proved on this return path
// Inside klonCalid(mK)
// Inside klonAllLines(m)
// Could not prove: forall k <- m.m.Keys :: klonLine(k, m.m[k], m)
// This is the only assertion in batch #1225 of 1227 in function CalidKV
// Batch #1225 resource usage: 32.8M RU
//


     reads hns(), k, v
     reads m.Keys, m.Values
{
  var mK := klonKV(this, k, v);
  assert mK.from(this);
  KlonReadyFromKV(mK,this,k,v);
  assert klonReady(mK);



  KlonCalidFrom(mK,this);
  assert klonCalid(mK);
  mK
}


//{:timeLimit 60} {:timeLimit 30}
  function {:isolate_assertions} {:verify false} OLDCalidKV(k : Object, v : Object) : (mK : Klon)
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




   predicate {:isolate_assertions} CKV_preconditions(k : Object, v : Object)
    //attempt to capture the common preconditions for CalidKV

    reads oHeap, m.Values, k, v
    reads m.Keys, m.Values
  {
//.    && SuperCalidFragilistic()
    && klonReady(this)
    && klonCalid(this)

    && k.Ready() //&& k.Valid() // should context go in here too?   probasbly?
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
    && klonLine(k,v,this)
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

//HACK
//   predicate {:isolate_assertions} CalidCanValue(k : Object, v : Object)
//     //conditions an object to be added as a Value into the Klon map
//     // dunno if I really need this but wrote it anyway as an extenion of CanCalidKey above
//     //  note this doesn't seem to deal with ougoing field values, but that will get
//     //  caught eventually via  HeapContextReady() &  ValueContextReady()
//     //doesn't seem to require Calid????
//     requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
//     requires v.Ready() //&& v.Valid()
//     requires ownersInKlown(k)
//     requires o.Ready() //&& o.Valid()
//     requires objectInKlown(o)
//
//     requires CalidCanKey(k)
//
//     //the six requirements of preCalid2 / computeOwnerForClone apocalypse
//     requires k.owner <= m.Keys <= oHeap
//     requires m.Values <= hns()
//     requires o.Ready()
//     requires objectInKlown(o)
//     requires HeapOwnersReady()
//     requires c_amfx <= oHeap
//
//     reads oHeap, m.Values
//   {
//     && (v !in m.Values)
//     && (v.Ready()) //&& v.Valid() && v.Context(hns({v})))
//     && (CalidLineKV(k,v)) //will this do?
//   }


//HACK
//   ghost predicate {:isolate_assertions} calidCanKV(k : Object, v : Object)
//     requires k.Ready() //&& k.Valid() // should context go in here too? probasbly?
//     requires v.Ready() //&& v.Valid()
//     requires ownersInKlown(k)
//     requires o.Ready() //&& o.Valid()
//     requires objectInKlown(o)
//
//
//     reads oHeap, m.Values
//
//   {
//     && SuperCalidFragilistic()
//     // && HeapContextReady()
//     // && ValuesContextReady()
//     // && Calid()
//     && CalidCanKey(k)
//     && CalidCanValue(k,v)
//   }
//



  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]     ]]]]]]]]]]]




    lemma {:isolate_assertions} CalidLineKVReflexive(k : Object, v : Object)
    //ensures that we can insert k:=k into the Klon
    requires klonReady(this)

    requires k in oHeap
    requires k == v
    requires outside(k,o)
    requires outside(v,c)
    requires klonBound(k,v,this)



    //requires klonCalid(this) //which is it?
    //the six requirements of preCalid2 / computeOwnerForClone apocalypse
     ensures apoCalidse()


    //generic?
    requires k.Ready()
    requires ownersInKlown(k)
    requires v.Ready()
     ensures o.Ready()
     ensures objectInKlown(o)

   //       ensures forall x <- m.Keys :: outside(x,o) ==> (m[x] == x)

     ensures klonReady(this)
     ensures klonBound(k,v,this)
     ensures klonModes(k,v,this)
     ensures klonGeometry(k,v,this)
     ensures klonIdentity(k,v,this)
     ensures klonLine(k,v,this)

//    requires forall x <- k.AMFO :: (m[o] == o)   //needs klonCalid

    ensures  checkOwnershipOfClone(k, v, this)
    ensures  checkBoundOfClone(k, v, this)
    ensures  mappingOwnersThruKlownKV(k,v,this)
    ensures  CalidLineKV(k, v)
  {
  // assert klonReady(this);
  // assert klonBound(k,v,this);
  // assert klonModes(k,v,this);
  // assert klonGeometry(k,v,this);
  // assert klonIdentity(k,v,this);
  }

  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]
  //[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[[]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]

///OwnersLine version


//Need to WORK The FUCK out wwhat to do about THIS
   predicate {:isolate_assertions}   preOwners() : (r : bool)
    reads oHeap, m.Values
  {
    klonReady(this)
    // // && HeapOwnersReady()    ///hmm
    // // && ValuesOwnersReady()
    // && (o.Ready() && (o in oHeap))
    // && (objectInKlown(o))  //progFUCK  do i want this in here? really?   ///Can U do without it??
    // && (o.AMFX == o_amfx)
    // && (flatten(clbound) >= o.AMFB)
    // && (o.AMFO == o_amfx+{o})
    // && (c_amfx >= flatten(clbound) >= flatten(o.bound))
  }



   predicate {:isolate_assertions} preOwners2() : (r : bool)
    reads {}
  {
    klonReady(this)
    // && (c_amfx <= oHeap) //should goto precalid1??
    // && ((o in m.Keys) ==> (
    //     var c := m[o]; //WE HAS KLONE
    //     && (c_amfx  == c.AMFX)
    //     && (clowner == c.owner)
    //     && (clbound == c.bound)
    //    ))
  }

   predicate {:isolate_assertions} SuperCalidOwners() : (r : bool)
    reads oHeap, m.Values
  {
    klonCalid(this)
    // // && HeapOwnersReady()
    // // && ValuesOwnersReady()
    // && CalidOwners()
  }

   predicate {:isolate_assertions} CalidOwners() : (r : bool)
    // requires  HeapOwnersReady()
    // requires  ValuesOwnersReady()
    reads oHeap, m.Values
  {
     klonCalid(this)
    //     // && HeapOwnersReady()
    //     // && ValuesOwnersReady()
    // && apoCalidse()
    // && preOwners()
    // && preOwners2()
    // && (m.Keys <= oHeap)
    // && objectInKlown(o)
    // && (forall k <- m.Keys :: OwnersLineKV(k, m[k]))
  }

//does this mean it MUST be in or it CAN be in
//with objectInKnown(k) this says it MUST ne in,. doesn;t it?
//FUCK FUCK FUCK compare CalidLineKV!!!
//ditto (v in hns({v}))) from earlier plain (v in hns())
 predicate {:isolate_assertions} OwnersLineKV(k : Object, v : Object)
    requires apoCalidse()
     ensures klonReady(this)
      reads hns(), k, v
    { klonLine(k, v, this) }
// //  && (k.Ready() && (objectInKlown(k)) && k in oHeap)   28 Oct 2025
//     && (k.Ready() && (ownersInKlown(k)) && k in oHeap)
//     && (v.Ready() && (v in hns({v})))
//
//  //   && (v.AMFO  >= v.AMFB  >= k.AMFB)  //GREENLAND
//       && (   (inside(k,o)) ==> (k.AMFB  <= o.AMFB))  //GREENLAND
//
//     && (not(inside(k,o)) ==> (v == k))
//     && (   (inside(k,o)) ==> ((v !in oHeap)) )
//
//   //MAPPING - progFEARSATAN
//     && (mappingOwnersThruKlownKV(k,v,this)


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
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////

///Important Klon Mappinhgs





predicate {:isolate_assertions}  checkOwnershipOfClone(k : Object, v : Object, m : Klon)
  //to work, this needs m.o and m.c to be set up
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

//  reads m.oHeap, m.m.Values
  ensures klonReady(m)
  reads m.hns(), k, v
{
  klonLine(k,v,m)
  // mappingOwnersThruKlownKV(k,v,m)
}




  predicate {:isolate_assertions} mappingOwnersThruKlownKV(k : Object, v : Object, m : Klon) : (r : bool)
    //prog FEAR SATAN
    //this vrsion currently matches CalidLineKV, i.e. k and v don't have to be in the klon
    //but that means we can't mapp intl and AMFO  //um,,
    //i think this is th4e INVARIANT
    //Sure seeems to be the  INVARIANT -- 22 Dec 2025

   decreases k.AMFO
    requires m.apoCalidse()
    requires m.ownersReadyInKlown(k)
//    reads m.oHeap, m.m.Values
  requires klonReady(m)
  reads m.hns(), k, v
  { klonIdentity(k,v,m) }
//     {
//       // prog FEAR SATAN!!
//
//       if (k == m.o) then (
//           && (v == m.c)
//           && (v.owner == m.clowner)
//           && (v.bound == m.clbound)
//         ) else if (outside(k, m.o) )
//           then (
//             k == v
//         ) else (
//           assert strictlyInside(k, m.o);
//               // && (v.bound == mapThruKlon(k.bound, m))
//               // && (v.owner == mapThruKlon(k.owner, m))
//               && mappingOWNRsThruKlownKV(k.bound, v.bound, m)
//               && mappingOWNRsThruKlownKV(k.owner, v.owner, m)
//         )
//     }



    //our shold this be MAPPING Owners?????
    //note that this is called ONLY strictly wihin the pivot - see the JDVANCE note
    predicate {:isolate_assertions} mappingOWNRsThruKlownKV(kk : OWNR, vv : OWNR, m : Klon) : (r : bool)
    //
    //this probably should be just deleted for good..
    //
    //
      //actual OWNR version of mappingOwnersThruKlownKV
      //within the pivot anyway!
      //prog FEAR SATAN
          //OK so wher doe this asy "inside the pivot"?   - it DO#ESNT
          //does that matter?  who knows?
      requires m.apoCalidse()
      // requires AllReady(kk)  // 29 Oct 2025
      // requires AllReady(vv)  // 29 Oct 2025
      requires kk <= m.m.Keys
  ////requires vv <= m.m.Values  ///hmm must be trie if kjk,s inside Klon...
  ////requires kk > m.o.AMFO  //gotta be inside kloned bit..  //JDVANCE yeah shoud do that!
  { vv == (mapThruKlon(kk, m)) }
//         {
// //I have NO FUCKING IDEA if this is dong te RIGHT THING or not.
// //anin't that great.
// //i think its dong CLOSE ENOUGH to the right thing for a paper
// //the visualisations all look OK now
// //but stil - 21 Sept 2025
//
//
// //FUCK!!! this is AMFO not OWNER!!!!!!!!!! !!!!!!!!!! !!!!!!!!! !!!!!!!!!!!
// //the argument types are called OWNR
// //they are passed in "owner" and "bound" - ie objects not Owners.  //FUCK.
//
//         && (vv == (mapThruKlon(kk - m.o.AMFO, m) + m.c.AMFO))
//         && (flatten(kk) <= m.oHeap)
//         && (flatten(vv) <= m.hns(vv))
//
//           // var inside1 := kk - m.o.AMFO;
//           // var option1 := mapThruKlon(inside1,m) + m.c.AMFO;
//           // (vv == option1)
//         }
//


function {:isolate_assertions} computeOwnerForClone(oo : Owner, m : Klon) : (nuowner : Owner)
  //given some flattened Owner oo, calculate the mapped / cloned version
  //EXCEPT OWNERS SHOULDNT BE FLATTENNED!!!
///TODO//Libertarian  //requires (flatten(oo) >= m.o.AMFO)   //should this be there or not?
  //
  //     7 Aug 2025 - prog thinks - this doesn't work if we're flatting the bound
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
///progA Naa will need Values...
  requires klonReady(m)
//  requires m.apoCalidse()  //note that this requires m.o already in m.m.Keys
  requires oo <= m.m.Keys
//  requires flatten(oo) >= m.o.AMFO //hmmmA
//  requires m.SuperCalidFragilistic()
   ensures nuowner <= m.hns()
   ensures flatten(oo) <= m.oHeap //so this MUST be preexisting.
   ensures flatten(nuowner) <= m.hns()
   ensures mappingOWNRsThruKlownKV(oo, nuowner, m)   //rather important
       //yes 'rathr imoportant" infdeed,


 //  ensures nuowner == global(sideways(local(oo, m),m),m)
 //   ensures nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.c.AMFO, m.m)

      //********also important that that's OWNRES NOT Owners **************//
      //***ot is it??
      //JDVANCE -- note that sholdlj constraint oo to be inside(the pivot)
      //so the new owner is strictly inside the blivet..../
 // requires flatten(oo) >= m.o.AMFO           //JDVANCE

 reads m.oHeap, m.m.Values
//  reads {}
{
  mapThruKlon(oo,m)
}
  //   assert m.ValuesContextReady();
//   var inside1 := oo - m.o.AMFO;
//   assert inside1 <= m.oHeap;
//
//   var nuowner := mapThruKlon(inside1,m) + m.c.AMFO;
//
//   assert nuowner == (set x <- (oo - m.o.AMFO) :: m.m[x]) + m.c.AMFO;
// //  assert nuowner == shiftAMFOZ(oo, m.o.AMFO,  m.c.AMFO, m.m);
//
//   assert mapThruKlon(inside1,m) <= m.m.Values <= m.hns();
//   assert m.c in m.hns();
//   assert m.c.AMFO <=  m.hns();
//
//   var fuck1 := local(oo, m);
//   var fuck2 := sideways(fuck1, m);
//   var fuck3 := global(fuck2, m);
//   assert fuck3 == nuowner;
//
//   assert fuck3 == global(sideways(local(oo, m),m),m);
//
//
// //  .AMFO <= m.m.Values <= m.hns();ƒƒ∂çƒ©
//   assert nuowner <= m.hns();
//   nuowner
//
//really this is to MATCH the checkClownershipINSIDE



















///////////////////////////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////////////////////////
lemma KLONVMAPREADY(ks : set<Object> := m.m.Keys, m : Klon)
   requires ks <= m.m.Keys
   requires klonReady(m)
    ensures klonVMapOK(m.m, ks)
  {}


predicate klonVMapOK(m : vmap<Object,Object>, ks : set<Object> := m.Keys)
  requires ks <= m.Keys
  //klonVMapOK the vmap parts of a klon are OK
  //still need to do something for iHeap and ns etc
  //should probably swizzle this to take a Klon, not a vmap/...
  //prog AND that shoud something like klonReady
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
//Readiness???  //progFEARSATAN
   && (forall k <- ks :: k.Ready() && m[k].Ready() )

  //AMFO
  && (forall k <- ks :: k.AMFO <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFO, m) == m[k].AMFO)

  //AMFB
  && (forall k <- ks :: k.AMFB <= m.Keys)
  //  && (forall k <- ks :: mapThruVMap(k.AMFB, m) == m[k].AMFB)

  //progOWNERS
  //region & owners?
  //  && (forall x <- ks :: x.owaner <= x.AMFO)//progOWNERS
//  && (forall x <- ks :: x.bound <= x.owner <= m.Keys) //should that bound be ks?
  //  && (forall k <- ks :: mapThruVMap(k.owner, m) == m[k].owner)
  //  && (forall k <- ks :: mapThruVMap(k.bound, m) == m[k].bound)

  //field values? //prog
  //
  //
  //  && (forall k <- ks :: k.fieldModes == m[k].fieldModes)
///
  //see rant above
}



  function {:isolate_assertions} {:timeLimit 60} klonKV(m' : Klon, k : Object, v : Object) : (m : Klon)   //TIME-3-OCT
    //aux function for adding k v to a m' giving m
//Klon.CalidKV does all the real work!
//KJX Sun 19 April - so WHAT THE FUCK does this one do then?
  requires k !in m'.m.Keys
  requires v !in m'.m.Values
  requires klonVMapOK(m'.m)
  requires klonCanKV(m', k, v)
  requires klonReady(m')


  ensures klonVMapOK(m.m)
  ensures klonCanKV(m', k, v)
//  ensures forall x <- m.m.Keys, y <- m.m.Values :: (y == v) ==> (x == k)
//  ensures m == m'.(m:=m'.m[k:=v])
  ensures m == m'.(m:=vmapKV(m'.m,k,v))
  ensures m.from(m')
  ensures m.m.Keys   == m'.m.Keys+{k}
  ensures m.m.Values == m'.m.Values+{v}
  ensures m.hns()    == m'.hns()+{k,v}
  ensures m.o        == m'.o
  ensures m.oHeap    == m'.oHeap
  ensures forall z <- m'.m.Keys :: modesEQ(m'.m[z].fieldModes, m.m[z].fieldModes)

  ensures klonReady(m)

  reads k, v, m'.oHeap, m'.hns(), m'.m.Keys, m'.m.Values

    // reads m'.m.Keys`fields, m'.m.Keys`fieldModes
    // reads m'.m.Values`fields, m'.m.Values`fieldModes

  //reads  m'.m.Values, m'.oHeap  //for ValuesContextReady?
{
   var r0 : vmap<Object,Object> := vmapKV(m'.m,k,v);
   var m := m'.(m:=r0);
   KlonReadyFromKV(m,m',k,v);
   m
//
//   assert klonVMapOK(m'.m);
//   assert klonCanKV(m', k, v);
//     assert m'.ownersInKlown(k);
//
//    assert forall x <- m'.m.Keys, y <- m'.m.Values :: (y == v) ==> (x == k);
//     // var m'fmodes := map z <- m'.m.Keys :: z := z.fieldModes;
//     // assert m'fmodes.Keys == m'.m.Keys;
//     // assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);
//
//   var r0 : vmap<Object,Object> := vmapKV(m'.m,k,v); // m'.m[k:=v];
//   assert klonVMapOK(r0);
//   assert r0 ==  m'.m[k:=v];
// // assert forall z <- m'.m.Keys :: modesEQ(z.fieldModes, m'fmodes[z]);
// // assert forall z <- m'.m.Keys :: modesEQ(r0[z].fieldModes, m'fmodes[z]);
//
//   var r1 := m'.(m:=r0);
//   assert r1 == m'.(m:=m'.m[k:=v]);
//
//   haventFuckedFieldModes(m',k,v,r1);
//
//  assert forall x <- m'.m.Keys :: m'.ownersInKlown(k);
//     assert k in r1.m.Keys;
//     assert r1.objectInKlown(k);
//     assert r1.m.Keys == m'.m.Keys + {k};
//  assert forall x <- r1.m.Keys :: r1.ownersInKlown(k);
//
// //  assert forall z <- m'.m.Keys :: z.fieldModes == r1.m[z].fieldModes;
//   r1
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
  && (k in m'.oHeap)  //prog do I want this here?
  && (if (v==k) then (v in m'.oHeap) else (v !in m'.oHeap)) //nope - happens after  wards

  //grrr. should refactor this
  && k.Ready() && k.Valid() && k.Context(m'.oHeap)
  && v.Ready() && v.Valid() && v.Context(m'.hns({v}))

  //  && k.Context(m'.m.Keys+{k})  ///what IS this?
  &&  m'.ownersInKlown(k)
  && (k.fieldModes == v.fieldModes)//hhhmm see anbove

  //  && (v.AMFX >= v.AMFB >= k.AMFB) //is this right?   really?
  //17 June 2025 prog thinks this iswrong & shoud be in CalidLineKV


  //END DOOUBLE BOWIE
}

// basic mappings


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

function mapBackKlon(os: set<Object>, m : Klon) : (r : set<Object>)
  //image of os under INVERSE klon mapping m
  // reads m.m.Keys`fields, m.m.Keys`fieldModes
  // reads m.m.Values`fields, m.m.Values`fieldModes
  requires os <= m.m.Values
  ensures  r  <= m.m.Keys
  reads {}
{ mapBackVMap(os,m.m) }

function objThruKlon(o : Object, m : Klon) : Object    requires o in m.m.Keys {m.m[o]}






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
//  && ()   //at some point needs to check mapping for fieldModes?    //OR NOT///
}


///// special purpose mappings - local/globa/sideways

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
  //  requires forall o <- oo :: inside(o,m.c)
  //  //ensures  isReallyFuckingFlat(rs)
  // //requires o >= m.o.AMFO
  //  //ensures isFlat(r)
   { oo + m.c.AMFO  }

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














predicate {:isolate_assertions} checkBoundOfClone(k : Object, v : Object, m : Klon)
  requires k.Ready()
  requires v.Ready()
  requires klonReady(m)
  requires m.ownersInKlown(k)
  reads m.hns(), k, v
 { klonIdentity(k,v,m) }
  // NO NO NO NO NO NO NO NO!!!
  // { && nuBoundsOK(k.owner, k.bound)
  //   && (mapThruKlon(k.owner, m) == v.owner)
  //   && (mapThruKlon(k.bound, m) == v.bound)
  //   && nuBoundsOK(v.owner, v.bound) }
