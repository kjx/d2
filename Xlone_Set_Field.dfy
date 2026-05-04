include "Xlone.dfy"




//{:resource_limit 75_000_000}   {:timeLimit 30}
method {:isolate_assertions}  {:timeLimit 30} {:verify true} Xlone_Set_Field(k : Object, v : Object, n : string,
                 t : Object, u : Object, m' : Klon)
  //with k.n := t,  Klon mappings including k->v, t->u,  set v.n := u
  //requires v !in m'.oHeap   //clone will ONLY need to fields into new objects...
  requires k.Ready()
  requires v.Ready()
  requires t.Ready()
  requires u.Ready()
  requires k != v
  requires v  in m'.hns()

  requires v.Valid()
  requires v.OwnersWithin(m'.hns())
  requires u.OwnersWithin(m'.hns()) //can't hurt
  //requires n  in v.fieldModes.Keys //subsumed by FieldValidNV
  requires n !in v.fields

  requires m'.SuperCalidFragilistic()
  requires m'.SuperCalidOwners()
  requires m'.CalidOwners()
  requires m'.objectInKlown(k)  //note that doing this *requires* objects to be in the Klon
  requires m'.m[k] == v         //BEFORE they are setup in the fields. is this the right way around?
  requires t.Ready()            //
  requires m'.objectInKlown(t)  //ditto
  requires m'.m[t] == u         //ditto ditto

  requires k in m'.m.Keys
//NO_FIELDMODES   requires k.fieldModes.Keys == v.fieldModes.Keys
  requires v.FieldValidNV(n, u)
  requires FVNU: v.FieldValidNV(n, u)


//FIELD MODEs-ISM HACK -- shouod go into calid or at laets supercalid!
//NO_FIELDMODES   requires forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES //   ensures forall z <- m'.m.Keys :: z.fieldModes == m'.m[z].fieldModes
//NO_FIELDMODES    ensures forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes) == m'.m[z].fieldModes
//NO_FIELDMODES    ensures unchanged( m'.oHeap`fieldModes, m'.m.Values`fieldModes )
//NO_FIELDMODES    ensures forall x <- m'.hns() :: old(allocated(x)) ==> unchanged(x`fieldModes)

//need to decide if origB -> u is in m.m.Keys or not
   ensures v.OwnersWithin(m'.hns({u}))
  // ensures v.Valid()
   ensures n in v.fields.Keys
   ensures v.fields[n] == u
//NO_FIELDMODES    ensures k.fieldModes.Keys == old(k.fieldModes.Keys)
//NO_FIELDMODES    ensures v.fieldModes.Keys == old(v.fieldModes.Keys)
   ensures k.fields.Keys == old(k.fields.Keys)
   ensures v.fields.Keys == old(v.fields.Keys) + {n}
   ensures k.fields == old(k.fields)
   ensures v.fields == old(v.fields)[n := u]
  //
   ensures (forall z <- m'.m.Keys | z != v :: z.fields == old(z.fields))
   ensures (forall z <- m'.m.Keys | z == v :: z.fields == old(z.fields)[n:=u])
   ensures (forall z <- m'.m.Keys :: z.fields ==
       if (z == v) then (old(z.fields)[n:=u])
                   else (old(z.fields)))

  ensures m'.CalidOwners()
  ensures m'.SuperCalidOwners()
  ensures m'.SuperCalidFragilistic()

  modifies v`fields
{
  assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);
  assert v.Valid();
  assert v.AllFieldsValid() by { assert v.Valid(); }
assert v.Ready();
//NO_FIELDMODES          assert v.fields.Keys <= v.fieldModes.Keys;
var vee_feeldKeyz := v.fields.Keys;
assert (forall z <- vee_feeldKeyz :: refOK(v, v.fields[z]));
//NO_FIELDMODES          assert (forall z <- vee_feeldKeyz :: modeOK(v, v.fieldModes[z], v.fields[z]));
assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, v.fields[z]));

 print "CALL KaTHUMP ", fmtobj(v), ".", n, " to ", fmtobj(u), "\n";
assert (forall z <- m'.m.Keys | z != v :: z.fields == old(z.fields));
//NO_FIELDMODES          assert forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes) == m'.m[z].fieldModes;

  assert v.AllFieldsValid() by { assert v.Valid(); }

  assert m'.CalidOwners();
  assert forall z <- m'.m.Keys :: m'.OwnersLineKV(z, m'.m[z]);
  var emKeys := m'.m.Keys;
  assert emKeys == m'.m.Keys;
  assert forall z <- emKeys :: m'.OwnersLineKV(z, m'.m[z]);
  assert forall z <- emKeys :: m'.CalidLineKV(z, m'.m[z]);

assert m'.AllLinesCalid();

  assert m'.SuperCalidOwners();
  assert m'.SuperCalidFragilistic();

  assert m'.HeapContextReady();

// var vee_feelds := v.fields;
// assert forall z <- v.fields.Keys :: z != n;
assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, v.fields[z]));

assert n !in vee_feeldKeyz;

var vee_feelds := v.fields;
//NO_FIELDMODES var vee_moodes := map z <- v.fieldModes.Keys :: v.fieldModes[z];
var vee_extra := map z <- vee_feeldKeyz :: v.fields[z];

//neither way around will prove
//assert vee_feelds == vee_extra;
//assert vee_feelds != vee_extra;

assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, vee_feelds[z]));
assert (forall z <- vee_feeldKeyz :: v.fields[z] == vee_feelds[z]);
assert (forall z <- vee_feeldKeyz :: v.fields[z] == vee_feelds[z] == vee_extra[z]);
assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, vee_extra[z]));

  assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);

opaque
  modifies v`fields
  ensures v.fields == vee_feelds[n:=u]
  ensures n !in vee_feeldKeyz
  ensures forall z <- vee_feeldKeyz :: v.fields[z] == vee_feelds[z]
  ensures k.fields == old(k.fields)
  ensures k.fields.Keys == old(k.fields.Keys)
//  ensures forall z <- vee_feeldKeyz :: v.FieldValidNV(z, v.fields[z])
//  ensures v.FieldValidNV(n, u)
    {  assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);
       assert vee_feelds == v.fields;
///////////////////////////////////////////////////////////////////////////////////
       v.fields := mapKV(v.fields,n,u);
///////////////////////////////////////////////////////////////////////////////////
       assert forall z <- vee_feelds.Keys :: v.fields[z] == vee_feelds[z];
       assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);
//      assert v.FieldValidNV(n, u) by { reveal FVNU; }
    }
// assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, vee_extra[z]));
// assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, vee_feelds[z]));

//NO_FIELDMODES          assert forall z <- vee_feeldKeyz :: z in vee_moodes.Keys;
assert forall z <- vee_feeldKeyz :: refOK(v, vee_extra[z]);
//NO_FIELDMODES          assert forall z <- vee_feeldKeyz :: modeOK(v, vee_moodes[z], vee_extra[z]);
//NO_FIELDMODES          assert forall z <- vee_feeldKeyz :: modeOK(v, v.fieldModes[z], vee_extra[z]);
//NO_FIELDMODES          assert forall z <- vee_feeldKeyz :: modeOK(v, v.fieldModes[z], v.fields[z]);

assert (forall z <- vee_feeldKeyz :: v.fields[z] == vee_feelds[z]);
assert (forall z <- vee_feeldKeyz :: v.fields[z] == vee_feelds[z] == vee_extra[z]);
// assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, v.fields[z]));

       assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);

// assert v.fields[n] == u;
// assert v.fields == vee_feelds[n:=u];
// assert v.fieldModes == vee_moodes;

assert n !in vee_feeldKeyz;
assert (forall z <- vee_feeldKeyz :: v.FieldValidNV(z, v.fields[z]));
assert v.FieldValidNV(n, u) by { reveal FVNU; }
assert vee_feeldKeyz + {n} == v.fields.Keys;
forall z <- v.fields.Keys ensures (v.FieldValidNV(z, v.fields[z]))
  {
    if (z == n) { assert v.FieldValidNV(n, u) by { reveal FVNU; }}
      else { assert z in vee_feeldKeyz;
             assert v.FieldValidNV(z, v.fields[z]); }
  }
print "Hello\n";

//assert forall x <- m'.hns() :: unchanged(x`fieldModes);
//NO_FIELDMODES    assert (forall x <- m'.hns() :: old(allocated(x)) ==> unchanged(x`fieldModes));
// opaque
//   modifies v`fields
//     ensures forall z <- v.fields.Keys ::
//       if (z in vee_feelds.Keys)
//         then (v.fields[z] == vee_feelds[z])
//         else ((z==n) && (v.fields[z]==u))
// //   ensures v.fields == v.fields[n:=u]
//   //  ensures forall z <- m'.m.Keys :: z.fieldModes == old(z.fieldModes)
//   //  ensures forall z <- m'.m.Keys :: m'.m[z].fieldModes == old(m'.m[z].fieldModes)
//   //   ensures forall z <- m'.m.Keys :: z.fieldModes   == m'.m[z].fieldModes
//  { v.fields := v.fields[n:=u]; }

////////assert v.fields == vee_feelds[n:=u];  /////////huh?

// assert forall z <- m'.m.Keys, y <- z.fieldModes.Keys ::
//   z.fieldModes[y] == old(z.fieldModes[y]) == m'.m[z].fieldModes[y];
// assert (forall z <- m'.m.Keys | z != v :: z.fields == old(z.fields));
  print "RETN KaTHUMP done ", fmtobj(v), "\n";

//NO_FIELDMODES          assert v.fieldModes.Keys == old(v.fieldModes.Keys);
assert          v.fields == old(v.fields)[n := u];
       assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);

  assert v.FieldValidNV(n, u) by { reveal FVNU; }

forall m <- v.fields.Keys  ensures ( v.FieldValidNV(m, v.fields[m]))  //by
  {
    if (m == n) {assert v.FieldValidNV(m, u) by { reveal FVNU; } }
    else {
      assert old(v.FieldValidNV(m, v.fields[m]));
//      assert    (v.FieldValidNV(m, v.fields[m]));
    }
  }

assert u.OwnersWithin(m'.hns({u})); //OK
assert u.Valid(); //OK
assert u.Context(m'.hns()); //OK

//  assert forall z <- emKeys :: m'.OwnersLineKV(z, m'.m[z]);  //NOT-OK
  assert emKeys == m'.m.Keys; //OK
//  assert forall z <- m'.m.Keys :: m'.OwnersLineKV(z, m'.m[z]);  //NOT-OK



  v.ValidMeansAllFieldsValid();
  assert v.AllFieldsValid();
  assert v.Valid();
  assert v.Ready(); //should be trivial!
  assert v.Context(m'.hns()); //or umm.

forall x <- m'.oHeap | x != v ensures (x.Ready() && x.Valid() && x.Context(m'.oHeap))
  {
    assert (x.Ready() && x.Valid() && x.Context(m'.oHeap)) ;
    }

    assert m'.apoCalidse();
    assert m'.preOwners();
    assert m'.preOwners2();
    assert m'.m.Keys <= m'.oHeap;
    assert m'.objectInKlown(m'.o);

forall x <- m'.m.Keys ensures  m'.OwnersLineKV(x, m'.m[x])
  {
    assert   m'.OwnersLineKV(x, m'.m[x]);
  }

forall x <- m'.m.Keys ensures  m'.CalidLineKV(x, m'.m[x])
  {
    assert   m'.CalidLineKV(x, m'.m[x]);
  }

  assert k.fields == old(k.fields);  assert k.fields.Keys == old(k.fields.Keys);

  assert m'.HeapContextReady();
  assert m'.ValuesContextReady();
  assert m'.CalidOwners();  //NOT-OK
  assert m'.SuperCalidOwners();
  assert m'.SuperCalidFragilistic(); //HeapContextReady() //AllLinesCalid
}
