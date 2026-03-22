include "Object.dfy"

method Main()
{
  var frame := new Object.make(fields({"counter"}), {}, {}, "frame");

  frame.setn("counter", 0);
  frame.setn("counter", 1 + frame.getn("counter"));

}


method NotMain()
 {
    var counter : nat := 0;
    counter := counter + 1;
 }

const application : Owner := {}

method LinkedList() {

var list  := new Object.make(fields({"head", "tail"}), application, application, "list");

var link0 := new Object.make(fields({"next", "data"}), {list}, {list}, "link0", {} );
var link1 := new Object.make(fields({"next", "data"}), {list}, {list}, "link1", {} );
var link2 := new Object.make(fields({"next", "data"}), {list}, {list}, "link2", {} );
var link3 := new Object.make(fields({"next", "data"}), {list}, {list}, "link3", {} );

 list.setf("head", link0); list.setf("tail", link3);

 link0.setf("next", link1); link1.setf("next", link2); link2.setf("next", link3);

}

type RObject = r : Object? | (r != null) && r.Ready() witness *

lemma Paper_NoIncomingPointers(f : RObject,
  o : RObject,
  t : RObject)

  requires outside(f,o)
  requires strictlyInside(t,o)

  ensures f != null
  ensures f is Object

   ensures not(refOK(f,t))
{}


method Paper_add(a : nat, b : nat) {





  var c := a + b;
  print "c == ", c, "\n";


}

type Frame = Object
type U = Owner

predicate without(frame : Frame, u : U)  {
 // frame !in u
 true
}

method drop(frame : Frame, u : U)
 ensures without(frame, u)
{
//  assume without(frame, u);
}

method {:isolate_assertions} {:timeLimit 30} Paper_Embedded_add(a : nat, b : nat, caller : Frame, u : U)
    returns(frame : Frame) ensures without(frame, u)
    requires caller.Ready()
    requires u >= flatten({caller})
  {
      frame := new Object.make(fields({"a","b","c"}), {caller}, u, "", {});
      frame.setn("a", a);
      frame.setn("b", b);
      frame.setn("c", frame.getn("a") + frame.getn("b"));
      print "c == ",  frame.getn("c"), "\n";
      drop(frame,u);
  }



const listX : map<string, Mode> := fields({"head"})
const linkX : map<string, Mode> := fields({"data","next"})
lemma shitX()
  ensures listX == fields({"head"})
  ensures "head" in listX
  ensures linkX == fields({"data","next"})
  ensures "next"  in linkX
 {}

method {:isolate_assertions} {:timeLimit 30} MakeList(caller : Frame, u : U)
    returns(frame : Frame) ensures without(frame, u)
    requires caller.Ready()
    requires caller.bound == caller.owner
    requires "ret" in caller.fieldModes.Keys
    requires u >= flatten({  caller   })
    modifies caller
  {
    frame := new Object.make(fields({"list"}), {caller}, u, "", {});

    var list  := new Object.make(listX, {caller}, u, "list", caller.bound);

    assert nuBoundsOK({list}, {   });   ///attempting to get verification times down;

    var i := new Object.make(linkX, {list}, flatten({list}), "i", {} );
    var j := new Object.make(linkX, {list}, flatten({list}), "j", {} );

    frame.setf("list", list);
    list.setf("head", i);
    i.setf("next", j);

    caller.setf("ret", frame.getf("list"));
    drop(frame,u);
  }



method {:isolate_assertions} {:timeLimit 30} list_method(list : Object, caller : Frame, u : U)
      returns(frame : Frame) ensures without(frame, u)
      requires caller.Ready()
      requires u >= flatten({  caller, list   })
                                                                                                                                                                                                                                                                                                                                                                                     requires AllReady({caller,list})
      requires nuBoundsOK({caller},{caller})
//NO_FIELDMODES      requires list.fieldModes == listX
      requires list.ownerf("head", {list})
      requires "ret" in caller.fieldModes.Keys
      requires refOK(caller, list)
      modifies list, caller
    {
      frame := new Object.make(fields({"list","n","link"}), {caller,list}, flatten({caller,list}+u), "", {caller,list});
                          assert frame.owner == {list, caller};
                          assert refOK(frame, list);
      frame.setf("list", list);
                         assert frame.fields == map["list":=list];
                         assert frame.fields["list"] == list;
                         assert frame.ownerf("list", list.owner);
      frame.setn("n", 0);
                         assert "list" in frame.fields;
                         assert frame.fields["list"] == list;
                         assert list.ownerf("head", {list});

      if ( frame.getf("list").isf("head") )
        {
            frame.incrn("n");
                            assert frame.fields["list"] == list;
                            assert frame.getf("list") == list;
                            var current_link := frame.getf("list").getf("head");
                            assert current_link == list.getf("head");
                            assert current_link.owner == {list};
                            assert frame.owner == {list, caller};
                            assert refBI(frame, current_link);
                            assert refOK(frame, current_link);


            frame.setf("link", frame.getf("list").getf("head"));
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            expect frame.ownerf("link", {list});
                            assert frame.ownerf("link", {list});
                            assert frame.fields["link"] == current_link;
                            var gas : nat := 100;


              while ( frame.getf("link").isf("next")  && gas > 1)
                            decreases gas
                            invariant frame.Valid()
                            invariant frame.isf("link")
                            invariant frame.fields["link"] == current_link
                            invariant frame.getf("link") == current_link
                            invariant frame.ownerf("link", {list})

              {
                            assert current_link.isf("next");
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            assert frame.ownerf("link", {list});
                            assert current_link.owner == {list};
                            gas := gas - 1;
                frame.incrn("n");
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            assert frame.ownerf("link", {list});
                            assert current_link.owner == {list};
                            assert frame.owner == {list, caller};

              } //while
         } //if
        drop(frame,u);
    }

//
// predicate allCompatible(oo : Owner)
// { forall a <- oo, b <- oo :: (a != b) ==> compatible(a,b) }
//
//
// predicate isThread(a : Object) reads a`fieldModes {"THRED" in a.fieldModes.Keys}
//
//
// predicate compatible(a : Object, b : Object)
//  reads a`fieldModes, b`fieldModes
//   { not(isThread(a) && isThread(b)) }

type Thread = Object

lemma {:isolate_assertions} {:timeLimit 30} ThreadSafe(ta : Thread, tb : Thread, a : Object, b : Object)
   requires ta.Ready() && tb.Ready() && a.Ready() && b.Ready()
   requires ta != tb
   requires isThread(ta)
   requires isThread(tb)
   requires strictlyInside(a,ta)
   requires strictlyInside(b,tb)
  //  requires inside(a,ta)
  //  requires inside(b,tb)
   requires allCompatible(a.AMFO)
   requires allCompatible(b.AMFO)
    ensures not(refOK(a,b))
  {
    assert not(compatible(ta,tb));
    // assert a.AMFO >= ta.AMFO;
    // assert ta in ta.AMFO;
    // assert b.AMFO >= tb.AMFO;
    // assert tb in tb.AMFO;
    // assert ta in a.AMFO;
    // assert tb in b.AMFO;

    // if (a == b) {
    //     assert ta in a.AMFO;
    //     assert tb in a.AMFO;
    //     assert allCompatible(a.AMFO);
    //     assert false;
    // }


  }
