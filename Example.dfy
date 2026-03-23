        include "Object.dfy"
include "Printing.dfy"
include "Ownership-Recursive.dfy"

method  {:isolate_assertions} ExampleMain(args : seq<string>)
{
  print "Yaunch\n";

  var frame := new Object.make(fields({"counter","ret"}), {}, {}, "top");

  frame.setn("counter", 0);
  frame.setn("counter", 1 + frame.getn("counter"));
  print "1 == ", frame.getn("counter"), "\n";
  frame.setn("counter", 41 + frame.getn("counter"));
  print "42 == ", frame.getn("counter"), "\n";

  print "c should be *33* ";
  var deadFrame := Paper_Embedded_add(11,22,frame,{frame});

  deadFrame := MakeList(frame,{frame});
  print "Makelist returns - ret shoudl be    list\n";
  printobject(frame);

print "PRUNTOBBJ-OJECT\n";

var list : Object;

assert frame.ownerf("ret", {frame});

print "TRAVERSE\n";
print "frame.fields=", frame.fields, "\n";
print "frame.fields.Keys=", fmtsetstr(frame.fields.Keys),"\n";
print "retrieving link_1\n";
list := frame.fields["ret"];
assume list.Ready();  //READYREADY
print "got frame.fields[\"ret\"]",fmtobj(list),"\n";
printobject(list);
    assume ("head" in list.fields.Keys);
    var link1 := list.getf("head");
                          print "GOT LKINK1\n";
        printobject(link1);
    assume ("next" in link1.fields.Keys);
    var link2 := link1.getf("next");
    print "GOT LKINK2\n";
    printobject(link2);
    print "\nrefOK list->link1 ", refOK(list,link1);
    print "\nrefOK list->link2 ", refOK(list,link2);
    print "\nrefOK link1->link2 ", refOK(link1,link2);
    print "\nrefOK link2->link1 ", refOK(link2,link1);
    print "\nrefOK link1->list ", refOK(link1,list);
    print "\nrefOK link2->list ", refOK(link2,list);
    print "\n";


assert frame.ownerf("ret", {frame});

expect list.ownerf("head", {list});
assert list.ownerf("head", {list});

  deadFrame := list_method(list,frame,flatten({list,frame}));

printobject(deadFrame);

  print "Mulberry\n";

}

method NotMain2()
 {
    var counter : nat := 0;
    counter := counter + 1;
 }

const application : Owner := {}

method LinkedList() {

var list  := new Object.make(fields({"head", "tail"   }), application, application, "list");

var link0 := new Object.make(fields({"next", "data"}), {list}, {list}, "link0", {list} );
var link1 := new Object.make(fields({"next", "data"}), {list}, {list}, "link1", {list} );
var link2 := new Object.make(fields({"next", "data"}), {list}, {list}, "link2", {list} );
var link3 := new Object.make(fields({"next", "data"}), {list}, {list}, "link3", {list} );

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

method {:isolate_assertions} {:timeLimit 10} Paper_Embedded_add(a : nat, b : nat, caller : Frame, u : U)
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
    requires caller.Valid()
    requires caller.bound == caller.owner
    requires "ret" in caller.fieldModes.Keys
    requires u >= flatten({  caller   })
     ensures caller.ownerf("ret", {caller})
    modifies caller
  {
    assert CV: caller.Valid();
    frame := new Object.make(fields({"list"}), {caller}, u, "", {caller});
    var list  := new Object.make(listX, {caller}, u, "list", {caller});
    assert list.owner == {caller};
    frame.setf("list", list);
assert caller.Valid() by { reveal CV; }  assert list.owner == {caller};  assert frame.fields["list"] == list;
    assert nuBoundsOK({list}, {list});   ///attempting to get verification times down;

    var i := new Object.make(linkX, {list}, flatten({list}), "i", {list} );
    var j := new Object.make(linkX, {list}, flatten({list}), "j", {list} );  assert JV: j.Valid();
    var k := new Object.make(linkX, {list}, flatten({list}), "k", {list} );
    var l := new Object.make(linkX, {list}, flatten({list}), "l", {list} );
assert caller.Valid() by { reveal CV; }
    list.setf("head", i);
    i.setf("next", j);
    j.setf("next", k) by { reveal JV; assert j.Valid(); }
    k.setf("next", l);

assume caller.Valid(); assume frame.fields["list"] == list;  assume list.owner == {caller};
    caller.setf("ret", frame.getf("list"));
    assert caller.ownerf("ret", {caller});
    drop(frame,u);
  }


lemma DifferentOwnersDifferentObjects(a : Object, b : Object)
  requires a.owner != b.owner
   ensures a != b
{}

method {:isolate_assertions} {:timeLimit 30} list_method(list : Object, caller : Frame, u : U)
      returns(frame : Frame) ensures without(frame, u)
      requires caller.Ready()
      requires list.Ready()
      requires list != caller
      requires AllReady(u)
      requires u >= flatten({  caller, list   })
      requires nuBoundsOK({caller},{caller})
//NO_FIELDMODES      requires list.fieldModes == listX
      requires list.ownerf("head", {list})
      requires list.bound == list.owner
//NO_FIELDMODES            requires "ret" in caller.fieldModes.Keys
      requires refOK(caller, list)
      modifies list, caller
    {
      frame := new Object.make(fields({"list","n","link"}), {caller,list}, flatten({caller,list}+u), "frame", {caller,list});
                          assert frame.owner == {list, caller};
                          assert refOK(frame, list);

assert forall o <- u :: o != frame;

      frame.setf("list", list);
                         assert frame.fields == map["list":=list];
                         assert frame.fields["list"] == list;
                         assert frame.ownerf("list", list.owner);
      frame.setn("n", 0);
                         assert "list" in frame.fields;
                         assert frame.fields["list"] == list;
                         assert list.ownerf("head", {list});

 assert frame.Valid();

      if ( frame.getf("list").isf("head") )
        {
            frame.incrn("n");
                            assert frame.fields["list"] == list;
                            assert frame.getf("list") == list;
                            assert frame.owner == frame.bound == {list, caller};
                            assert FO: frame.owner == frame.bound == {list, caller};
                            var current_link := frame.getf("list").getf("head");
                            assert current_link.Ready();
                            assert current_link == list.getf("head");
                            assert current_link.owner == current_link.bound == {list};
                            assert CL: current_link.owner == current_link.bound == {list};
                            DifferentOwnersDifferentObjects(frame,current_link) by
                                {
                                  reveal FO, CL;
                                  assert frame.owner == frame.bound == {list, caller};
                                  assert current_link.owner == current_link.bound == {list};
                                  assert {list} != {list, caller};
                                }
                            assert refBI(frame, current_link);
                            assert refOK(frame, current_link);

 assert frame.Valid();

            frame.setf("link", frame.getf("list").getf("head"));

 assert frame.Valid();
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            expect frame.ownerf("link", {list});
                            assert frame.ownerf("link", {list});
                            assert frame.fields["link"] == current_link;
                            assert current_link.owner == current_link.bound == {list};
                            assert frame.fields["link"].owner == frame.fields["link"].bound == {list};
                            var gas : nat := 100;

              while ( frame.getf("link").isf("next")  && gas > 1)
                            decreases gas
                            invariant frame.Valid()
                            invariant frame.isf("link")
                            invariant frame.fields["link"] == current_link
                            invariant frame.getf("link") == current_link
                            invariant frame.ownerf("link", {list})
                            invariant frame.owner == frame.bound == {caller, list}
                            invariant frame.fields["link"].owner == frame.fields["link"].bound == {list}
                            invariant current_link.Ready()
                            invariant current_link.owner == current_link.bound == {list}
                            invariant current_link != frame
              {
                            assert current_link.isf("next");
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            assert frame.ownerf("link", {list});
                            assert current_link.owner == current_link.bound == {list};
                            assert frame.fields["link"].owner == frame.fields["link"].bound == {list};
                            assert frame.owner == frame.bound == {caller, list};

                            print "HOP  ", fmtobj(frame), " ", fmtobj(current_link), " ", current_link.isf("next"), "\n";

 assert frame.Valid();

                            gas := gas - 1;
                frame.incrn("n");
                        //    assert frame.Valid();
 assert frame.Valid();
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            assert frame.ownerf("link", {list});
                            assert current_link.owner == current_link.bound == {list};
                            assert frame.fields["link"].owner == frame.fields["link"].bound == {list};
                            assert frame.owner == frame.bound == {caller, list};

                            expect current_link.ownerf("next", {list});
                            assert current_link.ownerf("next", {list});
                            current_link := current_link.fields["next"]; assume current_link.Ready();
                            printobject(frame); printobject(current_link);
                            assert current_link.owner == current_link.bound == {list};
                            assert current_link.Ready();
                            assert current_link.AMFX == flatten(current_link.owner) == flatten({list}) == list.AMFO;
                            assert current_link.AMFB == flatten(current_link.bound) == flatten({list}) == list.AMFO         ;
                            assert current_link.owner == {list};  assert current_link.AMFX == list.AMFO;
                            print (current_link.AMFX == current_link.AMFB == flatten({list}) == ({list} + flatten(list.owner)) == (list.AMFO)), "<<<===\n";
                            assert current_link.AMFX == current_link.AMFB == flatten({list}) == ({list} + flatten(list.owner)) == (list.AMFO);
                            assert frame.owner == frame.bound == {caller, list};
                            DifferentOwnersDifferentObjects(frame, current_link);
                            assert current_link != frame;
                            print "SKIP ", fmtobj(frame), " ", fmtobj(current_link), " refOK=", refOK(frame,current_link), " next=", current_link.isf("next"), "\n";
                            assert current_link.owner == {list};
                            assert flatten(current_link.owner) == flatten({list}) == ({list} + flatten(list.owner)) >= flatten(list.owner);
                            assert current_link.AMFX == current_link.AMFB == list.AMFO;
                            assert frame.owner == frame.bound == {caller, list};
                            assert flatten(frame.owner) == flatten({caller, list}) == (flatten({caller}) + flatten({list})) == (flatten({caller}) + ({list} + flatten(list.owner)));
                            assert frame.Ready();
                            assert flatten({frame}) == frame.AMFO == ({frame} + flatten(frame.owner));
                            assert frame.AMFX == frame.AMFB == (caller.AMFO + list.AMFO) >= list.AMFO > list.AMFX;
                            assert frame.AMFB == (caller.AMFO + list.AMFO);
                            assert current_link.owner == {list};   assert flatten(current_link.owner) == flatten({list}) == list.AMFO;
                            assert current_link.AMFX == list.AMFO;
                            assert (caller.AMFO + list.AMFO) >= list.AMFO;
                            assert frame.AMFB >= current_link.AMFX;
                            assert frame != list;
                            assert frame != current_link;
                            assert refBI(frame, current_link);
                            assert refOK(frame,current_link);
                            print "FUCKER ", refOK(frame,current_link), "\n";
 assert frame.Valid();

                frame.setf("link", frame.getf("link").getf("next"));

 assert frame.Valid();
                            print "JUMP\n";
                            assert frame.fields["link"] == current_link;
                            assert frame.getf("link") == current_link;
                            assert frame.ownerf("link", {list});
                            assert current_link.owner == current_link.bound == {list};
                            assert frame.fields["link"].owner == frame.fields["link"].bound == {list};
                            assert frame.owner == frame.bound == {caller, list};

//                          assume frame.Valid();
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
