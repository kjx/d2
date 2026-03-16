include "Ownership.dfy"


lemma FlattenIsFlat(os : Owner)
  requires AllReady(os)
   ensures isFlat(flatten(os))
  {
    var fs := flatten(os);
    assert os <= fs;
    assert (set o <- os, oo <- o.AMFO :: oo) <= fs;
    assert fs == (set o <- os, oo <- o.AMFO :: oo) + os;
    assert forall o : Object <- os, oo : Object <- o.AMFO :: oo in fs;
    assert forall o : Object <- fs, oo : Object <- o.AMFO :: oo in fs;
    assert isFlat(fs);
    assert isFlat(flatten(os));
  }


lemma FlattenIsOwners0(os : Owner)
  requires AllReady(os)
   ensures os <= (flatten(os))
   ensures flatten(os) + os == flatten(os)
{}

lemma FlattenIsOwners1(os : Owner)
  requires (forall o <- os :: o in o.AMFO)
   ensures os <= (set o <- os, oo <- o.AMFO :: oo)
   ensures (set o <- os, oo <- o.AMFO :: oo)  + os == (set o <- os, oo <- o.AMFO :: oo)
{}



lemma AllReadyMeansEachObject0(os : Owner)
  ensures forall o <- os :: o.Ready() ==> (o in o.AMFO)
{}

lemma AllReadyMeansEachObject1(os : Owner)
 requires AllReady(os)
  ensures forall o <- os :: o in o.AMFO
{}
