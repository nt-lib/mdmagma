X := New(MDCrvMod);
X`level := 1;

/*
procedure test_AttributeAsString_assigned()
  attr := MDAttributeAsString(X, "base_ring", "Default");
  TSTAssertEQ(attr, "1");
end procedure;
*/

procedure test_AttributeAsString_unassigned()
  attr := MDAttributeAsString(X, "", "Default");
  TSTAssertEQ(attr, "<unassigned>");
end procedure;

procedure test_MDMagmaSourceDir()
  source_dir := MDMagmaSourceDir();
  TSTAssertEQ(s[#s] where s := Split(source_dir,"/"), "v2");
end procedure;

procedure test_MDMultiset()
  A<x,y> := AffineSpace(GF(2),2);
  C := Curve(A, x-y);
  CF4 := RationalPoints(C,GF(4));
  S := MDMultiset([Places(P)[1] : P in CF4]);
  // this is the expected behaviour since CF4 contains two GF(2) points and a pair
  // of galois conjugate points over GF(4)
  TSTAssertEQ({Multiplicity(S,x) : x in S}, {1,2});
  S := Multiset([Places(P)[1] : P in CF4]);
  // magma correctly identifies conjugate points as the same place since V2.29-4
  TSTAssertEQ({Multiplicity(S,x) : x in S}, {1,2});
end procedure;

procedure test_MDValues()
    A := AssociativeArray();
    A["a"] := 1;
    A["b"] := 2;
    TSTAssertEQ(Sort(MDValues(A)), [1, 2]);
end procedure;

//test_AttributeAsString_assigned();
test_AttributeAsString_unassigned();
test_MDMagmaSourceDir();
test_MDMultiset();
test_MDValues();
