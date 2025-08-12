X := MDX11(2, 20, GF(3));

procedure test_Print()
  TSTAssertEQ(
    Sprint(X),
    "The modular curve X_1(2, 20) over Finite field of size 3"
  );
end procedure;

procedure test_MDX11()
  TSTAssertRaises(
    MDX11,
    "doesn't seem to contain a primitive ",
    3, 15, GF(17)
  );
end procedure;

procedure test_Level()
  TSTAssertEQ(Level(X), 20);
end procedure;

procedure test_Genus()
  TSTAssertEQ(Genus(X), 9);
end procedure;

procedure test_LevelStructure()
   x := Places(Curve(X), 4)[2];
   PQ := LevelStructure(X, x);
   TSTAssertEQ(Order(PQ`P), 2);
   TSTAssertEQ(Order(PQ`Q), 20);
   TSTAssertNE(PQ`P,10*PQ`Q);
end procedure;

procedure test_ModuliPoint()
   x := Places(Curve(X), 4)[2];
   E := EllipticCurve(X,x);
   PQ := LevelStructure(X, x);
   TSTAssertEQ(ModuliPoint(X, E, PQ), x);
end procedure;

procedure test_ApplyIsogeny()
   x := Places(Curve(X), 4)[3];
   E := EllipticCurve(X,x);
   PQ := LevelStructure(X, x);
   phi := MDIsogenies(E,7)[1];
   phi_t:=  DualIsogeny(phi);
   PQ1 := ApplyIsogeny(X, phi, PQ);
   PQ2 := ApplyIsogeny(X, phi_t, PQ1);
   E1 := Codomain(phi_t);
   // applying phi and then phi_t should
   // be multiplication by deg phi = 7.
   TSTAssertEQ(E1 ! (7*PQ`P), PQ2`P);
   TSTAssertEQ(E1 ! (7*PQ`Q), PQ2`Q);
end procedure;

procedure test_HeckeOperatorPlcCrvElt()
   X := MDX11(2, 14, GF(5));
   x := Places(Curve(X), 2)[18];
   TpX := HeckeOperator(X, 3, x);
   TSTAssertEQ(Degree(TpX), 8);
end procedure;

procedure test_HeckeOperatorDivCrvElt()
   X := MDX11(2, 14, GF(5));
   x := &+Places(Curve(X), 2)[17..18];
   TpX := HeckeOperator(X, 3, x);
   TSTAssertEQ(Degree(TpX), 16);
end procedure;

procedure test_DiamondOperatorPlcCrvElt()
   X := MDX11(2, 14, GF(5));
   x := Places(Curve(X), 2)[18];
   dx := DiamondOperator(X, 3, x);
   ddx := DiamondOperator(X, 5, dx);
   TSTAssertEQ(x, ddx);
end procedure;

procedure test_DiamondOperatorDivCrvElt()
   X := MDX11(2, 14, GF(5));
   x := &+Places(Curve(X), 2)[17..18];
   dx := DiamondOperator(X, 3, x);
   ddx := DiamondOperator(X, 5, dx);
   TSTAssertEQ(x, ddx);
end procedure;

procedure test_Cusps()
   X := MDX11(2, 20, GF(7));
   cusp_degrees := Sort([Degree(c) : c in Cusps(X)]);
   TSTAssertEQ(cusp_degrees,  [ 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 4, 4 ]);
end procedure;

test_Print();
test_MDX11();
test_Level();
test_Genus();
test_LevelStructure();
test_ModuliPoint();
test_ApplyIsogeny();
test_HeckeOperatorPlcCrvElt();
test_HeckeOperatorDivCrvElt();
test_DiamondOperatorPlcCrvElt();
test_DiamondOperatorDivCrvElt();
test_Cusps();
