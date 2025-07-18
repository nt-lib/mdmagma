// Base type for a all MDMagma modular curves
declare type MDCrvMod;
declare attributes MDCrvMod: level, curve, _E;

intrinsic Print(X::MDCrvMod)
{ Print X }
    printf "The MDCrvMod class shouldn't be used directly";
end intrinsic;

intrinsic _InitMDCrvMod(X::MDCrvMod, level::RngIntElt, curve::CrvPln, _E)
{Initialize an MDCrvMod object}
   char := Characteristic(BaseRing(curve));
   if char gt 0 then
     assert GCD(level, char) eq 1;
   end if;
   _InitMDCrvMod(X, level);
   X`curve := curve;
   X`_E := _E;
end intrinsic;

intrinsic _InitMDCrvMod(X::MDCrvMod, level::RngIntElt)
{Initialize an MDCrvMod object}
   X`level := level;
end intrinsic;

intrinsic Level(X::MDCrvMod) -> RngIntElt
{ Return the level }
    return X`level;
end intrinsic;

intrinsic Curve(X::MDCrvMod) -> CrvPln
{ Return the underlying CrvPln object used for calculations with this modular curve }
    return X`curve;
end intrinsic;

intrinsic Genus(X::MDCrvMod) -> CrvPln
{ Return the genus of this modular curve }
    return Genus(X`curve);
end intrinsic;

intrinsic BaseRing(X::MDCrvMod) -> Rng
{ Return the base ring over which this modular curve is defined }
    return (assigned X`curve ) select BaseRing(X`curve)  else "<unassigned>";
end intrinsic;

intrinsic EllipticCurve(X::MDCrvMod, x::PlcCrvElt) -> CrvEll
{ Return the elliptic curve corresponding to the place x on X }
    E := EllipticCurve([Evaluate(f, x) : f in X`_E]);
    return E;
end intrinsic;

intrinsic  jInvariantMap(X::MDCrvMod) -> CrvEll
{ Return the jInvariant map to X(1) }
    E := EllipticCurve(X`_E);
    return jInvariant(E);
end intrinsic;

intrinsic  jInvariant(X::MDCrvMod, x::PlcCrvElt) -> FldElt
{ Return the jInvariant of the elliptic curve corresponding to E }
    E := EllipticCurve(X, x);
    return jInvariant(E);
end intrinsic;

intrinsic  DiscriminantMap(X::MDCrvMod) -> CrvEll
{ Return the discriminant of the universal elliptic curve over X }
    E := EllipticCurve(X`_E);
    return Discriminant(E);
end intrinsic

intrinsic IsCusp(X::MDCrvMod, x::PlcCrvElt) -> BoolElt
{ Returns whether the place x on X  is a cusp}
    try
      E := EllipticCurve(X,x);
    catch e;
      return true;
    end try;
    return false;
end intrinsic;

intrinsic NoncuspidalPlaces(X::MDCrvMod, d::RngIntElt) -> SeqEnum[PlcCrvElt]
{ Return the noncuspidal places of degree d on X}
    return [x : x in Places(Curve(X), d) | not IsCusp(X, x)];
end intrinsic;

intrinsic Cusps(X::MDCrvMod, d::RngIntElt) -> SeqEnum[PlcCrvElt]
{ The cusps of degree d on this modular curve }
    return [C : C in Cusps(X) | Degree(C) eq d];
end intrinsic;

intrinsic HeckeOperator(X::MDCrvMod, p::RngIntElt, x::PlcCrvElt) -> DivCrvElt
{ Return the result of applying the hecke operator T_p on x as a divisor on X }
    char := Characteristic(BaseRing(X));
    if char gt 0 then
      assert GCD(char, p) eq 1;
    end if;
    ZZ := Integers();
    d := Degree(x);
    E := EllipticCurve(X, x);
    L := LevelStructure(X, x);
    isogenies := MDIsogenies(E,p);
    tp := [<Codomain(phi),ApplyIsogeny(X, phi, L)> : phi in isogenies];
    // the below doesn't work since magma has a bug where equal elements are not
    // identified in the multiset below.
    // tp := Multiset([ModuliPoint(X, EL[1], EL[2]): EL in tp]);
    tp := MDMultiset([ModuliPoint(X, EL[1], EL[2]): EL in tp]);
    Tpx := &+[ (ZZ ! (Multiplicity(tp,x)*d/Degree(x)))*x : x in MultisetToSet(tp)];
    return Tpx;
end intrinsic;

intrinsic HeckeOperator(X::MDCrvMod, p::RngIntElt, D::DivCrvElt) -> DivCrvElt
{ Return the result of applying the hecke operator T_p on D as a divisor on X }
    a,b := Support(D);
    TpD := [b[i]*HeckeOperator(X, p, a[i]) : i in [1..#a]];
    return &+TpD;
end intrinsic;

intrinsic DiamondOperator(X::MDCrvMod, d::RngIntElt, x::PlcCrvElt) -> PlcCrvElt
{ Return the result of applying the diamond operator <d> on x as a place on X }
    E := EllipticCurve(X, x);
    L := LevelStructure(X, x);
    return ModuliPoint(X, E, DiamondOperator(X, d, L));
end intrinsic;

intrinsic DiamondOperator(X::MDCrvMod, d::RngIntElt, D::DivCrvElt) -> DivCrvElt
{ Return the result of applying the diamond operator <d> on D as a divisor on X }
    a,b := Support(D);
    dD := [b[i]*DiamondOperator(X, d, a[i]) : i in [1..#a]];
    return &+dD;
end intrinsic;

intrinsic DiamondOrbit(X::MDCrvMod, x::PlcCrvElt) -> SeqEnum[PlcCrvElt]
{ Return the orbit of x under the diamond operators }
    E := EllipticCurve(X, x);
    L := LevelStructure(X, x);
    N := Level(X);
    diamonds := [i : i in [1..(N div 2)] | GCD(i,N) eq 1];
    return [ModuliPoint(X, E, DiamondOperator(X, d, L)) : d in diamonds];
end intrinsic;

intrinsic PlacesUpToDiamond(X::MDCrvMod, S::SeqEnum[PlcCrvElt]) -> SeqEnum[PlcCrvElt]
{ Return one representative of each orbit in S under the action of the diamond operators }
    representatives := [];
    orbits := AssociativeArray();
    // the orbits are grouped by minimap polynomial of the j-invariant to speed up
    // everything
    N := Level(X);
    F := PrimeField(BaseRing(X));
    diamonds := [i : i in [1..(N div 2)] | GCD(i,N) eq 1];
    for P in S do
        already_added := false;
        jP := MinimalPolynomial(jInvariant(X,P),F);
        if IsDefined(orbits, jP) then
            if P in orbits[jP] then
                already_added := true;
            end if;
        end if;
        if not already_added then
            Append(~representatives, P);
            orbit := DiamondOrbit(X, P);
            if IsDefined(orbits, jP) then
                orbits[jP] :=  orbits[jP] cat orbit;
            else
                orbits[jP] :=  orbit;
            end if;
        end if;
    end for;
    return representatives;
end intrinsic;

intrinsic NoncuspidalPlacesUpToDiamond(X::MDCrvMod, d::RngIntElt) -> SeqEnum[PlcCrvElt]
{ Return the noncuspidal places of degree d on X up to the action of the diamond operators}
     return PlacesUpToDiamond(X, NoncuspidalPlaces(X,d));
end intrinsic;

intrinsic DegeneracyMap(X::MDCrvMod, Y::MDCrvMod, D::DivCrvElt) -> DivCrvElt
{ Return the result of applying the degeneracy map on the level of divisors on X, see
  the documentation where D is a PlcCrvElt for more details.
}
    a,b := Support(D);
    dD := [b[i]*DegeneracyMap(X, Y, a[i]) : i in [1..#a]];
    return &+dD;
end intrinsic;

intrinsic ClassGroup(X::MDCrvMod : as_tuple := false) -> GrpAb, Map, Map
{ Return the class group of the curve underlying X
}
    if not assigned X`_classgroup then
        G, m1, m2 := ClassGroup(Curve(X));
        X`_classgroup := <G, m1, m2>;
    end if;
    if as_tuple then
        return X`_classgroup;
    end if;
    return Explode(X`_classgroup);
end intrinsic;

intrinsic CuspidalClassGroupQ(X::MDCrvMod) -> GrpAb, Map, Map
{ Return the subgroup of the class group of X generated by Gal(Q) orbits of cusps,
  See also CuspOrbitsQ(X).
}
    cusps := CuspOrbitsQ(X);
    return MDClassGroup(Curve(X),  cusps: classgroup:=ClassGroup(X : as_tuple:=true));
end intrinsic;

intrinsic CuspidalClassGroup(X::MDCrvMod, d::RngIntElt) -> GrpAb, Map, Map
{ Return the subgroup of the class group of X generated by the cusps of degree dividing d
}
    cusps := &cat [Cusps(X,d1) : d1 in Divisors(d)];
    return MDClassGroup(Curve(X),  cusps: classgroup:=ClassGroup(X : as_tuple:=true));
end intrinsic;
