
declare type MDCrvMod1: MDCrvMod;
declare attributes MDCrvMod1:level, curve, N, _E, _P,
    _coordinates, _coordinates_xy, _coordinates_F2F3, _cusp_data, _classgroup;

X1LevelStructure := recformat< P : PtEll>;


intrinsic Print(X::MDCrvMod1)
{Print X}
   base_ring := BaseRing(X);
   printf "The modular curve X_1(%o) over %o", X`N,  base_ring;
end intrinsic;

intrinsic MDX1(N::RngIntElt, base_ring::Rng) -> MDCrvMod1
{ Create the modular curve X_1(N) }
  require N ge 10: "X_1(N) is only implemented for N >= 10";
  X := New(MDCrvMod1);
  _InitMDCrvMod1(X, N, base_ring);
  return X;
end intrinsic;

intrinsic _InitMDCrvMod1(X::MDCrvMod1, N::RngIntElt,
    base_ring::Rng: equation_directory:="")
{Initialize an MDCrvMod1 object}
    X`N := N;
    curve, E, P, coordinates, coordinates_xy, coordinates_F2F3 := _equation_X1(
        N,base_ring : equation_directory:=equation_directory
    );
    X`_P := P;
    X`_coordinates := coordinates;
    X`_coordinates_xy := coordinates_xy;
    X`_coordinates_F2F3 := coordinates_F2F3;
    _InitMDCrvMod(X, N,  curve, E);
end intrinsic;

intrinsic LevelStructure(X::MDCrvMod1, x::PlcCrvElt) -> Rec
{   Return the level structure corresponding to the place x on Y1(N).
    To be precise. It returns is a RecFormat r such that r`P is a point of order N.
    It raises an error if x is a cusp.
}
    Ex := EllipticCurve(X, x);
    Px := Ex ! [Evaluate(f, x) : f in X`_P];
    return rec<X1LevelStructure | P := Px>;
end intrinsic;


intrinsic ModuliPoint(X::MDCrvMod1, E::CrvEll, levelstructure::Rec) -> PlcCrvElt
{   Return the place x on X1(N), corresponding to the pair (E, levelstructure).
    It assumes that levelstructure is a RecFormat  such that levelstructure`P is a point
    of order N.
}
    K := BaseRing(E);
    xy := TateNormalForm_xy(E, levelstructure`P);
    dP := Places(Curve(X)(K) ! xy);
    assert #dP eq 1;
    return dP[1];
end intrinsic;

intrinsic TateNormalForm_bc(E::CrvEll, P::PtEll) -> Seq
{ Return the b,c of the tate normal form of (E,P) as in equation (2) of http://arxiv.org/pdf/1307.5719v1.pdf }
    assert P[3] eq 1;
    x0:=P[1];
    y0:=P[2];

    a1,a2,a3,a4,a6:=Explode(aInvariants(E));
    aa1:=a1;
    aa3:=2*y0+a3+a1*x0;
    aa2:=3*x0+a2;
    aa4:=3*x0^2+2*x0*a2+a4-a1*y0;

    aaa1:=2*aa4/aa3+aa1;
    aaa3:=aa3;
    aaa2:=aa2-(aa4/aa3)^2-aa1*aa4/aa3;


    b:=-aaa2^3/aaa3^2;
    c:=-(aaa1*aaa2-aaa3)/aaa3;
    return [b,c];
end intrinsic;

intrinsic TateNormalForm_xy(E::CrvEll, P::PtEll) -> Seq
{ return the x,y of the tate normal form of (E,P) as in section 2.1 http://arxiv.org/pdf/1307.5719v1.pdf }
    b,c := Explode(TateNormalForm_bc(E,P));
    r := b/c;
    s := c^2/(b-c);
    t := (r*s-2*r+1);
    x := (s-r)/t;
    y := t/(s^2-s-r+1);
    return [x,y];
end intrinsic;


intrinsic ApplyIsogeny(X::MDCrvMod1, phi:: MapSch[CrvEll, CrvEll], levelstructure::Rec) -> Rec
{   Return the level structure corresponding to phi(levelstructure)
}
    return rec<X1LevelStructure | P := phi(levelstructure`P)>;
end intrinsic;

intrinsic DiamondOperator(X::MDCrvMod1, d::RngIntElt, levelstructure::Rec) -> Rec
{   Return the level structure corresponding to d*P; where d is coprime to the level
}
    require GCD(d, Level(X)) eq 1: "d should be coprime to the level";
    return rec<X1LevelStructure | P := d*levelstructure`P>;
end intrinsic;


intrinsic DegeneracyMap(X::MDCrvMod1, d::RngIntElt, levelstructure::Rec) -> Rec
{   Return the level structure corresponding to d*P; where d is a divisor of the level
}
    assert (Level(X) mod d) eq 0;
    return rec<X1LevelStructure | P := d*levelstructure`P>;
end intrinsic;


intrinsic DegeneracyMap(X::MDCrvMod1, Y::MDCrvMod1, x::PlcCrvElt) -> PlcCrvElt
{ If the place x corresponds to (E,P) the place y corresponding to (E,P*Level(X)/Level(Y))
  taking into account multiplicities. I.e. if deg(y) = deg(x) it returns y, if not
  y deg(x)/deg(y) is returned.}
    M := Level(X);
    N := Level(Y);
    require M mod N eq 0: "the level of Y should divide the level of X";
    E := EllipticCurve(X, x);
    L := LevelStructure(X, x);
    y := ModuliPoint(Y, E, DegeneracyMap(X, M div N, L));
    assert Degree(x) mod Degree(y) eq 0;
    return (Degree(x) div Degree(y))*y;
end intrinsic;

intrinsic _equation_X1(n,base_ring : equation_directory:="") -> CrvPln
{  Input: n - an integer
          base_ring - a ring
          equation_directory - directory with files FFFc<n>.txt containing models
    Output: C - a curve
    Returns an algebraic model C of the modular curve X_1(n) as a curve over base_ring
}
    if equation_directory eq "" then
      equation_directory := MDMagmaSourceDir() cat "/../models_X1_n";
    end if;

    n_str := IntegerToString(n);
    file_name := equation_directory cat "/FFFc" cat n_str cat ".txt";
    data := Read(file_name);

    A<x,y> := AffineSpace(base_ring,2);
    X := eval(data);
    C := Curve(A,X);
    FF := FunctionField(C);
    x := FF.1;
    y := FF.2;
    r := (x^2*y-x*y+y-1)/x/(x*y-1);
    s := (x*y-y+1)/x/y;
    b := r*s*(r-1);
    c := s*(r-1);
    E := [1-c, -b, -b, FF ! 0, FF ! 0];
    P := [FF ! 0, FF ! 0];
    coordinates := [b, c];
    coordinates_xy := [x, y];
    coordinates_F2F3 :=  [b/(16*b^2+(1-20*c-8*c^2)*b + c*(c-1)^3),b];
    return ProjectiveClosure(C), E, P, coordinates, coordinates_xy, coordinates_F2F3;
end intrinsic;

intrinsic CongruenceSubgroup(X::MDCrvMod1) -> GrpPSL2
{ The subgroup of PSL2 corresponding to this modular curve }
    return Gamma1(Level(X));
end intrinsic;

intrinsic Cusps(X::MDCrvMod1) -> SeqEnum[PlcCrvElt]
{ The cusps on this modular curve }
    cusps := Support(Divisor(DiscriminantMap(X)));
    nr_cusps := #Cusps(CongruenceSubgroup(X));
    xy := X`_coordinates_xy;
    cusps := Seqset(cusps cat Poles(xy[1]) cat Poles(xy[2]));
    assert &+[Degree(c) : c in cusps] eq nr_cusps;
    return Setseq(cusps);
end intrinsic;

intrinsic CuspSignature(X::MDCrvMod1, C::PlcCrvElt) -> SeqEnum[RngIntElt]
{ Returns the valuation of F2 and F3 at the place C }
    require IsCusp(X, C) : "C should be a cusp!";
    return [Valuation(f, C) : f in X`_coordinates_F2F3];
end intrinsic;

intrinsic CuspOrbitCountQ(X::MDCrvMod1) -> RngIntElt
{ Returns the number of Galois orbits of cusps of X_1(n) using 2.8(1) of
https://arxiv.org/pdf/2007.13929 . }
    n := Level(X);
    orbits:=0;
    divs:=Divisors(n);
    for d in divs do
        if d eq 1 or d eq 2 then
           orbits:=orbits+1;
        end if;
        if d gt 2 then
           orbits:=orbits+(EulerPhi(d) div 2);
        end if;
    end for;
    return orbits;
end intrinsic;

intrinsic _InitialiseCuspData(X::MDCrvMod1)
{ Compute the signatures of all cusps, and create a lookup table to get the cusps
corresponding to a signature. It raises an error if the signature doesn't uniquely
determine the galois orbit over Q. }
    if assigned X`_cusp_data then
        return;
    end if;
    cusp_data := AssociativeArray();
    for c in Cusps(X) do
        signature :=  CuspSignature(X,c);
        if IsDefined(cusp_data, signature) then
            Append(~cusp_data[signature], c);
        else
            cusp_data[signature] := [c];
        end if;
    end for;
    assert #cusp_data eq CuspOrbitCountQ(X);
    X`_cusp_data := cusp_data;
end intrinsic;

intrinsic _CuspData(X::MDCrvMod1) -> Assoc
{ Return the associative array mapping cusp signatures to cusps }
    _InitialiseCuspData(X);
    return X`_cusp_data;
end intrinsic;

intrinsic CuspsWithSignature(X::MDCrvMod1, signature::SeqEnum[RngIntElt]) -> SeqEnum[PlcCrvElt]
{ Returns the cusps of the given signature }
    _InitialiseCuspData(X);
    return X`_cusp_data[signature];
end intrinsic;

intrinsic IsCuspSignatureUnique(X::MDCrvMod1) -> BoolElt
{ Returns true if and only if there is only one galois orbit of cusps per cusp signature }
    return &and[#c eq 1 : c in MDValues(_CuspData(X))];
end intrinsic;

intrinsic CuspOrbitsQ(X::MDCrvMod1) -> SeqEnum[DivCrvElt]
{ The galois orbits over Q of cusps on this modular curve as divisors. Note that when
  the modular curve is defined over a finite field of positive characteristic one still
  has an action of the galois group over Q.
}
    orbits := [&+c : c in MDValues(_CuspData(X))];
    return orbits;
end intrinsic;

intrinsic HeckeOperatorFast(X::MDCrvMod1, q::RngIntElt, x::PlcCrvElt) -> DivCrvElt
{ Return T_q(x) as a divisor on X, for a non-cuspidal place x, using MDIsogeniesFast.

  Same result as HeckeOperator, but each of the q+1 isogenies is computed over the field
  of definition of its kernel rather than over the splitting field of the whole
  q-division polynomial, and only one isogeny per Frobenius orbit is computed at all:
  the conjugates of a subgroup give conjugate, hence equal, places of X, so one isogeny
  per orbit contributes with multiplicity the size of that orbit.

  Requires q to be an odd prime; for q = 2 use HeckeOperator.
}
    char := Characteristic(BaseRing(X));
    require char gt 0 : "the base ring must be a finite field";
    require IsPrime(q) and IsOdd(q) and GCD(char, q) eq 1 :
        "q must be an odd prime different from the characteristic";
    require GCD(Level(X), q) eq 1 : "q must be coprime to the level";
    ZZ := Integers();
    d := Degree(x);
    E := EllipticCurve(X, x);
    P := LevelStructure(X, x)`P;
    Tqx := DivisorGroup(Curve(X)) ! 0;
    for t in MDIsogeniesFast(E, q) do
        phi, e, F1 := Explode(t);
        EL := Domain(phi); L := BaseRing(EL);
        // P is defined over the base field of E, which sits inside L only through F1
        PL := EL ! [L ! (F1 ! c) : c in Eltseq(P)];
        y := ModuliPoint(X, Codomain(phi), rec<X1LevelStructure | P := phi(PL)>);
        Tqx +:= (ZZ ! (e*d/Degree(y))) * Divisor(y);
    end for;
    assert Degree(Tqx) eq (q+1)*d;
    return Tqx;
end intrinsic;

intrinsic HeckeOperatorFast(X::MDCrvMod1, q::RngIntElt, D::DivCrvElt) -> DivCrvElt
{ Return T_q(D) as a divisor on X, for a divisor D supported on non-cuspidal places }
    a, b := Support(D);
    return &+[b[i]*HeckeOperatorFast(X, q, a[i]) : i in [1..#a]];
end intrinsic;

intrinsic PlacesUpToDiamondFast(X::MDCrvMod1, S::SeqEnum[PlcCrvElt]) -> SeqEnum[PlcCrvElt]
{ Return one representative of each orbit in S under the diamond operators, deciding
  equivalence with isomorphism tests of elliptic curves instead of by computing the
  orbit of every place.

  PlacesUpToDiamond calls ModuliPoint once per diamond operator and per place, that is
  once per function field point; this does no function field work beyond reading off
  (E, P).  Reducing the 756 places of degree 5 of X_1(57) over GF(5) takes 11 seconds
  this way, against an estimated 16 to 21 hours for PlacesUpToDiamond.

  The criterion is that two non-cuspidal places x, x' of the same degree k, given by
  (E, P) over K and (E', P') over K', satisfy x' = <a>x for some a coprime to the level
  exactly when for some power sigma of the Frobenius of K there is an isomorphism
  iota : (E')^sigma -> E over K with iota((P')^sigma) a generator of <P>.  Such an iota
  is automatically defined over K: otherwise iota^F iota^-1 would be a non-trivial
  automorphism of E fixing the K-rational point aP of order N >= 5, while for a
  non-trivial automorphism zeta the kernel of zeta-1 has at most 4 geometric points.
}
    N := Level(X);
    p := #PrimeField(BaseRing(X));
    data := [* *];
    for x in S do
        E := EllipticCurve(X, x);
        data[#data+1] := <E, LevelStructure(X, x)`P,
                          MinimalPolynomial(jInvariant(E), PrimeField(BaseRing(X))),
                          Degree(x)>;
    end for;
    // the diamond operators preserve both the j-invariant and the degree, so grouping by
    // them cannot split an orbit
    groups := AssociativeArray();
    for i in [1..#S] do
        key := <data[i][3], data[i][4]>;
        if IsDefined(groups, key) then
            Append(~groups[key], i);
        else
            groups[key] := [i];
        end if;
    end for;
    representatives := [];
    for key in Keys(groups) do
        indices := groups[key];
        done := [false : i in indices];
        for a in [1..#indices] do
            if done[a] then continue; end if;
            done[a] := true;
            Append(~representatives, S[indices[a]]);
            E1 := data[indices[a]][1];
            P1 := data[indices[a]][2];
            K1 := BaseRing(E1);
            k := Degree(K1);
            generators := {@ c*P1 : c in [1..N-1] | GCD(c, N) eq 1 @};
            for b in [a+1..#indices] do
                if done[b] then continue; end if;
                E2 := data[indices[b]][1];
                P2 := data[indices[b]][2];
                K2 := BaseRing(E2);
                if K2 cmpeq K1 then
                    ainvs := aInvariants(E2); coords := Eltseq(P2);
                else
                    // the two places have the same degree, so K2 and K1 are isomorphic
                    ok := true;
                    try
                        ainvs := [K1 ! c : c in aInvariants(E2)];
                        coords := [K1 ! c : c in Eltseq(P2)];
                    catch err
                        ok := false;
                    end try;
                    if not ok then
                        Embed(K2, K1);
                        ainvs := [K1 ! c : c in aInvariants(E2)];
                        coords := [K1 ! c : c in Eltseq(P2)];
                    end if;
                end if;
                found := false;
                for i in [0..k-1] do
                    power := p^i;
                    E2i := EllipticCurve([c^power : c in ainvs]);
                    P2i := E2i ! [c^power : c in coords];
                    isomorphic, phi := IsIsomorphic(E2i, E1);
                    if not isomorphic then continue; end if;
                    for alpha in Automorphisms(E1) do
                        if alpha(phi(P2i)) in generators then found := true; break; end if;
                    end for;
                    if found then break; end if;
                end for;
                if found then done[b] := true; end if;
            end for;
        end for;
    end for;
    return representatives;
end intrinsic;

intrinsic NoncuspidalPlacesUpToDiamondFast(X::MDCrvMod1, d::RngIntElt) -> SeqEnum[PlcCrvElt]
{ Return the non-cuspidal places of degree d on X up to the diamond operators, using
  PlacesUpToDiamondFast }
    return PlacesUpToDiamondFast(X, NoncuspidalPlaces(X, d));
end intrinsic;
