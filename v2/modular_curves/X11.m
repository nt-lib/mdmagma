//Code for the modular curve X_1(M,N)
declare type MDCrvMod11: MDCrvMod;
declare attributes MDCrvMod11: level, curve, base_ring, N, M, _E, _P, _Q, _coordinates,
    _classgroup;

X11LevelStructure := recformat< P : PtEll, Q : PtEll >;

intrinsic Print(X::MDCrvMod11)
{Print X}
   M := (assigned X`M ) select X`M else "<unassigned>";
   N := (assigned X`N ) select X`N else "<unassigned>";
   base_ring := BaseRing(X);
   printf "The modular curve X_1(%o, %o) over %o", M, N, base_ring;
end intrinsic;

intrinsic MDX11(N::RngIntElt, M::RngIntElt, base_ring::Rng: equation_directory:="", zeta_M:=0) -> MDCrvMod11
{ Create the modular curve X_1(N, M) }
  assert M mod N eq 0;
  X := New(MDCrvMod11);
  _InitMDCrvMod11(X, N, M, base_ring: equation_directory:=equation_directory, zeta_M:=zeta_M);
  return X;
end intrinsic;

intrinsic _InitMDCrvMod11(X::MDCrvMod11, M::RngIntElt, N::RngIntElt,
    base_ring::Rng: equation_directory:="", zeta_M:=0)
{Initialize an MDCrvMod1 object}
    X`M := M;
    X`N := N;
    curve, E, P, Q, coordinates := _equation_X11(
        M, N,base_ring : equation_directory:=equation_directory, zeta_m:=zeta_M
    );
    X`_P := P;
    X`_Q := Q;
    X`_coordinates := coordinates;
    _InitMDCrvMod(X, N,  curve, E);
end intrinsic;

intrinsic LevelStructure(X::MDCrvMod11, x::PlcCrvElt) -> Rec
{   Return the level structure corresponding to the place x on Y1(M,N).
    To be precise. It returns is a RecFormat r such that r`P is a point of order M and
    r`Q a point of order N. It raises an error if x is a cusp.
}
    Ex := EllipticCurve(X, x);
    Px := Ex ! [Evaluate(f, x) : f in X`_P];
    Qx := Ex ! [Evaluate(f, x) : f in X`_Q];
    return rec<X11LevelStructure | P := Px, Q := Qx>;
end intrinsic;

intrinsic ModuliPoint(X::MDCrvMod11, E::CrvEll, levelstructure::Rec) -> PlcCrvElt
{   Return the place x on X1(M,N), corresponding to the pair (E, levelstructure).
    It assumes that levelstructure is a RecFormat  such that levelstructure`P is a point
    of order M and levelstructure`Q a point of order N. It only works if M = 2.
}
    assert X`M eq 2;
    bc := DerickxNormalForm_bc(E, levelstructure`P, levelstructure`Q);
    return MDPlace(X`_coordinates,bc);
end intrinsic;

intrinsic ApplyIsogeny(X::MDCrvMod11, phi:: MapSch[CrvEll, CrvEll], levelstructure::Rec) -> Rec
{   Return the level structure corresponding to phi(levelstructure)
}
    return rec<
        X11LevelStructure | P := phi(levelstructure`P), Q := phi(levelstructure`Q)
    >;
end intrinsic;

intrinsic DiamondOperator(X::MDCrvMod11, d::RngIntElt, levelstructure::Rec) -> Rec
{   Return the level structure corresponding to d*P, d*Q;
}
    assert GCD(d, Level(X)) eq 1;
    return rec<
        X11LevelStructure | P := d*levelstructure`P, Q := d*levelstructure`Q
    >;
end intrinsic;

intrinsic DegeneracyMap(X::MDCrvMod11, Y::MDCrvMod1, x::PlcCrvElt : i:=0 ) -> PlcCrvElt
{ If the place x corresponds to (E,P,Q) the place y corresponding to (E,(i*P+Q)*Level(X)/Level(Y))
  taking into account multiplicities. I.e. if deg(y) = deg(x) it returns y, if not
  y deg(x)/deg(y) is returned.}
    M := Level(X);
    N := Level(Y);
    require M mod N eq 0: "the level of Y should divide the level of X";
    E := EllipticCurve(X, x);
    L := LevelStructure(X, x);
    L1 := rec<X11LevelStructure | P := (M div N)*(i*L`P+L`Q)>;
    y := ModuliPoint(Y, E, L1);
    assert Degree(x) mod Degree(y) eq 0;
    return (Degree(x) div Degree(y))*y;
end intrinsic;


intrinsic DerickxNormalForm_bc(E::CrvEll, P::PtEll, Q::PtEll) -> Seq
{   Assumes that P is a 2 torsion point
    Return the b,c of the Derickx normal form of (E,P,Q). I.e.:

        E = [0,c,0,(1-b-c)*b,0]
        P = [0,0];
        Q = [b,b];
}
    assert P[3] eq 1;
    Px:=P[1];
    Py:=P[2];

    assert Q[3] eq 1;
    Qx:=Q[1];
    Qy:=Q[2];

    a1,a2,a3,a4,a6:=Explode(aInvariants(E));


    //translate P to 0,0
    Qx  := Qx - Px;
    Qy  := Qy - Py;
    aa1 := a1;
    aa3 := 2*Py+a3+a1*Px;
    aa2 := 3*Px+a2;
    aa4 := 3*Px^2+2*Px*a2+a4-a1*Py;

    assert aa3 eq 0; //P should be 2 torsion
    assert2 Qy^2 + aa1*Qx*Qy eq Qx^3+aa2*Qx^2+aa4*Qx;



    //make aa1 zero
    Qy  := Qy + aa1*Qx/2;
    aa2 := aa2 - aa1^2/2;
    assert2 Qy^2 eq Qx^3+aa2*Qx^2+aa4*Qx;

    u := Qx/Qy;

    Qx  := Qx  * u^2;
    Qy  := Qy  * u^3;
    aa2 := aa2 * u^2;
    aa4 := aa4 * u^4;
    assert2 Qx eq Qy;
    assert2 Qy^2 eq Qx^3+aa2*Qx^2+aa4*Qx;


    b:=Qx;
    c:=aa2;
    return [b,c];
end intrinsic;

intrinsic _equation_X11(m,n,base_ring : equation_directory:="", zeta_m:=0) -> CrvPln
{  Input: m,n - integers such that m divides n
          base_ring - a ring
          equation_directory - directory with files X1_m_n.txt containing models
          zeta_m - a primitive mth root of unity in the base_ring (if unspecified one will be chosen)
    Output: C - a curve
    Returns an algebraic model C of the modular curve X_1(m,n) as a curve over base_ring
}
    if equation_directory eq "" then
      equation_directory := MDMagmaSourceDir() cat "/../models_X1_m_n";
    end if;
    assert IsDivisibleBy(n,m);
    if m gt 2 then
        if zeta_m ne 0 then
            assert zeta_m^m eq 1 and &and[zeta_m^e ne 1: e in Divisors(m)| e ne m];
        else
            try
                zeta_m := RootOfUnity(m,base_ring);
                // Different fields in magma behave different, RootOfUnity raises an error if the base_ring 
                // is QQ but creates a field extension if base_ring is a finite field. The following assert
                // fixes this difference.
                assert zeta_m in base_ring;
            catch e
                message := Sprintf("The base ring: %o \n doesn't seem to contain a primitive %oth root of unity. If it has one please provide it using the optional argument  zeta_m := ...", base_ring, m);
                require false: message;
            end try;
        end if;
        z:=zeta_m; i:=zeta_m;
    end if;
    n_str := IntegerToString(n);
    m_str := IntegerToString(m);
    file_name := equation_directory cat "/X1_" cat m_str cat "_" cat n_str cat ".txt";
    data := Read(file_name);
    data := Split(data);
    //example contents of the file X1_2_10.txt
    //X := v^2 + (u^2 - 1)*v - 1;
    //q := 1/u;
    //t := -4*u/(u^2*v + u^2 - v + 3);
    //E:=[0,t^2-2*q*t-2,0,-(t^2-1)*(q*t+1)^2,0];
    //P:=[(t+1)*(q*t+1),t*(q*t+1)*(t+1)];
    //Q:=[0,0];
    A<u,v> := AffineSpace(base_ring,2);
    for line in data do
        val := Split(Split(line,"=")[2],";")[1];
        if line[1] eq "X" then X := eval(val); end if;
        if line[1] eq "q" then q := eval(val); end if;
        if line[1] eq "r" then r := eval(val); end if;
        if line[1] eq "s" then s := eval(val); end if;
        if line[1] eq "t" then t := eval(val); end if;
        if line[1] eq "E" then E := eval(val); end if;
        if line[1] eq "P" then P := eval(val); end if;
        if line[1] eq "Q" then Q := eval(val); end if;
    end for;
    C := Curve(A,X);
    FFX := FunctionField(C);

    if m eq 2 then
        b := (t+1)*(q*t+1)/t^2;
        c := (t^2-2*q*t-2)/t^2;
        E := [0, c, 0 , (1-b-c)*b ,0];
        P := [b, b];
        Q := [0, 0];
        coordinates := [FFX ! b, FFX ! c];
    else
        coordinates := [FFX ! q, FFX ! t];
    end if;


    E := [FFX ! f : f in E];
    P1 := [FFX ! f : f in Q];
    Q1 := [FFX ! f : f in P];


    return ProjectiveClosure(C), E, P1, Q1, coordinates;
end intrinsic;

intrinsic Cusps(X::MDCrvMod11) -> SeqEnum[PlcCrvElt]
{ The cusps on this modular curve }
    cusps := Poles(jInvariantMap(X));
    return cusps;
end intrinsic;
