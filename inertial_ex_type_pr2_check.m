/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 50);
ZZ2 := Integers(Q2);
OE<a> := UnramifiedExtension(ZZ2, x^2 + x + 1);
E := FieldOfFractions(OE);
OK<b> := ext<OE | x^3 + 2>;
K := FieldOfFractions(OK);
PolsK<z> := PolynomialRing(OK);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "648b1", "1296c1", "5184e1", "5184w1", "3456a1", "3456e1", "3456o1", "3456c1" ];
cond_exps := [ 4, 10, 22, 22, 16, 16, 16, 16 ];


/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq := [ x^8 + 20*x^2 + 20,
             x^8 + 28*x^2 + 20,
             x^8 + 2*x^6 + 20,
             x^8 + 6*x^6 + 20,
             x^8 + 4*x^7 + 12*x^2 + 14,
             x^8 + 4*x^7 + 4*x^2 + 14,
             x^8 + 4*x^7 + 12*x^2 + 10,
             x^8 + 4*x^7 + 12*x^2 + 2 ];

pol_seq2 :=
[
    [ z^2 + a*b*z + b, z^2 + b*z + b, z^2 + (a + 1)*b*z + b ],
    [ z^2 + a*b*z + b, z^2 + b*z + b, z^2 + (a + 1)*b*z + b ],
    [ z^2 + a*b*z + b, z^2 + b*z + b, z^2 + (a + 1)*b*z + b ],
    [ z^2 + a*b*z + b, z^2 + b*z + b, z^2 + (a + 1)*b*z + b ],
    [ z^2 - 2*a*z + b - 2*a - 2, z^2 - 2*z + b - 2, z^2 + (-2*a - 2)*z + b - 2*a ],
    [ z^2 - 2*a*z + b - 2*a - 2, z^2 - 2*z + b - 2, z^2 + (-2*a - 2)*z + b - 2*a ],
    [ z^2 - 2*a*z + b - 2*a - 2, z^2 - 2*z + b - 2, z^2 + (-2*a - 2)*z + b - 2*a ],
    [ z^2 - 2*a*z + b - 2*a - 2, z^2 - 2*z + b - 2, z^2 + (-2*a - 2)*z + b - 2*a ]
];


/* Some useful global polynomials. */

K2 := AbsoluteField(NumberField([ x^2 + x + 1, x^3 + 2 ]));
K2 := OptimizedRepresentation(K2);
PolsK2<t> := PolynomialRing(K2);
OK2 := Integers(K2);
a1 := Roots(x^2 + x + 1, OK2)[1][1];
a2 := Roots(x^3 + 2, OK2)[1][1];
BK2 := [ s1*s2 : s1 in [ 1, a1 ], s2 in [ 1, a2, a2^2 ] ];

pol_seq3 :=
[
    [ t^2 + a1*a2*t + a2, t^2 + a2*t + a2, t^2 + (a1 + 1)*a2*t + a2 ],
    [ t^2 + a1*a2*t + a2, t^2 + a2*t + a2, t^2 + (a1 + 1)*a2*t + a2 ],
    [ t^2 + a1*a2*t + a2, t^2 + a2*t + a2, t^2 + (a1 + 1)*a2*t + a2 ],
    [ t^2 + a1*a2*t + a2, t^2 + a2*t + a2, t^2 + (a1 + 1)*a2*t + a2 ],
    [ t^2 - 2*a1*t + a2 - 2*a1 - 2, t^2 - 2*t + a2 - 2, t^2 + (-2*a1 - 2)*t + a2 - 2*a1 ],
    [ t^2 - 2*a1*t + a2 - 2*a1 - 2, t^2 - 2*t + a2 - 2, t^2 + (-2*a1 - 2)*t + a2 - 2*a1 ],
    [ t^2 - 2*a1*t + a2 - 2*a1 - 2, t^2 - 2*t + a2 - 2, t^2 + (-2*a1 - 2)*t + a2 - 2*a1 ],
    [ t^2 - 2*a1*t + a2 - 2*a1 - 2, t^2 - 2*t + a2 - 2, t^2 + (-2*a1 - 2)*t + a2 - 2*a1 ]
];


/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  bl := type[2] eq 0 select true else false;
  return bl;
end function;

/*
fld_count := [ 0 : m in [1..8] ];
for h in pol_seq do
  OM := SplittingField(h, ZZ2);
  M := FieldOfFractions(OM);
  [ Valuation(Discriminant(OM, ZZ2)) ];
  for m in [1..#c_labels] do
    c_lab := c_labels[m];
    E := EllipticCurve(c_lab);
    if check_inertial_field(E, M) then
      fld_count[m] +:= 1;
    end if;
  end for;
end for;
*/



/* Finding the norm groups and their images inside G. */

Gs := [ ];
NGs := [ ];
for m in [1..#pol_seq] do
    M := ext<K | pol_seq2[m][2]>;
    OM<c> := Integers(M);
    BM := AbsoluteBasis(M);
    M2 := AbsoluteField(ext<K2 | pol_seq3[m][2]>);
    M2<u> := OptimizedRepresentation(M2);
    OM2 := Integers(M2);
    a3 := Roots(pol_seq3[m][2], OM2)[1][1];
    BM2 := [ u1*u2 : u1 in BK2, u2 in [ 1, a3 ] ];
    T := Matrix([ Eltseq(M2!s) : s in Basis(OM2) ])*Matrix([ Eltseq(M2!s) : s in BM2 ])^-1;
    assert [ P!MinimalPolynomial(s, Q2) : s in BM ] eq [ P!MinimalPolynomial(s, ZZ) : s in BM2 ];
    g := Factorisation(pol_seq[m], OM)[1][1];
    OL := SplittingField(g);
    PiM := UniformizingElement(OM);
    PiM2 := Factorisation(2*OM2)[1][1];
    R := quo<OM | PiM^cond_exps[m]>;
    R2 := quo<OM2 | PiM2^cond_exps[m]>;
    phi2 := hom< R -> R2 | x :-> R2!(&+[ (ZZ!u[n])*BM2[n] : n in [1..#BM] ])
                                    where u := &cat [ Eltseq(s) : s in Eltseq(ss), ss in Eltseq(M!OM!x) ] >;
    psi2 := hom< R2 -> R | x :-> R!(&+[ (QQ!u[n])*BM[n] : n in [1..#BM] ])
                                                            where u := Eltseq(Vector(QQ, Eltseq(OM2!x))*T) >;
    UM, toOM := UnitGroup(OM);
    UR2, mR2 := MultiplicativeGroup(R2);
    HR2 := sub<UR2 | [ phi2(R!OM!Norm(toOM(UM.l)))@@mR2 : l in [1..Ngens(UM)] ]>;
    G, toG := UR2/HR2;
    H, toH := NormGroup(OL, toOM);
    imH := sub<G | [ toG(phi2(R!toOM(H.l))@@mR2) : l in [1..Ngens(H)] ]>;
    G/imH;
    gens := [ OM!psi2(R2!mR2((G.m)@@toG)) : m in [1..Ngens(G)] ];
    [ Valuation(u - 1) : u in gens ];
  Append(~NGs, imH);
  Append(~Gs, G);
end for;
