/* This file checks to determine the group structures for the unit groups in Lemma 7.2.2. for the extension K/Q2(a)
   given by a^3 - 2 = 0 and x^2 + a*x + a^2 + a. */

ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 50);
ZZ2 := Integers(Q2);
OE<a> := ext<ZZ2 | x^3 - 2>;
E := FieldOfFractions(OE);
OK<b> := ext<OE | Polynomial([ a^2 + a, a, 1 ])>;
K := FieldOfFractions(OK);
BK := AbsoluteBasis(K);
PolsK<z> := PolynomialRing(OK);

gens := [
    a^2 + a + 1,
    -a^2*b - 1,
    (-2*a^2 + 4)*b - a^2 - a + 3,
    (-a^2 + 2)*b - a^2 - a + 1,
    -b + 1
];

/* Some useful global polynomials. */

K0<b1> := NumberField(x^3 - 2);
PolsK0<t> := PolynomialRing(K0);
K1<b2> := ext<K0 | t^2 + b1*t + b1^2 + b1>;
K2<c> := OptimizedRepresentation(AbsoluteField(K1));
OK2 := Integers(K2);
BK1 := [ K2 | s1*s2 : s1 in [ 1, b1, b1^2 ], s2 in [ 1, b2 ]  ];
BK2 := Basis(K2);
T := Matrix([ Eltseq(s) : s in BK2 ])*Matrix([ Eltseq(s) : s in BK1 ])^-1;
assert [ P!MinimalPolynomial(s, Q2) : s in BK ] eq [ P!MinimalPolynomial(s, ZZ) : s in BK1 ];
PiK := UniformizingElement(OK);
PiK2 := Factorisation(2*OK2)[1][1];



/* Finding the unit groups G and their structures. */

for m in [1..50] do
  R := quo<OK | PiK^m>;
  R2 := quo<OK2 | PiK2^m>;
  phi2 := hom< R -> R2 | x :-> R2!(&+[ (ZZ!u[n])*BK1[n] : n in [1..#BK] ])
                                    where u := &cat [ Eltseq(s) : s in Eltseq(ss), ss in Eltseq(K!OK!x) ] >;
  psi2 := hom< R2 -> R | x :-> R!(&+[ (QQ!u[n])*BK[n] : n in [1..#BK] ])
                                                            where u := Eltseq(Vector(QQ, Eltseq(K2!OK2!x))*T) >;
  UK, toOK := UnitGroup(OK);
  UE, toOE := UnitGroup(OE);
  UR2, mR2 := MultiplicativeGroup(R2);
  HR2 := sub<UR2 | [ phi2(R!OK!Norm(toOK(UK.l)))@@mR2 : l in [1..Ngens(UK)] ]>;
  NR2 := sub<UR2 | [ phi2(R!OK!toOE(UE.l))@@mR2 : l in [1..Ngens(UE)] ]>;
  G, toG := UR2/HR2;
  G2 := sub<G | [ toG(s) : s in NR2 ]>;
  gensG := [ toG((phi2(R!s))@@mR2) : s in gens ];
  H1 := sub<G | gensG[1]>;
  H2 := sub<G | gensG[2]>;
  H3 := sub<G | gensG[3]>;
  H4 := sub<G | gensG[4]>;
  H5 := sub<G | gensG[5]>;
  SG := {@ H1, H2, H3, H4, H5 @};
  S2 := Subsets({1..#SG}, 2);
  S2 := [ [ u : u in s2 ] : s2 in S2 ];
  int_count := (#S2 eq 0) select 1 else &*[ #(SG[m[1]] meet SG[m[2]]) : m in S2 ];
  G1 := sub<G | gensG>;
  [ int_count eq 1, G1 eq G ];
  //m, [ #(SG[m[1]] meet SG[m[2]]) : m in S2 ];
  //[ Order(s) : s in gensG ];
  m, G;
end for;

