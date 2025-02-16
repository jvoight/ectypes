/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

Attach("../../height_package/bdd_height_integers2.m");
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
E<a> := NumberField(x^3 - 2);
K1<b> := ext<E | x^2 + x + 1>;
K2<c> := OptimizedRepresentation(AbsoluteField(K1));
OK1 := Integers(K1);
OK2 := Integers(K2);
PiK2 := Factorisation(2*OK2)[1][1];

S := BoundedHeightElements(1*OK2, 60);
S := Remove([ s : s in S ], 1);
[ #S ];

/* Finding the unit groups G and their structures. */

  SS := [ ];
  for m in [20..20] do
    R2 := quo<OK2 | PiK2^m>;
    S1 := [ s : s in S | IsUnit(R2!s) ];
    UR2, mR2 := MultiplicativeGroup(R2);
    HR2 := sub<UR2 | [  (R2!OK2!Norm(OK1!mR2(UR2.l)))@@mR2 : l in [1..Ngens(UR2)] ]>;
    G, toG := UR2/HR2;
    S2 := [ toG((R2!s)@@mR2) : s in S1 ];
    S3 := [ [ S1[n] : n in [1..#S1] | Order(S2[n]) eq Order(G.l) ] : l in [1..Ngens(G)] ];
    [ #s : s in S3 ];
    SS1 := [ ];
    for g4 in S3[4], g3 in S3[3], g2 in S3[2], g1 in S3[1] do
      gens := [ g1, g2, g3, g4 ];
      gens := [ Roots(MinimalPolynomial(s), K1)[1][1] : s in gens ];
      gens := [ Denominator(u)*u : u in gens ];
      gensG := [ toG((R2!s)@@mR2) : s in gens ];
      SG := {@ sub<G | u> : u in gensG @};
      SS2 := Subsets({1..#SG}, 2);
      SS2 := [ [ u : u in s2 ] : s2 in SS2 ];
      int_count := &*[ #(SG[m[1]] meet SG[m[2]]) : m in SS2 ];
      G1 := sub<G | gensG>;
      if int_count eq 1 and G1 eq G then
        Append(~SS1, gens);
      end if;
      if #SS1 eq 50 then break g4; end if;
    end for;
    Append(~SS, SS1);
  end for;


/* Testing that the generators are correct. */

for m in [1..100] do
  gens := SS[1][1];
  R2 := quo<OK2 | PiK2^m>;
  UR2, mR2 := MultiplicativeGroup(R2);
  HR2 := sub<UR2 | [ (R2!OK2!Norm(OK1!mR2(UR2.l)))@@mR2 : l in [1..Ngens(UR2)] ]>;
  G, toG := UR2/HR2;
  gensG := [ toG((R2!s)@@mR2) : s in gens ];
  SG := {@ sub<G | u> : u in gensG @};
  S2 := Subsets({1..#SG}, 2);
  S2 := [ [ u : u in s2 ] : s2 in S2 ];
  int_count := (#S2 eq 0) select 1 else (&*[ #(SG[ll[1]] meet SG[ll[2]]) : ll in S2 ]);
  G1 := sub<G | gensG>;
  m, [ int_count eq 1, G1 eq G ];
end for;


