/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

Attach("../../height_package/bdd_height_integers2.m");
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
E<a> := NumberField(x^3 - 2);
PolsE<t> := PolynomialRing(E);

/* Quadratic extensions of Q(sqrt[3](2)). */

pol_seq := [ t^2 + a*t + a, t^2 + a*t + a^2 + a, t^2 + 2*t + a + 2, t^2 + 2*t + a + 6 ];

for h in pol_seq do
  K1<b> := ext<E | h>;
  K2<c> := OptimizedRepresentation(AbsoluteField(K1));
  OK1 := Integers(K1);
  OK2 := Integers(K2);
  PiK2 := Factorisation(2*OK2)[1][1];

  /* Finding elements of small height. */

  S := BoundedHeightElements(1*OK2, 600);
  S := Remove([ s : s in S ], 1);

  /* Finding possible generators for the unit groups. */

  SS := [ ];
  for m in [24..30] do
    R2 := quo<OK2 | PiK2^m>;
    S1 := [ s : s in S | IsUnit(R2!s) ];
    UR2, mR2 := MultiplicativeGroup(R2);
    HR2 := sub<UR2 | [  (R2!OK2!Norm(OK1!mR2(UR2.l)))@@mR2 : l in [1..Ngens(UR2)] ]>;
    G, toG := UR2/HR2;
    S2 := [ toG((R2!s)@@mR2) : s in S1 ];
    S1 := [ [ S1[n] : n in [1..#S1] | Order(S2[n]) eq Order(G.l) ] : l in [1..Ngens(G)] ];
    S2 := [ [ S2[n] : n in [1..#S2] | Order(S2[n]) eq Order(G.l) ] : l in [1..Ngens(G)] ];
    S3 := [ ];
    for l := 1 to Ngens(G) do
      S0 := [ ];
      gens := [ ];
      G1 := sub<G | gens>;
      for n in [1..#S2[l]] do
        if S2[l][n] notin G1 then
          Append(~gens, S2[l][n]);
          Append(~S0, S1[l][n]);
          G1 := sub<G | gens>;
        end if;
      end for;
      Append(~S3, S0);
    end for;
    [ #s : s in S3 ];
    SS1 := [ ];
    for g5 in S3[5], g4 in S3[4], g3 in S3[3], g2 in S3[2], g1 in S3[1] do
      gens := [ g1, g2, g3, g4, g5 ];
      gens := [ Roots(MinimalPolynomial(s), K1)[1][1] : s in gens ];
      gensG := [ toG((R2!s)@@mR2) : s in gens ];
      SG := {@ sub<G | u> : u in gensG @};
      SS2 := Subsets({1..#SG}, 2);
      SS2 := [ [ u : u in s2 ] : s2 in SS2 ];
      int_count := &*[ #(SG[m[1]] meet SG[m[2]]) : m in SS2 ];
      G1 := sub<G | gensG>;
      if int_count eq 1 and G1 eq G then
        Append(~SS1, gens);
      end if;
      if #SS1 eq 20 then break g5; end if;
    end for;
    Append(~SS, SS1);
  end for;
  SS := {@ s : s in SS @};
  SS := [ { s[l] : s in ss, ss in SS } : l in [1..5] ];
  SS := Flat(CartesianProduct(SS));
  SS := Set(SS);
  SS := [ [ s[l] : l in [1..#s] ] : s in SS ];

  /* Testing that the generators are correct. */

  SS2 := [ ];
  for l in [1..#SS] do
    gens := SS[l];
    flg := true;
    for m := 12 to 100 do
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
      if int_count eq 1 and G1 eq G then
        continue;
      else
        flg := false;
        break m;
      end if;
    end for;
    if flg then
      Append(~SS2, gens);
      end if;
  end for;
  h, SS2;
end for;
