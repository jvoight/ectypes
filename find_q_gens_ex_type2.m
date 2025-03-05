// Attach("../../height_package/bdd_height_integers2.m");
ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
E<a> := NumberField(x^3 - 2);
OE := Integers(E);
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

  S := BoundedHeightElements(1*OE, 200);
  S := Remove([ s : s in S ], 1);

  /* Finding possible generators for the unit groups. */

  SS := [ ];
  for m in [24..30] do
    R2 := quo<OK2 | PiK2^m>;
    S1 := [ s : s in S | IsUnit(R2!s) ];
    UR2, mR2 := MultiplicativeGroup(R2);
    HR2 := sub<UR2 | [  (R2!OK2!Norm(OK1!mR2(UR2.l)))@@mR2 : l in [1..Ngens(UR2)] ]>;
    S2 := [ (R2!s)@@mR2 : s in S1 ];
    G, toG := UR2/HR2;
    S1 := [ S1[l] : l in [1..#S2] | S2[l] notin HR2 ];
    S2 := [ S2[l] : l in [1..#S2] | S2[l] notin HR2 ];
    GQ := sub<G | [ toG(s) : s in S2 ]>;
    S1 := [ S1[n] : n in [1..#S1] | Order(toG(S2[n])) eq 2 ];
    S2 := [ S2[n] : n in [1..#S2] | Order(toG(S2[n])) eq 2 ];
    Append(~SS, S1);
  end for;
  [ #s : s in SS ];
  SS := [ { s : s in ss } : ss in SS ];
  SS := &meet SS;
  SS := [ s : s in SS ];

  /* Testing that the generators are correct. */

  SS2 := [ ];
  for l in [1..#SS] do
    g := SS[l];
    flg := true;
    for m := 24 to 100 do
      R2 := quo<OK2 | PiK2^m>;
      UR2, mR2 := MultiplicativeGroup(R2);
      HR2 := sub<UR2 | [ (R2!OK2!Norm(OK1!mR2(UR2.l)))@@mR2 : l in [1..Ngens(UR2)] ]>;
      G, toG := UR2/HR2;
      gQ := toG((R2!g)@@mR2);
      GQ := sub<G | gQ>;
      if #GQ eq 2 then
        continue;
      else
        flg := false;
        break m;
      end if;
    end for;
    if flg then
      Append(~SS2, g);
    end if;
  end for;
  h, SS2;
end for;
