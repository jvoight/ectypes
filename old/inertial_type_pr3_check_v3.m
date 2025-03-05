/* This file checks that each inertial type described for p = 3 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q3 := pAdicField(3, 200);
ZZ3 := Integers(Q3);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "27a1", "54a1" ];
discs := [ -3, 3 ];
cond_exp := [ 2, 2 ];
u_gens := [ [ 4 ], [ 4 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq := [ x^12 - 3*x^11 - 3*x^10 + 3*x^9 + 3*x^5 - 3*x^4 + 3*x^3 + 3, x^12 + 3*x^4 + 3 ];

 
/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  bl := type[2] eq 0 select true else false;
  return bl;
end function;


fld_count := [ 0 : m in [1..2] ];
for h in pol_seq do
  M := FieldOfFractions(SplittingField(h, ZZ3));
  for m in [1..#c_labels] do
    c_lab := c_labels[m];
    E := EllipticCurve(c_lab);
    if check_inertial_field(E, M) then
      fld_count[m] +:= 1;
    end if;
  end for;
end for;


/* Finding the norm groups and their images inside G. */

K := LocalField(Q3, x^2 + 1);
K := LocalField(K, x^2 + 3);
K := RamifiedRepresentation(K);
OK := Integers(K);
BK := AbsoluteBasis(K);
g := P!MinimalPolynomial(BK[4], Q3);
K2 := AbsoluteField(NumberField([ x^2 + 1, x^2 + 3 ]));
K2 := OptimizedRepresentation(K2);
OK2 := Integers(K2);
a1 := Roots(x^2 + 1, K2)[1][1];
a2 := Roots(x^2 + 3, K2)[1][1];
BK2 := [ 1, a1, a2, a1*a2 ];
[ P!MinimalPolynomial(s) : s in BK2 ];
[ P!MinimalPolynomial(s, Q3) : s in BK ];
PiK2 := Factorisation(3*OK2)[1][1];
PiK := UniformizingElement(OK);
UK, toOK := UnitGroup(OK);
Gs := [ ];
NGs := [ ];
for m := 1 to #discs do
  R := quo<OK | PiK^cond_exp[m]>;
  R2 := quo<OK2 | PiK2^cond_exp[m]>;
  phi2 := hom< R -> R2 | x :-> R2!(&+[ (ZZ!u[i])*BK2[i] : i in [1..#BK] ])
                                          where u := &cat [ Eltseq(s) : s in Eltseq(K!OK!x) ] >;
  UR2, mR2 := MultiplicativeGroup(R2);
  HR2 := sub<UR2 | [ phi2(R!OK!Norm(toOK(UK.i)))@@mR2 : i in [1..Ngens(UK)] ]>;
  G, toG := UR2/HR2;
  imUK := sub<G | [ toG((phi2(R!OK!toOK(UK.l))@@mR2)) : l in [1..Ngens(UK)] ]>;
  h := Factorisation(pol_seq[m], OK)[1][1];
  OL := SplittingField(h);
  G1 := AutomorphismGroup(OL, OK);
  G1; Exponent(G1);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ toG(phi2(R!toOK(H.l))@@mR2) : l in [1..Ngens(H)] ]>;
  Append(~NGs, imH);
  Append(~Gs, G);
end for;

/* Checking that each inertial type is realised by an elliptic curve. */

for l in [1..2] do
  printf "%o&%o&%o&%o\\\\\n" , c_labels[l], pol_seq[l], fld_count, NGs[l];
end for;
