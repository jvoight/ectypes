/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 200);
ZZ2 := Integers(Q2);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "96a1", "288a1", "192a2", "576f2", "256b2", "256c1" ];

discs := [ -20, -4, -20, -4, -4, -4 ];
cond_exp := [ 3, 3, 4, 4, 6, 6 ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */
 
pol_seq := [ [ x^2 - 2*x + 2, x^8 + 4*x^6 + 28*x^4 + 20 ], [ x^2 - 2*x + 2, x^8 + 8*x^4 + 336 ],
             [ x^8 - 6*x^4 + 16*x^2 - 3 ], [ x^8 + 2*x^4 + 21 ], [ x^2 - 2*x + 2, x^8 + 20*x^4 + 52 ],
             [ x^2 - 2*x + 2, x^8 + 4*x^4 + 84 ] ];

pol_seq := [
    x^16 + 8*x^15 - 2*x^14 + 8*x^13 + 8*x^12 + 8*x^11 + 4*x^9 + 6*x^8 + 8*x^7 +
        8*x^6 + 8*x^5 + 8*x^4 + 8*x^2 + 8*x + 4,
    x^16 - 8*x^15 + 24*x^14 + 28*x^12 + 24*x^11 + 24*x^10 + 16*x^9 + 12*x^8 +
        32*x^7 - 16*x^6 + 32*x^5 - 16*x^4 + 16*x^3 - 28,
    x^16 + 4*x^15 - 6*x^14 + 8*x^13 + 4*x^11 + 8*x^9 + 6*x^8 + 8*x^7 + 8*x^6 +
        8*x^4 + 8*x^2 + 4,
    x^16 + 4*x^15 - 6*x^14 + 8*x^13 + 4*x^12 - 4*x^11 + 8*x^10 + 8*x^9 + 2*x^8 +
        8*x^7 + 8*x^6 + 8*x^2 + 4,
    x^16 - 40*x^14 + 4*x^12 - 56*x^10 - 16*x^9 + 48*x^8 + 64*x^7 + 32*x^5 +
        8*x^4 + 64*x^3 + 16*x^2 + 32*x + 20,
    x^16 - 8*x^14 - 32*x^13 + 20*x^12 + 64*x^11 - 56*x^10 - 16*x^9 + 64*x^8 +
        64*x^7 + 64*x^6 - 32*x^5 - 56*x^4 + 64*x^3 - 48*x^2 + 32*x - 12
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


fld_count := [ 0 : m in [1..6] ];
for h in pol_seq do
  M := SplittingField(h, ZZ2);
  M := FieldOfFractions(M);
  for m in [1..#c_labels] do
    c_lab := c_labels[m];
    E := EllipticCurve(c_lab);
    if check_inertial_field(E, M) then
      fld_count[m] +:= 1;
    end if;
  end for;
end for;


/* Finding the norm groups and their images inside G. */

K := LocalField(Q2, x^2 + x + 1);
K := LocalField(K, x^2 - 2*x + 2);
K := RamifiedRepresentation(K);
OK := Integers(K);
BK := AbsoluteBasis(K);
g := P!MinimalPolynomial(BK[4], Q2);
K2 := NumberField(g);
OK2 := Integers(K2);
a1 := Roots(x^2 + x + 1, K2)[1][1];
a2 := Roots(x^2 - 2*x + 2, K2)[1][1];
BK2 := [ 1, a1, a2, a1*a2 ];
[ P!MinimalPolynomial(s) : s in BK2 ];
[ P!MinimalPolynomial(s, Q2) : s in BK ];
PiK2 := Factorisation(2*OK2)[1][1];
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

for l in [1..6] do
  printf "%o&%o\\\\\n" , c_labels[l], NGs[l];
end for;
