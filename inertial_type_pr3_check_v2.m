/* This file checks that each inertial type described for p = 3 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q3 := pAdicField(3, 200);
ZZ3 := Integers(Q3);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "36a1", "162d1", "162a2", "27a1", "54a1", "243a1", "243b1", "972b1" ];
discs := [ -1, -1, -1, 3, -3, -3, -3, -3 ];
cond_exp := [ 1, 2, 2, 2, 2, 4, 4, 4 ];
u_gens := [ [ -4 ], [ -4 ], [ -4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq := [ 
x^4 + 3,
x^3 + 3*x^2 + 3,
x^6 + 3*x^4 + 3, 
x^12 - 3*x^11 - 3*x^10 + 3*x^9 + 3*x^5 - 3*x^4 + 3*x^3 + 3,
x^12 + 3*x^4 + 3, 
x^12 + 9*x^10 + 9*x^9 - 9*x^8 + 6*x^6 + 9*x^5 - 9*x^4 - 3*x^3 + 9*x^2 - 9*x - 12,
x^12 + 9*x^11 + 9*x^10 + 9*x^9 + 9*x^8 - 9*x^7 - 12*x^6 - 9*x^2 - 3,
x^12 - 9*x^11 + 9*x^9 - 9*x^8 + 9*x^7 - 12*x^6 + 3*x^3 + 9*x^2 + 9*x - 12 ];

 
/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  bl := type[2] eq 0 select true else false;
  return bl;
end function;


fld_count := [ 0 : m in [1..8] ];
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

Gs := [ ];
NGs := [ ];
for m := 1 to #discs do
  K := LocalField(Q3, x^2 - discs[m]);
  K := RamifiedRepresentation(K);
  OK := Integers(K);
  g := P!MinimalPolynomial(OK.1);
  K2 := NumberField(g);
  OK2 := Integers(K2);
  g2 := MinimalPolynomial(OK2.2);
  UK, toOK := UnitGroup(OK);
  K2 := NumberField(x^2 - discs[m]);
  OK2 := Integers(K2);
  BK2 := Basis(K2);
  if discs[m] eq -3 then
    gens := (cond_exp[m] le 3) select [ a1 - 3 ] else [ -a1, a1 - 3 ] where a1 := Roots(x^2 - x + 1, K)[1][1];
  elif discs[m] eq -1 then
    gens := [ a1 + 2 ] where a1 := Roots(x^2 - discs[m], K)[1][1];
  else
    gens := [ a1 - 1 ] where a1 := Roots(x^2 - discs[m], K)[1][1];
  end if;
  PiK := UniformizingElement(OK);
  PiK2 := Factorisation(3*OK2)[1][1];
  R := quo<OK | PiK^cond_exp[m]>;
  R2 := quo<OK2 | PiK2^cond_exp[m]>;
  UR2, mR2 := MultiplicativeGroup(R2);
  phi2 := hom< R -> R2 | x :-> R2!(ZZ!u[1] + ZZ!u[2]*BK2[2]) where u := Eltseq(OK!x) >;
  HR2 := sub<UR2 | [ phi2(R!s)@@mR2 : s in u_gens[m] ]>;
  G, toG := UR2/HR2;
  gens2 := [ toG(phi2(R!s)@@mR2) : s in gens ];
  G2 := AbelianGroup([ Order(s) : s in gens2 ]);
  psi := hom< G2 -> G | gens2 >;
  L := SplittingField(PolynomialRing(K)!pol_seq[m]);
  OL := Integers(L);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ toG(phi2(R!OK!toOK(H.l))@@mR2) : l in [1..Ngens(H)] ]>;
  imH2 := [ (imH.m)@@psi : m in [1..Ngens(imH)] ];
  Append(~NGs, imH2);
  Append(~Gs, G2);
end for;


\\ \\ \\
/* Checking that each inertial type is realised by an elliptic curve. */

for l in [1..10] do
  printf "%o&%o&%o&%o\\\\\n" , c_labels[l], pol_seq[l], fld_count[l], NGs[l];
end for;
