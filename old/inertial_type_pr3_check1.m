/* This file checks that each inertial type described for p = 3 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q3 := pAdicRing(3, 200);
ZZ3 := Integers(Q3);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "36a1","162b1","162d1", "162c2", "162a2", "27a1", "54a1", "243a1", "243b1", "972b1" ];
discs := [ -1, 1, -1, 1, -1, -3, 3, -3, -3, -3 ];
cond_exp := [ 2, 2, 2, 2, 2, 2, 2, 4, 4, 4 ];
cond_exp := [ 2, 2, 2, 2, 2, 3, 3, 4, 4, 4 ];
u_gens := [ [ -4 ], [ ], [ -4 ], [ ], [ -4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq := [ 
x^4 + 3,
x^3 + 6*x^2 + 3, 
x^3 + 3*x^2 + 3,
x^6 - 3*x^4 + 9*x^2 + 18*x + 12,
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


fld_count := [ 0 : m in [1..10] ];
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
  K := (discs[m] eq 1) select Q3 else SplittingField(PolynomialRing(Q3)!(x^2 - discs[m]));
  OK := Integers(K);
  PolsOK := PolynomialRing(OK);
  UK, toOK := UnitGroup(OK);
  PiK := UniformizingElement(OK);
  R := quo<OK | PiK^cond_exp[m]>;
  UR, fromR := MultiplicativeGroup(R);
  HR := sub<UR | [ (R!s)@@fromR : s in u_gens[m] ]>;
  G, toG := UR/HR;
  imUK := sub<G | [ toG(((R!toOK(UK.l))@@fromR)) : l in [1..Ngens(UK)] ]>;
  L := SplittingField(PolynomialRing(K)!pol_seq[m]);
  OL := Integers(L);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ toG(((R!toOK(H.l))@@fromR)) : l in [1..Ngens(H)] ]>;
  Append(~NGs, imH);
  Append(~Gs, G);
end for;


\\ \\ \\
/* Checking that each inertial type is realised by an elliptic curve. */

for l in [1..10] do
  printf "%o&%o&%o&%o\\\\\n" , c_labels[l], pol_seq[l], fld_count, NGs[l];
end for;
