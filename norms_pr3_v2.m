/* This file checks that each inertial type described for p = 3 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q3 := pAdicField(3, 200);
ZZ3 := Integers(Q3);

/*************************************************************************************************************/
// The following proves that listed types in section 5 arise from elliptic curves over Q3.

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := ["162d1", "36a1", "162a2", "27a1", "54a1","972b1", "243b1", "243a1" ];
discs := [ -1, -1, -1, 3, -3, -3, -3, -3 ];
cond_exp := [ 2, 1, 2, 2, 2, 4, 4, 4 ];
u_gens := [ [ -4 ], [ -4 ], [ -4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ], [ 4 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq := [ 
x^3 + 3*x^2 + 3,
x^4 + 3,
x^6 + 3*x^4 + 3, 
x^12 - 3*x^11 - 3*x^10 + 3*x^9 + 3*x^5 - 3*x^4 + 3*x^3 + 3,
x^12 + 3*x^4 + 3, 
x^12 - 9*x^11 + 9*x^9 - 9*x^8 + 9*x^7 - 12*x^6 + 3*x^3 + 9*x^2 + 9*x - 12,
x^12 + 9*x^11 + 9*x^10 + 9*x^9 + 9*x^8 - 9*x^7 - 12*x^6 - 9*x^2 - 3,
x^12 + 9*x^10 + 9*x^9 - 9*x^8 + 6*x^6 + 9*x^5 - 9*x^4 - 3*x^3 + 9*x^2 - 9*x - 12
];

/* We made a choice above, let's check it matches the LMFDB labels. */

LMFDB_pol_seq := [
x^3 + 3*x^2 + 3, // LMFDB 3.3.4.4
x^4 + 3, // 3.4.3.1
x^6 + 3*x^4 + 3, // 3.6.9.12
x^12 + 6*x^6 + 6*x^4 + 3,  // 3.12.15.12
x^12 + 3*x^4 + 3, // 3.12.15.1
x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, // 3.12.23.122
x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, // 3.12.23.20
x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24 // 3.12.23.14
];

for i := 1 to #pol_seq do
  assert IsIsomorphic(ext<Q3 | pol_seq[i]>,ext<Q3 | LMFDB_pol_seq[i]>);
end for;

/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  return type[2] eq 0;
end function;

// the following establishes the two rows corresponding to principal series types in Table 4 
// note they are twist of each other


Eb:=EllipticCurve("162b1");
M := FieldOfFractions(SplittingField(x^3 + 6*x^2 + 3, ZZ3));  // 3.3.4.2
assert check_inertial_field(Eb, M);
assert #AutomorphismGroup(M) eq 3;

Ec:=EllipticCurve("162c2");
M := FieldOfFractions(SplittingField(x^6 - 3*x^4 + 9*x^2 + 18*x + 12, ZZ3)); // 3.6.9.11
assert IsIsomorphic(M,ext<Q3 | x^6 + 6*x^4 + 12>);
assert check_inertial_field(Ec, M); 
assert #AutomorphismGroup(M) eq 6;
assert IsCyclic(AutomorphismGroup(M));
assert IsQuadraticTwist(Eb,Ec);

// the following loop shows that for each curve in Table 4 with a supercuspidal type 
// achieves good reduction over one of the fields in pol_seq with only one of minimal degree for this property for each curve 

galoisGpsL:=[];
fld_count := [ 0 : m in [1..8] ];
for h in pol_seq do
  M := FieldOfFractions(SplittingField(h, ZZ3));
  Append(~galoisGpsL,AutomorphismGroup(M));
  for m in [1..#c_labels] do
    c_lab := c_labels[m];
    E := EllipticCurve(c_lab);
    if check_inertial_field(E, M) then
      fld_count[m] +:= 1;
    end if;
  end for;
end for;
fld_count;

// the following establishes the column on Galois groups of Table 4
tD6:=SmallGroup(24,8);
gps:=[*SymmetricGroup(3), DihedralGroup(4), DihedralGroup(6), tD6, tD6, tD6, tD6, tD6 *];
assert {IsIsomorphic(gps[i],galoisGps[i]) : i in [1..#galoisGpsL]} eq {true};


/* Finding the norm groups and their images inside G. */

Gs := [ ];
NGs := [* *];
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
  print "++++++++++++++++++++++++++++++++++++";
  c_labels[m], fld_count[m], discs[m], imH2,  G2;
  print "++++++++++++++++++++++++++++++++++++";
end for;

assert IsQuadraticTwist(EllipticCurve("162d1"),EllipticCurve("162a2"));



