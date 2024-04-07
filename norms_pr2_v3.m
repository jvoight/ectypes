

 

/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 400);
ZZ2 := Integers(Q2);


/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  bl := type[2] eq 0 select true else false;
  return bl;
end function;


/* The following proves that the principal series types in Propositions 6.2.1 arises from elliptic curves over Q2 */
/* There are two curves with principal series types corresponding to abelian fields in Table 9 */

print "+++++++++++++++++++++++++++++++++++++";
print "We first tests good reduction of the two curves giving rise to abelian fields L/Q2 and compute the corresponding norm subgroups";

C4:=CyclicGroup(4);
c_labels_ps:=["768b1", "768h1"];
pol_seq_ps:=[[ x^2 + x + 1, x^4 + 8*x^3 + 4*x^2 + 2 ], [ x^2 + x + 1, x^4 + 4*x^2 + 2 ]];
// LMFDB: 2.2.0.1, 2.4.11.1, 2.2.0.1, 2.4.11.2

fld_count := [ 0 : m in [1,2] ];
for h in pol_seq_ps do
  M := SplittingField(h[2], ZZ2);
  M := FieldOfFractions(M);
  assert IsIsomorphic(C4,AutomorphismGroup(M));
  for m in [1..#c_labels_ps] do
    c_lab := c_labels_ps[m];
    E := EllipticCurve(c_lab);
    if check_inertial_field(E, M) then
      fld_count[m] +:= 1;
    end if;
  end for;
end for;
fld_count;


Gs_ps := [ ];
NGs_ps := [* *];

for m in [1..#c_labels_ps] do
  UK, toOK := UnitGroup(ZZ2);
  R := quo<ZZ2 | 2^4>;
  G, fromG := MultiplicativeGroup(R);
  L := SplittingField(PolynomialRing(Q2)!pol_seq_ps[m][1]);
  L := SplittingField(PolynomialRing(L)!pol_seq_ps[m][2]);
  OL := Integers(L);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ ((R!toOK(H.l))@@fromG) : l in [1..Ngens(H)] ]>;
  gens:=[-1,5];
  gens2 := [ (R!s)@@fromG: s in gens ];
  G2 := AbelianGroup([ Order(s) : s in gens2 ]);
  psi := hom< G2 -> G | gens2 >;
  imH2 := [ (imH.m)@@psi : m in [1..Ngens(imH)] ];  
  Append(~NGs_ps, imH2);
  Append(~Gs_ps, G);
  c_labels_ps[m], imH2,  G;
  print "++++++++++++++++++++++++++++++++++++";	
end for;


print "+++++++++++++++++++++++++++++++++++++";
print "+++++++++++++++++++++++++++++++++++++";
print "+++++++++++++++++++++++++++++++++++++";

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

print "We now tests good reduction of the curves giving rise to non-abelian fields L/Q2 and compute the corresponding norm subgroups";


c_labels := [ "20a1", "256a1", "256d1", "80b1", "320c2", "320f2", "96a1", "288a1", "192a2", "576f2", "256b2", "256c1" ];
discs := [ 5, 5, 5, 5, 5, 5, -20, -4, -20, -4, -4, -4 ];
 cond_exp := [ 1, 4, 4, 2, 3, 3, 3, 3, 4, 4, 6, 6 ];
u_gens := [ [ ], [ -1, 3 ], [ -1, 3 ], [ -1 ], [ -1, 3 ], [ -1, 3 ], [ ], [ ], [ ], [ ], [ -3 ], [ -3 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */
 
pol_seq := [ [ x^3 - 2 ], [ x^2 + x + 1, x^4 + 12*x^2 + 6 ], [ x^2 + x + 1, x^4 + 4*x^2 + 6 ],
             [ x^6 + 3*x^4 - 4*x^3 + 3*x^2 + 12*x + 5 ], [ x^6 - 20*x^3 + 2 ], [ x^6 + 2 ],
             [ x^2 - 2*x + 2, x^8 + 4*x^6 + 28*x^4 + 20 ], [ x^2 - 2*x + 2, x^8 + 8*x^4 + 336 ],
             [ x^8 - 6*x^4 + 16*x^2 - 3 ], [ x^8 + 2*x^4 + 21 ], [ x^2 - 2*x + 2, x^8 + 20*x^4 + 52 ],
             [ x^2 - 2*x + 2, x^8 + 4*x^4 + 84 ] ];

lmfdb_pol_seq := 
[ 
  [ x^3 + 2 ],  // 2.3.2.1
  [ x^2 + x + 1,  // 2.2.0.1
    x^4 + 8*x + 18 ], // 2.4.11.18
  [ x^2 + x + 1, // 2.2.0.1
    x^4 + 8*x^3 + 8*x + 2 ], // 2.4.11.17
  [ x^6 + 2*x^3 + 2 ], // 2.6.8.1 
  [ x^6 + 4*x^3 + 2 ], // 2.6.11.1
  [ x^6 + 4*x^5 + 4*x^2 + 2 ], // 2.6.11.9
  [ x^2 + 2*x + 2, // 2.2.2.1
    x^8 + 2*x^6 + 4*x^3 + 4*x + 2 ], // 2.8.16.65
  [ x^2 + 2*x + 2, // 2.2.2.1
    x^8 + 2*x^6 + 4*x^3 + 4*x + 6 ], // 2.8.16.66
  [ x^8 + 2*x^6 + 4*x^5 + 4*x^3 + 10 ], // 2.8.18.74
  [ x^8 + 2*x^6 + 4*x^3 + 4*x^2 + 6 ], // 2.8.18.73
  [ x^2 + 2*x + 2, // 2.2.2.1
    x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14 ], // 2.8.24.66
  [ x^2 + 2*x + 2, // 2.2.2.1
    x^8 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 30 ] // 2.8.24.68
];

for i := 1 to #pol_seq do
  for j := 1 to #pol_seq[i] do
    Fpol := NumberField(pol_seq[i][j]);
    pp := Factorization(2*Integers(Fpol))[1][1];
    Fpolpp := Completion(Fpol,pp : Precision := 400);
    Kpol := NumberField(lmfdb_pol_seq[i][j]);
    pp := Factorization(2*Integers(Kpol))[1][1];
    Kpolpp := Completion(Kpol,pp : Precision := 400);
    assert IsIsomorphic(Fpolpp,Kpolpp);
  end for;
end for;

galoisGpsL:=[];
fld_count := [ 0 : m in [1..12] ];
for h in pol_seq do
  M := SplittingField(h, ZZ2);
  M := FieldOfFractions(M);
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


// the following establishes the column Galois groups of Table 9
tD4:=SmallGroup(16,8);
gps:=[*SymmetricGroup(3), DihedralGroup(4), DihedralGroup(4), DihedralGroup(6), DihedralGroup(6), DihedralGroup(6), tD4, tD4, tD4, tD4, tD4, tD4 *];
assert {IsIsomorphic(gps[i],galoisGpsL[i]) : i in [1..#galoisGpsL]} eq {true};


/* Finding the norm groups and their images inside G. */

Gs := [ ];
NGs := [* *];
for m := 1 to #discs do
  K := LocalField(Q2, x^2 - discs[m]);
  K := RamifiedRepresentation(K);
  OK := Integers(K);
  g := P!MinimalPolynomial(OK.1);
  g2 := P!MinimalPolynomial(K.1);
  K2 := ext<Rationals() | g>;
  OK2 := Integers(K2);
  BK := Basis(OK);
  BK2 := Basis(K2);
  gens := (discs[m] eq 5) select ([ 2*a1 + 1, a1 ] where a1 := Roots(x^2 + x - 1, K)[1][1]) else
                             ([ a1, 2*a1 - 1 ] where a1 := Roots(x^2 - Integers()!(discs[m]/4), K)[1][1]);
  UK, toOK := UnitGroup(OK);
  PiK := UniformizingElement(OK);
  PiK2 := Factorisation(2*OK2)[1][1];
  R := quo<OK | PiK^cond_exp[m]>;
  R2 := quo<OK2 | PiK2^cond_exp[m]>;
  phi2 := hom< R -> R2 | x :-> R2!(&+[ (ZZ!u[i])*BK2[i] : i in [1..#BK] ]) where u := Eltseq(OK!x) >;
  psi2 := hom< R2 -> R | x :-> R!(&+[ (ZZ!u[i])*BK[i] : i in [1..#BK] ]) where u := Eltseq(K2!(OK2!x)) >;
  UR2, mR2 := MultiplicativeGroup(R2);
  //HR2 := sub<UR2 | [ phi2(R!OK!Norm(toOK(UK.i)))@@mR2 : i in [1..Ngens(UK)] ]>;
  HR2:=sub<UR2 | [s@@mR2 : s in u_gens[m]]>;
  G, toG := UR2/HR2;
  gens2 := [ toG(phi2(R!s)@@mR2) : s in gens ];
  G2 := AbelianGroup([ Order(s) : s in gens2 ]);
  psi := hom< G2 -> G | gens2 >;
  L := SplittingField(PolynomialRing(K)!pol_seq[m][1]);
  if #pol_seq[m] eq 2 then
    L := SplittingField(PolynomialRing(L)!pol_seq[m][2]);
  end if;
  OL := Integers(L);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ toG(phi2(R!toOK(H.l))@@mR2) : l in [1..Ngens(H)] ]>;
  imH2 := [ (imH.m)@@psi : m in [1..Ngens(imH)] ];
  Append(~NGs, imH2);
  Append(~Gs, G2);
  print "++++++++++++++++++++++++++++++++++++";
  c_labels[m], fld_count[m], discs[m], imH2,  G2;
  print "++++++++++++++++++++++++++++++++++++";
end for;













                   
