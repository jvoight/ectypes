/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

ZZ := Integers();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 300);
ZZ2 := Integers(Q2);

/*************************************************************************************************************/
// The following proves that the types in Propositions 6.2.1, 6.4.1 and 6.5.1 arise from an elliptic curve over Q2

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "20a1", "256a1", "256d1", "768b1", "768h1", "80b1", "320c2", "320f2", "96a1", "288a1", "192a2", "576f2",
              "256b2", "256c1" ];

discs := [ 5, 5, 5, 1, 1, 5, 5, 5, -20, -4, -20, -4, -4, -4 ];
//discs := [ 5, 5, 5, 1, 1, 5, 5, 5, -20, -20, -20, -4, -4, -4 ];
//cond_exp := [ 1, 4, 4, 4, 4, 2, 3, 3, 3, 3, 3, 3, 6, 6 ];
cond_exp := [ 1, 4, 4, 4, 4, 2, 3, 3, 3, 3, 4, 4, 6, 6 ];
u_gens := [ [ ], [ -1, 3 ], [ -1, 3 ], [ ], [ ], [ -1 ], [ -1, 3 ], [ -1, 3 ], [ ], [ ], [ ], [ ], [ -3 ], [ -3 ] ];

/* Polynomials whose splitting fields are the fields of good reductions for the curves. */
 
pol_seq := [ [ x^3 - 2 ], [ x^2 + x + 1, x^4 + 12*x^2 + 6 ], [ x^2 + x + 1, x^4 + 4*x^2 + 6 ],
             [ x^2 + x + 1, x^4 + 8*x^3 + 4*x^2 + 2 ], [ x^2 + x + 1, x^4 + 4*x^2 + 2 ],
             [ x^6 + 3*x^4 - 4*x^3 + 3*x^2 + 12*x + 5 ], [ x^6 - 20*x^3 + 2 ], [ x^6 + 2 ],
             [ x^2 - 2*x + 2, x^8 + 4*x^6 + 28*x^4 + 20 ], [ x^2 - 2*x + 2, x^8 + 8*x^4 + 336 ],
             [ x^8 - 6*x^4 + 16*x^2 - 3 ], [ x^8 + 2*x^4 + 21 ], [ x^2 - 2*x + 2, x^8 + 20*x^4 + 52 ],
             [ x^2 - 2*x + 2, x^8 + 4*x^4 + 84 ] ];


/* This function checks the inertial field. */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  bl := type[2] eq 0 select true else false;
  return bl;
end function;


fld_count := [ 0 : m in [1..14] ];
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

Gs := [ ];
NGs := [ ];
for m := 1 to #discs do
  K := (discs[m] eq 1) select Q2 else SplittingField(PolynomialRing(Q2)!(x^2 - discs[m]));
  OK := Integers(K);
  PolsOK := PolynomialRing(OK);
  UK, toOK := UnitGroup(OK);
  PiK := UniformizingElement(OK);
  R := quo<OK | PiK^cond_exp[m]>;
  UR, fromR := MultiplicativeGroup(R);
  HR := sub<UR | [ (R!s)@@fromR : s in u_gens[m] ]>;
  G, toG := UR/HR;
  imUK := sub<G | [ toG(((R!toOK(UK.l))@@fromR)) : l in [1..Ngens(UK)] ]>;
  L := SplittingField(PolynomialRing(K)!pol_seq[m][1]);
  if #pol_seq[m] eq 2 then
    L := SplittingField(PolynomialRing(L)!pol_seq[m][2]);
  end if;
  OL := Integers(L);
  H, toH := NormGroup(OL, toOK);
  imH := sub<G | [ toG(((R!toOK(H.l))@@fromR)) : l in [1..Ngens(H)] ]>;
  Append(~NGs, imH);
  Append(~Gs, G);
end for;


\\ \\ \\

/* Checking that each inertial type is realised by an elliptic curve. */

for l in [1..14] do
  printf "%o&%o&%o&%o\\\\\n" , c_labels[l], NGs[l];
end for;
