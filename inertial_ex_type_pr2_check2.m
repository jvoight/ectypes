/* This file checks that each inertial type described for p = 2 are realised by some elliptic curve. */

ZZ := Integers();
QQ := Rationals();
P<x> := PolynomialRing(ZZ);
Q2 := pAdicField(2, 50);
ZZ2 := Integers(Q2);
OE<a> := ext<ZZ2 | x^3 - 2>;
E := FieldOfFractions(OE);
PolsE<t> := PolynomialRing(E);
K0<a1> := NumberField(x^3 - 2);
PolsK0<z> := PolynomialRing(K0);

// The following are the curves listed in Table 8 with e \neq 2 
c_labels := [ "648b1", "1296c1", "5184e1", "5184w1", "3456a1", "3456e1", "3456o1", "3456c1" ];
cond_exps := [ 3, 6, 12, 12, 11, 11, 11, 11 ];
n_gens := [ [5..5], [3..5], [1..5], [1..5], [2..5], [2..5], [2..5], [2..5] ];
gen_seqs :=
[
    [
        [ a^2 + a + 1, 0  ],
        [ -1, -a^2  ],
        [ -a^2 - a + 3, -2*a^2 + 4 ],
        [ -a^2 - a + 1, -a^2 + 2 ],
        [ 1, -1 ]
    ],
    [
        [ a^2 + a + 1, 0 ],
        [ -1, -a^2 ],
        [ -a^2 - a + 3, -2*a^2 + 4 ],
        [ -a^2 - a + 1, -a^2 + 2 ],
        [ 1, -1 ]
    ],
    [
        [ a^2 + a + 1, 0  ],
        [ -1, -a^2  ],
        [ -a^2 - a + 3, -2*a^2 + 4 ],
        [ -a^2 - a + 1, -a^2 + 2 ],
        [ 1, -1 ]
    ],
    [
        [ a^2 + a + 1, 0 ],
        [ -1, -a^2 ],
        [ -a^2 - a + 3, -2*a^2 + 4 ],
        [ -a^2 - a + 1, -a^2 + 2 ],
        [ 1, -1 ]
    ],
    [
        [ a^2 + 1, 0 ],
        [ -1, -1 ],
        [ -a^2 + 1, -2*a + 2 ],
        [ a^2 - a + 1, -a + 1 ],
        [ -2*a + 1, -a + 1 ]
    ],
    [
        [ a^2 + 1, 0 ],
        [ -1, -1 ],
        [ -a^2 + 1, -2*a + 2 ],
        [ a^2 - a + 1, -a + 1 ],
        [ -2*a + 1, -a + 1 ]
    ],
    [
        [ a^2 + 1, 0 ],
        [ -1, -1 ],
        [ -a^2 + 1, -2*a + 2 ],
        [ a^2 - a + 1, -a + 1 ],
        [ -2*a + 1, -a + 1 ]
    ],
    [
        [ a^2 + 1, 0 ],
        [ -1, -1 ],
        [ -a^2 + 1, -2*a + 2 ],
        [ a^2 - a + 1, -a + 1 ],
        [ -2*a + 1, -a + 1 ]
    ]
];



/* Polynomials whose splitting fields are the fields of good reductions for the curves. */

pol_seq1 := [ x^8 + 20*x^2 + 20,
             x^8 + 28*x^2 + 20,
             x^8 + 2*x^6 + 20,
             x^8 + 6*x^6 + 20,
             x^8 + 4*x^7 + 12*x^2 + 14,
             x^8 + 4*x^7 + 4*x^2 + 14,
             x^8 + 4*x^7 + 12*x^2 + 10,
             x^8 + 4*x^7 + 12*x^2 + 2 ];

pol_seq2 := [ [ t^2 + a*t + a, t^2 + a*t + a^2 + a ], [ t^2 + a*t + a, t^2 + a*t + a^2 + a ], 
              [ t^2 + a*t + a, t^2 + a*t + a^2 + a ], [ t^2 + a*t + a, t^2 + a*t + a^2 + a ],
              [ t^2 + 2*t + a + 2, t^2 + 2*t + a + 6 ], [ t^2 + 2*t + a + 2, t^2 + 2*t + a + 6 ],
              [ t^2 + 2*t + a + 2, t^2 + 2*t + a + 6 ], [ t^2 + 2*t + a + 2, t^2 + 2*t + a + 6 ] ];

pol_seq3 := [ [ z^2 + a1*z + a1, z^2 + a1*z + a1^2 + a1 ], [ z^2 + a1*z + a1, z^2 + a1*z + a1^2 + a1 ],
              [ z^2 + a1*z + a1, z^2 + a1*z + a1^2 + a1 ], [ z^2 + a1*z + a1, z^2 + a1*z + a1^2 + a1 ],
              [ z^2 + 2*z + a1 + 2, z^2 + 2*z + a1 + 6 ], [ z^2 + 2*z + a1 + 2, z^2 + 2*z + a1 + 6 ],
              [ z^2 + 2*z + a1 + 2, z^2 + 2*z + a1 + 6 ], [ z^2 + 2*z + a1 + 2, z^2 + 2*z + a1 + 6 ] ];

_<x2> := PolynomialRing(ZZ2);
_<x2E> := PolynomialRing(OE);

for i := 1 to #pol_seq1 do  // the 8 fields K_{i,r} with i = 1,2 and r = +/-1, +/-2
  f := pol_seq1[i];
  print f;
  Kir := SplittingField(Parent(x2)!f);
  assert #Roots(x^3-2,Kir) ge 1;
     // OK, now we can work with the relative extension, which will be a bit easier

  Kir := SplittingField(Parent(x2E)!f);
  for g in pol_seq2[i] do
    assert #Roots(g,Kir) ge 1;
  end for;
end for;


/* Some useful global polynomials. */

Gs := [ ];
NGs := [ ];
for m := 1 to #pol_seq1 do
  for l := 1 to #pol_seq2[m] do
    OK<b> := ext<OE | pol_seq2[m][l]>;
    K := FieldOfFractions(OK);
    BK := AbsoluteBasis(K);
    K1<b1> := ext<K0 | pol_seq3[m][l]>;
    K2 := AbsoluteField(NumberField(K1));
    K2 := OptimizedRepresentation(K2);
    OK2 := Integers(K2);
    BK1 := [ K2 | s1*s2 : s1 in [ 1, a1, a1^2 ], s2 in [ 1, b1 ] ];
    BK2 := Basis(K2);
    T := Matrix([ Eltseq(s) : s in BK2 ])*Matrix([ Eltseq(K2!s) : s in BK1 ])^-1;
    assert [ P!MinimalPolynomial(s, Q2) : s in BK ] eq [ P!MinimalPolynomial(s, ZZ) : s in BK1 ];
    PiK := UniformizingElement(OK);
    PiK2 := Factorisation(2*OK2)[1][1];

    /* Finding the norm groups and their images inside G. */

    g := Factorisation(pol_seq1[m], OK)[1][1];
    OL := SplittingField(g);
    R := quo<OK | PiK^cond_exps[m]>;
    R2 := quo<OK2 | PiK2^cond_exps[m]>;
    phi2 := hom< R -> R2 | x :-> R2!(&+[ (ZZ!u[n])*BK1[n] : n in [1..#BK] ])
                                        where u := &cat [ Eltseq(s) : s in Eltseq(ss), ss in Eltseq(K!OK!x) ] >;
    psi2 := hom< R2 -> R | x :-> R!(&+[ (QQ!u[n])*BK[n] : n in [1..#BK] ])
                                                            where u := Eltseq(Vector(QQ, Eltseq(K2!OK2!x))*T) >;
    UK, toOK := UnitGroup(OK);
    UR2, mR2 := MultiplicativeGroup(R2);
    HR2 := sub<UR2 | [ phi2(R!OK!Norm(toOK(UK.l)))@@mR2 : l in [1..Ngens(UK)] ]>;
    G, toG := UR2/HR2;
    gens := gen_seqs[m][n_gens[m]];
    gens2 := [ toG(phi2(R!s)@@mR2) : s in gens ];
    G2 := AbelianGroup([ Order(s) : s in gens2 ]);
    cond_exps[m];
    [ Order(s) : s in gens2 ];
    psi := hom< G2 -> G | gens2 >;
    H, toH := NormGroup(OL, toOK);
    imH := sub<G | [ toG(phi2(R!toOK(H.l))@@mR2) : l in [1..Ngens(H)] ]>;
    gg2 := [ (imH.m)@@psi : m in [1..Ngens(imH)] ];
    imH2 := sub<G2 | gg2>;
    ss := (#imH2 eq 1) select [] else [ Order(g) : g in gg2 ];
    ss;
    gg2;
    //Append(~NGs, imH2);
    //Append(~Gs, G2);
  end for;
end for;


\\ \\ \\

/* Checking that each inertial type is realised by an elliptic curve. */

for l in [1..14] do
  printf "%o&%o&%o&%o\\\\\n" , c_labels[l], NGs[l];
end for;


