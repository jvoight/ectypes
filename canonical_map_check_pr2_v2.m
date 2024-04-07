/* Some small checks on the canonical surjections. */


/* From Table 6 we see that for d=8,40,-8,-40 there is a new cyclic factor appearing in the case Q(sqrt(d)) when conductor goes from f=4 to f=5 */
/* The following computes the image of the chosen generators under the corresponding canonical projection map */

discs := [ 8, 40, -8, -40 ];
u_gens := [ [ -1 ], [ -1 ], [ 3 ], [ 3 ] ];
ZZ := Integers();
QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);

for m in [1..#discs] do
  K<b> := QuadraticField(discs[m]);
  OK := Integers(K);
  PiK := Factorisation(2*OK)[1][1];
  R1 := quo< OK | PiK^4 >;
  R2 := quo< OK | PiK^5 >;
  U1, mR1 := UnitGroup(R1);
  U2, mR2 := UnitGroup(R2);
  G1, mG1 := quo< U1 | [ s@@mR1 : s in u_gens[m] ] >;
  G2, mG2 := quo< U2 | [ s@@mR2 : s in u_gens[m] ] >;
  w := Roots(x^2 - ZZ!(discs[m]/4), OK)[1][1];
  gens := [ -3, w - 1 ];
  gens1 := [ mG1((R2!(w - 1))@@mR1) ];
  gens2 := [ mG2((R2!s)@@mR2) : s in gens ];
  gens2_images := [ mG1((R1!s)@@mR1) : s in gens ];
  G := AbelianGroup([ Order(gens1[1]) ]);
  H := AbelianGroup([ Order(s) : s in gens2 ]);
  psi := hom< G -> G1 | gens1 >;
  phi := hom< H -> G2 | gens2 >;

  /* Images of generators by the canonical surjection. */

  printf "The images of the chosen generators under the canonical map: %o -> %o\n\n", H, G;
  print "dicriminant equal to d = ", discs[m]; 
  [ mG1((R1!OK!mR2(phi(H.m)@@mG2))@@mR1)@@psi : m in [1..Ngens(H)] ];
printf "\n";
end for;

