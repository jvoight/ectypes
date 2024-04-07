/* From Table 2 we see there is a new cyclic factor appearing in the case Q(sqrt(-3)) when conductor groes frpm f=3 to f=4 */
/* The following computes the image of the chosen generators under the canonical projection map */


QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);
K<b> := QuadraticField(-3);
OK<w> := Integers(K);

PiK := Factorisation(3*OK)[1][1];
R1 := quo< OK | PiK^3 >;
R2 := quo< OK | PiK^4 >;
U1, mR1 := UnitGroup(R1);
U2, mR2 := UnitGroup(R2);
G1, mG1 := quo< U1 | 4@@mR1 >;
G2, mG2 := quo< U2 | 4@@mR2 >;
gens := [ -w, w - 3 ];
gens1 := [ mG1((R2!(w - 3))@@mR1) ];
gens2 := [ mG2((R2!s)@@mR2) : s in gens ];
gens2_images := [ mG1((R1!s)@@mR1) : s in gens ];

G := AbelianGroup([ Order(gens1[1]) ]);
H := AbelianGroup([ Order(s) : s in gens2 ]);
psi := hom< G -> G1 | gens1 >;
phi := hom< H -> G2 | gens2 >;



printf "The images of the chosen generators under the canonical map: %o -> %o\n\n", H, G;
[ mG1((R1!OK!mR2(phi(H.m)@@mG2))@@mR1)@@psi : m in [1..Ngens(H)] ];
