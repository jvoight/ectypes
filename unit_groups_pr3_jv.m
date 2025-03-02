// Gives Table 2 proving Lemma 5.1.2, describing unit groups and their quotients for p = 3

QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);

// choose a line here
d := -1; K<s> := QuadraticField(d); gs := [-4,s+2]; f0 := 1;
// d := 3; K<s> := QuadraticField(d); gs := [4,s-1]; f0 := 2;
// d := -3; K<s> := QuadraticField(d); xi := (1+s)/2; gs := [4,xi-3,-xi]; f0 := 4;

OK := Integers(K);
PiK := Factorisation(3*OK)[1][1];

// do finite calculation up to reasonable f
print "p=3 data\n=====\n\n";
for f := 1 to 20 do
  print "-----\nf =", f;
  OKf, mOKf := quo<OK | PiK^f>;
  OKfst, mf := UnitGroup(OKf);
  Uf := sub<OKfst | [mOKf(Norm((mf(u))@@mOKf))@@mf : u in Generators(OKfst)]>;
  assert sub<Uf | mOKf(gs[1])@@mf> eq Uf;
  print "  ", gs[1], "generates U_ff with order", #Uf;
  
  OUq, mOUq := quo<OKfst | Uf>;
  if sub<OUq | mOUq(mOKf(gs[2])@@mf)> eq OUq then
    print "  ", gs[2], "generates (O_K/ff)^*/U_ff with order", #OUq;
  else
    assert d eq -3 and sub<OUq | [mOUq(mOKf(x)@@mf) : x in gs[2..3]]> eq OUq;
    print "  ", Explode(gs[2..3]), "generates (O_K/ff)^*/U_ff with orders", 
      Explode([Order(mOUq(mOKf(x)@@mf)) : x in gs[2..3]]);
  end if;
end for;

// induction argument
print "\n\n.. Base case and induction step\n";
OKf, mOKf := quo<OK | PiK^f0>;
OKfst, mf := UnitGroup(OKf);
assert sub<OKfst | [mOKf(x)@@mf : x in gs]> eq OKfst;
print "  ", Explode(gs), "generates (O_K/pp^f)^*, f =", f0;

topf := [Order(mOKf(x)@@mf) : x in gs[1..2]];
OKf1, mOKf1 := quo<OK | PiK^(f0+1)>;
OKf1st, mf1 := UnitGroup(OKf1);
lvf := sub<OKf1st | [mOKf1(1+x)@@mf1 : x in Basis(PiK^f0)]>;  // (1 + pp^f)/(1 + pp^(f+1))
assert sub<lvf | [mOKf1(gs[i]^topf[i])@@mf1 : i in [1..2]]> eq lvf;
printf "  %o^%o (%o)^%o generates (1 + pp^f)/(1+pp^(f+1))\n", gs[1], topf[1], gs[2], topf[2];

/* Remark 5.1.5: images of generators by the canonical surjection. */

if d eq -3 then
  w := (1+s)/2;
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
end if;

