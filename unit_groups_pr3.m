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

e := Valuation(3*OK, PiK);
topf := [Order(mOKf(x)@@mf) : x in gs[1..2]];
OKf1, mOKf1 := quo<OK | PiK^(f0+e)>;
OKf1st, mf1 := UnitGroup(OKf1);
lvf := sub<OKf1st | [mOKf1(1+x)@@mf1 : x in Basis(PiK^f0)]>;  // (1 + pp^f)/(1 + pp^(f+e))
assert sub<lvf | [mOKf1(gs[i]^topf[i])@@mf1 : i in [1..2]]> eq lvf;
printf "  %o^%o (%o)^%o generates (1 + pp^f)/(1+pp^(f+1))\n", gs[1], topf[1], gs[2], topf[2];
