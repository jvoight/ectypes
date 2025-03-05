// Gives Tables 5 and 6 proving Lemma 6.1.1, describing unit groups and their quotients for p = 2

QQ := Rationals();
PolsQ<x> := PolynomialRing(QQ);

// choose a line here
d := 5; K<s> := NumberField(x^2-d); gs_fin := [-1,3]; gs_inf := [s,s*(-1+s)/2]; f0 := 3;
// d := -4; K<s> := NumberField(x^2-d); gs_fin := [-3]; gs_inf := [s/2,s-1]; f0 := 5;
// d := -20; K<s> := NumberField(x^2-d); gs_fin := [-3]; gs_inf := [s/2,s-1]; f0 := 5;
// d := 8; K<s> := NumberField(x^2-d); gs_fin := [-1,9]; gs_inf := [-3,s/2-1]; f0 := 7;
// d := 40; K<s> := NumberField(x^2-d); gs_fin := [-1,9]; gs_inf := [-3,s/2-1]; f0 := 7;
// d := -8; K<s> := NumberField(x^2-d); gs_fin := [3]; gs_inf := [-3,s/2-1]; f0 := 7;
// d := -40; K<s> := NumberField(x^2-d); gs_fin := [3]; gs_inf := [-3,s/2-1]; f0 := 7;

gs := gs_inf cat gs_fin;
gs_oo := [gs_fin[#gs_fin], gs_inf[#gs_inf]];

OK := Integers(K);
PiK := Factorisation(2*OK)[1][1];

e := Valuation(2*OK,PiK);
assert f0 gt e;

// do finite calculation up to reasonable f
print "p=2 data\n=====\n\n";
for f := 1 to 20 do
  print "-----\nf =", f;
  OKf, mOKf := quo<OK | PiK^f>;
  OKfst, mf := UnitGroup(OKf);
  Uf := sub<OKfst | [mOKf(Norm((mf(u))@@mOKf))@@mf : u in Generators(OKfst)]>;
  if sub<Uf | mOKf(gs_fin[1])@@mf> eq Uf then
    print "  ", gs_fin[1], "generates U_ff with order", #Uf;
  else
    assert #gs_fin eq 2 and sub<Uf | [mOKf(x)@@mf : x in gs_fin[1..2]]> eq Uf;
    print "  ", Explode(gs_fin[1..2]), "generates U_ff with orders", 
      Explode([Order(mOKf(x)@@mf) : x in gs_fin[1..2]]);
  end if;
  
  OUq, mOUq := quo<OKfst | Uf>;
  if sub<OUq | mOUq(mOKf(gs_inf[2])@@mf)> eq OUq then
    print "  ", gs_inf[2], "generates (O_K/ff)^*/U_ff with order", #OUq;
  else
    assert #gs_inf eq 2 and sub<OUq | [mOUq(mOKf(x)@@mf) : x in gs_inf[1..2]]> eq OUq;
    print "  ", Explode(gs_inf[1..2]), "generates (O_K/ff)^*/U_ff with orders", 
      Explode([Order(mOUq(mOKf(x)@@mf)) : x in gs_inf[1..2]]);
  end if;
end for;

// induction argument
print "\n\n.. Base case and induction step\n";
OKf, mOKf := quo<OK | PiK^f0>;
OKfst, mf := UnitGroup(OKf);
assert sub<OKfst | [mOKf(x)@@mf : x in gs]> eq OKfst;
print "  ", Explode(gs), "generates (O_K/pp^f)^*, f =", f0;

topf := [Order(mOKf(x)@@mf) : x in gs_oo[1..2]];
OKf1, mOKf1 := quo<OK | PiK^(f0+e)>;
OKf1st, mf1 := UnitGroup(OKf1);
lvf := sub<OKf1st | [mOKf1(1+x)@@mf1 : x in Basis(PiK^f0)]>;  // (1 + pp^f)/(1 + pp^(f+e))
assert sub<lvf | [mOKf1(gs_oo[i]^topf[i])@@mf1 : i in [1..2]]> eq lvf;
printf "  %o^%o (%o)^%o generates (1 + pp^f)/(1+pp^(f+e))\n", gs_oo[1], topf[1], gs_oo[2], topf[2];

