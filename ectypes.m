/* This file computes the inertial type of an elliptic curve over QQ_ell, following [DFV] */

function check_inertial_field(E, L)
  EL := BaseChange(E, L);
  // compute reduction information and a minimal model of E over L
  type, Emin := LocalInformation(EL);
  //type[2] ne 0: minimal disc not a unit --> not the right field
  return type[2] eq 0;
end function;

intrinsic InertialType(E::CrvEll[FldRat], p::RngIntElt : ExtremeCare := false) -> MonStgElt, SeqEnum[RngIntElt]
  {Returns the inertial type of E as a string, with the data (d,f,r) as described by [DFV],
   and if E has potential good reduction return a field over which E obtains good reduction.}

  require IsPrime(p) : "p must be prime";
  return InertialType(ChangeRing(E,pAdicField(p,200)) : ExtremeCare := ExtremeCare);
end intrinsic;

intrinsic InertialType(E::CrvEll[FldPad] : ExtremeCare := false) -> 
        MonStgElt, SeqEnum[RngIntElt], FldPad
  {Returns the inertial type of E as a string, with the data (d,f,r) as described by [DFV],
   and if E has potential good reduction return a field over which E obtains good reduction.}

  QQ_p := BaseField(E);
  _<x> := PolynomialRing(Rationals());
  p := Prime(QQ_p);
  pstr := IntegerToString(p);
  _, _, vpNE, c_p, kodaira := Explode(LocalInformation(E));
  
  // Good reduction
  if vpNE eq 0 then
    return "trivial", _, QQ_p;
  // Multiplicative reduction
  elif vpNE eq 1 then
    return "special: tau_{St," cat pstr cat "}", _, _;
  end if;

  // This leaves additive reduction.
  assert vpNE ge 2;  // otherwise, what the heck?
  // First deal with p >= 5
  if p ge 5 then
    L := ext<QQ_p | x^2-p>;
    if Valuation(Conductor(ChangeRing(E,L))) eq 1 then 
      // Potentially multiplicative reduction is exactly type In* for n > 0
      // Equivalently, the quadratic twist by L has good reduction
      // this is just for sanity tho
      if ExtremeCare then
        n := NumberOfComponents(kodaira) - 5;
        assert kodaira eq KodairaSymbol("I" cat IntegerToString(n) cat "*");
        assert Valuation(Conductor(QuadraticTwist(E,p))) eq 1;
        G := InertiaGroup(GaloisRepresentation(E));
        assert #G eq 2;
      end if;  
      return "special: tau_{St," cat pstr cat "} tensor eps_" cat pstr, _, _;
    else 
      // additive, potentially good
      for e in [2,3,4,6] do
        estr := IntegerToString(e);
        L := ext<QQ_p | x^e-p>;
        if check_inertial_field(E,L) then
          if e eq 2 then
            if ExtremeCare then
              G := InertiaGroup(GaloisRepresentation(E));
              assert #G eq 2;
            end if;
            return "principal series: eps_" cat pstr, _, L;
          else
            red := [(p-1) mod e, (p+1) mod e];
            assert 0 in red;
            if ExtremeCare then
              G := InertiaGroup(GaloisRepresentation(E));
              assert IsCyclic(G) and #G eq e;
            end if;
            if red[1] eq 0 then // p = 1 (mod e)
              return "principal series: tau_{ps," cat pstr cat "}(1,1," cat 
                     estr cat ")", [1,1,e], L;
            else // red[2] eq 0
              u := Integers()!Nonsquare(GF(p));
              return "supercuspidal: tau_{sc," cat pstr cat "}(" cat 
                     IntegerToString(u) cat ",2," cat estr cat ")", [u,2,e], L;
            end if;
          end if;
        end if;
      end for;
      error "Something went wrong";
    end if;

  // Now p = 2 or p = 3
  else
    // check for potentially multiplicative reduction
    if p eq 3 then
      L := ext<QQ_p | x^2-3>;
      if Valuation(Conductor(ChangeRing(E,L))) eq 1 then 
        // Potentially multiplicative reduction; same as p >= 5
        if ExtremeCare then
          assert Valuation(Conductor(QuadraticTwist(E,p))) eq 1;
          G := InertiaGroup(GaloisRepresentation(E));
          assert #G eq 2;
        end if;
        return "special: tau_{St,3} tensor eps_3";
      end if;
    else
      for d in [-4,8,-8] do
        Lnum := NumberField(Polynomial([-d,0,1]));
        L := Completion(Lnum, Factorization(p*Integers(Lnum))[1][1] : Precision := 200);
        if Valuation(Conductor(ChangeRing(E,L))) eq 1 then 
          if ExtremeCare then
            assert Valuation(Conductor(QuadraticTwist(E,d))) eq 1;
            G := InertiaGroup(GaloisRepresentation(E));
            assert #G eq 2;
            if d eq -4 then 
              assert vpNE eq 4; 
            else;
              assert vpNE eq 6;
            end if;
          end if;
          return "special: tau_{St,2} tensor eps_{" cat IntegerToString(d) cat "}";
        end if;
      end for;  
    end if;
    
    // so additive, potentially good
    if p eq 3 then
			LMFDB_pol_seq := 
			[
			x^2 + 6, // LMFDB 3.2.1.1, same as x^2 - 3
			x^3 + 6*x^2 + 3, // LMFDB 3.3.4.2
			x^3 + 3*x^2 + 3, // 3.3.4.4
			x^4 + 3, // 3.4.3.1
			x^6 - 3*x^4 + 9*x^2 + 18*x + 12, // 3.6.9.11
			x^6 + 3*x^4 + 3, // 3.6.9.12
			x^12 + 3*x^4 + 3, // 3.12.15.1
			x^12 + 6*x^6 + 6*x^4 + 3,  // 3.12.15.12
			x^12 + 6*x^9 + 6*x^6 + 24*x^3 + 9*x^2 + 18*x + 6, // 3.12.23.122
			x^12 + 21*x^6 + 9*x^4 + 9*x^2 + 6, // 3.12.23.20
			x^12 + 3*x^9 + 15*x^6 + 9*x^5 + 9*x^4 + 18*x^2 + 24 // 3.12.23.14
			];
  
      // string, [d,f,r], e, N
			types_out := 
			[
			[* "principal series: eps_3", [], 2, 2 *],
			[* "principal series: tau_{ps,3}(1,2,3)", [1,2,3], 3, 4 *],
			[* "supercuspidal: tau_{sc,3}(-1,2,3)", [-1,2,3], 3, 4 *],
			[* "supercuspidal: tau_{sc,3}(-1,1,4)", [-1,1,4], 4, 2 *],
			[* "principal series: tau_{ps,3}(1,2,3) tensor eps_3", [1,2,3], 6, 4 *],
			[* "supercuspidal: tau_{sc,3}(-1,2,3) tensor eps_3", [-1,2,3], 6, 4 *],
			[* "supercuspidal: tau_{sc,3}(3,2,6)", [3,2,6], 12, 3 *],
			[* "supercuspidal: tau_{sc,3}(-3,2,6)", [-3,2,6], 12, 3 *],
			[* "supercuspidal: tau_{sc,3}(-3,4,6)_0", [-3,4,6], 12, 5 *],
			[* "supercuspidal: tau_{sc,3}(-3,4,6)_1", [-3,4,6], 12, 5 *],
			[* "supercuspidal: tau_{sc,3}(-3,4,6)_2", [-3,4,6], 12, 5 *] 
			];
    else // p eq 2
			LMFDB_pol_seq := 
			[ 
			x^2 + 2*x + 2, // 2.2.2.1
			x^2 + 4*x + 2, // 2.2.3.1
			x^2 + 2, // 2.2.3.3
			x^3 + 2,  // 2.3.2.1
			x^4 + 8*x + 18, // 2.4.11.18
			x^4 + 8*x^3 + 8*x + 2, // 2.4.11.17
			x^4 + 8*x^3 + 4*x^2 + 2, // 2.4.11.1
			x^4 + 4*x^2 + 2, // 2.4.11.2
			x^6 + 2*x^3 + 2, // 2.6.8.1 
			x^6 + 4*x^3 + 2, // 2.6.11.1
			x^6 + 4*x^5 + 4*x^2 + 2, // 2.6.11.9
			x^8 + 2*x^6 + 4*x^3 + 4*x + 2, // 2.8.16.65
			x^8 + 2*x^6 + 4*x^3 + 4*x + 6, // 2.8.16.66
			x^8 + 2*x^6 + 4*x^5 + 4*x^3 + 10, // 2.8.18.74
			x^8 + 2*x^6 + 4*x^3 + 4*x^2 + 6, // 2.8.18.73
			x^8 + 8*x^7 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 14, // 2.8.24.66
			x^8 + 12*x^6 + 14*x^4 + 4*x^2 + 8*x + 30  // 2.8.24.68
      ];
      LMFDB_pol_seq_exceptional := 
      // exceptional
      [
      x^8 + 2*x^3 + 2*x^2 + 2, // 2.8.10.2
      x^8 + 2*x^5 + 2*x^2 + 6, // 2.8.12.29
      x^8 + 4*x^6 + 4*x^5 + 4*x^4 + 2*x^2 + 4*x + 2, // 2.8.16.73 
      x^8 + 4*x^7 + 4*x^5 + 6*x^2 + 4*x + 10, // 2.8.16.71
      x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 4*x^2 + 8*x + 10, // 2.8.22.132
      x^8 + 4*x^7 + 4*x^2 + 8*x + 10, // 2.8.22.136
      x^8 + 4*x^7 + 8*x^4 + 8*x^3 + 12*x^2 + 2, // 2.8.22.138
      x^8 + 4*x^7 + 8*x^3 + 4*x^2 + 2 // 2.8.22.137
			];

			// string, [d,f,r], e, N
			types_out := 
      [
			[* "principal series: eps_{-1}", [], 2, 4 *],
			[* "principal series: eps_2", [], 2, 6 *],
			[* "principal series: eps_{-2}", [], 2, 6 *],
			[* "supercuspidal: tau_{sc,2}(5,1,3)", [5,1,3], 3, 2 *],
			[* "supercuspidal: tau_{sc,2}(5,4,4)", [5,4,4], 4, 8 *],
			[* "supercuspidal: tau_{sc,2}(5,4,4) tensor eps_{-4}", [5,1,3], 4, 8 *],
			[* "principal series: tau_{ps,2}(1,4,4)", [1,4,4], 4, 8 *],
			[* "principal series: tau_{ps,2}(1,4,4) tensor eps_{-4}", [1,4,4], 4, 8 *],
			[* "supercuspidal: tau_{sc,2}(5,1,3) tensor eps_{-4}", [5,1,3], 6, 4 *],
			[* "supercuspidal: tau_{sc,2}(5,1,3) tensor eps_8", [5,1,3], 6, 6 *],
			[* "supercuspidal: tau_{sc,2}(5,1,3) tensor eps_{-8}", [5,1,3], 6, 6 *],
			[* "supercuspidal: tau_{sc,2}(-20,3,4)", [-20,3,4], 8, 5 *],
			[* "supercuspidal: tau_{sc,2}(-4,3,4)", [-4,3,4], 8, 5 *],
			[* "supercuspidal: tau_{sc,2}(-20,3,4) tensor eps_8", [-20,3,4], 8, 6 *],
			[* "supercuspidal: tau_{sc,2}(-4,3,4) tensor eps_8", [-4,3,4], 8, 6 *],
			[* "supercuspidal: tau_{sc,2}(-4,6,4) tensor eps_8", [-4,6,4], 8, 8 *],
			[* "supercuspidal: tau_{sc,2}(-4,6,4)", [-4,6,4], 8, 8 *]
      ];
      types_out_exceptional :=
      [
      // exceptional
			[* "exceptional supercuspidal: tau_{ex,2,1}", [], 24, 3 *],
			[* "exceptional supercuspidal: tau_{ex,2,1} tensor eps_{-4}", [], 24, 4 *],
			[* "exceptional supercuspidal: tau_{ex,2,1} tensor eps_8", [], 24, 6 *],
			[* "exceptional supercuspidal: tau_{ex,2,1} tensor eps_{-8}", [], 24, 6 *],
			[* "exceptional supercuspidal: tau_{ex,2,2}", [], 24, 7 *],
			[* "exceptional supercuspidal: tau_{ex,2,2} tensor eps_{-4}", [], 24, 7 *],
			[* "exceptional supercuspidal: tau_{ex,2,2} tensor eps_8", [], 24, 7 *],
			[* "exceptional supercuspidal: tau_{ex,2,2} tensor eps_{-8}", [], 24, 7 *]
			];
    end if;

		if ExtremeCare then
      goodornot := [];
      for f in LMFDB_pol_seq do 
        Lnum := NumberField(f);
        L := Completion(Lnum, Factorization(p*Integers(Lnum))[1][1] : Precision := 200);
		  	Append(~goodornot, check_inertial_field(E,L));
      end for;
      blcnt := #[bl : bl in goodornot | bl]; 
			if blcnt gt 1 then
				degs := [Degree(LMFDB_pol_seq[i]) : i in [1..#LMFDB_pol_seq] | goodornot[i]];
        assert #[d : d in degs | d eq Min(degs)] eq 1;
      elif blcnt eq 0 then
        assert p eq 2;  // exceptional;
        goodornot_exceptional := [];
        for f in LMFDB_pol_seq_exceptional do
          Lnum := AbsoluteField(NumberField([f, x^3-2]));
          L := Completion(Lnum, Factorization(p*Integers(Lnum))[1][1] : Precision := 240);
  		  	Append(~goodornot_exceptional, check_inertial_field(E,L));
        end for;
        assert #[bl : bl in goodornot_exceptional | bl] eq 1;
			end if;
		end if;

		for i := 1 to #LMFDB_pol_seq do
			f := LMFDB_pol_seq[i];
			L := ext<QQ_p | f>;
			if check_inertial_field(E,L) then
				type := types_out[i];
        if ExtremeCare then
          assert SemistabilityDefect(E) eq Degree(L);
          assert vpNE eq type[4];
        end if;
        if ExtremeCare then
          try
            G := InertiaGroup(GaloisRepresentation(E));
            assert IsIsomorphic(G,GL(2,3));
          catch e
            print "Asked for ExtremeCare, but GalRep not verified";
          end try;
        end if;
				return type[1], type[2], L;
			end if;
		end for;
    
    // exceptional
    assert p eq 2;
    for i := 1 to #LMFDB_pol_seq_exceptional do
			f := LMFDB_pol_seq_exceptional[i];
			Lp := ext<QQ_p | f>;
      pi := UniformizingElement(Lp);
      L := ext<Lp | Polynomial([pi,0,0,1])>;
			if check_inertial_field(E,L) then
				type := types_out_exceptional[i];
        if ExtremeCare then
          assert SemistabilityDefect(E) eq 24;
          assert vpNE eq type[4];
          if ExtremeCare then
/*
            try
              G := InertiaGroup(GaloisRepresentation(E));  // hangs
              assert IsIsomorphic(G,GL(2,3));
            catch e
              print "Asked for ExtremeCare, but GalRep not verified";
            end try;
*/
            print "Asked for ExtremeCare, but GalRep not verified as exceptional";
          end if;
        end if;
				return type[1], type[2], Lp;
			end if;
		end for;

		error "Something went wrong";
	end if;
end intrinsic;



/* Test
while true do
  E := Random(CremonaDatabase());
  for pf in Factorization(Conductor(E)) do
    print pf[1], InertialType(E,pf[1] : ExtremeCare := true);
  end for;
end while;
*/



// these functions are wasteful, but good for sanity checks

intrinsic SemistabilityDefect(E::CrvEll[FldRat], p::RngIntElt) -> RngIntElt
  {For an elliptic curve E with potentially good reduction at p, 
   returns the semistability defect (the degree of the inertial field over the
   maximal unramified extension) of E over the p-adic numbers.}

  require IsPrime(p) : "p must be prime";
  return SemistabilityDefect(ChangeRing(E,pAdicField(p,200)));
end intrinsic;

intrinsic SemistabilityDefect(E::CrvEll[FldPad]) -> RngIntElt
  {For an elliptic curve E over the p-adic numbers with potentially good reduction, 
   returns the semistability defect (the degree of the inertial field over the
   maximal unramified extension).}

  QQ_p := BaseField(E);
  p := Prime(QQ_p);
  if p ne 3 then
    m := 3;
  else
    m := 4;
  end if;

  psim := DivisionPolynomial(E,m);
  _<x,y> := PolynomialRing(QQ_p, 2);
  f,h := HyperellipticPolynomials(E);
  // don't forget need y coordinate too
  g := Resultant(Evaluate(psim,x), y^2 - Evaluate(h^2+4*f,x), x);
  assert Degree(g) eq 2*Degree(psim);
  _<t> := PolynomialRing(QQ_p);
  g0t := Evaluate(g,[0,t]);
  L := SplittingField(g0t*Evaluate(psim,t));
  assert check_inertial_field(E, L);  // otherwise not semistable?
  return RamificationDegree(L);

/*
  psim := DivisionPolynomial(E,m);
  // don't forget need y coordinate too
  // just need y^2 = f(x) to have a root, which means we need sqrt(f(x)), 
  // and up to unramified extension that's just the parity of the valuation of f(x)
  f := HyperellipticPolynomials(SimplifiedModel(E));
  L := SplittingField(psim);
  L2 := UnramifiedExtension(L,2);
  rts := Roots(psim, L2);
  assert #rts eq Degree(psim);
  sqs := [L2 | 1];
  for r in rts do
    y2 := Evaluate(f,r[1]);
    if not &or[IsSquare(c*y2) : c in sqs] then
      sqs cat:= [c*y2 : c in sqs];
    end if;
  end for;
  assert UnramifiedSquareSymbol(sqs[1]) eq 1 and {UnramifiedSquareSymbol(s) : s in sqs[2..#sqs]} eq {0};
  return #sqs*RamificationDegree(L);  
*/
end intrinsic;
