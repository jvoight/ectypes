The following code accompanies the paper _On Galois inertial types of elliptic curves over QQ_p_ (https://arxiv.org/abs/2203.07787) by Lassina Dembele, Nuno Freitas, and John Voight.  

The code was developed to run in Magma V2.27-4.

* Table 1 is implemented as follows (running over random elliptic curves):

```
Attach("ectypes.m");
while true do
  E := Random(CremonaDatabase());
  for pf in Factorization(Conductor(E)) do
    print pf[1], InertialType(E,pf[1]);
  end for;
end while;
```

One can use the flag `ExtremeCare := true` for further sanity checks.

* Lemma 5.1.2 (calculating Table 2, unit groups in residue characteristic $3$) is verified in `canonical_map_check_pr3.m`.  For example:
```
load "canonical_map_check_pr3.m";
```
* Correctness of Table 4, realizing types for elliptic curves over QQ_3, is verified in `norms_pr3_v2.m`.

* Lemma 6.1.1 (calculating Tables 5-7, unit groups in residue characteristic $2$) is verified in `canonical_map_check_pr2.m` and `canonical_map_check_pr2_v2.m`.  

* Table 10, realizing nonexceptional types for elliptic curves over QQ_2, is verified in `norms_pr2_v3.m`.

* Table 17, realizing the exceptional types for elliptic curves over QQ_2, is verified in `inertial_ex_type_pr2_check2.m`.
