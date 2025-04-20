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

* The computations in Lemma 5.1.2 (giving Tables 2 and 3) is in `unit_groups_pr3.m`.

* Correctness of Table 4, realizing types for elliptic curves over QQ_3, is verified in `inertial_type_pr3_check_v2`.

* The computations in Lemma 6.1.1 (giving Tables 5 and 6, and then 7) is in `unit_groups_pr2.m`.

* The projection maps (Remarks 5.1.3 and 6.1.2) are verified in `canonical_map_check_pr2_v2.m` and `canonical_map_check_pr3.m`.  
For example:
```
load "canonical_map_check_pr3.m";
```

* Table 10, realizing nonexceptional types for elliptic curves over QQ_2, is verified in `inertial_type_pr2_check_v3.m`.

* The computations in Lemma 7.2.2 (giving Tables 11 through 15) are given in `unit_grps_ex_type1.m` through `unit_grps_ex_type5.m`, depending on the field.

* Table 16 is verified in `inertial_ex_type_pr2_check2.m`.

* Table 17, realizing the exceptional types for elliptic curves over QQ_2, is verified in `inertial_ex_type_pr2_check_v2`.
