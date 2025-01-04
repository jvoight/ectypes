The following code accompanies the paper _On Galois inertial types of elliptic curves over QQ_p_ (https://arxiv.org/abs/2203.07787) by Lassina Dembele, Nuno Freitas, and John Voight.  

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

* Lemma 5.1.2 (calculating Table 2, unit groups in residue characteristic $3$) is verified in `canonical_map_check_pr3.m`.

* Lemma 6.1.1 (calculating Tables 5--7, unit groups in residue characteristic $2$) is verified in `canonical_map_check_pr2.m` and `canonical_map_check_pr2_v2.m`.  

* To verify the correctness of Tables 4 and 10, realizing types for elliptic curves over QQ_3 and QQ_2, respectively.  The code was developed to run in Magma V2.27-4, for example as follows.
```
load "norms_pr2_v3.m";
load "norms_pr3_v2.m";
```
