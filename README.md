The following code accompanies the paper "On Galois inertial types of elliptic curves over QQ_p" by Lassina Dembele, Nuno Freitas, and John Voight.

To verify the correctness of Tables 4 and 10, concerning types for elliptic curves over QQ_3 and QQ_2, respectively.  The code was developed to run in Magma V2.27-4, for example as follows.
```
load "norms_pr2_v3.m";
load "norms_pr3_v2.m";
```

There is also an implementation of Table 1 using the fields in Tables 4, 10, and 17.

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