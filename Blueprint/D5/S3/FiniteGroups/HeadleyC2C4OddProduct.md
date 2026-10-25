# HeadleyC2C4OddProduct

## Abstract

An ordinary R-cycle on an arbitrary finite odd group supplies the exceptional product.

**Definition 1.1 (The complete original-coordinate constructor).**

Lean statement: `D5/S3/FiniteGroups/HeadleyC2C4OddProduct.c2c4_odd_product`

*Formalization.* `D5/S3/FiniteGroups/HeadleyC2C4OddProduct.c2c4_odd_product` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sigma and delta are the supplied RCycle successor and actual difference permutations. Both fix zero. The nonzero sigma orbit and delta injectivity give sigma(h) nonzero and sigma(h) unequal to h for h nonzero. No RStar, additive ranking or cyclic generator is assumed.

The original odd_box additive equivalence e:H→Box(ds) conjugates the original doubling permutation to B2(h)=h+h. DeltaT is negative doubling. Set f_a=sigma at a=0 and at the last column, and f_a=negation at the other six columns; set Delta_a=delta or DeltaT correspondingly.

A(a,h)=(a,h-s_a), F(a,x)=(a,f_a(x)), C_P(a,x)=(P(a),x), B(a,x)=(a,s_a+x). S0=A.trans F.trans C_P.trans B. With E(a,x)=(a,Delta_a(x)), R(a,y)=(a,y+s_(P(a))-s_a) and C_Q(a,y)=(Q(a),y), D0=A.trans E.trans R.trans C_Q. Each stage is an actual equivalence. Assume Q(a)=P(a)-a for every a. Then D0(a,h)=(Q(a),Delta_a(h-s_a)+s_(P(a))-s_a)=S0(a,h)-(a,h), including every closing edge.

The inverse of S0 at (b,t) has a=P.symm(b) and value (a,s_a+f_a.symm(t-s_b)). The inverse of D0 has a=Q.symm(b) and value (a,s_a+Delta_a.symm(t-s_(P(a))+s_a)). These are reverse compositions of the actual constituent inverses.

For the listed seven columns a_i, V(inl h)=(0,h) and V(inr(i,x))=(a_i,s_(a_i)+(-1)^i x). For a nonzero first coordinate its inverse looks up i and gives inr(i,(-1)^i(h-s_a)); at a=0 it gives inl h. V is a set equivalence. It is not used to transport differences. Assume P(0)=0, s(0)=0 and P(a_i)=a_(i+1 mod 7) for every i in Fin(7). Under these premises V conjugates sum(sigma,cylinder(sigma,4)) to S0: the six ordinary rows negate and the last row applies sigma after the even parity gauge.

The original cylinder_partial, cylinder_round and cylinder_rounds give intermediate columns j<7, return (0,h) after seven steps to (0,sigma(h)), and repeated seven-step returns. Distinct column indices exclude an earlier anchor visit. The input IsCycleOn bounded orbit has length m=card(H)-1 on nonzero h, so the nonzero return period is m. Its implemented equivalence uses exists_pow_eq and injOn_pow_apply, and pow_card_apply supplies the closing return used in connectivity. The original cylinder_connect and sum_sameCycle lifts give exactly three nonzero components: C_H={(0,h):h nonzero}, C_Z={(a,s_a):a nonzero}, and C_N={(a,h):a nonzero and h unequal to s_a}. Their sizes are m,7,7m; the remaining vertex is the fixed origin.

The source successor is Sprime=S0*swap(X,Y)*swap(Z,W). First X in C_H and Y in C_Z join different cycles, separated by the zero-column invariant. The nonzero-offset predicate is invariant under S0 and the first swap. Thus Z in the joined class and W in C_N still lie on different cycles, and the second original swap_joins merges them. The preservation clauses and the chart coverage connect every nonzero vertex; bijOn_complement at the untouched origin completes IsCycleOn.

The successor pairing is tau=swap(X,Y)*swap(Z,W) in both products. The label-source pairing is separately Lambda=swap(X,Z)*swap(Y,W) for HeadleyCubeOddProduct and Lambda=swap(X,W)*swap(Y,Z) for HeadleyC2C4OddProduct. Dprime=Lambda.trans D0. The four source calculations and identity away from those sources prove Dprime(x)=Sprime(x)-x universally. The successor inverse is S0.symm.trans(tau.symm), with tau=swap(X,Y)*swap(Z,W); the difference inverse is D0.symm.trans(Lambda.symm).

All formulas keep arbitrary finite odd noncyclic H. For nontrivial H, n=card(H) is odd and at least three, and m=n-1 is at least two. Allowed coincidences between shifts and between parameters are retained. For trivial H, the definition constructs Subsingleton H and Unique H with default zero and transports the same fixed coefficient RCycle through AddEquiv.prodUnique.symm.

The construction formalizes the supplied native R-only four-source proof. Original HeadleyExtension cylinder, invariant, sum-lift and swap-join proofs are reused at their source; odd_box and doubling reuse the original Gordon normalization. The existing RStar product has a stronger premise and is not applied here. This is repo-derived formal composition, with no mathematical novelty claim. The four-slot audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21215 for successor_ne_self, row_zero, shiftedSuccessor_apply, shifted_difference_spec, gauge_zero, chart_inr and joined_nonzero_cycle. Their current source owner and namespace are D5/S3/FiniteGroups/HeadleyCubeOddProduct and D5.S3.FiniteGroups.HeadleyCubeOddProduct, respectively; the issue uses their former HeadleyExceptionalRows owner, and each final declaration name is unchanged. No declared_validated registration is supplied. The arbitrary-subset, same-M, original-coordinate, coefficient-one parent and unrestricted AM remain open.

Original coordinates are K=ZMod(2)×ZMod(4). A=(0,2), B=(1,3), C=(0,3), D=(1,1), E=(1,0), F=(1,2), G=(0,1). In source order 0,A,B,C,D,E,F,G, P has image row 0,B,C,D,E,F,G,A and Q=P-id has row 0,D,E,F,C,A,B,G. Both explicit inverses are the reverse lookup rows. P is nonlinear; no additive-automorphism supplier is used. The closing G→A label is G, whereas -G=C on the later G→0 seam.

Choose v nonzero, w=sigma(v), d=w-v, q=-d, z=sigma(q). The elements v,w,d,q,z are nonzero; w is unequal to v and z is unequal to q. Thus z+d is nonzero and -z is unequal to d. No other parameter distinctness is imposed. In source order, shifts are 0,w,0,0,v,w,w-z,v. The chart columns are F,G,A,B,C,D,E.

Let r_j=sigma^j(z), 0≤j<m. These enumerate H minus zero, r_0=z, r_(m-1)=q and delta(q)=z+d. Define B(r)=((F,w-z+r),(G,v-r),(A,w+r),(B,-r),(C,r),(D,v-r),(E,w+r)).

The complete cyclic word is ((0,v),(A,w),(B,0),(C,0),(D,v),B(r_0),...,B(r_(m-1)),(E,w),(F,w-z),(G,v),(0,sigma(v)),(0,sigma^2(v)),...,(0,sigma^(m-1)(v))). Its last vertex is followed by its first. Blocks omit exactly the listed shift in each nonzero K fiber, restored by the seven exterior vertices; the zero fiber is the input nonzero orbit. Length 1+4+7m+3+(m-1)=8n-1.

The six internal block labels are (B,z-d-2r),(G,d+2r),(D,-w-2r),(E,2r),(F,v-2r),(C,d+2r). For j<m-1 the interblock label is (A,delta(r_j)-z).

Seam 1: (0,v)→(A,w), label (A,d).

Seam 2: (A,w)→(B,0), label (D,-w).

Seam 3: (B,0)→(C,0), label (E,0).

Seam 4: (C,0)→(D,v), label (F,v).

Seam 5: (D,v)→first B(z)=(F,w), label (G,d).

Seam 6: last B(q)=(E,v)→(E,w), label (0,d).

Seam 7: (E,w)→(F,w-z), label (A,-z).

Seam 8: (F,w-z)→(G,v), label (B,z-d).

Seam 9: (G,v)→(0,w), label (C,d), with -G=C.

The tail edges are (0,sigma^i(v))→(0,sigma^(i+1)(v)), 1≤i<m, with sigma^m(v)=v and labels (0,delta(sigma^i(v))). At i=m-1 this is the true closing edge to (0,v), label (0,v-sigma^(m-1)(v)). The full partition has 6m+(m-1)+9+(m-1)=8n-1 edges.

Bulk inventory by K label: 0 has the tail labels, omitting d among H minus zero, restored by seam 6. A has delta(r)-z for r outside {0,q}, omitting -z,d, restored by seams 7,1. B has z-d-2r, r nonzero, omitting z-d, restored by seam 8. C has d+2r, omitting d, restored by seam 9. D has -w-2r, omitting -w, restored by seam 2. E has 2r, omitting zero, restored by seam 3. F has v-2r, omitting v, restored by seam 4. G has d+2r, omitting d, restored by seam 5. Repeated formulas in distinct K fibers cannot collide. The A omissions follow from delta({0,q})={0,z+d} and are distinct because z is unequal to q=-d. All six affine families use the actual doubling equivalence. These are consequences of the universal consumed edge formula.

Cuts, in X,Y,Z,W order: X=(0,v), old image (0,w), old label (0,d), component C_H, new label (A,d). Y=(G,v), old image (A,w), old label (G,d), component C_Z, new label (C,d). Z=(D,v), old image (E,w), old label (C,d), component C_Z, new label (G,d). W=(E,v), old image (F,w), old label (A,d), component C_N with offset q, new label (0,d). Lambda=swap(X,W)*swap(Y,Z). The common-output equation at W is w-z+sigma(q)=w.

For trivial H the cyclic vertices (A,0),(B,0),(C,0),(D,0),(E,0),(F,0),(G,0) have labels (D,0),(E,0),(F,0),(C,0),(A,0),(B,0),(G,0), closing included. For n=3, w=-v,d=v,q=-v,z=v,m=2; the single A-interblock H label is zero and seams 7,1 supply -v,v. The single tail edge is the actual closing edge. No separate bounded H case replaces the construction.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyC2C4OddProduct.c2c4_odd_product`
- Dependency: [D5/S3/FiniteGroups/HeadleyCubeOddProduct](HeadleyCubeOddProduct.md)
