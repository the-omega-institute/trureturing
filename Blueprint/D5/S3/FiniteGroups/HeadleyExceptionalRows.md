# HeadleyExceptionalRows

## Abstract

Shared shifted rows and the seven-column cylinder serve both exceptional products.

**Remark 1.1 (Actual row and difference equivalences).**

Lean statement: `D5/S3/FiniteGroups/HeadleyExceptionalRows.shiftedSuccessor`

*Formalization.* `D5/S3/FiniteGroups/HeadleyExceptionalRows.shiftedSuccessor` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Sigma and delta are the supplied RCycle successor and actual difference permutations. Both fix zero. The nonzero sigma orbit and delta injectivity give sigma(h) nonzero and sigma(h) unequal to h for h nonzero. No RStar, additive ranking or cyclic generator is assumed.

The original odd_box additive equivalence e:H→Box(ds) conjugates the original doubling permutation to B2(h)=h+h. DeltaT is negative doubling. Set f_a=sigma at a=0 and at the last column, and f_a=negation at the other six columns; set Delta_a=delta or DeltaT correspondingly.

A(a,h)=(a,h-s_a), F(a,x)=(a,f_a(x)), C_P(a,x)=(P(a),x), B(a,x)=(a,s_a+x). S0=A.trans F.trans C_P.trans B. With E(a,x)=(a,Delta_a(x)), R(a,y)=(a,y+s_(P(a))-s_a) and C_Q(a,y)=(Q(a),y), D0=A.trans E.trans R.trans C_Q. Each stage is an actual equivalence. D0(a,h)=(Q(a),Delta_a(h-s_a)+s_(P(a))-s_a)=S0(a,h)-(a,h), including every closing edge.

The inverse of S0 at (b,t) has a=P.symm(b) and value (a,s_a+f_a.symm(t-s_b)). The inverse of D0 has a=Q.symm(b) and value (a,s_a+Delta_a.symm(t-s_(P(a))+s_a)). These are reverse compositions of the actual constituent inverses.

For the listed seven columns a_i, V(inl h)=(0,h) and V(inr(i,x))=(a_i,s_(a_i)+(-1)^i x). For a nonzero first coordinate its inverse looks up i and gives inr(i,(-1)^i(h-s_a)); at a=0 it gives inl h. V is a set equivalence. It is not used to transport differences. V conjugates sum(sigma,cylinder(sigma,4)) to S0: the six ordinary rows negate and the last row applies sigma after the even parity gauge.

The original cylinder_partial, cylinder_round and cylinder_rounds give intermediate columns j<7, return (0,h) after seven steps to (0,sigma(h)), and repeated seven-step returns. Distinct column indices exclude an earlier anchor visit. The input IsCycleOn bounded orbit has length m=card(H)-1 on nonzero h, so the nonzero return period is m. Its implemented equivalence uses exists_pow_eq and injOn_pow_apply, and pow_card_apply supplies the closing return used in connectivity. The original cylinder_connect and sum_sameCycle lifts give exactly three nonzero components: C_H={(0,h):h nonzero}, C_Z={(a,s_a):a nonzero}, and C_N={(a,h):a nonzero and h unequal to s_a}. Their sizes are m,7,7m; the remaining vertex is the fixed origin.

The source successor is Sprime=S0*swap(X,Y)*swap(Z,W). First X in C_H and Y in C_Z join different cycles, separated by the zero-column invariant. The nonzero-offset predicate is invariant under S0 and the first swap. Thus Z in the joined class and W in C_N still lie on different cycles, and the second original swap_joins merges them. The preservation clauses and the chart coverage connect every nonzero vertex; bijOn_complement at the untouched origin completes IsCycleOn.

The label-source permutation Lambda has the separate pairing listed below. Dprime=Lambda.trans D0. The four source calculations and identity away from those sources prove Dprime(x)=Sprime(x)-x universally. The successor inverse is S0.symm.trans(tau.symm), with tau=swap(X,Y)*swap(Z,W); the difference inverse is D0.symm.trans(Lambda.symm).

All formulas keep arbitrary finite odd noncyclic H. For nontrivial H, n=card(H) is odd and at least three, and m=n-1 is at least two. Allowed coincidences between shifts and between parameters are retained. For trivial H, the definition constructs Subsingleton H and Unique H with default zero and transports the same fixed coefficient RCycle through AddEquiv.prodUnique.symm.

The construction formalizes the supplied native R-only four-source proof. Original HeadleyExtension cylinder, invariant, sum-lift and swap-join proofs are reused at their source; odd_box and doubling reuse the original Gordon normalization. The existing RStar product has a stronger premise and is not applied here. This is repo-derived formal composition, with no mathematical novelty claim. The new public shared-helper four-slot audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21215; no declared_validated registration is supplied. The arbitrary-subset, same-M, original-coordinate, coefficient-one parent and unrestricted AM remain open.

## References

- Truth anchor: `D5/S3/FiniteGroups/HeadleyExceptionalRows.shiftedSuccessor`
- Dependency: [D5/S3/FiniteGroups/HeadleyExtension](HeadleyExtension.md)
- Dependency: [D5/S3/FiniteGroups/HeadleyOddRows](HeadleyOddRows.md)
