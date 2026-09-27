# Exact Pairing-Graph Filtration of Transvection Generators

## Abstract

The actual Lie-generation filtration equals the independently constructed pairing-graph distance bands. Nondegeneracy gives a coefficientwise support obstruction beyond each band.

Let K be a field with 2 nonzero, I a finite index type with decidable equality, and H a skew-symmetric I-by-I matrix. Define N_i=e_i H(i,*) and C_ij=(E_ij+E_ji)H. All edges are tested by H(i,j) being nonzero.

L_0 is the linear span of the actual N_i. Recursively L_(k+1) is L_k plus the span of the actual commutators [X,N_i] for X in L_k. Independently, Within(H,k,i,j) means that there is an actual pairing walk from i to j using at most k edges. B_k is the span of C_ij with this property. Thus L_k uses at most k+1 generator occurrences. No graph-distance assumption is placed into the definition of the Lie layer.

**Theorem 1.1 (Every generation layer has an exact graph description).**

$$\operatorname{Skew}(H) \land \operatorname{Nonzero}(2) \Rightarrow \forall k, \operatorname{layer}(H, k) = \operatorname{band}(H, k)$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Monodromy/TransvectionLieFiltration.layer_eq_band` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every natural k, L_k=B_k. Neither invertibility of H nor connectedness of its graph is assumed. The proof uses C_ii=2N_i for the base. For the forward induction, [C_ij,N_v]=H_jv C_iv+H_iv C_jv either extends a path by one actual edge or has zero coefficient. For the reverse induction, split a path at its last edge, subtract the already available edge direction, and divide by the nonzero last-edge coefficient.

**Theorem 1.2 (A shorter calculation cannot hide an out-of-band coefficient).**

$$\operatorname{Skew}(H) \land \operatorname{Nonzero}(2) \land \operatorname{Nonzero}(\operatorname{det}(H)) \land \operatorname{Member}(X, \operatorname{layer}(H, k)) \land \operatorname{NoWalkWithin}(H, k, r, c) \Rightarrow \operatorname{inverseCoefficient}(X, H, r, c) = 0$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/Monodromy/TransvectionLieFiltration.layer_support` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If det(H) is nonzero and X belongs to L_k, then the (r,c) entry of X H-inverse is zero whenever no pairing walk of at most k edges joins r to c. The proof computes C_ij H-inverse=E_ij+E_ji from the actual inverse identity and extends the resulting zero-entry property through linear combinations. This is a lower bound from a genuine matrix coefficient, not a declared complexity label.

Yelton, arXiv:1703.10917v5, Remark 3.4, is prior art for diameter-dependent transvection-generation bounds in an l-adic setting. This development proves the exact full linear filtration together with its support obstruction. No claim of global priority or solution of the order-two Fano monodromy expectation is made.

## References

- Truth anchor: `D5/S3/Observer/Monodromy/TransvectionLieFiltration.layer_eq_band`
- Truth anchor: `D5/S3/Observer/Monodromy/TransvectionLieFiltration.layer_support`
