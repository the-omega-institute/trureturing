# Coarse Endpoint Spectrum

## Abstract

The nested compensation family has all three coarse endpoints at size one, three at size two, and none thereafter.

**Definition 1.1 (Literal small-family routes).**

Lean statement: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.endpointRoute`

*Formalization.* `D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.endpointRoute` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The source names are P0, X1 through Xk, and Y0 through Y(k-1). Lean stores Xj at index j-1 and Yi at index i. Write qt=L R^(t-1) L L R, bh=R L R^(h-1) L L R and d=R R. At k=1 the lists for P0, X1 and Y0 are respectively [q1,q2], [q2,d] and [q1,b2]. At k=2 the lists for P0, Y0 and Y1 are [q1,b1,q2,q3], [q1,b1,b2,b3] and [q1,b1,q2,b2]. The route continues on the target leaf label and stops on the first merged nonleaf reply. Values of endpointRoute outside these cases impose no safety assertion.

**Theorem 1.2 (Exact targets and paid sets).**

$$\forall k: Nat, ((1 \le k) \implies (\forall z: \operatorname{Fin}\left(m\right), (((\exists qs: \operatorname{List}\left(Address\right), (\operatorname{Safe}\left(F, z, qs\right))) \iff \operatorname{E}\left(k, z\right)) \land ((\operatorname{E}\left(k, z\right)) \implies ((\operatorname{Safe}\left(F, z, \operatorname{R}\left(k, z\right)\right)) \land (\exists pi: Strategy, ((\operatorname{CoarseObservable}\left(\operatorname{policy}\left(pi\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), (\operatorname{C}\left(pi, \operatorname{F}\left(i\right)\right) = 3k+14-\operatorname{indicator}\left(i = z\right))) \land (\operatorname{J}\left(pi, \operatorname{F}\left(z\right)\right) = \operatorname{L}\left(\operatorname{F}\left(z\right)\right)) \land (\forall i: \operatorname{Fin}\left(m\right), ((i \neq z) \implies (\exists q: Address, ((\operatorname{First}\left(\operatorname{R}\left(k, z\right), F, i\right) = \operatorname{some}\left(q\right)) \land (\neg (\operatorname{Member}\left(q, \operatorname{L}\left(\operatorname{F}\left(i\right)\right)\right))) \land (\operatorname{J}\left(pi, \operatorname{F}\left(i\right)\right) = \operatorname{L}\left(\operatorname{F}\left(i\right)\right) \cup \{q\}))))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every k at least one, F is the existing nested compensation family transported from Unit plus Fin(k) plus Fin(k) to Fin(m) by Fintype.equivFin. Thus m=2k+1 and every member has n=3k+13 leaves. E(k,z) abbreviates the condition k=1, or k=2 with z equal to P0 or some Yi. Safe(F,z,qs) means the existing Peels predicate from the full survivor set. This gives the full endpoint spectrum: at k=1 every target, at k=2 exactly P0,Y0,Y1, and at k at least three the empty set.

R(k,z) denotes endpointRoute(k,e.symm(z)). L(U) denotes the actual leaf-address set; J(pi,U) denotes paid(terminal(pi,U).1); C(pi,U) denotes cost(pi,U). First(R,F,i) is List.find? for the predicate leafLabel(F(i),a)=none. The theorem gives the literal list's safety and a globally correct Strategy with CoarseObservable policy. The target pays exactly its leaves. Each different member pays its leaves together with its first nonleaf exit address, which is actually reached and is outside its leaf set.

The full target-leaf response table rules out all other targets. For Xj with j at least two, Yi at the two adjacent contraction positions have identical replies on every target leaf, so a safe list cannot split them. For X1 at k at least two, every target-leaf nonleaf group contains at least two competitors. For P0 and each Yi at k at least three, retain every member except X1. The first left slot is constant on this retained set; each other nonempty nonleaf group has at least two retained members. Induction along any proposed safe list preserves the retained set and contradicts the final singleton condition.

The six small endpoint lists safely remove one competitor at each nonleaf exit. The existing coarse peeling equivalence compiles each list with the complete labelled-leaf verifier and finite acquisition fallback. Its exact paid-set contract supplies the stated bills and endpoint costs.

## References

- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.endpointRoute`
- Truth anchor: `D5/S3/Arith/FibonacciAtomic/CoarseEndpointSpectrum.result`
- Dependency: [D5/S3/Arith/FibonacciAtomic/CoarseEndpointPeeling](CoarseEndpointPeeling.md)
- Dependency: [D5/S3/Arith/FibonacciAtomic/Scale38LeafFrontierResponse](Scale38LeafFrontierResponse.md)
