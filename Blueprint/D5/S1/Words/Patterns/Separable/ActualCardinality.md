# Actual Separable-Permutation Cardinalities

## Abstract

Actual minimum-cut partitions identify the literal avoidance and indecomposable counts.

**Theorem 1.1 (Disjoint minimum-cut enumeration).**

$$\operatorname{d}\left(s, n\right)=\operatorname{sum}\left(0<m<n, \operatorname{b}\left(s, m\right)\times\operatorname{a}\left(n-m\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCardinality.actual_signed_cut_enumeration` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

U(n) is the actual subtype of literal permutations avoiding 2413 and 3142; J(s,n) consists of the members with no proper cut of sign s. D(s,n) consists of the members admitting a proper cut, with no padding at length zero or one. Their cardinalities are a, b and d respectively.

For every Boolean sign and every natural length, the theorem supplies an equivalence from D(s,n) to the dependent sum over 0<m<n of J(s,m) times U(n-m). Its index is a minimum cut of the original actual permutation. The finite sum above is the exact cardinality of that disjoint union, including the empty index sets at n=0 and n=1.

The proof constructs the least-cut partition and proves its injectivity from minimum-cut uniqueness. Each fiber then uses the frozen actual minimum-cut Cartesian equivalence, with an explicit length transport. It does not import the unfrozen greatest-cut enumeration.

**Theorem 1.2 (The exact large and shifted small Schroder counts).**

$$n>0 \Rightarrow \operatorname{a}\left(n\right)=\operatorname{largeSchroder}\left(n-1\right) \land \operatorname{b}\left(s, n\right)=\operatorname{smallSchroder}\left(n\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Patterns/Separable/ActualCardinality.actual_schroder_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The empty actual avoiding class has cardinality one. For all positive n, a(n)=largeSchroder(n-1). For every sign and every natural n, b(s,n)=smallSchroder(n), using the pinned Mathlib shifted definition: smallSchroder(0)=smallSchroder(1)=1 and 2*smallSchroder(r+1)=largeSchroder(r) for r>0. In particular both actual indecomposable classes have cardinality one at n=0 and n=1.

Only for n>=2, twice either indecomposable cardinality equals a(n), and d(s,n)=b(not s,n). At lengths zero and one, d(s,n)=0. The theorem retains these genuine boundaries instead of padding proper signed classes or asserting sign-half at the singleton.

Value complementation exchanges the literal forbidden patterns and the cut sign, proving equal indecomposable counts. The frozen proper-sign/blocked-opposite interface and the actual finite complement partition give sign-half. Minimum-cut enumeration then gives a(n)=2*a(n-1)+sum(1<m<n,a(m)*a(n-m)); strong induction identifies the pinned large Schroder recurrence, and natural-number cancellation gives the shifted small counts.

These are source-faithful known enumeration bridges and reusable actual-carrier results, not a claim of mathematical originality, count-ratio asymptotics, an infinite limiting law, or completion of the full derangement-ratio conjecture.

## References

- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCardinality.actual_schroder_cardinality`
- Truth anchor: `D5/S1/Words/Patterns/Separable/ActualCardinality.actual_signed_cut_enumeration`
- Dependency: [D5/S1/Words/Patterns/Separable/EndpointHistoryKernel](EndpointHistoryKernel.md)
