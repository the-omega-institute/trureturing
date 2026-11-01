# Exact maximal-independent spectra for binary cyclic matchings

## Abstract

Every admissible cardinality is realized by an actual maximal independent vertex set, including both closing twists.

A vertex is (i,b), where i lies in Fin(m+2) and b lies in ZMod 2. The graph contains the rung edge and the two orientations of forward matching transport. The function closing(m,q) is zero except at the closing edge, where it adds q. Spectrum means cardinalities of actual finite independent sets that dominate every omitted vertex. The parameter m is arbitrary natural, so m+2 includes the two-rung boundary. For a prism we instead write r+3, covering every cycle length at least three.

**Theorem 1.1 (Complete twisted spectrum).**

$$\forall m \in \mathrm{Nat},\; \forall q \in \operatorname{ZMod}\left(2\right),\; \forall k \in \mathrm{Nat},\; \operatorname{mem}\left(k, \operatorname{spectrum}\left(\operatorname{graph}\left(\operatorname{closing}\left(m, q\right)\right)\right)\right) \Leftrightarrow \left(\operatorname{add}\left(m, 2\right) \le \operatorname{mul}\left(2, k\right) \land \left(k \le \operatorname{add}\left(m, 2\right) \land \operatorname{castZMod2}\left(k\right) = q\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.closing_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Independence permits at most one selected vertex in each rung. Maximality forbids two consecutive empty rungs, giving m+2 at most twice the cardinality. Transporting the selected labels around the cycle gives the parity constraint. Conversely, place the requested number of occupied rungs with gaps of size at most one and solve the binary phase recursion. The resulting vertex Finset is independent and dominates every omitted vertex; its closing phase is exactly its cardinality modulo two.

**Theorem 1.2 (All native prisms).**

$$\forall r \in \mathrm{Nat},\; \forall k \in \mathrm{Nat},\; \operatorname{mem}\left(k, \operatorname{spectrum}\left(\operatorname{prism}\left(r\right)\right)\right) \Leftrightarrow \left(\operatorname{add}\left(r, 3\right) \le \operatorname{mul}\left(2, k\right) \land \left(k \le \operatorname{add}\left(r, 3\right) \land \operatorname{Even}\left(k\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.prism_spectrum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The zero closing twist is proved equal to the native Cartesian graph cycleGraph(r+3) box-product K2 on the same vertices. The two spectrum directions therefore give exactly the even cardinalities between the ceiling of half the rung count and the rung count.

**Theorem 1.3 (First-power prism classification).**

$$\forall r \in \mathrm{Nat},\; \operatorname{WellCovered}\left(\operatorname{prism}\left(r\right)\right) \Leftrightarrow \left(r = 0 \lor r = 2\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.prism_wellCovered_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The attained even spectrum is a singleton precisely for three or five rungs. Outside those two orders it contains two distinct admissible cardinalities.

**Theorem 1.4 (First-power twisted classification).**

$$\forall m \in \mathrm{Nat},\; \operatorname{WellCovered}\left(\operatorname{graph}\left(\operatorname{closing}\left(m, 1\right)\right)\right) \Leftrightarrow m \le 2$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.twisted_wellCovered_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The attained odd spectrum is a singleton precisely for two, three or four rungs. The two-rung graph includes its repeated closing boundary rather than assuming a longer cycle.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.closing_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.prism_spectrum`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.prism_wellCovered_iff`
- Truth anchor: `D5/S3/Combinatorics/Graph/Walks/BinaryRungSpectrum.twisted_wellCovered_iff`
- Dependency: [D5/S3/Combinatorics/Graph/Walks/MatchingCliqueCycle](MatchingCliqueCycle.md)
