# The unrestricted grid-power zero-forcing conjecture is false

## Abstract

Conjecture 12 as printed fails: two initially black vertices force the three-by-two grid at power one, whereas the conjectured value is three.

**Definition 1.1 (Distance powers).**

$$\forall (V : Type), \forall (G : \operatorname{SimpleGraph}\left(V\right)), \forall (k : \mathbb{N}), \forall (x : V), \forall (y : V), (\operatorname{graphPower}\left(G, k\right).\operatorname{Adj}\left(x, y\right)) \Leftrightarrow ((x \ne y) \land (\operatorname{edist}\left(G, x, y\right) \le (k:ENat)))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.graphPower` (`✓ std3`).

*Citation.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

Section 2 defines the graph power on the same vertices by 1 ≤ distance ≤ k. The compiled definition uses distinct endpoints and SimpleGraph.edist, the shortest-walk length in extended natural numbers. Distinct endpoints have positive extended distance; unreachable endpoints have infinite distance and cannot be adjacent for a natural k. This gives the source semantics throughout the quantified domain, including all powers, rather than defining only the counterexample. The grid is Mathlib's Cartesian product of its n-vertex pathGraph.

**Definition 1.2 (Conjecture 12 as printed).**

$$(claim) \Leftrightarrow (\forall (b : \mathbb{N}), \forall (k : \mathbb{N}), \forall (ell : \mathbb{N}), (1 \le b) \Rightarrow ((1 \le k) \Rightarrow ((k + 1 \le ell) \Rightarrow (\operatorname{zeroForcingNumber}\left(\operatorname{graphPower}\left(\operatorname{boxProd}\left(\operatorname{pathGraph}\left(b\right), \operatorname{pathGraph}\left(ell\right)\right), k\right)\right) = b \cdot k))))$$

*Formalization.* `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.claim` (`✓ std3`).

*Citation.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

Exact source quote: Let b≥1, k≥1 and ℓ≥k+1. Then Z((P_b □ P_ℓ)^k)=bk. All three parameters are natural numbers; no b≤ℓ assumption is present. Fin n labels the source's n vertices by 0 through n−1. The imported zeroForcingNumber is the minimum cardinality of an initial finite black set whose Black closure is all vertices. Black.force is the ordinary unique-white-neighbor rule; no positive semidefinite or multiple-neighbor forcing variant is used. The full source immediately cites the classical k=1 formula min(b,ℓ) and reports computational support on a range containing (3,2,1); the classical formula conflicts with the unrestricted conjecture, and the reported computational support conflicts with the explicit counterexample. The classical formula is existing mathematics, not a novelty claim.

**Theorem 1.3 (The three-by-two counterexample).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/abiad-flagg-ghasemi-nezhad-zeijlemaker-2026-grid-power-zero-forcing` (refuted) by `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"abiad-flagg-ghasemi-nezhad-zeijlemaker-2026-grid-power-zero-forcing","declaration_gid":"D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Aida Abiad; Mary Flagg; Sina Ghasemi Nezhad; Sjanne Zeijlemaker (2026). *The Zero Forcing Number of Graph Powers*. DOI: [10.48550/arXiv.2610.03892](https://doi.org/10.48550/arXiv.2610.03892). URL: <https://arxiv.org/abs/2610.03892v1>.

*Commentary.*

Use b=3, k=1, ℓ=2. Label the vertices A=(0,0), B=(0,1), C=(1,0), D=(1,1), E=(2,0), F=(2,1). The edges are AB, AC, BD, CD, CE, DF and EF. With A and B initially black, the forces A→C, B→D, C→E, D→F color all six vertices. At each force, every neighbor other than the target is already black. Mathlib's edist_le_one_iff_adj_or_eq identifies the first graph power with the base graph. Nat.sInf_le applied to the two-element forcing set gives zeroForcingNumber≤2, contradicting the proposed value 3. Exact Z is unnecessary. The proof instantiates existing forcing constructors and distance/minimum interfaces and checks finite facts. A corrected conjecture with b≤ℓ is outside this result.

## References

- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.graphPower`
- Truth anchor: `D5/S3/Combinatorics/Graph/ZeroForcing/GridPowerZeroForcingRefutation.result`
- Dependency: [D5/S3/Combinatorics/GeneralizedPetersen/ZeroForcingThree](../../GeneralizedPetersen/ZeroForcingThree.md)
