# All-size enumeration of matchings avoiding 132, 213 and 321

## Abstract

An explicit formal series enumerates the original P13 avoiding perfect matchings at every natural size.

This unit concerns the P13 clause of Section 6, Question 1 in Biswas, Shankar and Sivasubramanian, arXiv:2609.08562v1. The carrier is the existing subtype of fixed-point-free involutions on Fin(2n) avoiding every pattern in P13 = {132, 213, 321}. An occurrence requires the three left endpoints to precede all three right endpoints; pattern labels follow the complementary right-endpoint convention. Empty and disconnected matchings are included. The P1 clause is outside this unit.

Write a_n for the natural cardinality of that subtype and A_0(X) = Σ a_n Xⁿ for actualSeries. All identities below hold in ℚ⟦X⟧. Put δ = (1 − X)², P = Φ₁, R = Φ₂, D = δ(1 − 2X − X²)P − X³(1 + X)R, and G = 1 + X(1 − X)³PD⁻¹. The inverse is the formal unit inverse of D, whose constant coefficient is one.

The scalar supplier defines Φ_j independently of matching counts: its coefficient at degree n is the finite sum, for 0 ≤ k ≤ n, of the coefficients of c_k (X^(j+1)δ⁻¹)^k. Here c_k = (−1)^k X^(k.choose 2) Σ_{r=0}^k DenInv(r)DenInv(k−r), and DenInv(r) is the unit inverse of ∏_{i=1}^r (1 − Xⁱ). This specifies the coefficient formula without a recurrence definition of a_n.

**Theorem 1.1 (The actual transformed series equals G).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actual_A_eq_G`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actual_A_eq_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The actual H supplier defines h_k as the kth polynomial-coefficient row of its transformed literal completion series. Its three boundary laws and its proved Bulk recurrence supply every premise of the private boundary elimination. The t² law contains X(1−X)h₀. The actual minimal-solution identity at j=2 and the explicit Φ difference at j=1 give the remaining two equations. They imply (A−1)D = X(1−X)³P. Comparing with G_cleared and cancelling the unit D proves A=G. The proof never divides by X, h₀ or h₁, and assumes no equality with G.

**Theorem 1.2 (Lawful change of variable on the actual carrier).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_subst_zeta_eq_G`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_subst_zeta_eq_G` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The original counting series satisfies A_0.subst ζ = G, where ζ = X(1+X)⁻². The proof identifies the H supplier’s Z with the Catalan supplier’s ζ using their square-unit identities, then uses Mathlib’s subst_eq_eval₂ under the discrete coefficient topology to identify the actual eval₂ series. The catalytic marker remains polynomial coefficient evaluation, not substitution of a nonzero-constant outer series.

**Theorem 1.3 (Recovering the original counting series).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_eq_G_subst_q`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_eq_G_subst_q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Ira M. Gessel (2016). *Lagrange Inversion*. DOI: [10.48550/arXiv.1609.05988](https://doi.org/10.48550/arXiv.1609.05988). URL: <https://arxiv.org/abs/1609.05988v1>.

*Commentary.*

Let q be the rational image of Mathlib’s Catalan series minus one. Then A_0 = G.subst q. Both ζ and q have zero constant coefficient, so HasSubst is proved for each. Mathlib’s lawful substitution associativity and the retained inverse identity ζ.subst q = X recover the original series. The unused reverse inverse is omitted from this delivery.

**Theorem 1.4 (The unconditional cardinality coefficient formula).**

Lean statement: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Sucharita Biswas, Umesh Shankar, Sivaramakrishnan Sivasubramanian (2026). *Matchings and shape-Wilf-Equivalence of sets of patterns of length three I: Triples*. DOI: [10.48550/arXiv.2609.08562](https://doi.org/10.48550/arXiv.2609.08562). URL: <https://arxiv.org/abs/2609.08562v1>.

*Commentary.*

The empty matching count is a₀=1. For every natural n≥1, the rational cast of the original cardinality a_n is coeff n ((1−X)(1+X)^(2n−1)G). The arbitrary-series Catalan/Lagrange transform applies to the explicit G after recovery of A_0. There is no Bulk, H, recurrence, height bound, finite-n restriction, or equality-to-G hypothesis in the final statement. This is a formal P13 enumeration proof; it does not assert official acceptance, unique credit, worldwide novelty, or resolution of all of Question 1.

## References

- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_eq_G_subst_q`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actualSeries_subst_zeta_eq_G`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.actual_A_eq_G`
- Truth anchor: `D5/S3/Combinatorics/PatternMatchings/P13Enumeration.result`
- Dependency: [D5/S3/Combinatorics/Nonnesting/CatalanLagrangeBridge](../Nonnesting/CatalanLagrangeBridge.md)
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13HCoefficients](P13HCoefficients.md)
- Dependency: [D5/S3/Combinatorics/PatternMatchings/P13Scalar](P13Scalar.md)
