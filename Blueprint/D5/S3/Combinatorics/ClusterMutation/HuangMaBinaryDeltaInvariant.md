# The binary delta invariant for a fixed skew-symmetrizer

## Abstract

A fixed positive skew-symmetrizer permits at most two delta residues.

**Definition 1.1 (A positive skew-symmetrizer).**

$$\forall n \in \mathrm{Nat},\; \forall d \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right),\; (\operatorname{IsSkewSymmetrizer}\left(d, B\right)) \Leftrightarrow ((\forall i \in \operatorname{Fin}\left(n\right),\; 0 < d\left(i\right)) \land (\forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; (d\left(i\right): \mathbb{Z}) \cdot B\left(i, j\right) = -((d\left(j\right): \mathbb{Z}) \cdot B\left(j, i\right))))$$

*Formalization.* `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.IsSkewSymmetrizer` (`✓ std3`).

*Citation.* Min Huang and Qiling Ma (2026). *A mutation invariant for skew-symmetrizable matrices*. DOI: [10.1016/j.jalgebra.2026.07.040](https://doi.org/10.1016/j.jalgebra.2026.07.040). URL: <https://arxiv.org/abs/2602.03194v1>.

*Commentary.*

Section 1, p. 1: “A matrix B = (b_ij) ∈ M_n(Z) is called skew-symmetrizable if there exists a diagonal matrix D = diag(d_1, …, d_n) with positive integers d_i such that DB is skew-symmetric. Such a matrix D is called a skew-symmetrizer of B.” The index set is Fin n, the entries of B are integers, and d is a vector of positive natural numbers. The entrywise equation is exactly skew-symmetry of diag(d)·B; it also forces every diagonal entry of B to vanish.

**Definition 1.2 (The real symmetrization).**

$$\forall n \in \mathrm{Nat},\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right),\; \forall i \in \operatorname{Fin}\left(n\right),\; \forall j \in \operatorname{Fin}\left(n\right),\; \operatorname{symmetrization}\left(B\right)\left(i, j\right) = \operatorname{ite}\left(i = j, 2, \operatorname{ite}\left(i < j, (\operatorname{Int}.\operatorname{sign}\left(B\left(i, j\right)\right): \mathrm{Real}) \cdot \operatorname{Real}.\operatorname{sqrt}\left(\left|((B\left(i, j\right): \mathbb{Z}): \mathrm{Real}) \cdot (B\left(j, i\right): \mathrm{Real})\right|\right), (\operatorname{Int}.\operatorname{sign}\left(B\left(j, i\right)\right): \mathrm{Real}) \cdot \operatorname{Real}.\operatorname{sqrt}\left(\left|((B\left(i, j\right): \mathbb{Z}): \mathrm{Real}) \cdot (B\left(j, i\right): \mathrm{Real})\right|\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.symmetrization` (`✓ std3`).

*Citation.* Min Huang and Qiling Ma (2026). *A mutation invariant for skew-symmetrizable matrices*. DOI: [10.1016/j.jalgebra.2026.07.040](https://doi.org/10.1016/j.jalgebra.2026.07.040). URL: <https://arxiv.org/abs/2602.03194v1>.

*Commentary.*

Section 1, p. 2: “we define its symmetrization to be the symmetric matrix S(B) = (s_ij) ∈ M_n(R) given by s_ij = 2 if i = j, s_ij = sgn(b_ij)√|b_ij b_ji| if i < j, s_ij = sgn(b_ji)√|b_ij b_ji| if i > j, where sgn(x) denotes the sign of x, with the convention sgn(0) = 0.” The displayed ite expressions follow these three cases in order. Integer entries and Int.sign are coerced to Real, Real.sqrt is the nonnegative square root, and the absolute value is taken after multiplying the real entries.

**Definition 1.3 (Huang–Ma Remark 2.7).**

$$(claim) \Leftrightarrow (\forall n \in \mathrm{Nat},\; \forall d \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < d\left(i\right)) \Rightarrow (\exists r1 \in \operatorname{ZMod}\left(4\right),\; \exists r2 \in \operatorname{ZMod}\left(4\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right),\; (\operatorname{IsSkewSymmetrizer}\left(d, B\right)) \Rightarrow (\exists k \in \mathbb{Z},\; (\operatorname{Matrix}.\operatorname{det}\left(\operatorname{symmetrization}\left(B\right)\right) = (k: \mathrm{Real})) \land (((k: \operatorname{ZMod}\left(4\right)) = r1) \lor ((k: \operatorname{ZMod}\left(4\right)) = r2)))))$$

*Formalization.* `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.claim` (`✓ std3`).

*Citation.* Min Huang and Qiling Ma (2026). *A mutation invariant for skew-symmetrizable matrices*. DOI: [10.1016/j.jalgebra.2026.07.040](https://doi.org/10.1016/j.jalgebra.2026.07.040). URL: <https://arxiv.org/abs/2602.03194v1>.

*Commentary.*

Remark 2.7, p. 7: “We also conjecture that for any fixed n and any choice of skew-symmetrizer d₁, …, dₙ, the invariant δ is binary. This is supported by several explicit computations.” Definition 1.3, p. 2: “The δ-invariant of a skew-symmetrizable matrix B ∈ M_n(Z) is defined as δ(B) := det(S(B)) (mod 4)”. Binary means at most two residues, which may coincide; n = 1 has only the residue 2. The two residues are chosen after n and d and before B. The integer k records both integrality of the real determinant and its residue in ZMod 4. The formula also includes n = 0, whose determinant is 1.

**Theorem 1.4 (The delta invariant has at most two values).**

$$\forall n \in \mathrm{Nat},\; \forall d \in \operatorname{Fin}\left(n\right) \to \mathrm{Nat},\; (\forall i \in \operatorname{Fin}\left(n\right),\; 0 < d\left(i\right)) \Rightarrow (\exists r1 \in \operatorname{ZMod}\left(4\right),\; \exists r2 \in \operatorname{ZMod}\left(4\right),\; \forall B \in \operatorname{Matrix}\left(\operatorname{Fin}\left(n\right), \operatorname{Fin}\left(n\right), \mathbb{Z}\right),\; (\operatorname{IsSkewSymmetrizer}\left(d, B\right)) \Rightarrow (\exists k \in \mathbb{Z},\; (\operatorname{Matrix}.\operatorname{det}\left(\operatorname{symmetrization}\left(B\right)\right) = (k: \mathrm{Real})) \land (((k: \operatorname{ZMod}\left(4\right)) = r1) \lor ((k: \operatorname{ZMod}\left(4\right)) = r2))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.result` (`✓ std3`). ∎

*Resolves.* `Problems/huang-ma-2026-binary-delta-invariant` (proved) by `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"huang-ma-2026-binary-delta-invariant","declaration_gid":"D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Min Huang and Qiling Ma (2026). *A mutation invariant for skew-symmetrizable matrices*. DOI: [10.1016/j.jalgebra.2026.07.040](https://doi.org/10.1016/j.jalgebra.2026.07.040). URL: <https://arxiv.org/abs/2602.03194v1>.

*Commentary.*

The real symmetrization is diagonally similar to the integer matrix with diagonal 2, upper entries B(i,j), and lower entries −B(i,j). In odd size its determinant is even. In size 2m, pairing each determinant term with the inverse permutation gives the congruence det(A) = (−1)^m det(B) in ZMod 4. When det(DB) = 0, it is already a square. When det(DB) ≠ 0, the rational alternating form associated to DB is nondegenerate and has a symplectic basis. This basis gives a Gram matrix of determinant one, and change of basis shows that det(DB) is a rational square. Thus the product of the weights times det(B) is an integer square. Cancelling a common nonzero weight in two square products shows that any two nonzero attainable determinant residues agree in ZMod 4. The sign twist therefore leaves at most one nonzero residue, in addition to zero. This proves the conjecture without a coprimality assumption on the weights; it does not assert that both residues are attained or identify the even-size nonzero residue explicitly.

## References

- Truth anchor: `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.IsSkewSymmetrizer`
- Truth anchor: `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.claim`
- Truth anchor: `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.result`
- Truth anchor: `D5/S3/Combinatorics/ClusterMutation/HuangMaBinaryDeltaInvariant.symmetrization`
- Dependency: [D5/S3/QuadraticForms/SymplecticBasis](../../QuadraticForms/SymplecticBasis.md)
