# Gorenstein pairs for alternating adjacent-sum polytopes

## Abstract

For s at least two, the alternating adjacent-sum polytope in dimension 2r is Gorenstein exactly when s = 3 and r = 1.

**Definition 1.1 (The alternating adjacent-sum polytope).**

$$\forall s \in \mathbb{N},\; \forall d \in \mathbb{N},\; \operatorname{P}\left(s, d\right) = \{x : (\operatorname{Fin}\left(d\right) \to \mathbb{R}) \mid (\forall i \in \operatorname{Fin}\left(d\right),\; 0 \le x\left(i\right)) \land (\forall i \in \operatorname{Fin}\left(d\right),\; \forall j \in \operatorname{Fin}\left(d\right),\; (\operatorname{val}\left(j\right) = \operatorname{val}\left(i\right) + 1) \Rightarrow (x\left(i\right) + x\left(j\right) \le (s : \mathbb{R}) + \operatorname{ite}\left(\left(\operatorname{val}\left(i\right) + 1\right) \bmod 2 = 0, 1, 0\right)))\}$$

*Formalization.* `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.P` (`✓ std3`).

*Citation.* Xinru Jiang, Suzhen Wen, Yueming Zhong (2026). *Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series*. URL: <https://arxiv.org/abs/2607.14887v1>.

*Commentary.*

Section 1, equation (1), p. 2, reads: “For integers d ≥ 2 and s ≥ 1, define” followed by P_d^(s) = {x = (x₁,…,x_d) ∈ ℝ^d_{≥0} : x_i + x_{i+1} ≤ s + δ_i, 1 ≤ i ≤ d − 1}, and “where δ_i = 0 for i odd and δ_i = 1 for i even.” Coordinates in Fin d start at zero, so the capacity at i is s + ite((val(i) + 1) % 2 = 0, 1, 0). Here ite is Lean's conditional and % is natural-number remainder. The pair i,j with val(j) = val(i) + 1 gives exactly the paper's adjacent constraints. The formula also defines the set for other natural parameters; the theorem uses s ≥ 2 and d = 2r ≥ 2.

**Definition 1.2 (Interior lattice points and translation).**

$$\forall s \in \mathbb{N},\; \forall d \in \mathbb{N},\; (\operatorname{IsGorenstein}\left(s, d\right)) \Leftrightarrow (\exists q \in \mathbb{N},\; (1 \le q) \land (\exists c \in \operatorname{Fin}\left(d\right) \to \mathbb{Z},\; \forall n \in \mathbb{N},\; \forall x \in \operatorname{Fin}\left(d\right) \to \mathbb{Z},\; ((\lambda i : \operatorname{Fin}\left(d\right) \mapsto (x\left(i\right) : \mathbb{R})) \in \operatorname{interior}\left(\operatorname{smul}\left((n + q : \mathbb{R}), \operatorname{P}\left(s, d\right)\right)\right)) \Leftrightarrow ((\lambda i : \operatorname{Fin}\left(d\right) \mapsto (\left(x - c\right)\left(i\right) : \mathbb{R})) \in \operatorname{smul}\left((n : \mathbb{R}), \operatorname{P}\left(s, d\right)\right))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.IsGorenstein` (`✓ std3`).

*Citation.* Xinru Jiang, Suzhen Wen, Yueming Zhong (2026). *Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series*. URL: <https://arxiv.org/abs/2607.14887v1>.

*Commentary.*

The proof of Theorem 1.9, p. 44, states: “We use the standard interior-lattice-point characterization of Gorenstein lattice polytopes; see, for example, [13, 7].” It gives int((n + 3)T₁^r) ∩ ℤ^(2r) = c_r + (nT₁^r ∩ ℤ^(2r)) for all n ≥ 0. Here the same characterization allows any positive natural index q and integral translation c. The ambient interior is Mathlib's interior in Fin d → ℝ. The operator smul is the real scalar action on sets, including the actual zero dilation. The pointwise casts of x and x − c embed the integral lattice in that real space. Parenthesized ascriptions to ℝ denote these canonical casts; no change of lattice or relative interior is used.

**Definition 1.3 (Question Q1 and its answer).**

$$(claim) \Leftrightarrow (\forall s \in \mathbb{N},\; \forall r \in \mathbb{N},\; (2 \le s) \Rightarrow ((1 \le r) \Rightarrow ((\operatorname{IsGorenstein}\left(s, 2 \cdot r\right)) \Leftrightarrow ((s = 3) \land (r = 1)))))$$

*Formalization.* `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Xinru Jiang, Suzhen Wen, Yueming Zhong (2026). *Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series*. URL: <https://arxiv.org/abs/2607.14887v1>.

*Commentary.*

Question Q1, §4, p. 48, reads: “Theorem 1.9, Proposition 3.21, and Corollary 3.24 show that s = 1 yields an infinite Gorenstein family, whereas every s ≥ 2 eventually fails. For s = 3, direct computation (Propositions 3.22 and 3.23) shows that only d = 2 is Gorenstein in even dimensions d ≤ 6; we conjecture this extends to all d ≥ 4. Characterize all (s, r) with s ≥ 2 for which P_{2r}^(s) is Gorenstein.” The natural parameter r is positive, and the displayed claim supplies the complete answer to the characterization question: precisely s = 3 and r = 1.

**Theorem 1.4 (The unique Gorenstein pair).**

$$claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result` (`✓ std3`). ∎

*Resolves.* `Problems/jiang-wen-zhong-2026-alternating-polytope-gorenstein-pairs` (proved) by `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"jiang-wen-zhong-2026-alternating-polytope-gorenstein-pairs","declaration_gid":"D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Xinru Jiang, Suzhen Wen, Yueming Zhong (2026). *Alternating adjacent-sum polytopes: transfer matrices and Ehrhart series*. URL: <https://arxiv.org/abs/2607.14887v1>.

*Commentary.*

At n = 0 the translation identity makes the interior lattice point of qP unique. Positivity forces each coordinate of c to be at least one and qs ≥ 3. The all-ones point is interior, so uniqueness gives c = 1. If qs ≥ 4, the point (2,1,…,1) is a second interior lattice point. Thus qs = 3, and s ≥ 2 forces q = 1 and s = 3. In every dimension d ≥ 3, the integral point (1,4,3,1,…,1) belongs to the interior of 2P: its adjacent sums are 5, 7, 4, 2, …, below the alternating capacities 6, 8, 6, 8, …. After subtracting one, its second adjacent sum is 5, exceeding capacity 4. This contradicts the n = 1 translation identity. In dimension two, q = 1 and c = (1,1) give the required identity for every n, including n = 0. The classification concerns the stated lattice-translation characterization; no assertion about unimodality or real-rootedness is needed.

## References

- Truth anchor: `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.IsGorenstein`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.P`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.claim`
- Truth anchor: `D5/S3/Combinatorics/Geometry/AlternatingAdjacentSumGorenstein.result`
