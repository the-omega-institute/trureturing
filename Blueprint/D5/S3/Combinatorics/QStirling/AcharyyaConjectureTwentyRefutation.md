# Acharyya's pointwise Conjecture 20

## Abstract

The full universal pointwise identity in Acharyya's Conjecture 20 fails for one standard signed partition with n = 3 and k = 1: the two sides are 1 and 2.

**Definition 1.1 (The original universal pointwise identity).**

$$(claim) \Leftrightarrow (\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall pi \in \operatorname{List}\left(\operatorname{Finset}\left(\mathbb{Z}\right)\right),\; (\operatorname{Standard}\left(n, k, pi\right)) \Rightarrow (\operatorname{rcb}\left(\operatorname{f}\left(n, k, pi\right)\right) = \operatorname{ros}\left(pi\right) + k \cdot (k - 1)))$$

*Formalization.* `D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.claim` (`✓ std3`).

*Citation.* Amrita Acharyya (2024). *Type B Set partitions, an analogue of restricted growth functions*. DOI: [10.61091/ars162-14](https://doi.org/10.61091/ars162-14). URL: <https://arxiv.org/abs/2404.14439v1>.

*Commentary.*

Amrita Acharyya, arXiv:2404.14439v1, Conjecture 20: “We have that $\operatorname{rcb}\left(\operatorname{f}\left(n, k, pi\right)\right) = \operatorname{ros}\left(pi\right) + k \cdot (k - 1)$ for all π ∈ S_B(⟨n⟩,k).” The journal locator is DOI 10.61091/ars162-14, Conjecture 3.16. The quantifiers range over all natural n and k and every list of finite signed blocks; Standard imposes the original domain, not a finite search window.

Write Blocks = List(Finset(ℤ)), ℓ = length(π), and S_i = block(π,i), with S_i = ∅ outside the list. For a finite signed block S, negate(S) = {−s : s ∈ S}. The absolute extrema used by the source and the implementation are:

$\forall S \in \operatorname{Finset}\left(\mathbb{Z}\right),\; (\operatorname{minAbs}\left(S\right) = \operatorname{ite}\left(S = \left\{\right\}, 0, \min\{\left|s\right|:s \in S\}\right)) \land (\operatorname{maxAbs}\left(S\right) = \max(\left\{0\right\}\cup\{\left|s\right|:s \in S\}))$

The empty minimum and maximum are both zero. On Standard inputs every indexed block is nonempty, so these defaults do not affect the claim. All natural extrema in signed comparisons are coerced to integers. Definition 7 gives the following complete predicate; range(t) is {0,…,t−1}, Icc(a,b) is the integer interval including both endpoints, and pairwise disjointness is literal disjointness of the signed sets.

$\forall n \in \mathbb{N},\; \forall k \in \mathbb{N},\; \forall pi \in \operatorname{List}\left(\operatorname{Finset}\left(\mathbb{Z}\right)\right),\; (\operatorname{Standard}\left(n, k, pi\right)) \Leftrightarrow ((ell = 2 \cdot k + 1) \land ((\forall i \in \operatorname{range}\left(ell\right),\; \neg S_{i} = \left\{\right\}) \land ((\forall i \in \operatorname{range}\left(ell\right),\; \forall j \in \operatorname{range}\left(ell\right),\; (\neg i = j) \Rightarrow (\operatorname{Disjoint}\left(S_{i}, S_{j}\right))) \land ((\operatorname{biUnion}\left(\operatorname{range}\left(ell\right), S\right) = \operatorname{Icc}\left(-n, n\right)) \land ((0 \in S_{0}) \land ((\operatorname{negate}\left(S_{0}\right) = S_{0}) \land ((\forall r \in \operatorname{range}\left(k\right),\; S_{2 \cdot r + 2} = \operatorname{negate}\left(S_{2 \cdot r + 1}\right)) \land ((\forall r \in \operatorname{range}\left(k\right),\; \operatorname{minAbs}\left(S_{2 \cdot r + 2}\right) \in S_{2 \cdot r + 2}) \land ((\operatorname{minAbs}\left(S_{0}\right) = 0) \land (\forall r \in \operatorname{range}\left(k + 1\right),\; \forall t \in \operatorname{range}\left(k + 1\right),\; (r < t) \Rightarrow (\operatorname{minAbs}\left(S_{2 \cdot r}\right) < \operatorname{minAbs}\left(S_{2 \cdot t}\right))))))))))))$

Thus the list has 2k+1 nonempty disjoint blocks covering {−n,…,n}; S_0 contains zero and is closed under negation; each even block is the negative of the preceding odd block; the positive absolute minimum belongs to the even block; and the even-block minima strictly increase from zero. There is no positivity restriction on a general signed letter in ros.

Definition 13 fixes zero and complements absolute values while preserving signs. Its total implementation on integers is:

$\forall n \in \mathbb{N},\; \forall z \in \mathbb{Z},\; \operatorname{complementLetter}\left(n, z\right) = \operatorname{ite}\left(z = 0, 0, \operatorname{ite}\left(0 < z, n + 1 - z, -(n + 1 + z)\right)\right)$

Here image(c_n,S) means {c_n(s) : s ∈ S}; complement(n,π) maps this image operation over every block in its original order. For every natural n,k and list π, to standardize, orient every nonzero adjacent pair, and then sort all pairs by the absolute minimum of their even component:

$\forall A \in \operatorname{Finset}\left(\mathbb{Z}\right),\; \forall B \in \operatorname{Finset}\left(\mathbb{Z}\right),\; \operatorname{orient}\left(A, B\right) = \operatorname{ite}\left(\operatorname{minAbs}\left(A\right) \in A, (B, A), (A, B)\right)$

$\begin{aligned}P = [\operatorname{orient}\left(S_{2 \cdot r + 1}, S_{2 \cdot r + 2}\right):r \in \operatorname{range}\left(k\right)]\\Q = \operatorname{mergeSort}\left(P, (p,q)\mapsto\operatorname{minAbs}\left(p_{2}\right) \le \operatorname{minAbs}\left(q_{2}\right)\right)\\\operatorname{standardize}\left(k, pi\right) = \operatorname{cons}\left(S_{0}, \operatorname{flatten}\left(Q\right)\right)\\\operatorname{f}\left(n, k, pi\right) = \operatorname{standardize}\left(k, \operatorname{complement}\left(n, pi\right)\right)\end{aligned}$

In this display P is the list indexed by r = 0,…,k−1; Q is its merge sort with comparison minAbs(p₂) ≤ minAbs(q₂); flatten replaces each pair by its odd component followed by its even component. The zero block is retained first. Consequently f(n,k,π) = standardize(k,complement(n,π)), the complement followed by full standardization specified in Lemma 19. This implements the general algorithm with no witness-specific branch. General preservation of Standard and the involution assertion in Lemma 19 are not separately proved here.

For any list π, let U(π) be the union of all its blocks and C(π) = U(π) × range(ℓ). Definition 12(1) and (4) are encoded as the cardinalities of these exact pair sets:

$\forall pi \in \operatorname{List}\left(\operatorname{Finset}\left(\mathbb{Z}\right)\right),\; (\operatorname{rosPairs}\left(pi\right) = \{(s, j) \in \operatorname{C}\left(pi\right) | (\exists i \in \operatorname{range}\left(j\right),\; s \in S_{i}) \land (\operatorname{minAbs}\left(S_{j}\right) \le s)\}) \land ((\operatorname{rcbPairs}\left(pi\right) = \{(s, j) \in \operatorname{C}\left(pi\right) | (\exists i \in \operatorname{range}\left(j\right),\; s \in S_{i}) \land ((0 < s) \land (s \le \operatorname{maxAbs}\left(S_{j}\right)))\}) \land ((\operatorname{ros}\left(pi\right) = \operatorname{card}\left(\operatorname{rosPairs}\left(pi\right)\right)) \land (\operatorname{rcb}\left(pi\right) = \operatorname{card}\left(\operatorname{rcbPairs}\left(pi\right)\right))))$

The comparison s ≥ minAbs(S_j) in ros and 0 < s ≤ maxAbs(S_j) in rcb is signed and inclusive. An index j identifies the target block S_j, so a counted pair (s,j) is exactly the source pair (s,S_j) on a partition. The existential earlier-block index ranges over all i < j. The natural-number shift k(k−1) uses truncated subtraction, which agrees with the integer expression for every natural k because the k = 0 factor is zero.

The generating-function equality printed after Conjecture 20 remains unsettled by this result. A failure of the pointwise identity does not decide that separate assertion.

**Theorem 1.2 (The universal identity is false).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/acharyya-2024-conjecture-20-pointwise-refutation` (refuted) by `D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"acharyya-2024-conjecture-20-pointwise-refutation","declaration_gid":"D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Amrita Acharyya (2024). *Type B Set partitions, an analogue of restricted growth functions*. DOI: [10.61091/ars162-14](https://doi.org/10.61091/ars162-14). URL: <https://arxiv.org/abs/2404.14439v1>.

*Commentary.*

Use the same original-domain witness throughout:

$pi = [\left\{0\right\}, \left\{-1, 2, 3\right\}, \left\{1, -2, -3\right\}]$

At n = 3 and k = 1 its three blocks are nonempty, pairwise disjoint and cover −3 through 3. The zero block is {0}; the even block is the negative of the odd block and contains its positive minimum 1; the even minima are 0 < 1. The proof checks the full Standard predicate by decide +kernel.

$\operatorname{f}\left(3, 1, pi\right) = [\left\{0\right\}, \left\{3, -2, -1\right\}, \left\{-3, 2, 1\right\}]$

Complementation sends the odd block to {−3,2,1} and the even block to {3,−2,−1}; orientation swaps this pair because the complemented odd block contains its positive absolute minimum. Sorting the single pair leaves it in place. The proof checks the entire output list, not just its statistics.

$(\operatorname{rosPairs}\left(pi\right) = \left\{(2, 2), (3, 2)\right\}) \land ((\operatorname{rcbPairs}\left(\operatorname{f}\left(3, 1, pi\right)\right) = \left\{(3, 2)\right\}) \land ((\operatorname{ros}\left(pi\right) = 2) \land (\operatorname{rcb}\left(\operatorname{f}\left(3, 1, pi\right)\right) = 1)))$

The proof checks both complete pair sets by decide +kernel. Their cardinalities are respectively 2 and 1, while k(k−1) = 0. Instantiating the full universal claim at this one admissible witness would give 1 = 2, a contradiction. Complementation followed by orientation changes the cardinality of the signed, inclusive comparison pairs; it does not transport the two ros pairs to two rcb pairs. The result has proof_shape bind-only and admission_basis open-problem-resolution under issue #30070; it is the designated Reg-exempt refutation result and supplies no escape witness. The problem dossier states the original question, the source correspondence and the limits of this resolution. The generating-function equality and general preservation or involution of f remain separate assertions.

## References

- Truth anchor: `D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/QStirling/AcharyyaConjectureTwentyRefutation.result`
