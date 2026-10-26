# A counterexample to packing-maximum Conjecture 7.1

## Abstract

The interleaved minimal pattern need not maximize the prescribed packing count.

Blitvic, Kammoun and Steingrimsson, arXiv:2610.29846v1, Conjecture 7.1: “For overlap m ≤ K/2, the maximum is obtained when prefix and suffix are interleaved and minimal, that is, for patterns with prefix 135…(2m−1) and suffix 246…(2m).” A maximum-attainment assertion means that a prescribed pattern exists whose count dominates every compatible comparison pattern. Its middle order is unrestricted. No uniqueness of a maximum is asserted.

**Definition 1.1 (Zero-based one-line entries).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Fin}\left(n\right),\; \forall i \in \mathbb{N},\; \operatorname{entry}\left(w, i\right) = \operatorname{getD}\left(\operatorname{ofFn}\left(k\mapsto\operatorname{val}\left(\operatorname{w}\left(k\right)\right)\right), i, 0\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.entry` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Both positions and ranks use Fin(n)={0,…,n−1}. Adding one to a position and its rank gives the source's one-based notation; strict comparisons are unchanged. entry(w,i) is the i-th entry of the finite list of ranks, with default zero outside the list. Prefix and suffix queries are in range throughout the asserted parameter domain.

**Definition 1.2 (Positions in prescribed windows).**

$$\forall K \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall t \in \operatorname{Fin}\left(j\right),\; \forall a \in \operatorname{Fin}\left(K\right),\; \operatorname{val}\left(\operatorname{windowIndex}\left(K, m, j, t, a\right)\right) = \operatorname{val}\left(t\right) \cdot \left(K - m\right) + \operatorname{val}\left(a\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The window indexed by t in Fin(j) begins at t(K−m), which is source position 1+t(K−m). For a in Fin(K), t(K−m)+a is below n=K+(j−1)(K−m): t≤j−1 and multiplication by K−m preserves this bound. The Fin-valued construction includes this bound, so no window lookup uses an out-of-range default.

**Definition 1.3 (All prescribed source occurrences).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right) \to \operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right),\; \operatorname{Packs}\left(p, m, j, w\right) \Leftrightarrow \left(\forall t \in \operatorname{Fin}\left(j\right),\; \forall a \in \operatorname{Fin}\left(K\right),\; \forall b \in \operatorname{Fin}\left(K\right),\; \operatorname{w}\left(\operatorname{windowIndex}\left(K, m, j, t, a\right)\right) < \operatorname{w}\left(\operatorname{windowIndex}\left(K, m, j, t, b\right)\right) \Leftrightarrow \operatorname{p}\left(a\right) < \operatorname{p}\left(b\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Packs` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Definition 2.2 uses agreement of every pairwise strict comparison. Definition 2.6 and equation (2.1) require precisely j contiguous windows of length K at the prescribed starts. The displayed predicate tests every pair in every such window. Remark 2.7 permits additional occurrences; this predicate makes no test at any other start and places no avoidance condition on the permutation.

**Definition 1.4 (The actual source permutations).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{SourcePacking}\left(p, m, j\right) = \operatorname{Subtype}\left(\operatorname{Perm}\left(\operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right)\right), w\mapsto\operatorname{Packs}\left(p, m, j, w\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.SourcePacking` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

A source packing is an equivalence Fin(n)→Fin(n) whose one-line values satisfy Packs. Thus each rank occurs once. Its elements are actual labeled permutations, rather than equivalence classes, posets or lists of occurrence locations.

**Definition 1.5 (The original packing cardinality).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{count}\left(p, m, j\right) = \operatorname{card}\left(\operatorname{SourcePacking}\left(p, m, j\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

count(p,m,j) is the natural cardinality of SourcePacking(p,m,j), the set denoted S_p^m(j) in the source. It counts each source permutation once, including permutations with extra occurrences.

**Definition 1.6 (Compatible comparison patterns).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \operatorname{Admissible}\left(p, m\right) \Leftrightarrow \left(\operatorname{Injective}\left(p\right) \land \left(\forall a \in \operatorname{Fin}\left(m\right),\; \forall b \in \operatorname{Fin}\left(m\right),\; \operatorname{entry}\left(p, \operatorname{val}\left(a\right)\right) < \operatorname{entry}\left(p, \operatorname{val}\left(b\right)\right) \Leftrightarrow \operatorname{entry}\left(p, K - m + \operatorname{val}\left(a\right)\right) < \operatorname{entry}\left(p, K - m + \operatorname{val}\left(b\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Admissible` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The pattern is injective on Fin(K), hence bijective because its domain and codomain are the same finite set. The m-prefix and m-suffix agree on all pairwise strict comparisons, as required after Definition 3.3. No increasing-order or first-value hypothesis narrows this domain. The source's normalized presentation uses increasing prefix and suffix with the first prefix value smaller; the two displayed patterns already obey it.

**Definition 1.7 (Every prescribed middle order remains available).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \operatorname{Prescribed}\left(p, m\right) \Leftrightarrow \left(\left(\forall a \in \operatorname{Fin}\left(m\right),\; \operatorname{entry}\left(p, \operatorname{val}\left(a\right)\right) = 2 \cdot \operatorname{val}\left(a\right)\right) \land \left(\forall a \in \operatorname{Fin}\left(m\right),\; \operatorname{entry}\left(p, K - m + \operatorname{val}\left(a\right)\right) = 2 \cdot \operatorname{val}\left(a\right) + 1\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Prescribed` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

For each a=0,…,m−1 the prefix rank is 2a and the suffix rank at K−m+a is 2a+1. After adding one these are 1,3,…,2m−1 and 2,4,…,2m. Together with Admissible, these equations leave every ordering of the remaining ranks 2m,…,K−1 in the middle.

**Definition 1.8 (The full existential maximum-attainment assertion).**

$$claim \Leftrightarrow \left(\forall K \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; 2 \le K \Rightarrow \left(1 \le m \Rightarrow \left(m < K \Rightarrow \left(2 \cdot m \le K \Rightarrow \left(1 \le j \Rightarrow \left(\exists rho \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \operatorname{Admissible}\left(rho, m\right) \land \left(\operatorname{Prescribed}\left(rho, m\right) \land \left(\forall pi \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \operatorname{Admissible}\left(pi, m\right) \Rightarrow \operatorname{count}\left(pi, m, j\right) \le \operatorname{count}\left(rho, m, j\right)\right)\right)\right)\right)\right)\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.claim` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

All natural K,m,j satisfying K≥2, 1≤m<K, 2m≤K and j≥1 are quantified. For each triple there must exist an admissible prescribed rho dominating every admissible pi. The equality boundary 2m=K and j=1 are included. There is no fixed middle order, restriction on other occurrences or quotient by symmetry.

**Definition 1.9 (The pattern 13472568).**

$$competitor = \operatorname{vector}\left(0, 2, 3, 6, 1, 4, 5, 7\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.competitor` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

This is the zero-based vector for 13472568. Its prefix 1347 and suffix 2568 are increasing, with first values 1<2; in particular it is source-admissible at m=4.

**Definition 1.10 (The pattern 13572468).**

$$prescribed = \operatorname{vector}\left(0, 2, 4, 6, 1, 3, 5, 7\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.prescribed` (`✓ std3`).

*Citation.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

This is the zero-based vector for 13572468, with the prescribed prefix 1357 and suffix 2468.

**Definition 1.11 (An exact two-way rank-assignment correspondence).**

$$\forall K \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \operatorname{encodingEquiv}\left(p, m, j\right):\operatorname{Equiv}\left(\operatorname{SourcePacking}\left(p, m, j\right), \operatorname{Subtype}\left(\operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right) \to \operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right), w\mapsto\operatorname{Injective}\left(w\right) \land \operatorname{Packs}\left(p, m, j, w\right)\right)\right)$$

*Formalization.* `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.encodingEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Sending an actual permutation to its underlying rank function preserves every window comparison. Conversely, an injective rank function on the same finite set is bijective by Mathlib's Finite.injective_iff_bijective, so Equiv.ofBijective reconstructs the source permutation. Both composites are identities. This is the direct rank-assignment counterpart of the source's Lemma 5.1 and Theorem 5.3; it introduces neither a labeling factor nor a missing inverse-permutation convention.

**Theorem 1.12 (Cardinality without representation multiplicity).**

$$\forall K \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall p \in \operatorname{Fin}\left(K\right) \to \operatorname{Fin}\left(K\right),\; \operatorname{count}\left(p, m, j\right) = \operatorname{card}\left(\operatorname{Subtype}\left(\operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right) \to \operatorname{Fin}\left(K + \left(j - 1\right) \cdot \left(K - m\right)\right), w\mapsto\operatorname{Injective}\left(w\right) \land \operatorname{Packs}\left(p, m, j, w\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.source_cardinality` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Nat.card_congr transports the original count through encodingEquiv. The encoded subtype consists of all injective rank assignments satisfying the same pairwise window predicate, in both directions.

**Theorem 1.13 (Nine packings of 13472568).**

$$\operatorname{count}\left(competitor, 4, 2\right) = 9$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count_competitor` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Here n=12 and the windows begin at source positions 1 and 5. Writing x_i for the source entries, their exact chains are x1<x5<x2<x3<x6<x7<x4<x8 and x5<x9<x6<x7<x10<x11<x8<x12. They are equivalent to ordered groups x1 < x5 < {x2,x3,x9} < x6 < x7 < {x4,x10,x11} < x8 < x12, with x2<x3 and x10<x11 inside the two three-element groups. The first group receives ranks 3,4,5 in three ways, and the second receives 8,9,10 in three ways. The other ranks are forced. The finite certificate contains the nine resulting one-line rank functions. Its membership equivalence proves completeness from the source chains and injectivity, and checks every original comparison for each listed function. Fintype.card_of_subtype and the exact cardinality bridge give 9.

**Theorem 1.14 (Eight packings of 13572468).**

$$\operatorname{count}\left(prescribed, 4, 2\right) = 8$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count_prescribed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

The exact chains are x1<x5<x2<x6<x3<x7<x4<x8 and x5<x9<x6<x10<x7<x11<x8<x12. Their ordered groups are x1 < x5 < {x2,x9} < x6 < {x3,x10} < x7 < {x4,x11} < x8 < x12. The pairs receive ranks {3,4}, {6,7} and {9,10}, with either order in each pair; singleton ranks are 1,2,5,8,11,12. The eight resulting functions are precisely the injective source packings, as established by the two-way certificate membership proof. Cardinality transport therefore gives 8.

**Theorem 1.15 (The full prescribed family at the equality boundary).**

$$\forall p \in \operatorname{Fin}\left(8\right) \to \operatorname{Fin}\left(8\right),\; \operatorname{Prescribed}\left(p, 4\right) \Rightarrow p = prescribed$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.prescribed_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

At K=8,m=4 the middle is empty. The four prefix equations and four suffix equations determine all eight entries, so every prescribed candidate is 13572468. This is a statement about the entire prescribed family at this boundary, without a global uniqueness assumption.

**Theorem 1.16 (A strict count inequality refutes the whole assertion).**

$$\neg claim$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/blitvic-kammoun-steingrimsson-2026-packing-maximum` (refuted) by `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"blitvic-kammoun-steingrimsson-2026-packing-maximum","declaration_gid":"D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Natasha Blitvić, Mohammed Slim Kammoun, and Einar Steingrímsson (2026). *Permutations, Pattern Covers, Posets and Positivity: Part I: Patterns and Posets*. DOI: [10.48550/arXiv.2610.29846](https://doi.org/10.48550/arXiv.2610.29846). URL: <https://arxiv.org/abs/2610.29846v1>.

*Commentary.*

Specializing the whole claim to K=8,m=4,j=2 would produce a prescribed rho dominating every compatible pattern. The boundary theorem forces rho=13572468, while the admissible pattern 13472568 has 9 packings and rho has 8. The impossible inequality 9≤8 refutes the full claim. It does not identify the actual maximum, settle the strict-overlap range 2m<K, or answer the separate cutoff question in Section 7 item 8. The difference is two independent three-way choices versus three independent binary choices, rather than an avoidance or labeling effect.

## References

- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Admissible`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Packs`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.Prescribed`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.SourcePacking`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.claim`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.competitor`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count_competitor`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.count_prescribed`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.encodingEquiv`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.entry`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.prescribed`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.prescribed_boundary`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.result`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.source_cardinality`
- Truth anchor: `D5/S3/Combinatorics/Permutation/PackingMaximumRefutation.windowIndex`
