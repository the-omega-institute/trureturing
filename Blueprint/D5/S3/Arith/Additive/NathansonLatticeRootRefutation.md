# A counterexample to the exact lattice-root bound

## Abstract

The full two-fold triple range gives interval diameter three and square diameter two.

**Definition 1.1 (The complete integer range).**

$$\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \operatorname{integerRange}\left(h, k\right) = \{t : \mathbb{N} \mid \exists (A : \operatorname{Finset}\left(\mathbb{Z}\right)), (\operatorname{Finset}.\operatorname{card}\left(A\right) = k) \land (\operatorname{Finset}.\operatorname{card}\left(\operatorname{nsmulRec}\left(h, A\right)\right) = t)\}$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.integerRange` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

The source defines the h-fold sumset using “h not necessarily distinct elements of A” (p. 1). Its range is R_X(h,k) = {|hA| : A ⊆ X and |A| = k}. Here X is the integers, and Finset enumerates every finite k-element subset. The operation nsmulRec is repeated pointwise addition, with the zero-fold sumset {0}; it permits repeated summands.

**Definition 1.2 (The inclusive integer lattice cube).**

$$\forall (n : \mathbb{N}), \forall (D : \mathbb{N}), \operatorname{cube}\left(n, D\right) = \operatorname{Fintype}.\operatorname{piFinset}\left(\operatorname{Function}.\operatorname{const}\left(\operatorname{Fin}\left(n\right), \operatorname{Finset}.\operatorname{Icc}\left((0 : \mathbb{Z}), (D : \mathbb{Z})\right)\right)\right)$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cube` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Theorem 1 (pp. 1–2) equates the ordinary integer and lattice-point ranges. The cube in Problem 3 therefore contains integer-coordinate points. A point is a function Fin n → ℤ, and each coordinate belongs to the closed integer interval [0,D]. Fintype.piFinset forms the Cartesian product of those intervals; Function.const supplies the same coordinate interval at every index.

**Definition 1.3 (Covering the whole range in an interval).**

$$\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \forall (D : \mathbb{N}), \operatorname{intervalCovers}\left(h, k, D\right) = ((0 < D) \land (\operatorname{integerRange}\left(h, k\right) = \{t : \mathbb{N} \mid \exists (A : \operatorname{Finset}\left(\mathbb{Z}\right)), (\operatorname{Finset}.\operatorname{card}\left(A\right) = k) \land ((A \subseteq \operatorname{Finset}.\operatorname{Icc}\left((0 : \mathbb{Z}), (D : \mathbb{Z})\right)) \land (\operatorname{Finset}.\operatorname{card}\left(\operatorname{nsmulRec}\left(h, A\right)\right) = t))\}))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.intervalCovers` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Problem 3 (p. 3) asks: “Let N(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N(h,k)] and |A| = k}. “and let N_n(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N_n(h,k)]^n and |A| = k}. “Prove or disprove the following inequality:” N_n(h,k) ≤ N(h,k)^(1/n). The diameter D must be positive. Equality of sets of cardinalities requires every value in the complete integer range, with all endpoints included.

**Definition 1.4 (Covering the same whole range in a cube).**

$$\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \forall (n : \mathbb{N}), \forall (D : \mathbb{N}), \operatorname{cubeCovers}\left(h, k, n, D\right) = ((0 < D) \land (\operatorname{integerRange}\left(h, k\right) = \{t : \mathbb{N} \mid \exists (A : \operatorname{Finset}\left(\operatorname{Fin}\left(n\right) \to \mathbb{Z}\right)), (\operatorname{Finset}.\operatorname{card}\left(A\right) = k) \land ((A \subseteq \operatorname{cube}\left(n, D\right)) \land (\operatorname{Finset}.\operatorname{card}\left(\operatorname{nsmulRec}\left(h, A\right)\right) = t))\}))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cubeCovers` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Problem 3 (p. 3) asks: “Let N(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N(h,k)] and |A| = k}. “and let N_n(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N_n(h,k)]^n and |A| = k}. “Prove or disprove the following inequality:” N_n(h,k) ≤ N(h,k)^(1/n). The right side ranges over all k-element subsets of the integer lattice cube. Both inclusions in this equality are required: witnessing two values alone does not establish it.

**Definition 1.5 (The least positive interval diameter).**

$$\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \forall (H : \exists (D : \mathbb{N}), \operatorname{intervalCovers}\left(h, k, D\right)), \operatorname{N}\left(h, k, H\right) = \operatorname{Nat}.\operatorname{find}\left(H\right)$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.N` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Nat.find takes the least natural D satisfying intervalCovers. Its argument H proves that such a D exists. Positivity is part of the predicate, so the minimum is a positive integer. Nat.find_spec and Nat.find_min' give attainment and leastness. The value is independent of the proof H by proof irrelevance.

**Definition 1.6 (The least positive lattice-cube diameter).**

$$\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \forall (n : \mathbb{N}), \forall (H : \exists (D : \mathbb{N}), \operatorname{cubeCovers}\left(h, k, n, D\right)), \operatorname{Nn}\left(h, k, n, H\right) = \operatorname{Nat}.\operatorname{find}\left(H\right)$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.Nn` (`✓ std3`).

*Citation.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

The same least-natural construction uses the entire common integer range and the inclusive n-dimensional lattice cube. Its proof argument supplies existence on the declared domain; there is no default diameter and no assumed global inhabitedness.

**Definition 1.7 (The full universal exact-root inequality).**

$$\operatorname{claim} = (\forall (h : \mathbb{N}), \forall (k : \mathbb{N}), \forall (n : \mathbb{N}), (2 \le h) \Rightarrow ((2 \le k) \Rightarrow ((1 \le n) \Rightarrow (\exists (H : \exists (D : \mathbb{N}), \operatorname{intervalCovers}\left(h, k, D\right)), \exists (J : \exists (D : \mathbb{N}), \operatorname{cubeCovers}\left(h, k, n, D\right)), (\operatorname{Nn}\left(h, k, n, J\right) : \mathbb{R}) \le (\operatorname{N}\left(h, k, H\right) : \mathbb{R})^{\frac{1}{(n : \mathbb{R})}}))))$$

*Formalization.* `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Problem 3 (p. 3) asks: “Let N(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N(h,k)] and |A| = k}. “and let N_n(h,k) be the smallest positive integer such that ” R_Z(h,k) = {|hA| : A ⊆ [0,N_n(h,k)]^n and |A| = k}. “Prove or disprove the following inequality:” N_n(h,k) ≤ N(h,k)^(1/n). All h,k ≥ 2 and all n ≥ 1 are quantified. The source's existence of the minima is explicit in the existential proof arguments H and J. These are existence conclusions, not additional hypotheses restricting h, k or n. The diameter values are cast to real numbers and Real.rpow uses exponent 1/n, giving the exact nonnegative nth root. There is no ceiling or relaxation of that inequality.

**Theorem 1.8 (The entire triple range is five or six).**

$$\operatorname{integerRange}\left(2, 3\right) = \{5, 6\}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.range_two_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

Sort any integer triple as a < b < c. Its pair sums are 2a, a+b, a+c, 2b, b+c, 2c. The strict inequalities exclude every collision except a+c = 2b, giving five or six distinct values. The sets {0,1,2} and {0,1,3} attain five and six respectively. Thus the equality concerns every integer triple, not just these two examples.

**Theorem 1.9 (The interval minimum is three).**

$$(\operatorname{intervalCovers}\left(2, 3, 3\right)) \land (\forall (D : \mathbb{N}), (\operatorname{intervalCovers}\left(2, 3, D\right)) \Rightarrow (3 \le D))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.interval_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

At D=3 the two displayed integer triples attain every value in the full range. Conversely any positive D<3 lies at most at two. A three-element subset of [0,2] must equal {0,1,2}; its pair-sum cardinality is five, so six is missing. This proves attainment and leastness.

**Theorem 1.10 (The square minimum is two).**

$$(\operatorname{cubeCovers}\left(2, 3, 2, 2\right)) \land (\forall (D : \mathbb{N}), (\operatorname{cubeCovers}\left(2, 3, 2, D\right)) \Rightarrow (2 \le D))$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cube_minimum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

At D=2 the line {(0,0),(1,0),(2,0)} has five pair sums and the triangle {(0,0),(1,0),(0,1)} has six. Exhausting every three-element subset of the finite lattice square proves that no other cardinality occurs there. At D=1 the exhaustive check gives six for every triple, so five is missing. Geometrically, a midpoint equality in a binary coordinate forces both endpoints to equal the midpoint; the unit square admits no three distinct points in arithmetic progression. Positivity leaves only D=1 below two.

**Theorem 1.11 (The original universal bound is false).**

$$\neg \operatorname{claim}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/nathanson-2026-problem3-lattice-root-bound` (refuted) by `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"nathanson-2026-problem3-lattice-root-bound","declaration_gid":"D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* Melvyn B. Nathanson (2026). *A problem on sumset sizes of sets of lattice points*. DOI: [10.48550/arXiv.2607.20571](https://doi.org/10.48550/arXiv.2607.20571). URL: <https://arxiv.org/abs/2607.20571v1>.

*Commentary.*

The covering diameters three and two construct both existence proofs. Leastness then identifies the actual values N(2,3)=3 and N_2(2,3)=2, independently of which proofs the universal proposition supplies. Its specialization would give 2 ≤ sqrt(3). The nonnegative square root has square three, contradicting 2²=4>3. This negates the complete universal proposition while proving existence of both minima at the counterexample; no failure of existence is used.

## References

- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.N`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.Nn`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.claim`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cube`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cubeCovers`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.cube_minimum`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.integerRange`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.intervalCovers`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.interval_minimum`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.range_two_three`
- Truth anchor: `D5/S3/Arith/Additive/NathansonLatticeRootRefutation.result`
