# A379464 path counting

## Abstract

Literal path counting and optional-letter insertion for OEIS A379464.

The unpaginated OEIS A379464 Name field states: “a(n) is the total number of paths starting at (0, 0), ending at (n, 0), consisting of steps (1, 1), (1, 0), (1, -3), and staying on or above y = -2.” The vertical increments are 1, 0, and -3; the empty path is included. Removing zero increments gives a zero-free word; inserting optional letters is counted by a binomial transform.

**Definition 1.1 (The three vertical increments).**

$$\operatorname{Step}\left(\right) = \operatorname{Subtype}\left((s: \mathbb{Z} \mapsto s \in \operatorname{Finset}.\operatorname{insert}\left(1, \operatorname{Finset}.\operatorname{insert}\left(0, \operatorname{Finset}.\operatorname{singleton}\left(-3\right)\right)\right))\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/MatharA379464Counting.Step` (`✓ std3`).

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The displayed formula records the finite-word counting statement and its coefficient identity.

**Definition 1.2 (The bounded path predicate).**

$$\forall n \in \mathbb{N},\; \forall w \in \operatorname{Fin}\left(n\right) \to \operatorname{Step}\left(\right),\; \operatorname{IsPath}\left(w\right) = \left((\sum_{i \in \operatorname{Fin}\left(n\right)} \operatorname{Subtype}.\operatorname{val}\left(\operatorname{w}\left(i\right)\right) = 0) \land (\forall r \in \mathbb{N},\; (r \le n) \Rightarrow ((-2) \le \sum_{i \in \operatorname{Fin}\left(n\right)} \operatorname{ite}\left(\operatorname{Fin}.\operatorname{val}\left(i\right) < r, \operatorname{Subtype}.\operatorname{val}\left(\operatorname{w}\left(i\right)\right), 0\right)))\right)$$

*Formalization.* `D5/S1/Words/LatticePaths/MatharA379464Counting.IsPath` (`✓ std3`).

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The displayed formula records the finite-word counting statement and its coefficient identity.

**Definition 1.3 (The path count).**

$$\forall n \in \mathbb{N},\; \operatorname{a}\left(n\right) = (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subtype}\left((w: \operatorname{Fin}\left(n\right) \to \operatorname{Step}\left(\right) \mapsto \operatorname{IsPath}\left(w\right))\right)\right):\mathbb{Z})$$

*Formalization.* `D5/S1/Words/LatticePaths/MatharA379464Counting.a` (`✓ std3`).

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The displayed formula records the finite-word counting statement and its coefficient identity.

**Theorem 1.4 (Three positive cyclic rotations).**

$$\forall w \in \operatorname{List}\left(\mathbb{Z}\right),\; (\forall x \in \mathbb{Z},\; (x \in w) \Rightarrow (x \le 1)) \Rightarrow ((\operatorname{List}.\operatorname{sum}\left(w\right) = 3) \Rightarrow (\operatorname{Fintype}.\operatorname{card}\left(\operatorname{Subtype}\left((j: \operatorname{Fin}\left(\operatorname{List}.\operatorname{length}\left(w\right)\right) \mapsto \forall r \in \mathbb{N},\; (0 < r) \Rightarrow ((r \le \operatorname{List}.\operatorname{length}\left(w\right)) \Rightarrow (0 < \operatorname{List}.\operatorname{sum}\left(\operatorname{List}.\operatorname{take}\left(r, \operatorname{List}.\operatorname{rotate}\left(w, \operatorname{Fin}.\operatorname{val}\left(j\right)\right)\right)\right))))\right)\right) = 3))$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/MatharA379464Counting.three_positive_rotations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The displayed formula records the finite-word counting statement and its coefficient identity.

**Theorem 1.5 (The optional-letter count).**

$$\forall n \in \mathbb{N},\; (\operatorname{a}\left(n\right):\mathbb{Q}) = \sum_{k \in \operatorname{Finset}.\operatorname{range}\left(n + 1\right)} (\operatorname{Nat}.\operatorname{choose}\left(n, 4 \cdot k\right):\mathbb{Q}) \cdot \frac{3 \cdot (\operatorname{Nat}.\operatorname{factorial}\left(4 \cdot k + 2\right):\mathbb{Q})}{(\operatorname{Nat}.\operatorname{factorial}\left(k\right):\mathbb{Q}) \cdot (\operatorname{Nat}.\operatorname{factorial}\left(3 \cdot k + 3\right):\mathbb{Q})}$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/LatticePaths/MatharA379464Counting.binomial_counting` (`✓ std3`). ∎

*Citation.* R. J. Mathar; Emely Hanna Li Lobnig; Thomas Scheuerle (2025). *OEIS A379464, generalized Motzkin paths with negative boundary*. URL: <https://oeis.org/A379464/internal>.

*Commentary.*

The displayed formula records the finite-word counting statement and its coefficient identity.

## References

- Truth anchor: `D5/S1/Words/LatticePaths/MatharA379464Counting.IsPath`
- Truth anchor: `D5/S1/Words/LatticePaths/MatharA379464Counting.Step`
- Truth anchor: `D5/S1/Words/LatticePaths/MatharA379464Counting.a`
- Truth anchor: `D5/S1/Words/LatticePaths/MatharA379464Counting.binomial_counting`
- Truth anchor: `D5/S1/Words/LatticePaths/MatharA379464Counting.three_positive_rotations`
- Dependency: [D5/S1/Words/Compositions/ZeroSumWordCount](../Compositions/ZeroSumWordCount.md)
