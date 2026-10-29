# Polygon and three-time inequalities are insufficient

## Abstract

Six-time pair probabilities satisfy the polygon and three-time inequalities without admitting a joint distribution.

**Definition 1.1 (Real pair tables).**

$$\forall (n: \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right) = \left((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Fin}\left(n\right)) \to ((\operatorname{Bool}) \to ((\operatorname{Bool}) \to (\mathbb{R}))))\right))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.PairTables` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

For a natural number n, PairTables n is the type of real arrays indexed by two times and two Boolean outcomes. The sign of true is 1 and the sign of false is -1, using the real-valued function sgn. Only entries with i < j constrain the probability conditions below; the array also assigns values to the other entries. The dichotomic pairwise setting is described in the source's TeX lines 148-159.

**Definition 1.2 (Compatible pair probabilities).**

$$\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.IsPairFamily}\left(p\right)) \Leftrightarrow ((\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((i < j) \Rightarrow ((\forall (a: \operatorname{Bool}), (\forall (b: \operatorname{Bool}), ((0: \mathbb{R}) \le p\left(i, j, a, b\right)))) \land (\sum_{(a: \operatorname{Bool})} (\sum_{(b: \operatorname{Bool})} (p\left(i, j, a, b\right))) = (1: \mathbb{R})))))) \land (\exists (m: (\operatorname{Fin}\left(n\right)) \to ((\operatorname{Bool}) \to (\mathbb{R}))), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((i < j) \Rightarrow ((\forall (a: \operatorname{Bool}), (\sum_{(b: \operatorname{Bool})} (p\left(i, j, a, b\right)) = m\left(i, a\right))) \land (\forall (b: \operatorname{Bool}), (\sum_{(a: \operatorname{Bool})} (p\left(i, j, a, b\right)) = m\left(j, b\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.IsPairFamily` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

Each table at i < j has nonnegative entries summing to one. A single family m of one-time marginals gives both the row and column sums of every such table, so shared times have the same marginal in all pairs. This expresses the compatibility condition in TeX lines 150-153 and the nonnegative pairwise probabilities assumed in Section 4.B, line 551. There is no condition on i >= j.

**Definition 1.3 (The pair correlation).**

$$\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.corr}\left(p, i, j\right) = \sum_{(a: \operatorname{Bool})} (\sum_{(b: \operatorname{Bool})} (\operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(a\right) \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(b\right) \cdot p\left(i, j, a, b\right)))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.corr` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

The real correlation is the sum of the product of the two signs weighted by their pair-table entry. This is the correlator in TeX lines 155-159. The definition applies to every pair of indices, including those outside i < j.

**Definition 1.4 (The n-gon inequalities).**

$$\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.NGonInequalities}\left(p\right)) \Leftrightarrow (\forall (s: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), (\operatorname{ite}\left(\operatorname{Odd}\left(n\right), (1: \mathbb{R}), (0: \mathbb{R})\right) \le (\operatorname{Nat.cast}\left(n\right): \mathbb{R}) + (2: \mathbb{R}) \cdot \sum_{(i: \operatorname{Fin}\left(n\right))} (\sum_{(j: \operatorname{Fin}\left(n\right))} (\operatorname{ite}\left(i < j, \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(s\left(i\right)\right) \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(s\left(j\right)\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.corr}\left(p, i, j\right), (0: \mathbb{R})\right)))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.NGonInequalities` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

For every Boolean sign assignment s, the signed sum of pair correlations obeys the polygon bound of Section 4.A, equation (neweq), TeX lines 494-512. The lower bound is one for odd n and zero for even n. The natural number n is cast to a real number in the right-hand side. The double sum includes exactly the terms with i < j.

**Definition 1.5 (All three-time Leggett-Garg inequalities).**

$$\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.ThreeTimeLG}\left(p\right)) \Leftrightarrow (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), (\forall (k: \operatorname{Fin}\left(n\right)), ((i < j) \Rightarrow ((j < k) \Rightarrow (\forall (a: \operatorname{Bool}), (\forall (b: \operatorname{Bool}), (\forall (c: \operatorname{Bool}), ((0: \mathbb{R}) \le (1: \mathbb{R}) + \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(a\right) \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(b\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.corr}\left(p, i, j\right) + \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(a\right) \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(c\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.corr}\left(p, i, k\right) + \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(b\right) \cdot \operatorname{D5.S3.Combinatorics.IsingUniquenessSets.sgn}\left(c\right) \cdot \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.corr}\left(p, j, k\right))))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.ThreeTimeLG` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

Every ordered triple of distinct times i < j < k satisfies the three-time inequality for every choice of Boolean outcomes a, b and c. This is equation (LGcomp) in Section 4.B, TeX lines 554-559, with signs represented by sgn.

**Definition 1.6 (A matching nonnegative joint distribution).**

$$\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.HasJointDistribution}\left(p\right)) \Leftrightarrow (\exists (\mu: ((\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})) \to (\mathbb{R})), ((\forall (x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), ((0: \mathbb{R}) \le \mu\left(x\right))) \land (\forall (i: \operatorname{Fin}\left(n\right)), (\forall (j: \operatorname{Fin}\left(n\right)), ((i < j) \Rightarrow (\forall (a: \operatorname{Bool}), (\forall (b: \operatorname{Bool}), (\sum_{(x: (\operatorname{Fin}\left(n\right)) \to (\operatorname{Bool})), (x\left(i\right) = a) \land (x\left(j\right) = b)} (\mu\left(x\right)) = p\left(i, j, a, b\right)))))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.HasJointDistribution` (`✓ std3`).

*Citation.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

There exists a nonnegative real mass function on all Boolean time assignments whose two-time marginals equal the specified tables for every i < j and every pair of outcomes. The finite sum is restricted to assignments having those outcomes. This is the matching-joint-probability requirement in TeX line 551. The definition does not separately require total mass one; when n is at least two and a pair table is normalized, that marginal identity forces normalization. The definition also permits n equal to zero or one.

**Definition 1.7 (The sufficiency assertion).**

$$(\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (\forall (p: \operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.PairTables}\left(n\right)), (((3: \mathbb{N}) \le n) \Rightarrow ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.IsPairFamily}\left(p\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.NGonInequalities}\left(p\right)) \Rightarrow ((\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.ThreeTimeLG}\left(p\right)) \Rightarrow (\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.HasJointDistribution}\left(p\right))))))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

For every natural n at least three and every compatible family of normalized nonnegative pair tables, the n-gon inequalities and all three-time Leggett-Garg inequalities imply a matching joint distribution. This is the universal assertion corresponding to the conjecture in Section 4.B, TeX lines 549-561. It imposes the polygon inequalities on the full set of n times; it does not additionally impose them on every subset.

**Theorem 1.8 (A six-time obstruction to a joint distribution).**

$$\neg (\operatorname{D5.S3.Quantum.Contextuality.LeggettGargSixTimeSufficiencyRefutation.claim})$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result` (`✓ std3`). ∎

*Resolves.* `Problems/halliwell-mawby-2019-leggett-garg-six-time-sufficiency` (refuted) by `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"halliwell-mawby-2019-leggett-garg-six-time-sufficiency","declaration_gid":"D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result","resolution_kind":"refuted"} -->

*Source.* Repository-derived.

*Acknowledgement.* J. J. Halliwell; C. Mawby (2019). *Fine's theorem for Leggett-Garg tests with an arbitrary number of measurement times*. DOI: [10.1103/PhysRevA.100.042103](https://doi.org/10.1103/PhysRevA.100.042103). URL: <https://arxiv.org/abs/1906.04865v2>.

*Commentary.*

Use the six time indices 0, 1, 2, 3, 4 and 5. Set the correlations between index 5 and indices 0, 1, 2 and 3 to 1/2, the correlation between 4 and 5 to -1/2, and all other correlations at distinct indices to zero. For each pair of Boolean outcomes, take the table entry to be one quarter of one plus the product of the two signs and the specified correlation.

Evaluation of the finitely many indices and outcomes shows that every ordered pair table is nonnegative and normalized, with both one-time marginals equal to the constant 1/2. Summing the four signed entries recovers each specified correlation. Since six is even, the polygon lower bound is zero; evaluation on all 64 Boolean sign assignments verifies every six-gon inequality. Evaluation on every ordered triple i < j < k and every triple of outcomes verifies the three-time inequalities.

Choose the real coefficients (1, 1, 1, 1, -1, -2), and let W(x) be their scalar product with the six signs of an assignment x. Expansion on the 64 assignments gives W(x) squared as the sum of the coefficient squares plus twice the sum, over i < j, of the two coefficients multiplied by the corresponding two signs.

Suppose a nonnegative joint mass function matches the pair tables. Partitioning its assignments by the outcomes at indices 0 and 1 and using that pair's normalization shows that its total mass is one. For any i < j, partitioning by the two outcomes similarly shows that the expectation of the product of the two signs is the specified pair correlation.

Distribute the mass function through the finite double sum and interchange the sums over assignments and time indices. The square expansion and the pair expectations then express the expectation of W squared as the sum of the coefficient squares times the total mass, plus twice the sum of coefficient products weighted by the pair correlations.

Evaluation on all 64 assignments gives W(x) squared at least one at every assignment. Nonnegative mass and total mass one therefore give an expectation at least one. But the sum of the coefficient squares is 9, and the sum of their pair products weighted by the specified correlations is -5. The same expectation is consequently 9 + 2(-5) = -1, a contradiction.

Thus these six-time tables satisfy every hypothesis of the sufficiency assertion and admit no matching joint distribution. Applying that assertion at n = 6 would give the impossible joint distribution, so the universal assertion is false.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.HasJointDistribution`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.IsPairFamily`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.NGonInequalities`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.PairTables`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.ThreeTimeLG`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.corr`
- Truth anchor: `D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.result`
- Dependency: [D5/S3/Combinatorics/IsingUniquenessSets](../../Combinatorics/IsingUniquenessSets.md)
