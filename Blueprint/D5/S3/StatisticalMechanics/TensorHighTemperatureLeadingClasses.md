# The two leading tensor high-temperature classes

## Abstract

For every n at least two and every positive rank, the all-ones and transposition classes have the two largest tensor high-temperature degrees.

**Definition 1.1 (The degree of a partition).**

$$\forall (s: \mathbb{N}), (\forall (n: \mathbb{N}), (\forall (p: \operatorname{Nat.Partition}\left(n\right)), ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, p\right): \mathbb{Q}) = \sum_{t: (\operatorname{Fin}\left(s\right)) \to (\{(x: \mathbb{N}) // x \in \operatorname{Multiset.toFinset}\left(\operatorname{Nat.Partition.parts}\left(p\right)\right)\})} (\frac{\prod_{j: \operatorname{Fin}\left(s\right)} ((\operatorname{Nat.cast}\left((\operatorname{Subtype.val}\left(t\left(j\right)\right): \mathbb{N})\right): \mathbb{Q}) \cdot (\operatorname{Nat.cast}\left(\operatorname{Multiset.count}\left((\operatorname{Subtype.val}\left(t\left(j\right)\right): \mathbb{N}), \operatorname{Nat.Partition.parts}\left(p\right)\right)\right): \mathbb{Q}))}{(\operatorname{Nat.cast}\left(\operatorname{Finset.lcm}\left(\operatorname{Finset.image}\left(\lambda (j: \operatorname{Fin}\left(s\right)) \mapsto ((\operatorname{Subtype.val}\left(t\left(j\right)\right): \mathbb{N})), (\operatorname{Finset.univ}: \operatorname{Finset}\left(\operatorname{Fin}\left(s\right)\right))\right), (\operatorname{id}: (\mathbb{N}) \to (\mathbb{N}))\right)\right): \mathbb{Q})}))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.degree` (`✓ std3`).

*Citation.* Denjoe O'Connor and Sanjaye Ramgoolam (2025). *Gauged permutation invariant tensor quantum mechanics, least common multiples and the inclusion-exclusion principle*. DOI: [10.48550/arXiv.2506.18813](https://doi.org/10.48550/arXiv.2506.18813). URL: <https://arxiv.org/abs/2506.18813v2>.

*Commentary.*

For a partition p of n, each tuple t chooses s entries from the set of distinct part values; the entries of t may repeat. Its weight is the product of each chosen value and its multiplicity. The degree sums this weight divided by the least common multiple of the chosen values. This is the degree function of Section 7.2, equation (7.21), in the v2 TeX, lines 1079-1087. Each subtype value and each multiplicity is cast separately from the natural numbers to the rationals before multiplication. The least common multiple is computed in the natural numbers and then cast to the rationals. The definition is total for all natural s and n, including zero.

**Definition 1.2 (The transposition class).**

$$\forall (n: \mathbb{N}), ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right): \operatorname{Nat.Partition}\left(n\right)) = \operatorname{dite}\left((2: \mathbb{N}) \le n, (\lambda (h: (2: \mathbb{N}) \le n) \mapsto (\operatorname{D5.S1.Recurrence.Partitions.GawronUlasFactorialSignConjecture.partition126}\left(n, 1, 0, h\right))), (\operatorname{Function.const}\left(\neg ((2: \mathbb{N}) \le n), \operatorname{Nat.Partition.indiscrete}\left(n\right)\right))\right))$$

*Formalization.* `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.transpositionClass` (`✓ std3`).

*Citation.* Denjoe O'Connor and Sanjaye Ramgoolam (2025). *Gauged permutation invariant tensor quantum mechanics, least common multiples and the inclusion-exclusion principle*. DOI: [10.48550/arXiv.2506.18813](https://doi.org/10.48550/arXiv.2506.18813). URL: <https://arxiv.org/abs/2506.18813v2>.

*Commentary.*

For n at least two, the transposition class has one part equal to two and n minus two parts equal to one. This is [2,1^(n-2)] in the v2 TeX, lines 1099-1116. The positive branch is the published partition126 n 1 0 constructor; its proof argument converts 2 ≤ n to the required 2·1 + 6·0 ≤ n. The subtraction n minus two is natural subtraction. Below that range the total definition returns Nat.Partition.indiscrete n, the partition obtained from the singleton multiset containing n by removing zeros. This last branch is a convention extending the class notation.

**Definition 1.3 (The leading-class assertion).**

$$(\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \Rightarrow (\forall (s: \mathbb{N}), (((1: \mathbb{N}) \le s) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)\right) = ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}))^{s}) \land ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right) = \frac{((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}))^{s} + ((\operatorname{Nat.cast}\left((n - (2: \mathbb{N}): \mathbb{N})\right): \mathbb{Q}))^{s}}{(2: \mathbb{Q})}) \land ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right) < \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)\right)) \land (\forall (p: \operatorname{Nat.Partition}\left(n\right)), ((p \ne \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)) \Rightarrow ((p \ne \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)) \Rightarrow (\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, p\right) < \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right))))))))))))$$

*Formalization.* `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Denjoe O'Connor and Sanjaye Ramgoolam (2025). *Gauged permutation invariant tensor quantum mechanics, least common multiples and the inclusion-exclusion principle*. DOI: [10.48550/arXiv.2506.18813](https://doi.org/10.48550/arXiv.2506.18813). URL: <https://arxiv.org/abs/2506.18813v2>.

*Commentary.*

For every n at least two and every positive rank s, the assertion gives the two exact degrees, places the transposition degree strictly below the all-ones degree, and places every other partition strictly below the transposition degree. It expresses the leading-class conjecture in the v2 TeX, line 1068, and the request for a proof in lines 1320-1322 as an ordering of rational pole orders. In the second exact value, n minus two is formed in the natural numbers before being cast to the rationals.

**Theorem 1.4 (Strict dominance of the two leading classes).**

$$\forall (n: \mathbb{N}), (((2: \mathbb{N}) \le n) \Rightarrow (\forall (s: \mathbb{N}), (((1: \mathbb{N}) \le s) \Rightarrow ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)\right) = ((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}))^{s}) \land ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right) = \frac{((\operatorname{Nat.cast}\left(n\right): \mathbb{Q}))^{s} + ((\operatorname{Nat.cast}\left((n - (2: \mathbb{N}): \mathbb{N})\right): \mathbb{Q}))^{s}}{(2: \mathbb{Q})}) \land ((\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right) < \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)\right)) \land (\forall (p: \operatorname{Nat.Partition}\left(n\right)), ((p \ne \operatorname{D5.S3.Combinatorics.Partitions.ColouredOddMultiplicity.onesPartition}\left(n\right)) \Rightarrow ((p \ne \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)) \Rightarrow (\operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, p\right) < \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.degree}\left(s, \operatorname{D5.S3.StatisticalMechanics.TensorHighTemperatureLeadingClasses.transpositionClass}\left(n\right)\right)))))))))))$$

*Proof.* Machine-checked in Lean as `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.result` (`✓ std3`). ∎

*Resolves.* `Problems/oconnor-ramgoolam-2025-tensor-high-temperature-leading-classes` (proved) by `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"oconnor-ramgoolam-2025-tensor-high-temperature-leading-classes","declaration_gid":"D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Denjoe O'Connor and Sanjaye Ramgoolam (2025). *Gauged permutation invariant tensor quantum mechanics, least common multiples and the inclusion-exclusion principle*. DOI: [10.48550/arXiv.2506.18813](https://doi.org/10.48550/arXiv.2506.18813). URL: <https://arxiv.org/abs/2506.18813v2>.

*Commentary.*

Fix n at least two, a positive rank s, and a partition p of n. First sum the tuple weights without their least-common-multiple denominators. The sum of a part value times its multiplicity is n, because the parts sum to n. Distributing the product over the s coordinates therefore gives total weight n^s.

For positive s, let f be the number of parts of p equal to one. Split the tuples into those whose entries are all one and the remaining tuples. The first group has total weight f^s and denominator one: it consists of the single constant tuple when one is a part, and is empty otherwise, when f is zero. Every tuple in the second group has a positive entry at least two. That entry divides its positive least common multiple, so the denominator is at least two. The weights are nonnegative; hence this group contributes at most (n^s - f^s)/2. Consequently the degree of p is at most (n^s + f^s)/2.

For the all-ones partition with n at least two, the only distinct part value is one, with multiplicity n. The unique tuple has denominator one and weight n^s, giving the first exact value. For the transposition class every available value is one or two, with respective multiplicities n minus two and one. Every all-ones tuple has denominator one. Any other tuple contains two, so its least common multiple is divisible by two; since every entry divides two, that least common multiple also divides two and is exactly two. The split is therefore an equality, giving degree (n^s + (n-2)^s)/2. When n is two the all-ones group is empty and its weight is zero, so the same formula applies.

Natural subtraction gives n minus two strictly less than n. Raising to the positive power s preserves that strict inequality, and casting to the rationals preserves it again. The two exact values then put the transposition degree strictly below the all-ones degree.

Next split the multiset of parts into its ones and its parts different from one. The ones form a replicate multiset with cardinality f. If p differs from the all-ones partition, the other multiset is nonempty; each of its parts is at least two, so its sum is at least two. Since the two sums add to n, this proves f at most n minus two.

Equality f = n minus two characterizes the transposition class. Indeed, equality forces the sum of the parts different from one to be two. Each such part is at least two, so twice their cardinality is at most two. Their sum is nonzero, so the cardinality is one and the sole part is two. Together with the f ones this recovers exactly the transposition partition. Conversely, counting the ones in that partition gives n minus two.

Thus a partition different from both displayed classes has f strictly less than n minus two. Strict monotonicity of a positive natural power, followed by the rational cast, gives f^s strictly less than (n-2)^s. Combining this with the half-weight bound puts its degree strictly below the exact transposition degree. The two exact values and the two strict comparisons give all four clauses for every n at least two and every s at least one.

## References

- Truth anchor: `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.claim`
- Truth anchor: `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.degree`
- Truth anchor: `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.result`
- Truth anchor: `D5/S3/StatisticalMechanics/TensorHighTemperatureLeadingClasses.transpositionClass`
- Dependency: [D5/S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture](../../S1/Recurrence/Partitions/GawronUlasFactorialSignConjecture.md)
- Dependency: [D5/S3/Combinatorics/Partitions/ColouredOddMultiplicity](../Combinatorics/Partitions/ColouredOddMultiplicity.md)
