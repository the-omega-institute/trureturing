# The least ternary stabilization threshold at deficits four and five

## Abstract

The ternary near-maximum weak metric dimensions at deficits four and five stabilize exactly in dimension three.

Kumar's Theorem 6.4 proves an eventual formula for every nonbinary alphabet, with a sufficient dimension inequality. The present result fixes the ternary alphabet and deficits four and five and determines every dimension at least two. Its least threshold concerns these two deficits only. The published two-dimensional values of Fernandez, Klavzar, Kuziak, Munoz-Marquez and Yero are used to establish leastness.

**Definition 1.1 (Ternary words).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.Word`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.Word` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

Word d is the literal finite function type Fin d to Fin 3. A landmark or omitted set is a Finset of distinct words.

**Definition 1.2 (Hamming distance).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

The distance sums one over the coordinates where two words differ, and zero elsewhere.

**Theorem 1.3 (Agreement with the native metric).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance_eq_hammingDist`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance_eq_hammingDist` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every dimension and both words, distance equals Mathlib's native hammingDist.

**Definition 1.4 (Weak separation).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

For a finite set T and words x,y, separation T x y sums Nat.dist(distance x z, distance y z) over z in T. This is the sum of absolute differences of distances.

**Definition 1.5 (Weak resolving sets).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.IsWeakResolving`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.IsWeakResolving` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

For every ordered pair of distinct words, the separation is at least k. No pair is omitted from this quantifier.

**Definition 1.6 (Weak metric dimension).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.metricDimension`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.metricDimension` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

The natural infimum of the cardinalities of weak k-resolving Finsets. The construction in the theorem proves that this collection is nonempty at each requested parameter.

**Definition 1.7 (The maximum parameter).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.kappa`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.kappa` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

kappa d is 2 times 3 to the power d minus one; it is the full-universe separation of an adjacent pair.

**Definition 1.8 (The eventual omitted capacity).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omittedCapacity`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omittedCapacity` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

omittedCapacity t is 3 times the natural quotient t/2 plus t mod 2, so its values at four and five are six and seven.

**Definition 1.9 (Complement in the actual universe).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement`

*Formalization.* `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement` (`✓ std3`).

*Citation.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Commentary.*

complement T is univ minus T in the finite type Word d.

**Theorem 1.10 (Cardinalities of complementary sets).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement_card`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every dimension and omitted set T, the cardinalities of T and its complement sum to 3 to the power d.

**Theorem 1.11 (Separation splits over complements).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation_complement`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation_complement` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every dimension, finite set T, and words x,y, the separation over T plus that over its complement equals the separation over all words.

**Theorem 1.12 (The uniform separation gain).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.full_separation_bound`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.full_separation_bound` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every d at least three and every distinct x,y, the full-universe separation is at least kappa d plus 6 times (distance x y minus one). Write F(x,y) for full separation and Z(x,y) for the number of words equally distant from x and y. Prefixing equal letters multiplies F by three. Prefixing different letters gives 3F+2Z, from the integer identity |u-1|+|u|+|u+1|=3|u|+2 times the indicator of u=0. A neutral word chooses the third letter in each differing coordinate. It witnesses Z at least one. Changing one differing coordinate to either endpoint gives distance differences plus or minus one. In a tail of dimension at least two, equal prefix letters give three neutral extensions; different prefix letters with a nonconstant tail use the three distance differences; an equal tail has 3 to the tail dimension neutral extensions. Thus Z is at least three. Induction first gives F at least kappa plus 2 times (distance minus one). Applying one coordinate recurrence to that estimate and Z at least three gives the stated factor six. The proof is symbolic in every dimension.

**Theorem 1.13 (The published weak two-metric boundary).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_four`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_four` (`✓ std3`). ∎

*Citation.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

At d=2 and deficit four, kappa minus four equals two and the metric dimension is four. The four corners with both coordinates in {0,1} attain it. For the lower bound, at most three weak two-landmarks would have one landmark in each row and column. Opposite corners from two of them are equally distant from all three.

**Theorem 1.14 (The published weak one-metric boundary).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_five`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_five` (`✓ std3`). ∎

*Citation.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

At d=2 and deficit five, kappa minus five equals one and the metric dimension is three. The L consisting of (0,0),(0,1),(1,0) resolves. Differences between the distances to two landmarks in a row recover one coordinate, and a pair in a column recovers the other. Two landmarks fail: when they share a coordinate, the other two letters in that coordinate are indistinguishable; otherwise the two opposite corners are indistinguishable.

**Theorem 1.15 (Every requested dimension).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.result`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.result` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every natural d at least two and t equal to four or five, the weak (2 times 3^(d-1) minus t)-metric dimension is four or three, respectively, at d=2. For every d at least three it is 3^d minus six or seven, respectively. An adjacent pair forces the sum of two column frequencies of an omitted set to be at most t. Adding the three pair constraints bounds its size by floor(3t/2). For attainment, take the translation orbit of the constant zero word and that of the word whose first coordinate is zero and whose remaining coordinates are one. They are disjoint actual three-element sets. For deficit five also insert the word with first two coordinates zero and two and every remaining coordinate zero. The first two coordinates prove this seventh word is distinct. Each orbit loses at most twice the pair distance, and a singleton at most the pair distance. The uniform separation gain therefore makes every complement weak resolving: the residual surplus is at least (6-t) times (distance minus one).

**Theorem 1.16 (Actual attainers and universal maxima).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omitted_maximum`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omitted_maximum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For every d at least two and t equal to four or five, an actual omitted Finset realizes the maximum, and every omitted Finset with a weak resolving complement has at most that cardinality. The maxima are five and six at d=2, and six and seven at every d at least three. The existential statement and universal bound use the same literal Word d carrier.

**Theorem 1.17 (The least eventual threshold).**

Lean statement: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.least_threshold`

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.least_threshold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Aryan Kumar (2026). *Weak k-metric dimension of Hamming graphs: rectangular products and near-maximum parameters*. DOI: [10.48550/arXiv.2609.32161](https://doi.org/10.48550/arXiv.2609.32161). URL: <https://arxiv.org/abs/2609.32161>.

*Acknowledgement.* Elena Fernandez; Sandi Klavzar; Dorota Kuziak; Manuel Munoz-Marquez; Ismael G. Yero (2025). *On the weak k-metric dimension of Hamming graphs*. DOI: [10.1016/j.disopt.2026.100945](https://doi.org/10.1016/j.disopt.2026.100945). URL: <https://arxiv.org/abs/2505.19642>.

*Commentary.*

For each t in {4,5}, three is the least natural D for which the eventual formula holds for every d at least two with D at most d. The all-dimensional construction proves the formula from three onward. The exact d=2 values contradict it at every D at most two. This does not claim the full q,d,t threshold question is settled.

## References

- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.IsWeakResolving`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.Word`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.complement_card`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_five`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.d2_metricDimension_four`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.distance_eq_hammingDist`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.full_separation_bound`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.kappa`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.least_threshold`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.metricDimension`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omittedCapacity`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.omitted_maximum`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.result`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation`
- Truth anchor: `D5/S3/Combinatorics/Hamming/TernaryWeakMetricStability.separation_complement`
