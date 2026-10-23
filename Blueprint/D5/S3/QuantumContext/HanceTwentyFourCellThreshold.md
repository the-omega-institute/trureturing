# Exact preparation-noncontextuality threshold of the twenty-four-cell

## Abstract

The twenty-four-cell preparation subtheory admits a preparation-noncontextual model exactly up to visibility one half.

**Definition 1.1 (Four signs).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Signs`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Signs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

Signs is Bool times Bool times Bool times Bool. True denotes plus one and false denotes minus one.

**Definition 1.2 (All twenty-four preparation labels).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Vertex`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

Vertex is the disjoint union of Fin 4 times Bool and Signs. Its first eight labels are the signed coordinate axes; its remaining sixteen labels are all half-sign vectors. No parity class is omitted.

**Definition 1.3 (The twelve sharp binary questions).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Question`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Question` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

Question is Fin 4 disjoint union Bool times Bool times Bool. The four coordinate directions and eight half-sign directions with positive first coordinate represent all twelve antipodal pairs. Both binary outcomes are retained.

**Definition 1.4 (Signs as real numbers).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.sign`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.sign` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every Boolean b, sign b is one if b is true and minus one otherwise.

**Definition 1.5 (The four coordinates of a sign tuple).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.bits`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.bits` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every sign tuple s, bits s is the Fin 4 indexed vector of its four entries in tuple order.

**Definition 1.6 (Preparation vectors).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.vertex`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.vertex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every coordinate i and Boolean b, vertex (inl (i,b)) has sign b in coordinate i and zero elsewhere. For every sign tuple s, vertex (inr s) has coordinate sign (bits s j) divided by two at every j. Thus its image is exactly the union of all signed coordinate axes and all sixteen half-sign vectors.

**Definition 1.7 (Sharp measurement directions).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.question`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.question` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every coordinate i, question (inl i) is the positive coordinate axis. For every triple (a,b,c), question (inr (a,b,c)) is the vector (1,sign a,sign b,sign c) divided by two.

**Definition 1.8 (Real coordinate pairing).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.dot`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.dot` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every pair of real Fin 4 vectors x and y, dot x y is the sum over all four coordinates of x i times y i.

**Definition 1.9 (Statistics of every classical preparation mixture).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.statistics`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.statistics` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every real visibility lambda, every nonnegative weight vector alpha on Vertex, every question n and Boolean outcome b, statistics lambda alpha n b is the sum over x of alpha x times (1 + sign b times lambda times dot (question n) (vertex x)) divided by two. Probability mixtures have total weight one. Noise acts on preparations only; there is exactly one visibility factor. Classical mixtures of questions take the corresponding convex sums of these statistics.

**Definition 1.10 (Countably additive ontic preparation mixtures).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.mixture`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.mixture` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every measurable space Omega, every nonnegative weight vector alpha and every family mu of measures on Omega, mixture alpha mu is the finite sum of alpha x times mu x as measures. Real nonnegative weights are coerced through NNReal to ENNReal. This is convex randomization when the weights sum to one.

**Definition 1.11 (An original measurable ontological model).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Model`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Model` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every real lambda and every arbitrary measurable space Omega, Model lambda Omega consists of: one countably additive probability measure preparation x for each of all twenty-four labels; a real measurable response n b on Omega for every sharp question and binary outcome; nonnegativity at every ontic state; response n true plus response n false equal to one; and the exact integral of response n b against preparation x equal to (1 + sign b times lambda times dot (question n) (vertex x)) divided by two. Responses may be stochastic. For every pair alpha,beta of nonnegative preparation weight vectors of total weight one, equality of statistics for every question and both outcomes implies equality of the entire ontic mixture measures. This quantifies over every operationally equal pair, not just the equivalences used in the upper argument. Convex randomization extends preparation measures and measurement responses by their actual finite sums. No measurement-noncontextuality, outcome determinism, density representation, topology or countable-generation premise is imposed.

**Definition 1.12 (Existence on an arbitrary measurable ontic space).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.admissible`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.admissible` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every universe level u and every real lambda, admissible at level u means that there exist a type Omega in Type u, a measurable-space structure on Omega, and an inhabitant of Model lambda Omega. The result is polymorphic in u. The upper argument applies to every such space; the lower argument lifts its finite construction into the chosen universe.

**Definition 1.13 (Opposite sign tuple).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.anti`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.anti` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every sign tuple s, anti s negates each of its four Boolean entries.

**Definition 1.14 (The coordinate midpoint mixture).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.zeroWeights`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.zeroWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

zeroWeights assigns one half to each of the two preparations on coordinate zero, and zero to all other preparations. Its operational vector is zero at every visibility.

**Definition 1.15 (A zero-vector mixture for every sign tuple).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.boundWeights`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.boundWeights` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every s, boundWeights s assigns one sixth to each of the four signed axis preparations selected by s, and one third to the half-sign preparation with sign tuple anti s. All other weights are zero. The weights sum to one and their vector is zero, so this mixture is operationally equal to zeroWeights.

**Definition 1.16 (The twenty-four explicit ontic states).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Ontic`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Ontic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

Ontic is Fin 6 times Bool times Bool. The six labels select an unordered pair of different coordinates, and the two Boolean entries select their signs.

**Definition 1.17 (The six coordinate pairs).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.pairs`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.pairs` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

In Fin 6 order, pairs is (0,1), (0,2), (0,3), (1,2), (1,3), (2,3). Each coordinate pair occurs exactly once.

**Definition 1.18 (Ontic root vectors).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.ontic`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.ontic` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every ontic label u, ontic u is sign u's first Boolean times the first selected coordinate axis plus sign u's second Boolean times the second selected coordinate axis. These are all vectors epsilon e_i + delta e_j with i less than j.

**Definition 1.19 (The full preparation model).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.weight`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.weight` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every real lambda, preparation x and ontic label u, weight lambda x u is (1 + 2 times lambda times dot (ontic u) (vertex x)) divided by twenty-four. When zero is at most lambda and lambda is at most one half, these are nonnegative and sum to one. At lambda zero every preparation has the same uniform distribution.

**Definition 1.20 (Stochastic binary responses).**

Lean statement: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.onticResponse`

*Formalization.* `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.onticResponse` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Commentary.*

For every question n, Boolean b and ontic label u, onticResponse n b u is (1 + sign b times dot (ontic u) (question n)) divided by two. Both responses are nonnegative and sum to one. Their definition has no visibility factor.

**Theorem 1.21 (Exact threshold for the full preparation scenario).**

$$\forall (u:\operatorname{Level}\left(\right)), \forall (lambda:\mathbb{R}), (0\leq lambda\land lambda\leq 1)\implies (\operatorname{admissible}\left(u, lambda\right)\iff lambda\leq \frac{1}{2})$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result` (`✓ std3`). ∎

*Resolves.* `Problems/hance-2026-twenty-four-cell-preparation-threshold` (proved) by `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"hance-2026-twenty-four-cell-preparation-threshold","declaration_gid":"D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Jonte R. Hance (2026). *Why three? A two-level system with four mutually unbiased questions*. URL: <https://arxiv.org/abs/2609.10078v1>.

*Acknowledgement.* André Chailloux; Iordanis Kerenidis; Srijita Kundu; Jamie Sikora (2016). *Optimal bounds for parity-oblivious random access codes*. DOI: [10.1088/1367-2630/18/4/045003](https://doi.org/10.1088/1367-2630/18/4/045003). URL: <https://arxiv.org/abs/1404.5153v3>.

*Commentary.*

For every universe level u and every real visibility lambda in the closed interval from zero to one, the original measurable-space model exists if and only if lambda is at most one half. The ontic existence quantifier includes arbitrary measurable spaces and countably additive probability preparations; the statement includes all twenty-four preparations, all twelve sharp binary questions, all classical mixtures and every operational preparation equivalence. The zero-visibility collapse is included.

For the upper implication, multiply the four stochastic coordinate responses to form a nonnegative measurable weight for each of the sixteen sign tuples. Their sum is one and their coordinate marginals are the original responses. Integrate the zero-vector mixture identities against these weights. The omitted half-sign term has nonnegative integral, and summing the remaining inequalities gives 4(1+lambda) at most 6. This is the known parity-oblivious random-access-code obstruction, applied directly to the original measures without a finite-space reduction.

For the converse, place the displayed weights and responses on all twenty-four ontic root vectors. Exact sign symmetry gives total preparation mass one and the required statistics. Coordinate questions determine the actual noisy mixture coordinates. For any normalized alpha the ontic mass at u is (1 + 2 times dot (ontic u) with lambda times the alpha-weighted preparation vector) divided by twenty-four. Therefore every operationally equal pair has identical ontic measures, including at lambda zero. The exact full-scenario attainment supplies the threshold; no separate novelty claim is made for the upper bound or the generic measure and convexity facts.

## References

- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Model`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Ontic`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Question`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Signs`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.Vertex`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.admissible`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.anti`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.bits`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.boundWeights`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.dot`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.mixture`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.ontic`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.onticResponse`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.pairs`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.question`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.result`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.sign`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.statistics`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.vertex`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.weight`
- Truth anchor: `D5/S3/QuantumContext/HanceTwentyFourCellThreshold.zeroWeights`
