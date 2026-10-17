# Finite Gilbreath extensions and maximal step-two runs

## Abstract

The exact finite Gilbreath extension component question over every integer extension.

**Definition 1.1 (Adjacent absolute differences).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.difference`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.difference` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

The ordered zip of the input and its tail takes the absolute difference of each consecutive pair.

**Definition 1.2 (The finite difference triangle).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.row`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.row` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

Row zero is the input list and row r plus one is the absolute-difference row of row r. The source entry s_a^b corresponds to row s b at zero-based position a minus one, for valid triangle indices.

**Definition 1.3 (The Gilbreath left edge).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.isGilbreath`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.isGilbreath` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

For every natural r with zero less than r less than the input length, the head of row r is some one. The row-length induction gives length n minus r, and the source recurrence agrees with every valid list entry.

**Definition 1.4 (Eligible prefixes).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.admissible`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.admissible` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

A list has length n, is pairwise strictly increasing, starts with two and three, and is Gilbreath. List position i corresponds to source position i plus one.

**Definition 1.5 (All integer extensions).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.validExtensions`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.validExtensions` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

An integer k belongs exactly when appending k gives a Gilbreath list. In particular k need not exceed the last prefix entry.

**Definition 1.6 (Literal maximal step-two runs).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.maximalStepTwoRuns`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.maximalStepTwoRuns` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

A pair a,b has a at most b in one parity class. Every integer of that parity between them belongs to X; a minus two and b plus two do not. On a finite one-parity set these endpoint pairs represent precisely its nonempty maximal runs. The literal-run bridge writes b as a plus twice a natural m and enumerates exactly a,a+2,...,a+2m. Endpoint membership and uniqueness of the right endpoint justify finite run counting.

**Definition 1.7 (One integer parity class).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.oneParity`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.oneParity` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

All members have the same remainder modulo two as some integer p. Neither even nor odd extensions are excluded in advance.

**Definition 1.8 (Finite geometry as a conclusion).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.extensionGeometry`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.extensionGeometry` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

Both the extension set and its set of literal run endpoints must be finite, and the extension set must lie in one parity class. The recursive extension preimage proves these properties for every eligible prefix; they are conclusions of the result.

**Definition 1.9 (Counting literal runs).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.stepTwoRunCount`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.stepTwoRunCount` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

The natural cardinality counts endpoint pairs. Its use in the whole target is accompanied by explicit finiteness conclusions; the convention assigning zero to infinite sets does not discharge those conclusions.

**Definition 1.10 (The exact whole question).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.componentMaximum`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.componentMaximum` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

For every natural n at least five, all eligible prefixes satisfy the finite geometry and the upper bound two to the power n minus four; at least one eligible prefix has finite geometry and equality. This defines the question proved by the result below. No prime, uniqueness, cardinality-maximum or bounded-length substitute occurs.

**Definition 1.11 (The source index recurrence).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.sourceTriangle`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.sourceTriangle` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

Source row b and one-based column a correspond to sourceTriangle s b (a minus one). At every valid index this is the corresponding row-list entry, by induction using adjacent list entries. Values outside the finite triangle are irrelevant to the statement.

**Definition 1.12 (A parity interval).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.parityInterval`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.parityInterval` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

The integers from a through b congruent to a modulo two. Empty intervals are permitted. A finite cover by r such intervals gives at most r literal maximal runs, because each run start must be an interval start and a run start has a unique right endpoint.

**Definition 1.13 (The known attaining family).**

Lean statement: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.attainingPrefix`

*Formalization.* `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.attainingPrefix` (`✓ std3`).

*Citation.* Leila Muney (2026). *Holes in Valid-Extension Sets of Finite Gilbreath Sequences*. URL: <https://arxiv.org/html/2606.23721v2>.

*Commentary.*

The parameter m is length minus four. Put U zero equal to the singleton two and append two to the power j plus one at step j. Then attainingPrefix m is U at m plus two followed by two to the power m plus three minus one. Thus lengths at least five are exactly Muney Definition 31 and Theorem 35. The length-four seed is (2,3,5,7). No separate resolution credit is attached to this known attaining family.

**Theorem 1.14 (The component maximum at every length).**

$$\forall n \in \mathrm{Nat},\; (5 \le n) \Rightarrow ((\forall s \in \operatorname{List}\left(\mathrm{Int}\right),\; (\operatorname{admissible}\left(n, s\right)) \Rightarrow ((\operatorname{extensionGeometry}\left(s\right)) \land (\operatorname{stepTwoRunCount}\left(\operatorname{validExtensions}\left(s\right)\right) \le 2^{(n - 4)}))) \land (\exists s \in \operatorname{List}\left(\mathrm{Int}\right),\; (\operatorname{admissible}\left(n, s\right)) \land ((\operatorname{extensionGeometry}\left(s\right)) \land (\operatorname{stepTwoRunCount}\left(\operatorname{validExtensions}\left(s\right)\right) = 2^{(n - 4)}))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result` (`✓ std3`). ∎

*Resolves.* `Problems/muney-gilbreath-component-maximum` (proved) by `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"muney-gilbreath-component-maximum","declaration_gid":"D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Commentary.*

For every n at least five, every eligible prefix has finite single-parity unrestricted extension geometry and at most two to the power n minus four maximal step-two runs; an eligible prefix attains equality. The appended integer is unrestricted.

The actual triangle gives K of s as the absolute-value preimage of K of its difference row. Each parity interval has at most two parity intervals in this preimage, including clipping at zero. The realizable bottom rows force the four-entry seed to be one parity interval. Induction therefore gives the upper bound for every length. This proof uses no graph representation.

For the attributed attaining family, the difference of V at the next length is V at the preceding length shifted down by one. Its extension set lies between two m plus three and two to the power m plus four minus two m minus five. After shifting down by one every extension is at least two, so the absolute-value preimage has two separated reflected copies of its maximal runs. Starting with the single run from three through eleven at length four, the count doubles at every step.

All auxiliary proofs belong to the live whole development or the explicit source-index bridge. The solved maximum-cardinality and uniqueness question and the prime Gilbreath conjecture are outside the theorem.

## References

- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.admissible`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.attainingPrefix`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.componentMaximum`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.difference`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.extensionGeometry`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.isGilbreath`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.maximalStepTwoRuns`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.oneParity`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.parityInterval`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.result`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.row`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.sourceTriangle`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.stepTwoRunCount`
- Truth anchor: `D5/S3/Combinatorics/FiniteDifferences/GilbreathExtension.validExtensions`
