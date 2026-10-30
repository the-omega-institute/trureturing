# Parity of eighteen-mode bosonic occupation assignments

## Abstract

The eighteen-mode bosonic occupation model admits an assignment exactly for even particle numbers.

**Definition 1.1 (The eighteen modes).**

$$(\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.modes}: \operatorname{Finset}\left(\mathbb{N} \times \mathbb{N}\right)) = \left\{(1, 2), (1, 6), (1, 7), (1, 8), (2, 3), (2, 8), (2, 9), (3, 4), (3, 7), (3, 9), (4, 5), (4, 7), (4, 8), (5, 6), (5, 8), (5, 9), (6, 7), (6, 9)\right\}$$

*Formalization.* `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.modes` (`✓ std3`).

*Citation.* Paweł Kurzyński (2017). *Contextuality of identical particles*. DOI: [10.1103/PhysRevA.95.012133](https://doi.org/10.1103/PhysRevA.95.012133). URL: <https://arxiv.org/abs/1609.01250v1>.

*Commentary.*

Each pair (i,j) labels the mode shared by contexts i and j. The eighteen pairs give the mode labels in Kurzyński's eighteen-projector set. The interpretation of the labels is stated in contextuality_fermions.tex, line 83; the nine contexts are displayed in lines 132–221. Context i consists of precisely the pairs in modes whose first or second coordinate equals i.

**Definition 1.2 (Context-independent occupations with conserved particle number).**

$$\forall (n: \mathbb{N}), (\forall (v: (\mathbb{N} \times \mathbb{N}) \to \mathbb{N}), ((\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment}\left(n, v\right)) \Leftrightarrow (\forall (i: \mathbb{N}), ((i \in \operatorname{Finset.Icc}\left(1, 9\right)) \Rightarrow (\sum_{(p: \mathbb{N} \times \mathbb{N}) \in \operatorname{D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity.incident}\left(\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.modes}, \operatorname{Prod.fst}, \operatorname{Prod.snd}, i\right)} (v\left(p\right)) = n)))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment` (`✓ std3`).

*Citation.* Paweł Kurzyński (2017). *Contextuality of identical particles*. DOI: [10.1103/PhysRevA.95.012133](https://doi.org/10.1103/PhysRevA.95.012133). URL: <https://arxiv.org/abs/1609.01250v1>.

*Commentary.*

For a natural particle number n, one function v assigns a natural occupation to each pair of natural numbers. The same value is used whenever a mode occurs in either of its contexts. Each of the nine context sums must equal n, as required by equation (1) and the bosonic occupation model in contextuality_fermions.tex, lines 74–81. Values on pairs outside modes do not enter any of these sums.

**Definition 1.3 (The particle numbers admitting an occupation assignment).**

$$(\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.claim}) \Leftrightarrow (\forall (n: \mathbb{N}), ((\exists (v: (\mathbb{N} \times \mathbb{N}) \to \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment}\left(n, v\right))) \Leftrightarrow (\operatorname{Even}\left(n\right))))$$

*Formalization.* `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.claim` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Paweł Kurzyński (2017). *Contextuality of identical particles*. DOI: [10.1103/PhysRevA.95.012133](https://doi.org/10.1103/PhysRevA.95.012133). URL: <https://arxiv.org/abs/1609.01250v1>.

*Commentary.*

For every natural n, a context-independent occupation assignment exists if and only if n is even. This includes n equal to zero. It gives a classification in the occupation-assignment model addressing the question for more than two bosons in contextuality_fermions.tex, line 233.

**Theorem 1.4 (Existence is equivalent to even particle number).**

$$\forall (n: \mathbb{N}), ((\exists (v: (\mathbb{N} \times \mathbb{N}) \to \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment}\left(n, v\right))) \Leftrightarrow (\operatorname{Even}\left(n\right)))$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.result` (`✓ std3`). ∎

*Resolves.* `Problems/kurzynski-2017-eighteen-mode-bosonic-assignment-parity` (proved) by `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.result`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"kurzynski-2017-eighteen-mode-bosonic-assignment-parity","declaration_gid":"D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.result","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Paweł Kurzyński (2017). *Contextuality of identical particles*. DOI: [10.1103/PhysRevA.95.012133](https://doi.org/10.1103/PhysRevA.95.012133). URL: <https://arxiv.org/abs/1609.01250v1>.

*Commentary.*

First count the contexts containing a fixed mode p. Its two coordinates are distinct and both lie between 1 and 9, as follows by checking the eighteen listed pairs. Membership in context i is equivalent to p.1 = i or p.2 = i. Since the coordinates are distinct, the indicator of this disjunction is the sum of the two coordinate indicators. Summing over i from 1 to 9 therefore gives two occurrences of p.

Express each context sum as a sum over all eighteen modes, with zero contribution from modes outside that context. Interchange the finite sums, factor each occupation v(p) out of its sum of incidence indicators, and use the count of two. Factoring out this common multiplier gives:

$$
\forall (v: (\mathbb{N} \times \mathbb{N}) \to \mathbb{N}), (\sum_{(i: \mathbb{N}) \in \operatorname{Finset.Icc}\left(1, 9\right)} (\sum_{(p: \mathbb{N} \times \mathbb{N}) \in \operatorname{D5.S3.Combinatorics.Graph.BipartiteSubgraphDensity.incident}\left(\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.modes}, \operatorname{Prod.fst}, \operatorname{Prod.snd}, i\right)} (v\left(p\right))) = 2 \cdot \sum_{(p: \mathbb{N} \times \mathbb{N}) \in \operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.modes}} (v\left(p\right)))
$$

If v is an assignment for n, its nine context sums also total 9n. Consequently 9n equals twice the sum of the eighteen occupations, so 9n is even. Evenness of a product of natural numbers implies evenness of at least one factor; since 9 is odd, n is even.

Conversely, for a natural m define v(p) to be m on {(1,2),(1,6),(2,8),(3,7),(3,9),(4,7),(4,8),(5,6),(5,9)} and zero elsewhere. Check the nine contexts individually: their selected pairs are respectively {(1,2),(1,6)}, {(1,2),(2,8)}, {(3,7),(3,9)}, {(4,7),(4,8)}, {(5,6),(5,9)}, {(1,6),(5,6)}, {(3,7),(4,7)}, {(2,8),(4,8)} and {(3,9),(5,9)}. Thus each sum of support indicators is two. Each occupation sum is that indicator sum multiplied by m, and hence equals 2m:

$$
\forall (m: \mathbb{N}), (\operatorname{D5.S3.Quantum.Contextuality.EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment}\left(2 \cdot m, \lambda (p: \mathbb{N} \times \mathbb{N}) \mapsto (\operatorname{ite}\left(p \in \left\{(1, 2), (1, 6), (2, 8), (3, 7), (3, 9), (4, 7), (4, 8), (5, 6), (5, 9)\right\}, m, 0\right))\right))
$$

For any n, an assignment therefore implies that n is even. In the reverse direction, express an even n as 2m and apply the construction just given. This proves both directions for every natural n. In particular every odd particle number, including three, is excluded, whereas zero and every even particle number admit an assignment. The classification concerns the existence of occupation assignments for these nine contexts.

## References

- Truth anchor: `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.IsNoncontextualAssignment`
- Truth anchor: `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.claim`
- Truth anchor: `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.modes`
- Truth anchor: `D5/S3/Quantum/Contextuality/EighteenModeBosonicAssignmentParity.result`
- Dependency: [D5/S3/Combinatorics/Graph/BipartiteSubgraphDensity](../../Combinatorics/Graph/BipartiteSubgraphDensity.md)
