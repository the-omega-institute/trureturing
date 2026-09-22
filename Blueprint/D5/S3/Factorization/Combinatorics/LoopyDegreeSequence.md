# Ordinary Loopy Equality Recovers Every Degree

## Abstract

Equality of ordinary Loopy polynomials determines the complete actual degree multiset.

The graph inputs are independent finite vertex sets, lists of edge occurrences and accumulated-loop functions. Pending loops count twice through their two stored endpoints; accumulated loops count twice explicitly. Mapping every retained vertex preserves isolates, so degree zero remains part of the multiset.

**Definition 1.1 (Incidence of one stored endpoint pair).**

$$\operatorname{incidence}\left(e, v\right) = [\operatorname{fst}\left(e\right) = v] + [\operatorname{snd}\left(e\right) = v]$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.incidence` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

incidence e v is the sum of the two endpoint equality indicators. A pending loop at v therefore contributes two.

**Definition 1.2 (Degree from pending occurrences).**

$$\operatorname{pendingDegree}\left(nil, v\right) = 0, \operatorname{pendingDegree}\left(\operatorname{cons}\left(e, E\right), v\right) = \operatorname{incidence}\left(e, v\right) + \operatorname{pendingDegree}\left(E, v\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.pendingDegree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

pendingDegree folds incidence over the entire edge list, retaining the multiplicity of parallel edge occurrences.

**Definition 1.3 (The actual graph-theoretic degree).**

$$\operatorname{degree}\left(E, ell, v\right) = 2 \cdot \operatorname{ell}\left(v\right) + \operatorname{pendingDegree}\left(E, v\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degree` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

degree E ell v is 2*ell(v) plus pendingDegree E v. Both accumulated and pending loops count twice.

**Definition 1.4 (The complete degree multiset).**

$$\operatorname{degreeMultiset}\left(V, E, ell\right) = \operatorname{map}\left(\operatorname{degree}\left(E, ell\right), \operatorname{val}\left(V\right)\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degreeMultiset` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

degreeMultiset maps degree E ell over the underlying multiset of V. It includes every retained vertex, hence isolates, and preserves multiplicity.

**Definition 1.5 (Finite geometric sums).**

$$\operatorname{geometricSum}\left(h\right) = \sum_{i \in \operatorname{range}\left(h\right)} t^{i}$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.geometricSum` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

geometricSum h is the integer polynomial sum of t^i for 0 <= i < h.

**Definition 1.6 (The degree-product specialization).**

$$degreeSpecialization = \operatorname{eval2Hom}\left(\operatorname{id}\left(\operatorname{Polynomial}\left(Int\right)\right), r \mapsto \operatorname{geometricSum}\left(2 \cdot r + 1\right)\right), \operatorname{degreeSpecialization}\left(\operatorname{C}\left(t\right)\right) = t, \operatorname{degreeSpecialization}\left(\operatorname{x}\left(r\right)\right) = \operatorname{geometricSum}\left(2 \cdot r + 1\right)$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degreeSpecialization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

degreeSpecialization fixes the deletion variable and sends x_r to geometricSum(2*r+1). This substitution is proved effective in this repository; it is not attributed to source section 6.5.

**Definition 1.7 (The order specialization).**

$$\operatorname{orderSpecialization}\left(\operatorname{C}\left(t\right)\right) = 1, \operatorname{orderSpecialization}\left(\operatorname{x}\left(r\right)\right) = z$$

*Formalization.* `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.orderSpecialization` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

orderSpecialization evaluates the deletion variable at one and sends every x_r to one common polynomial variable.

**Theorem 1.8 (Ordinary Loopy equality determines the full degree multiset).**

$$\forall V: \operatorname{Finset}\left(Nat\right), \forall W: \operatorname{Finset}\left(Nat\right), \forall E: \operatorname{List}\left(Edge\right), \forall F: \operatorname{List}\left(Edge\right), \forall ell: Nat \to Nat, \forall eta: Nat \to Nat, (\operatorname{Valid}\left(V, E, ell\right)) \Rightarrow ((\operatorname{Valid}\left(W, F, eta\right)) \Rightarrow ((\operatorname{loopy}\left(V, E, ell\right) = \operatorname{loopy}\left(W, F, eta\right)) \Rightarrow (\operatorname{degreeMultiset}\left(V, E, ell\right) = \operatorname{degreeMultiset}\left(W, F, eta\right))))$$

*Proof.* Machine-checked in Lean as `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset` (`✓ std3`). ∎

*Resolves.* `Problems/loopy-degree-sequence-with-loops` (proved) by `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset`.

<!-- scribe-open-problem-resolution-v1 {"problem_slug":"loopy-degree-sequence-with-loops","declaration_gid":"D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset","resolution_kind":"proved"} -->

*Source.* Repository-derived.

*Acknowledgement.* Anatol Kirillov, Gleb Nenashev, Boris Shapiro, and Arkady Vaintrob (2026). *The Loopy Polynomial: from Tutte's Universal V-Function to Bizonotopal Geometry*. URL: <https://arxiv.org/abs/2609.07728v1>.

*Commentary.*

For independent V, W, E, F, ell and eta, the only hypotheses are Valid V E ell, Valid W F eta and equality of the two ordinary Loopy polynomials. The conclusion is equality of the actual degree multisets. There is no equal-order, connectedness, nonemptiness, simplicity or looplessness premise.

The live first induction gives P = product_v [degree(v)+1] after the new substitution x_r=[2r+1]. The live second induction makes U monic of degree |V| and derives the common order from Loopy equality. Thus q=(1-t)^n P is the product of 1-t^(degree(v)+1). For c(r)=-count(degree=r), finite representation splits at d<N; k<=N and not d<N give k<d+1 for the omitted tail, including N=k=0. The frozen primitive Euler-ledger uniqueness theorem is then applied directly, and coordinate zero recovers isolates.

## References

- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degree`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degreeMultiset`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.degreeSpecialization`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.geometricSum`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.incidence`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.loopy_determines_degree_multiset`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.orderSpecialization`
- Truth anchor: `D5/S3/Factorization/Combinatorics/LoopyDegreeSequence.pendingDegree`
- Dependency: [D5/S1/Recurrence/Witt/PrimitiveEulerLedger](../../../S1/Recurrence/Witt/PrimitiveEulerLedger.md)
- Dependency: [D5/S3/Factorization/Combinatorics/LoopyEvaluator](LoopyEvaluator.md)
