# Restricted Context Minimality

## Abstract

A complete complementary-context family is minimal among its context subfamilies.

**Definition 1.1 (Restricted context readout).**

$$\forall n\in \mathbb{N}, C: \operatorname{Fin}\left(n+2\right) \to \operatorname{RankOneContext}\left(n+1\right), S: \operatorname{Finset}\left(\operatorname{Fin}\left(n+2\right)\right),\\{}X: \operatorname{Matrix}\left(\operatorname{Fin}\left(n+1\right), \operatorname{Fin}\left(n+1\right), \mathbb{C}\right), ell\in S, j\in \operatorname{Fin}\left(n+1\right),\\{}\operatorname{restrictedContextReadout}\left(C, S, X, ell, j\right) = \operatorname{trace}\left(\operatorname{mul}\left(X, \operatorname{projector}\left(C, ell, j\right)\right)\right).$$

*Formalization.* `D5/S3/Quantum/Tomography/RestrictedContextMinimality.restrictedContextReadout` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a finite subfamily S of the supplied contexts, the readout retains exactly the projector-trace coordinates indexed by S.

**Theorem 1.2 (An omitted context supplies indistinguishable projectors).**

$$\forall n\in \mathbb{N}, 1 \leq n, C: \operatorname{Fin}\left(n+2\right) \to \operatorname{RankOneContext}\left(n+1\right),\\{}\forall ell, k, j, r, \operatorname{trace}\left(\operatorname{mul}\left(\operatorname{projector}\left(C, ell, j\right), \operatorname{projector}\left(C, k, r\right)\right)\right) = \operatorname{if}\left(\operatorname{Eq}\left(ell, k\right), \operatorname{if}\left(\operatorname{Eq}\left(j, r\right), 1, 0\right), \operatorname{inverse}\left(n+1\right)\right), S: \operatorname{Finset}\left(\operatorname{Fin}\left(n+2\right)\right), ell\in \operatorname{Fin}\left(n+2\right), ell \neg \in S \Rightarrow\\{}\operatorname{projector}\left(C, ell, 0\right) \neq \operatorname{projector}\left(C, ell, 1\right) \land \operatorname{restrictedContextReadout}\left(C, S, \operatorname{projector}\left(C, ell, 0\right)\right) = \operatorname{restrictedContextReadout}\left(C, S, \operatorname{projector}\left(C, ell, 1\right)\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RestrictedContextMinimality.omitted_context_projectors_indistinguishable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension n+1 at least two, assume the complete complementary overlap law. If context ell is absent from S, its outcome-zero and outcome-one projectors are distinct but every retained context gives them the same trace coordinates.

The two matrices are explicit and uniform for every omitted context; no positivity or density-state premise is used.

**Theorem 1.3 (Exact classification of injective context subfamilies).**

$$\forall n\in \mathbb{N}, 1 \leq n, C: \operatorname{Fin}\left(n+2\right) \to \operatorname{RankOneContext}\left(n+1\right),\\{}\forall ell, k, j, r, \operatorname{trace}\left(\operatorname{mul}\left(\operatorname{projector}\left(C, ell, j\right), \operatorname{projector}\left(C, k, r\right)\right)\right) = \operatorname{if}\left(\operatorname{Eq}\left(ell, k\right), \operatorname{if}\left(\operatorname{Eq}\left(j, r\right), 1, 0\right), \operatorname{inverse}\left(n+1\right)\right), S: \operatorname{Finset}\left(\operatorname{Fin}\left(n+2\right)\right),\\{}\operatorname{Injective}\left(\operatorname{restrictedContextReadout}\left(C, S\right)\right) \iff S = \operatorname{univ}\left(\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Tomography/RestrictedContextMinimality.restricted_contextReadout_injective_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Under the same dimension and overlap hypotheses, the restricted readout is injective on the full complex matrix carrier exactly when S is the full finite context family.

The forward obstruction uses the explicit omitted-context pair; the reverse implication reuses complete context tomography.

## References

- Truth anchor: `D5/S3/Quantum/Tomography/RestrictedContextMinimality.omitted_context_projectors_indistinguishable`
- Truth anchor: `D5/S3/Quantum/Tomography/RestrictedContextMinimality.restrictedContextReadout`
- Truth anchor: `D5/S3/Quantum/Tomography/RestrictedContextMinimality.restricted_contextReadout_injective_iff`
- Dependency: [D5/S3/Quantum/Tomography/ObserverDiagonalSeparation](ObserverDiagonalSeparation.md)
