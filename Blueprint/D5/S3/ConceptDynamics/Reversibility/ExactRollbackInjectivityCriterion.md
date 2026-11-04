# Exact Rollback and Joint-Record Injectivity

## Abstract

Exact rollback from a joint update-log record is equivalent to injectivity.

For a fixed root of a typed named graph, let P be all finite legal words from that root, including the empty word. Apply the criterion with X equal to P, Y the residual vertex set, M the nonnegative reals, U the endpoint and L the descended accumulated duration. The empty word supplies nonemptiness even when no positive-length execution exists. Exact recovery then means injectivity of this same joint endpoint-duration map on the entire legal word language.

The possible observations are the actual image of that map. A total left inverse on the product restricts to its inverse on the image; an inverse on the image can be extended outside it using the empty word. This extension adds no realizable observations and imposes no independence assumption on the endpoint and duration fields.

Fix one strictly positive real duration for each actual named arrow before choosing words. If native one-step durations equal these values at every representative in a common unit and calibration, and the descended duration is zero on the empty word and additive under concatenation, induction identifies it with the sum of the actual arrow durations. Arrow-dependent path weights keep parallel names separate. This accounting identity and the rollback criterion do not require rationality, rational independence or equal edge values.

The criterion does not decide when this joint map is injective. For a finite strongly connected named multigraph with at least one edge, equivalence with one exhaustive directed cycle is a separate graph statement. Its noncycle direction must produce distinct legal words with both the same endpoint and the same duration, and its converse must retain every finite stopping point, the empty word and the single-loop cycle. No acquisition procedure, arbitrary-real decoding algorithm, physical clock or resource optimum follows from the set-theoretic inverse.

**Theorem 1.1 (Exact rollback criterion).**

$$\begin{gathered}\forall X, Y, M: \operatorname{Type},\\{}\operatorname{Nonempty}\left(X\right) \Rightarrow\\{}\forall U: X \to Y, L: X \to M,\\{}(\exists R: Y \times M \to X, \forall x: X, R(\operatorname{conceptJoin}\left(U, L\right)(x)) = x) \iff \operatorname{Injective}\left(\operatorname{conceptJoin}\left(U, L\right)\right).\end{gathered}$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The joint record is the canonical product readout of the update and log channels. An exact rollback map is precisely a left inverse of this readout.

Pinned Mathlib equates existence of a left inverse with injectivity. Applying that equivalence gives both directions of the criterion.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Reversibility/ExactRollbackInjectivityCriterion.exact_rollback_iff_joint_record_injective`
- Dependency: [D5/S3/ConceptDynamics/ConceptJoinUniversal](../ConceptJoinUniversal.md)
