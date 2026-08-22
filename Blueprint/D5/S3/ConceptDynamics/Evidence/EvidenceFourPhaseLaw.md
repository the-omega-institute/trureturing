# The Four-Phase Law for Finite Evidence

## Abstract

Every finite evidence fiber with a decidable proposition has exactly one of four epistemic phases.

**Theorem 1.1 (A finite evidence fiber has exactly one phase).**

$$\forall X: \operatorname{Type}, R: \operatorname{Finset}\left(X\right), P: X \to \operatorname{Prop},\ [\operatorname{DecidableEq}\left(X\right)], [\operatorname{DecidablePred}\left(P\right)],\ \exists! phase: \operatorname{EvidencePhase}, \operatorname{PhaseHolds}\left(R, P, phase\right).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Evidence/EvidenceFourPhaseLaw.finite_classical_four_phase_law` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The finset R represents the admissible evidence fiber R_E^A(b). Its membership is decidable, and the DecidablePred instance makes the proposition P decidable at every member.

PhaseHolds gives the four source meanings without weakening them: the fiber is empty; it is nonempty and every member satisfies P; it is nonempty and every member refutes P; or it contains both a P-witness and a counterexample.

The proof separates the empty case, the all-true case, the all-false case, and the remaining mixed case. In each branch, the displayed witnesses also refute every other phase, yielding existence and uniqueness rather than only a four-way disjunction.

Repository searches found no existing four-phase evidence theorem. Pinned Mathlib supplies finite membership, decidable finite nonemptiness, and Finset.mem_filter; these generic results are reused directly. Four Boolean examples realize the four constructors, so none of the named phases is definitionally empty.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Evidence/EvidenceFourPhaseLaw.finite_classical_four_phase_law`
