# Ledger Integrity and Input Veracity

## Abstract

An injective ledger can exactly preserve reports that systematically contradict events.

**Theorem 1.1 (Ledger integrity does not imply input veracity).**

$$\exists O, R, E: Bool \to Bool,\\{}L := E \circ R,\\{}\operatorname{Injective}\left(E\right) \land\\{}{\forall x, y\in Bool, (L(x) \neq L(y) \iff R(x) \neq R(y))} \land\\{}{\forall x\in Bool, R(x) \neq O(x)} \land\\{}\operatorname{Injective}\left(L\right) \land\\{}\neg (\operatorname{Injective}\left(L\right) \iff R = O).$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Audits/LedgerIntegrityVeracitySeparation.ledger_integrity_does_not_imply_input_veracity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Take Boolean events. The true-event readout is the identity, while the report readout negates every event. The encoder is the identity and the ledger is constructed as the encoder composed with the report.

The induced ledger distinguishes two inputs exactly when their reports differ. Boolean negation is injective, but every report is unequal to the corresponding true event.

All five clauses are public: encoder injectivity, exact report distinction, systematic report/event inequality, ledger injectivity, and the failure of ledger integrity to have the same truth value as input veracity.

Repository searches found no exact combined theorem. The proof directly applies the pinned Boolean injectivity and inequality theorems.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Audits/LedgerIntegrityVeracitySeparation.ledger_integrity_does_not_imply_input_veracity`
