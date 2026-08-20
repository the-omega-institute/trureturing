# Minimal Failure of Macroscopic Factorization

## Abstract

A deterministic three-state process need not descend through a two-class readout.

**Theorem 1.1 (A deterministic process can fail to descend through observation).**

$$q(0)=q(1)=A, q(2)=B;\\F(0)=0, F(1)=2, F(2)=2;\\q(F(0))=A \neq B=q(F(1));\\\neg \exists \overline{F}: O \to O,\ q\circ F = \overline{F}\circ q.$$

*Proof.* Machine-checked in Lean as `D5/S3/ObserverMemory/FiniteCountermodels/MinimalMacroFactorizationCounterexample.deterministic_three_state_process_has_no_macro_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The microscopic domain is Fin 3. The named observation map sends zero and one to class A and two to class B. The named total process fixes zero and sends one and two to two, so determinism is represented by an ordinary function rather than an extra hypothesis.

Zero and one have the same present observation, while their next observations are A and B. Any proposed macroscopic map would therefore send A to both A and B, which is impossible.

Pinned Mathlib supplies Function.FactorsThrough and factorsThrough_iff. The proof first refutes fiber constancy at zero and one and then uses that exact bridge to rule out every factor map. Repository searches found adjacent factorization machinery but no equal finite model.

## References

- Truth anchor: `D5/S3/ObserverMemory/FiniteCountermodels/MinimalMacroFactorizationCounterexample.deterministic_three_state_process_has_no_macro_factorization`
