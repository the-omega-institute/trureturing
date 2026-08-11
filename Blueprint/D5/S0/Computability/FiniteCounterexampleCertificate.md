# Finite Counterexample Certificates

## Abstract

A false universal finite readout has exactly a bounded counterexample certificate.

**Theorem 1.1 (A false universal finite readout has a bounded certificate).**

$$\neg(\forall h, D(h) = true) \iff \exists n, h, \operatorname{findCounterexample}(D, n) = \operatorname{some}(h) \land D(h) = false.$$

*Proof.* Machine-checked in Lean as `D5/S0/Computability/FiniteCounterexampleCertificate.finite_readout_counterexample_certificate` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A finite readout is an executable function from finite marker histories to `Bool`, with `true` as acceptance and `false` as rejection. Failure of universal acceptance is equivalent to an explicit natural bound and a history returned by bounded search with a certified false readout. The rejected history is therefore a checkable counterexample certificate.

The proof first extracts a rejected history from the failed universal statement. That history's length supplies a finite search bound. Completeness of the existing bounded search then returns a counterexample, and soundness certifies its rejection. Conversely, any certified rejected history directly contradicts universal acceptance.

The library was searched before proving. Pinned Mathlib provides `not_forall` and `Bool.eq_false_of_not_eq_true`, but it has no declaration about this marker-history search. The repository's `findCounterexample_complete` and `findCounterexample_sound` supply the executable core, so the new result is an honest composition rather than a reproof of either dependency.

## References

- Truth anchor: `D5/S0/Computability/FiniteCounterexampleCertificate.finite_readout_counterexample_certificate`
- Dependency: [D5/S0/History/MarkerHistorySearch](../History/MarkerHistorySearch.md)
