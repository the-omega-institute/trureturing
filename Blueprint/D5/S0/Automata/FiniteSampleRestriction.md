# Finite Sample Restriction

## Abstract

Unsatisfiability on any exact finite subsample implies nonexistence of a globally correct DFAO on the same state carrier.

**Theorem 1.1 (Finite sample UNSAT implies global nonexistence).**

$$\neg \exists M: \operatorname{FitsSubsample}(M, S) \Rightarrow \neg \exists M: \operatorname{CorrectOnFamily}(M).$$

*Proof.* Machine-checked in Lean as `D5/S0/Automata/FiniteSampleRestriction.no_global_fin_model_of_no_subsample_fin_model` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every globally correct machine restricts to every selected family of sample indices.

Consequently a certified finite-sample exclusion is already a sound lower-bound certificate for the infinite sparse family on the same state carrier.

The converse is deliberately absent: fitting a finite sample does not establish global correctness.

## References

- Truth anchor: `D5/S0/Automata/FiniteSampleRestriction.no_global_fin_model_of_no_subsample_fin_model`
- Dependency: [D5/S0/Automata/DFAOStateLowerBound](DFAOStateLowerBound.md)
