# Quadratic-Residue Counterexample at Two

## Abstract

The prime two refutes the unqualified quadratic-residue equivalence.

**Theorem 1.1 (The prime two refutes the unqualified equivalence).**

$$\neg(\operatorname{IsSquare}(5 : \operatorname{ZMod} 2) \Leftrightarrow 2\equiv\pm1\ (\operatorname{mod} 5))$$

*Proof.* Machine-checked in Lean as `D5/S3/PrimeForms/QuadraticResidueCounterexample.two_refutes_unqualified_quadratic_residue_equivalence` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

At p = 2, five is a square modulo two, witnessed by one, but two is congruent to neither one nor four modulo five. Thus the quadratic-residue equivalence stated only with p unequal to five is false, and the odd-prime premise in the corrected criterion is necessary.

Pinned Mathlib supplies ZMod and IsSquare. The repository's existing corrected criterion handles odd primes; no existing Mathlib or D5 declaration states this p = 2 counterexample.

## References

- Truth anchor: `D5/S3/PrimeForms/QuadraticResidueCounterexample.two_refutes_unqualified_quadratic_residue_equivalence`
- Dependency: [D5/S3/PrimeForms/GoldenPrimeClassification](GoldenPrimeClassification.md)
