# Class Preservation and Charge Monotonicity

## Abstract

Tight legal palindrome cuts preserve class S and do not increase the literal signed-digit charge.

**Theorem 1.1 (The tight-cut transition law).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \left(\left(\left(\operatorname{classS}\left(n\right) \land j < n\right) \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(i:\operatorname{Fin}\left(\operatorname{Nat.sub}\left(n, j\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(j + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(j + 1, 2\right), \mathbb{Z}\right)\right) + 1\right) \Rightarrow \left(\operatorname{classS}\left(j\right) \land \operatorname{signedDigitCharge}\left(j\right) \le \operatorname{signedDigitCharge}\left(n\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/TightCutCharge.tight_cut_class_and_Q` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A cut is tight when the minimum signed weight of the rounded half drops by exactly one. Complete path realization gives an accepting base path. The class-escape potential bound zero excludes the invalid-output mode, since its f charge is one. In the valid-output mode the q+3f bound with terminal phase gives Q(j)≤Q(n). The path's output signed expansion has the literal rounded-half value and class spacing; equal-length zero padding and nonadjacent uniqueness identify it with the triple-binary expansion defining class S. div denotes natural integer quotient, and Nat.sub denotes truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/TightCutCharge.tight_cut_class_and_Q`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic](BaseArithmetic.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseClassStreams](BaseClassStreams.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation](CutRepresentation.md)
