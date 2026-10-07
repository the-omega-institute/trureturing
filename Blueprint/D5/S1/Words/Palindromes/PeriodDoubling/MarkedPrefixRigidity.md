# Arithmetic Rigidity of a Marked Prefix

## Abstract

The marked prefix survives tight odd palindromic cuts with a corrected charge inequality.

**Theorem 1.1 (Retained and removed prefix alternatives).**

$$\forall n \in \mathbb{N},\; \forall j \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall p \in \mathbb{N},\; \forall T \in \mathbb{Z},\; \left(\left(\left(\left(\left(\left(0 < m \land \operatorname{classS}\left(n\right)\right) \land \operatorname{markedPrefix}\left(n, m, p, T\right)\right) \land j < n\right) \land \operatorname{mod}\left(n, 2\right) \ne \operatorname{mod}\left(j, 2\right)\right) \land \operatorname{Palindrome}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(\operatorname{Nat.sub}\left(n, j\right)\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(j + \operatorname{val}\left(i\right)\right)\right)\right)\right) \land \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(j + 1, 2\right), \mathbb{Z}\right)\right) + 1\right) \Rightarrow \left(\left(\exists U \in \mathbb{Z},\; \operatorname{markedPrefix}\left(j, m, p, U\right) \land \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(j\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(n\right), \mathbb{Z}\right) + (1 + 2 \cdot \operatorname{cast}\left(\operatorname{mod}\left(p, 2\right), \mathbb{Z}\right) - 1) \cdot (\operatorname{ite}\left(2 \cdot U - \operatorname{cast}\left(\operatorname{mod}\left(j, 2\right), \mathbb{Z}\right) < 0, 1, 0\right) - \operatorname{ite}\left(2 \cdot T - \operatorname{cast}\left(\operatorname{mod}\left(n, 2\right), \mathbb{Z}\right) < 0, 1, 0\right)) \le 0\right) \lor \left(\left(\left(\operatorname{markedPrefix}\left(j, \operatorname{Nat.sub}\left(m, 1\right), p + 3, \operatorname{neg}\left(T\right)\right) \land \operatorname{ite}\left(2 \cdot T - \operatorname{cast}\left(\operatorname{mod}\left(n, 2\right), \mathbb{Z}\right) < 0, 1, 0\right) = 1\right) \land \operatorname{ite}\left(2 \cdot \operatorname{neg}\left(T\right) - \operatorname{cast}\left(\operatorname{mod}\left(j, 2\right), \mathbb{Z}\right) < 0, 1, 0\right) = 0\right) \land \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(j\right), \mathbb{Z}\right) - \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(n\right), \mathbb{Z}\right) + 1 + 2 \cdot \operatorname{cast}\left(\operatorname{mod}\left(p, 2\right), \mathbb{Z}\right) + 1 \le 0\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.marked_prefix_rigidity_and_charge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A tight palindromic cut between endpoints of opposite parity preserves every positive digit of a literal marked prefix, or removes precisely its lowest digit. In the retained case, the lower tail may change and the difference of signed-digit charges is bounded after correcting by the difference of lower-tail phases. In the removed case, the new lower tail is the exact negative of the old one, with input phase one and output phase zero. The position weight is 1+2(p mod 2), and the phase is the indicator of 2T minus the endpoint parity being negative. The selected digit position and phase snapshots are reconstructed from the path before the marker; the terminal potential then supplies the charge inequality. div and mod denote natural integer quotient and remainder, and Nat.sub denotes truncated natural subtraction.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity.marked_prefix_rigidity_and_charge`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BaseArithmetic](BaseArithmetic.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/BasePositionMemory](BasePositionMemory.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/CutRepresentation](CutRepresentation.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedBaseProjection](MarkedBaseProjection.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedInputAnnotation](MarkedInputAnnotation.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathSelection](MarkedPathSelection.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixExpansion](MarkedPrefixExpansion.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/SignedDigitPhase](SignedDigitPhase.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/UnmarkedFlipSemantics](UnmarkedFlipSemantics.md)
