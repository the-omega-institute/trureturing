# Marked Charge Obstruction

## Abstract

Marked Charge Obstruction

**Theorem 1.1 (Marked Charge Obstruction).**

$$\forall n \in \mathbb{N},\; \forall m \in \mathbb{N},\; \forall q \in \mathbb{N},\; \forall T \in \mathbb{Z},\; \left(\left(\left(\left(\operatorname{classS}\left(n\right) \land \operatorname{markedPrefix}\left(n, m, q, T\right)\right) \land \operatorname{mod}\left(n, 2\right) = 0\right) \land \operatorname{mod}\left(\operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right), 2\right) = 0\right) \land \operatorname{PL}\left(\operatorname{ofFn}\left(\lambda i:\operatorname{Fin}\left(n\right) \mapsto \left(u_{\mathrm{pd}}\right)\left(\operatorname{val}\left(i\right)\right)\right)\right) = \operatorname{signedWeight}\left(\operatorname{cast}\left(\operatorname{div}\left(n + 1, 2\right), \mathbb{Z}\right)\right)\right) \Rightarrow 2 \cdot \operatorname{sum}\left(\operatorname{range}\left(m\right), s:\mathbb{N} \mapsto 1 + 2 \cdot \operatorname{cast}\left(\operatorname{mod}\left(q + 3 \cdot s, 2\right), \mathbb{Z}\right)\right) \le \operatorname{cast}\left(\operatorname{signedDigitCharge}\left(n\right), \mathbb{Z}\right) + 2 \cdot \operatorname{cast}\left(\operatorname{mod}\left(q, 2\right), \mathbb{Z}\right) \cdot \operatorname{ite}\left(2 \cdot T - \operatorname{cast}\left(\operatorname{mod}\left(n, 2\right), \mathbb{Z}\right) < 0, 1, 0\right)$$

*Proof.* Machine-checked in Lean as `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction.marked_charge_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A class-S endpoint of even parity and even signed weight can attain its signed-weight lower bound only if twice its marked-prefix weight fits inside the signed-digit charge plus the lower-tail phase correction. The proof follows an optimal tight path and accounts for each removed marked digit. div and mod denote natural integer quotient and remainder; cast explicitly denotes the displayed coercions.

## References

- Truth anchor: `D5/S1/Words/Palindromes/PeriodDoubling/MarkedPathObstruction.marked_charge_obstruction`
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/EvenTightPaths](EvenTightPaths.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/MarkedPrefixRigidity](MarkedPrefixRigidity.md)
- Dependency: [D5/S1/Words/Palindromes/PeriodDoubling/TightFactorization](TightFactorization.md)
