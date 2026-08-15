# Squaring the Negative-Pell Unit

## Abstract

A norm-minus-one quadratic integer squares to an explicit norm-one Pell unit.

**Theorem 1.1 (The negative-Pell element has an explicit norm-one square).**

$$\forall j\in\mathbb{Z},\quad d=36j^{2}+1,\quad u=(6j, 1)\in\operatorname{Zsqrtd}(d),\quad \operatorname{norm}(u)=-1 \land u^{2}=(72j^{2}+1, 12j) \land \operatorname{norm}(u^{2})=1$$

*Proof.* Machine-checked in Lean as `D5/S3/ArithUnits/NegativePellSquare.negative_pell_square_unit` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For any integer j, put d = 36 j^2 + 1 and take the quadratic integer u with coordinates (6j, 1) in Zsqrtd d. Its norm is -1. Squaring u gives coordinates (72 j^2 + 1, 12j), and multiplicativity of the norm then makes this square a norm-one Pell unit.

The formalization closes only the negative-Pell and unit-square clause of the source atom. It does not claim the Eisenstein-norm realization criterion, the finite implementation table, or the odd-core purity and mixed-residence conclusions from the same appendix entry.

Repository and pinned Mathlib searches found no declaration for this 36 j^2 + 1 parameter family. The proof reuses Mathlib revision fabf563a7c95a166b8d7b6efca11c8b4dc9d911f through Zsqrtd.normMonoidHom.map_pow for norm multiplicativity; only the explicit coordinate and norm computations are discharged locally. Loogle returned zero exact matches, and GitHub code search returned no result for the parameter formula.

## References

- Truth anchor: `D5/S3/ArithUnits/NegativePellSquare.negative_pell_square_unit`
