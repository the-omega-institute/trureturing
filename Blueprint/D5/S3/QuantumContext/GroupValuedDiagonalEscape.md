# Group-Valued Diagonal Escape

## Abstract

A free group action shifts diagonal coordinates and forces pointwise escape.

**Theorem 1.1 (Group-valued diagonal escape).**

$$\forall a,\ \operatorname{orbit}(h \cdot E(a,a)) = \operatorname{orbit}(E(a,a)) \land \forall a,\ \operatorname{coord}(h \cdot E(a,a)) = h\,\operatorname{coord}(E(a,a)) \land (h \neq 1 \Rightarrow \forall a,\ h \cdot E(a,a) \neq E(a,a)).$$

*Proof.* Machine-checked in Lean as `D5/S3/QuantumContext/GroupValuedDiagonalEscape.group_valued_diagonal_escape` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose one representative in every orbit of a free left group action. The resulting normal-form coordinate writes each point uniquely as a group element acting on its chosen orbit representative.

Left translation by h does not change the orbit projection and multiplies the normal-form group coordinate on the left by h. If h is not the identity, freeness excludes equality with the original diagonal value at every address.

The pinned Mathlib declaration MulAction.selfEquivOrbitsQuotientProd' supplies the free-action normal form directly. IsCancelSMul.eq_one_of_smul supplies the exact final escape step. The formal theorem is more general than the finite group setting because neither conclusion uses finiteness.

## References

- Truth anchor: `D5/S3/QuantumContext/GroupValuedDiagonalEscape.group_valued_diagonal_escape`
