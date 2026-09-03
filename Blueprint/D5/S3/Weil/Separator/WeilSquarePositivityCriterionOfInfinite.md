# Weil-Square Positivity Criteria Under Infinitely Many Zeros

## Abstract

Assuming infinitely many nontrivial zeros, the Riemann hypothesis is equivalent to repository Weil-square positivity for every ZeroData and for some ZeroData.

**Theorem 1.1 (RH is equivalent to positivity for every ZeroData).**

$$\operatorname{Infinite}\left(\{\rho \mid \operatorname{IsNontrivialZero}\left(\rho\right)\}\right) \Rightarrow \left(\operatorname{RiemannHypothesis} \Leftrightarrow \left(\forall Z \in ZeroData,\; \forall g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; 0 \le \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite.rh_iff_forall_zeroData_weilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis hInf is M1-b, infinitely many nontrivial zeros, and is not proved in this repository. The ZeroData construction used behind M1-a is noncomputable and depends on Classical.choice.

The right side is this repository's Weil-square positivity for zeroSum and convolutionSquare. The results bind the frozen fixed-Z criterion and nonemptiness bridge; these conditional equivalences are not a proof of RH.

**Theorem 1.2 (RH is equivalent to positivity for some ZeroData).**

$$\operatorname{Infinite}\left(\{\rho \mid \operatorname{IsNontrivialZero}\left(\rho\right)\}\right) \Rightarrow \left(\operatorname{RiemannHypothesis} \Leftrightarrow \left(\exists Z \in ZeroData,\; \forall g \in WeilTestFunction, hZero \in \operatorname{SymmetricConvergent}\left(Z, \operatorname{convolutionSquare}\left(g\right)\right),\; 0 \le \Re (\operatorname{zeroSum}\left(Z, \operatorname{convolutionSquare}\left(g\right), hZero\right))\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite.rh_iff_exists_zeroData_weilSquarePositivity` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis hInf is M1-b, infinitely many nontrivial zeros, and is not proved in this repository. The ZeroData construction used behind M1-a is noncomputable and depends on Classical.choice.

The right side is this repository's Weil-square positivity for zeroSum and convolutionSquare. The results bind the frozen fixed-Z criterion and nonemptiness bridge; these conditional equivalences are not a proof of RH.

## References

- Truth anchor: `D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite.rh_iff_exists_zeroData_weilSquarePositivity`
- Truth anchor: `D5/S3/Weil/Separator/WeilSquarePositivityCriterionOfInfinite.rh_iff_forall_zeroData_weilSquarePositivity`
- Dependency: [D5/S3/Weil/Separator/WeilSquarePositivityCriterion](WeilSquarePositivityCriterion.md)
- Dependency: [D5/S3/Weil/ZetaBridge/ZeroDataNonemptyIffInfinite](../ZetaBridge/ZeroDataNonemptyIffInfinite.md)
