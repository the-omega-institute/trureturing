# Schur Shifted-Template Lifts

## Abstract

Literal Schur templates give the classical threefold lift and the width-10 shifted-template lift.

**Theorem 1.1 (Small Schur colorings and the first obstruction).**

$$HasSchurColoring(1, 1) \land HasSchurColoring(2, 4) \land \neg \left(HasSchurColoring(1, 2)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schurColoringSmallValues` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The first clause constructs the singleton one-coloring. The second uses the explicit two-color assignment with color classes {1,4} and {2,3}. The final clause rules out a one-coloring of {1,2} using the monochromatic equation 1+1=2.

**Theorem 1.2 (The classical Schur threefold lift).**

$$\forall k, n\in \mathbb{N}, HasSchurColoring(k, n) \Rightarrow HasSchurColoring(k+1, 3n+1)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.classicalLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k and n, two translated copies of the input coloring surround the interval from n+1 through 2n+1, which is assigned one new color. The construction yields length 3n+1.

**Theorem 1.3 (Finite compatibility and width-10 carry certificates).**

$$\begin{aligned}\forall f_{x}, f_{y}: Bool, u, v: Fin(10), a: Fin(2), \neg \left(shiftedTemplateNewLabel(shiftedTemplateLabel(f_{x}, u)) = some(a) \land shiftedTemplateNewLabel(shiftedTemplateLabel(f_{y}, v)) = some(a) \land shiftedTemplateNewLabel(shiftedTemplateLabel(shiftedTemplateResultFirst(f_{x}, f_{y}, u, v), shiftedTemplateOutCol(u, v))) = some(a)\right) \land\\\forall f_{x}, f_{y}: Bool, u, v: Fin(10), shiftedTemplateOldCompatible(f_{x}, f_{y}, u, v) = true \land\\\forall f_{x}, f_{y}: Bool, u, v: Fin(10), val(u)+val(v) = 9 \Rightarrow \neg \left(shiftedTemplateNewLabel(shiftedTemplateLabel(f_{x}, u)) = some(0) \land shiftedTemplateNewLabel(shiftedTemplateLabel(f_{y}, v)) = some(0)\right) \land\\\forall f_{x}, f_{y}: Bool, u, v: Fin(10), \left(val(u)+val(v) = 0 \Rightarrow \neg \left(f_{x} = true \land f_{y} = true\right)\right) \Rightarrow \left(val(u)+val(v) = 0 \lor val(u)+val(v) = 10\right) \Rightarrow \neg \left(shiftedTemplateNewLabel(shiftedTemplateLabel(f_{x}, u)) = some(1) \land shiftedTemplateNewLabel(shiftedTemplateLabel(f_{y}, v)) = some(1)\right) \land\\\forall x, y, z\in \mathbb{N}, 1 \leq x \land 1 \leq y \land x+y = z \Rightarrow \left(blockRow(z) = blockRow(x)+blockRow(y)+shiftedTemplateCarry(blockCol(x), blockCol(y)) \land blockCol(z) = shiftedTemplateOutCol(blockCol(x), blockCol(y))\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.shiftedTemplateCompatibilityCertificates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The five conjuncts state the ordinary-label compatibility check, the shifted old-label carry check, the two separate tail checks for A and B, and the quotient-remainder addition law for positive block coordinates. The labels are the literal Table-II rows F and M=L, with the two-cell tail Q=(A,B).

**Theorem 1.4 (The width-10 shifted-template lift).**

$$\forall k, n\in \mathbb{N}, HasSchurColoring(k, n) \Rightarrow HasSchurColoring(k+2, 10n+2)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.shiftedTemplateLift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For arbitrary natural k and n, the literal width-10 shifted template and its two-cell tail transform any k-color Schur coloring of length n into a (k+2)-color Schur coloring of length 10n+2.

**Theorem 1.5 (Numerical consequences of the two lifts).**

$$HasSchurColoring(3, 13) \land HasSchurColoring(4, 42)$$

*Proof.* Machine-checked in Lean as `D5/S3/Arith/SchurShiftedTemplateLift.schurLiftNumericalConsequences` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Applying the classical lift to the explicit two-coloring gives a three-coloring of length 13. Applying the width-10 lift to the same base coloring gives a four-coloring of length 42.

## References

- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.classicalLift`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schurColoringSmallValues`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.schurLiftNumericalConsequences`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.shiftedTemplateCompatibilityCertificates`
- Truth anchor: `D5/S3/Arith/SchurShiftedTemplateLift.shiftedTemplateLift`
