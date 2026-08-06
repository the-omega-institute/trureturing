# Recursive Definitions as Selected Fixed Points

## Abstract

Recursive definitions are fixed points with explicit extremal selections.

**Theorem 1.1 (A recursive equation is a fixed-point equation).**

$$f(x)=x\iff x\in\operatorname{Fix}(f).$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/RecursiveDefinition.is_recursive_definition_iff_fixed_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary endomorphism and candidate value, the equation f(x) = x is equivalent to membership in Function.fixedPoints f.

**Theorem 1.2 (Distinct extremal fixed points make the selection observable).**

$$\operatorname{lfp}(f)\neq\operatorname{gfp}(f)\Rightarrow f(\operatorname{select}_f(\mathrm{least}))=\operatorname{select}_f(\mathrm{least})\land f(\operatorname{select}_f(\mathrm{greatest}))=\operatorname{select}_f(\mathrm{greatest})\land \operatorname{select}_f(\mathrm{least})\neq\operatorname{select}_f(\mathrm{greatest}).$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/RecursiveDefinition.extremal_selection_distinguishes_fixed_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The selector is explicit data with least and greatest cases. For a monotone endomorphism of a complete lattice, if its least and greatest fixed points differ, both selected values satisfy the fixed-point equation and the two selected values are unequal.

**Theorem 1.3 (Uniqueness identifies the least and greatest fixed points).**

$$\left(\exists!x,\ f(x)=x\right)\Rightarrow \operatorname{lfp}(f)=\operatorname{gfp}(f).$$

*Proof.* Machine-checked in Lean as `D5/S1/Dynamics/RecursiveDefinition.unique_fixed_point_implies_lfp_eq_gfp` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For a monotone endomorphism of a complete lattice, the existence of exactly one value satisfying f(x) = x implies that the least and greatest fixed points coincide.

## References

- Truth anchor: `D5/S1/Dynamics/RecursiveDefinition.extremal_selection_distinguishes_fixed_points`
- Truth anchor: `D5/S1/Dynamics/RecursiveDefinition.is_recursive_definition_iff_fixed_point`
- Truth anchor: `D5/S1/Dynamics/RecursiveDefinition.unique_fixed_point_implies_lfp_eq_gfp`
- Dependency: [D5/S1/Dynamics/KnasterTarski](KnasterTarski.md)
