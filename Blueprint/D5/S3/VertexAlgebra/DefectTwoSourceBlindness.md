# Two-source determinant blindness

## Abstract

Every finite binary tree built from two defect directions has zero cubic carry response.

Let E be F2 cubed, with the explicit sign table f0 of (FC.4), its alternating correction b_m, and the character ell_m(g)_i=f_m(g,u_i). Fix two coarse defect labels g and h. A coefficient tree has a pair (a,b) in F2 squared at each leaf. The source tree replaces that leaf by ag+bh and retains each binary fork; total adds all source labels. Let T denote the finite coefficient trees.

**Theorem 1.1 (No finite two-source tree detects the cubic carry).**

$$\forall m, g, h\in E, L, M, R\in T,\ \operatorname{dot}\left(\operatorname{carry}\left(\operatorname{ell}\left(m\right), \operatorname{total}\left(\operatorname{sourceTree}\left(g, h, L\right)\right), \operatorname{total}\left(\operatorname{sourceTree}\left(g, h, M\right)\right)\right), \operatorname{total}\left(\operatorname{sourceTree}\left(g, h, R\right)\right)\right)=0$$

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Induction on each tree shows that its total remains in the plane spanned by g and h. Direct evaluation of the eight finite sign choices shows that their carry is the same wedge product. Pairing the carry of two tree totals with a third total from that plane is therefore zero. This claim concerns additive label composition, not a physical fusion operation or a nonzero OPE coefficient.

## References

- Truth anchor: `D5/S3/VertexAlgebra/DefectTwoSourceBlindness.two_source_carry_blind`
- Dependency: [D5/S3/VertexAlgebra/CharacterCarryCompletion](CharacterCarryCompletion.md)
