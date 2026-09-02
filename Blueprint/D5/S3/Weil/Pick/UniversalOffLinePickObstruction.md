# Universal Off-Line Pick Obstruction

## Abstract

Every right-side zero image gives the same determinant-minus-one two-point Pick matrix, independently of its ordinate.

**Theorem 1.1 (The two-point obstruction is independent of the ordinate).**

$$\forall s: \mathbb{C} \to \mathbb{C}, sigma, gamma \in \mathbb{R}, (\frac{1}{2} < sigma \land \operatorname{s}\left(0\right) = 0 \land \operatorname{s}\left(1-\frac{1}{{sigma+i\cdot gamma}}\right) = 1) \Rightarrow \operatorname{let}(rho := sigma+i\cdot gamma, zrho := 1-\frac{1}{rho}, K := (z, w \mapsto \frac{1-\operatorname{s}\left(z\right)\times\overline{\operatorname{s}\left(w\right)}}{1-z\times\overline{w}}), p := \operatorname{vector}\left(0, zrho\right), R := (i, j \mapsto \operatorname{K}\left(\operatorname{p}\left(i\right), \operatorname{p}\left(j\right)\right)))\;\left\lVert zrho \right\rVert < 1 \land R = \operatorname{matrix}\left(1, 1, 1, 0\right) \land \operatorname{det}\left(R\right) = -1.$$

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/UniversalOffLinePickObstruction.universal_off_line_pick_obstruction` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source point rho is constructed from its real coordinate sigma and ordinate gamma, and its disk image is one minus the reciprocal of rho.

When the arithmetic Schur object vanishes at the origin and has unit contact at that image, the standard Pick kernel gives the fixed matrix with rows (1,1) and (1,0). Its determinant is minus one, with gamma publicly bound but absent from the resulting constants.

## References

- Truth anchor: `D5/S3/Weil/Pick/UniversalOffLinePickObstruction.universal_off_line_pick_obstruction`
- Dependency: [D5/S3/Weil/Pick/MinimalRelationalVisibility](MinimalRelationalVisibility.md)
