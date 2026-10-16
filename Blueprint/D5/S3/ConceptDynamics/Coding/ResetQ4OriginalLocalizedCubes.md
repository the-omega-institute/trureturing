# Dyadic cube factorization of the original reset action

## Abstract

Dyadic Bezout gluing transports original quartic unit cube forms to every original history automorphism.

Let D=Int[1/2] and index matrices by the eight original signed vertices Sigma (_:Fin 4), Sign. The actual full group is ResetFullAut(4). Transport its original beam-set-image action rho through resetNativeEquiv to the original vertex module, take its column matrix, and extend coefficients from Int to D; this defines rhoD. T is the column matrix of the literal forward reset transition, with the same scalar extension. It is the transpose of the expanded row adjacency. The original unit shift has image T, and the original evenAut(4) has image I+T.

Write f=X^4-X^3-X^2-X-1, g=X^4+X^3+X^2+X+1, and F=f*g. The integral certificate X*f+(2-X)*g=2 gives (X/2)*f+(1-X/2)*g=1 over D. Thus the original quotient D[X]/(F) is isomorphic to D[X]/(f) times D[X]/(g). The two projectors are (1-X/2)*g and (X/2)*f. Monic representatives give the inverse map. Component units and their inverses glue together without any residue compatibility requirement on the chosen roots.

For each actual h, the published scalarUnit construction gives an integral unit u_h in Int[X]/(F), from the action rho(h) and its inverse. Its components are compatible modulo two. ResetQ4UnitCubes supplies u_plus=alpha^i*Bplus^j*v^3 and u_minus=Bminus^k*w^3 with i,j,k in Fin 3. Compatibility forces j=k. Time has components (alpha,beta), while I+time has components (Bplus,Bminus). Since beta^5=1, replacing w by beta^(3*i)*w gives beta^i*(beta^(3*i)*w)^3=w^3. This exact correction aligns the two component forms before the roots are glued.

The cyclic integral chart and the original vertex basis identify multiplication by X with forward T. Polynomial ring-hom extensionality then gives F(T)=0 and the evaluation identity for every integral scalar, including u_h. Evaluation descends from D[X]/(F) to the original matrix ring. Evaluating a glued unit also evaluates its actual inverse, and commutativity of the source proves that its matrix commutes with T. Centralizer is the subgroup of matrix units centralizing the unit with matrix value T.

**Theorem 1.1 (Every original automorphism has a commuting dyadic cube factorization).**

$$\forall h \in \operatorname{ResetFullAut}\left(4\right),\; \exists i \in \operatorname{Fin}\left(3\right), j \in \operatorname{Fin}\left(3\right), v \in Centralizer,\; \operatorname{rhoD}\left(h\right) = \operatorname{pow}\left(T, \operatorname{val}\left(i\right)\right) \cdot \operatorname{pow}\left(1 + T, \operatorname{val}\left(j\right)\right) \cdot \operatorname{pow}\left(\operatorname{matrixValue}\left(v\right), 3\right) \land \operatorname{Commute}\left(\operatorname{matrixValue}\left(v\right), T\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.original_localized_cube_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The matrix V is a genuine unit over D and commutes with the literal forward T. The proof factors the actual integral scalar unit, then evaluates the factorization in the original action diagram. The bounded exponents are representatives modulo three; no uniqueness of them or of the cube root is asserted.

The conclusion constrains every actual original image but does not assert that every centralizing matrix is an image. It supplies neither a presentation of the full original group nor an SGCC character or cochain. Given a separately supplied additive character of the full matrix-unit centralizer with values in ZMod(3) that kills the original shift, a cube contributes zero and each original image has character value j times the value at I+T. This conditional application constructs no character and proves no nonzero value at I+T.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4OriginalLocalizedCubes.original_localized_cube_factorization`
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetNativeUnitNormalForm](ResetNativeUnitNormalForm.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes](ResetQ4UnitCubes.md)
