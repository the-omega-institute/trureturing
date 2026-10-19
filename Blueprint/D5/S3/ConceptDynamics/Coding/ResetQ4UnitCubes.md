# Cube normal forms in the quartic reset orders

## Abstract

Independent finite cubic characters saturate the Dirichlet rank of the original quartic reset orders.

**Definition 1.1 (Expose the oriented character of the literal common residue units).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter`

*Formalization.* `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Expose the existing oriented readout cK as an additive homomorphism from the common residue units into ZMod 3. It selects the native exponent in the integral unit factorization.

**Theorem 1.2 (Read the residue coordinate of a supplied integral cube factorization).**

Lean statement: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter_plus_factorization`

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter_plus_factorization` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For the stated plus-order unit factorization, the native common residue character reads the one-plus-time exponent j in ZMod 3. The same j is carried into the original centralizer factorization.

Use the literal original orders Plus(4)=Int[X]/(X^4-X^3-X^2-X-1) and Minus(4)=Int[X]/(X^4+X^3+X^2+X+1). alpha and beta are the classes of X as units, and Bplus=1+alpha, Bminus=1+beta. Their integral inverse polynomials are X^3-X^2-X-1, X^4, 2-X+2X^2-X^3 and -X-X^3, respectively. The field of the plus polynomial has signature (2,1); the minus field has signature (0,2). Positive plus roots are classified by the existing Perron reciprocal-sum theorem; a strictly monotone polynomial in the negative variable gives its unique negative root. The primitive fifth root excludes real minus places. A real embedding excludes plus three-torsion; simultaneous primitive third and fifth roots would force degree at least eight on the minus side. Both actual fields have degree four, so Dirichlet ranks are two and one.

**Theorem 1.3 (Every original plus-order unit has a two-coordinate cube form).**

$$\forall u \in \operatorname{Units}\left(\operatorname{Plus}\left(4\right)\right),\; \exists i \in \operatorname{Fin}\left(3\right), j \in \operatorname{Fin}\left(3\right), v \in \operatorname{Units}\left(\operatorname{Plus}\left(4\right)\right),\; u = \operatorname{pow}\left(alpha, \operatorname{val}\left(i\right)\right) \cdot \operatorname{pow}\left(Bplus, \operatorname{val}\left(j\right)\right) \cdot \operatorname{pow}\left(v, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.plus_cube_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Gauss divisibility embeds the monic original order into its quartic field, and integral elements land in the integer ring. FiniteKernelModThree applies to the actual image lattice, with a finite torsion kernel, and gives dimension at most two for original cube classes. It does not infer cube-quotient injectivity from the order embedding. The actual common mod-two quotient is the sixteen-element field. Its oriented cubic character cK and the alpha=5 mod-seven character cSeven have matrix [[0,1],[1,0]] on alpha,Bplus. Thus the two classes are independent. Their synthesis map attains the dimension bound and is surjective. The kernel of the original quotient returns v in Units(Plus(4)) itself.

**Theorem 1.4 (Every original minus-order unit has a one-coordinate cube form).**

$$\forall u \in \operatorname{Units}\left(\operatorname{Minus}\left(4\right)\right),\; \exists k \in \operatorname{Fin}\left(3\right), v \in \operatorname{Units}\left(\operatorname{Minus}\left(4\right)\right),\; u = \operatorname{pow}\left(Bminus, \operatorname{val}\left(k\right)\right) \cdot \operatorname{pow}\left(v, 3\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.minus_cube_normal_form` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The same descent bounds the original minus cube quotient by one. The common finite-field character takes Bminus to one, so this class is independent and spans. Quotient equality produces the cube preimage in Units(Minus(4)), rather than only in the surrounding number field. No fundamental-unit or maximal-order identification is required.

**Theorem 1.5 (Compatible original units have the same common cube coordinate).**

$$\forall u \in \operatorname{Units}\left(\operatorname{Plus}\left(4\right)\right), w \in \operatorname{Units}\left(\operatorname{Minus}\left(4\right)\right),\; \operatorname{UnitsMap}\left(\operatorname{rplus}\left(4\right), u\right) = \operatorname{UnitsMap}\left(\operatorname{rminus}\left(4\right), w\right) \Rightarrow \left(\exists i \in \operatorname{Fin}\left(3\right), j \in \operatorname{Fin}\left(3\right), k \in \operatorname{Fin}\left(3\right), v \in \operatorname{Units}\left(\operatorname{Plus}\left(4\right)\right), t \in \operatorname{Units}\left(\operatorname{Minus}\left(4\right)\right),\; u = \operatorname{pow}\left(alpha, \operatorname{val}\left(i\right)\right) \cdot \operatorname{pow}\left(Bplus, \operatorname{val}\left(j\right)\right) \cdot \operatorname{pow}\left(v, 3\right) \land \left(w = \operatorname{pow}\left(Bminus, \operatorname{val}\left(k\right)\right) \cdot \operatorname{pow}\left(t, 3\right) \land \operatorname{castZMod3}\left(\operatorname{val}\left(j\right)\right) = \operatorname{castZMod3}\left(\operatorname{val}\left(k\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.compatible_cube_normal_forms` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The hypothesis is literal equality of the residue units under rplus(4) and rminus(4). Applying cK to both original-order normal forms kills cubes and alpha, leaving j=k in ZMod(3). Both cube roots remain in their respective original orders. These component normal forms do not assert exhaustion of a history representation image or the original-h SGCC factorization.

## References

- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.compatible_cube_normal_forms`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.minus_cube_normal_form`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.plus_cube_normal_form`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter`
- Truth anchor: `D5/S3/ConceptDynamics/Coding/ResetQ4UnitCubes.residueCharacter_plus_factorization`
- Dependency: [D5/S0/Tower/DBonacci/Irreducibility](../../../S0/Tower/DBonacci/Irreducibility.md)
- Dependency: [D5/S0/Tower/DBonacci/PerronRoot](../../../S0/Tower/DBonacci/PerronRoot.md)
- Dependency: [D5/S3/ConceptDynamics/Coding/ResetIntegralGluing](ResetIntegralGluing.md)
- Dependency: [D5/S3/Factorization/Embeddings/FiniteKernelModThree](../../Factorization/Embeddings/FiniteKernelModThree.md)
