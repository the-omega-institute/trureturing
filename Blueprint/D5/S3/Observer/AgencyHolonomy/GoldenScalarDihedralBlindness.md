# Golden Scalar Dihedral Blindness

## Abstract

Golden-unit scalar completion is blind to ordered prime-word dihedral holonomy.

**Theorem 1.1 (The complete scalar world does not recover dihedral holonomy).**

$$\begin{aligned}sigmaPlus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaPlus}\left((a, b)\right) := a + b \times \varphi,\\sigmaMinus: \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{sigmaMinus}\left((a, b)\right) := a + b \times \psi,\\anisotropicForm: \mathbb{R} \to \mathbb{Z} \times \mathbb{Z} \to \mathbb{R}, \operatorname{anisotropicForm}\left(eta, (a, b)\right) := \operatorname{exp}\left(eta\right) \times \operatorname{sigmaPlus}\left((a, b)\right)^{2} + \operatorname{exp}\left(-eta\right) \times \operatorname{sigmaMinus}\left((a, b)\right)^{2},\\goldenUnitZeta: \mathbb{C} \to \mathbb{R} \to \mathbb{C}, \operatorname{goldenUnitZeta}\left(s, eta\right) := \sum_{alpha \in {\mathbb{Z} \times \mathbb{Z}} \setminus \{(0, 0)\}} \operatorname{anisotropicForm}\left(eta, alpha\right)^{-s},\\\operatorname{let} completedWorld: \mathbb{R} \to \left(\operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right) \to \left(\mathbb{C} \to \mathbb{C}\right)\right) = (eta: \mathbb{R} \mapsto (w: \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right) \mapsto (s: \mathbb{C} \mapsto \operatorname{goldenUnitZeta}\left(s, \operatorname{act}\left(\operatorname{goldenPrimeHolonomy}\left(w\right), eta\right)\right)))), \left(\forall s \in \mathbb{C}, eta \in \mathbb{R}, g \in \operatorname{DihedralGroup}\left(0\right),\; \operatorname{goldenUnitZeta}\left(s, \operatorname{act}\left(g, eta\right)\right) = \operatorname{goldenUnitZeta}\left(s, eta\right)\right) \land \left(\left(\forall eta \in \mathbb{R},\; \neg \left(\exists R \in \left(\mathbb{C} \to \mathbb{C}\right) \to \operatorname{DihedralGroup}\left(0\right),\; \forall w \in \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right),\; R\left(\operatorname{completedWorld}\left(eta, w\right)\right) = \operatorname{goldenPrimeHolonomy}\left(w\right)\right)\right) \land \left(\left(\exists w1 \in \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right), w2 \in \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right),\; \operatorname{goldenPrimeHolonomy}\left(w1\right) \ne \operatorname{goldenPrimeHolonomy}\left(w2\right)\right) \land \left(\forall eta \in \mathbb{R}, w1 \in \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right), w2 \in \operatorname{List}\left(\operatorname{UnramifiedPrime}\left(\right)\right),\; \operatorname{completedWorld}\left(eta, w1\right) = \operatorname{completedWorld}\left(eta, w2\right)\right)\right)\right).\end{aligned}$$

*Proof.* Machine-checked in Lean as `D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness.golden_scalar_dihedrally_blind` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The rapidity carrier uses Mathlib's infinite dihedral group. Its rotation r(-1) is the positive golden regulator boost, and its reflection sr(0) negates rapidity.

Each unramified prime contributes the proper boost followed by reflection exactly when its imported golden character is negative. The ordered product is the source prime holonomy.

The imported lattice-zeta owner supplies reflection and one period. Integral periodicity gives invariance under every dihedral normal form. A split-inert word and its reverse have unequal holonomies but identical complete scalar worlds, ruling out a decoder that recovers every word holonomy.

## References

- Truth anchor: `D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness.golden_scalar_dihedrally_blind`
- Dependency: [D5/S3/Analytic/Dilation/GoldenUnitZetaReflection](../../Analytic/Dilation/GoldenUnitZetaReflection.md)
- Dependency: [D5/S3/Observer/AgencyHolonomy/GoldenCharacterQuotient](GoldenCharacterQuotient.md)
