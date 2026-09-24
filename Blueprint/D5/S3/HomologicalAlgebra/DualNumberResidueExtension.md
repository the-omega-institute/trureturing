# A Nonzero Dual-Number Residue Extension

## Abstract

The epsilon-ideal sequence over the rational dual numbers is a short exact sequence with nonzero degree-one extension class.

**Definition 1.1 (The epsilon-ideal residue complex).**

Lean statement: `D5/S3/HomologicalAlgebra/DualNumberResidueExtension.dualNumberResidueComplex`

*Formalization.* `D5/S3/HomologicalAlgebra/DualNumberResidueExtension.dualNumberResidueComplex` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* The Stacks Project Authors (2026). *The Stacks project*. URL: <https://stacks.math.columbia.edu/tag/0A5Q>.

*Acknowledgement.* Charles A. Weibel (1994). *Tor and Ext*. DOI: [10.1017/CBO9781139644136.004](https://doi.org/10.1017/CBO9781139644136.004).

*Commentary.*

Let A be the rational dual-number ring and let the residue copy of the rationals carry its A-module structure through augmentation. The complex sends q to q epsilon and then takes augmentation.

**Theorem 1.2 (The residue extension class is nonzero).**

$$\exists hS: ShortExact(Sepsilon), (hS.extClass: Ext^{1}_{A}(\mathbb{Q}, \mathbb{Q})) \neq 0$$

*Proof.* Machine-checked in Lean as `D5/S3/HomologicalAlgebra/DualNumberResidueExtension.dual_number_residue_extension_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* The Stacks Project Authors (2026). *The Stacks project*. URL: <https://stacks.math.columbia.edu/tag/0A5Q>.

*Acknowledgement.* Charles A. Weibel (1994). *Tor and Ext*. DOI: [10.1017/CBO9781139644136.004](https://doi.org/10.1017/CBO9781139644136.004).

*Commentary.*

The two coordinate maps make the displayed complex short exact. If its Ext-one class vanished, Mathlib's contravariant long exact sequence and the Ext-zero/Hom equivalence would give a retraction of the epsilon inclusion.

Evaluating the retraction at epsilon gives one. A-linearity gives zero because epsilon acts through augmentation on the residue module. This contradiction proves that the extension class is nonzero.

The sources support the periodic dual-number resolution and the standard Ext machinery. The concrete rational specialization and nonvanishing argument are repository-derived. The next frontier is to identify the full graded Ext algebra and its Yoneda product.

## References

- Truth anchor: `D5/S3/HomologicalAlgebra/DualNumberResidueExtension.dualNumberResidueComplex`
- Truth anchor: `D5/S3/HomologicalAlgebra/DualNumberResidueExtension.dual_number_residue_extension_nonzero`
