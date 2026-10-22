# Charged Two-Sheet Full Normal Jets

## Abstract

Actual charged retained-energy fields and literal two-sheet normal jets

The construction keeps the original unrestricted lattice, determinant-unit witness, integral charges, signed pairing, chargeScalar, and actual tensor target. The retained Gaussian is applied through the existing native correction evaluation, so every asserted equality remains an equality of the original fields or their original integer modes on arbitrary targets.

**Theorem 1.1 (Formal Two-Sheet Composition).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.two_sheet_composition`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.two_sheet_composition` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

For t=4u/(1-u)^2 with 1-u nonzero, the formal composition identity t(1-u)^2=4u is proved directly. This is only the algebraic coordinate relation; it does not by itself identify either charged chart with the original field.

**Theorem 1.2 (Whole-Field Retained-Energy Recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_recurrence` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The original full retained polynomial recurrence is transported through nativeCorrectionEvaluation and the genuine Ytw source bridge. It is therefore consumed by a whole field, not by a scalar evaluation or vacuum-only projection.

**Theorem 1.3 (Every Integer Normal Jet Satisfies the Recurrence).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_recurrence`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_recurrence` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

Applying an arbitrary original mode to an arbitrary actual target tensor gives the retained recurrence componentwise. The target is unrestricted and no polynomial coefficient is discarded.

**Theorem 1.4 (Whole-Field Finite Gaussian Expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_finite_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_finite_gaussian` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The compiled finite expansion retains every normal-energy label, the actual chargedEnergyGaussian coefficient, and the independent X(none) shift before native field evaluation.

**Theorem 1.5 (Finite Gaussian Expansion At Every Normal Jet).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_finite_gaussian`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_finite_gaussian` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The whole-field finite expansion is projected to each original integer mode and arbitrary actual target tensor by linearity of the HVertexOperator coefficient map.

**Theorem 1.6 (Exact Charged Product Normalization).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The exact charged tensor ordered-product theorem is consumed with its literal chargeScalar product and halfContraction finsum. No auxiliary chart binomial or replacement target is introduced.

**Theorem 1.7 (Both Literal Charts Vanish Below Their Signed Starts).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization_below_start`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization_below_start` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The exact plus and minus below-start bounds are applied to the charged product target, preserving the signed g distinction and the negative-charge monodromy already present in the original chart supplier.

**Theorem 1.8 (Source Gaussian Closure On Every Normal Jet).**

Lean statement: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.source_normal_jet_gaussian_closed`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.source_normal_jet_gaussian_closed` (`✓ std3`). ∎

*Citation.* Igor B. Frenkel, James Lepowsky, and Arne Meurman (1988). *Vertex Operator Algebras and the Monster*. DOI: [10.1016/S0079-8169(08)X6136-7](https://doi.org/10.1016/S0079-8169(08)X6136-7).

*Commentary.*

The existing genuine source-field Gaussian theorem is consumed at every integer mode and arbitrary actual target. It remains a source-power bridge and does not claim complete charged all-j closure.

These results close the actual whole-field retained Gaussian consumer and its arbitrary normal jets, and expose the exact charged product normalization and both below-start chart branches. The regular charged scalar ratio, complete Lambda/J jet comparison, twisted Jacobi closure, and both original all-j endpoint identities remain open. The broader moonshine, VOA, CFT, anomaly, fusion, string, and AdS/CFT objective remains active and is not claimed complete by this scoped module.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.charged_product_two_sheet_normalization_below_start`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_finite_gaussian`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_field_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_finite_gaussian`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.retained_energy_normal_jet_recurrence`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.source_normal_jet_gaussian_closed`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeHalfFockActualChargedTwoSheetFullNormalJets.two_sheet_composition`
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOrderedProducts](LatticeHalfFockOrderedProducts.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockOriginalTwoSheetChartRecurrence](LatticeHalfFockOriginalTwoSheetChartRecurrence.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockRetainedEnergyFactorization](LatticeHalfFockRetainedEnergyFactorization.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeHalfFockScalarLabelledGaussian](LatticeHalfFockScalarLabelledGaussian.md)
