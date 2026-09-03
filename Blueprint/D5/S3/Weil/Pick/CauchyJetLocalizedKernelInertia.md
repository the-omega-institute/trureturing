# Cauchy-Jet Localized-Kernel Inertia

## Abstract

A distinct signed-support Cauchy-jet sampling has negative index exactly equal to the active reflected-orbit count.

**Definition 1.1 (Observer signed-support profile).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportProfile`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The finite profile evaluates the signed-support coordinate for every orbit.

**Definition 1.2 (Complex support embedding).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportComplex`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportComplex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The real signed-support profile is embedded into the complex plane.

**Definition 1.3 (Localized weight profile).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedWeightProfile`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedWeightProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Each signed support is multiplied by its supplied positive mass.

**Definition 1.4 (Canonical observer Cauchy-jet feature matrix).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerCauchyJetFeatureMatrix`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerCauchyJetFeatureMatrix` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The sampling center is fixed at i, which avoids every real signed-support coordinate.

**Definition 1.5 (Localized Cauchy-jet Gram matrix).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGram`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGram` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The signed diagonal form is pulled back through the canonical finite Cauchy-jet feature matrix.

**Definition 1.6 (Localized Gram Hermitian witness).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGramIsHermitian`

*Formalization.* `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGramIsHermitian` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Hermitianity is inherited from conjugate-transpose pullback of the real diagonal form.

**Theorem 1.7 (Sampled negative index equals the active barcode count).**

Lean statement: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.cauchy_jet_localized_kernel_barcode_inertia`

*Proof.* Machine-checked in Lean as `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.cauchy_jet_localized_kernel_barcode_inertia` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Distinct signed supports make the feature matrix invertible. Inertia therefore equals diagonal sign count, and positive masses identify that count with active reflected-orbit intervals. Positive and zero negative-index characterizations are included.

## References

- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportProfile`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerSupportComplex`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedWeightProfile`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerCauchyJetFeatureMatrix`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGram`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.observerLocalizedCauchyJetGramIsHermitian`
- Truth anchor: `D5/S3/Weil/Pick/CauchyJetLocalizedKernelInertia.cauchy_jet_localized_kernel_barcode_inertia`
