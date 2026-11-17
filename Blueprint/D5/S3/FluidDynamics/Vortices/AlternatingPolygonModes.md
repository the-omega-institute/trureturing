# Alternating Polygon Modes

## Abstract

Folded modes retain one endpoint copy and two internal copies. The complete characteristic polynomial includes zero and every complex root after coefficient extension. The separate dipole and square polynomials use the actual Cartesian derivative. The paired restriction argument proves nonzero generalized eigenspaces equal ordinary eigenspaces.

The full extension is set out in the 4 November 2026 note by Haobo Ma and Wenlin Zhang, in that order. Barry and Kevrekidis retain prior credit for equilibrium, instability and the small-spectrum classification. The existing Conjecture 4.4 real-root theorem and its field, rotation, Fourier and determinant proof bodies are reused. No priority certification is made.

**Definition 1.1 (fold).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The folded label is min(q,2*m-q) for the canonical cyclic representative.

**Definition 1.2 (ell).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The radial Fourier coefficient is -(m-q) squared / 2.

**Theorem 1.3 (fold le).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_le`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Every folded cyclic label lies between zero and m.

**Theorem 1.4 (ell fold).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_fold`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_fold` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Folding preserves the radial squared coefficient.

**Theorem 1.5 (ell shift).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_shift`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_shift` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The tangential frequency shift by m gives the complementary folded square.

**Theorem 1.6 (mode product).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.mode_product`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.mode_product` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Multiplying the two actual restriction entries gives the canonical squared spectral value.

**Theorem 1.7 (ell add one ne zero).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_add_one_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_add_one_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The second off-diagonal restriction entry never vanishes at an integral Fourier label.

**Theorem 1.8 (gamma zero iff).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.gamma_zero_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.gamma_zero_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The neutral squared value occurs exactly at folded label m.

**Theorem 1.9 (fold eq iff).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_eq_iff`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_eq_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Folding retains exactly the pair of opposite cyclic labels.

**Theorem 1.10 (fold fibre card).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_fibre_card`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_fibre_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

End labels occur once; every interior folded label occurs twice.

**Theorem 1.11 (charpoly folded).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_folded`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_folded` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Folded mode factors, with endpoint multiplicity one and interior multiplicity two. This identity includes the separate small polygons.

**Theorem 1.12 (charpoly factored).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_factored`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_factored` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The complete normalized polynomial at every m >= 3.

**Theorem 1.13 (dipole charpoly).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.dipole_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.dipole_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

Dipole polynomial, derived separately from the all-mode identity.

**Theorem 1.14 (square charpoly).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.square_charpoly`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.square_charpoly` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The square constants follow from the actual Cartesian derivative. They are not the constants printed in BK arXiv v2 Eq. (12).

**Theorem 1.15 (neutral denominator ne zero).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.neutral_denominator_ne_zero`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.neutral_denominator_ne_zero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The source-chain denominator 1-m squared / 2 is nonzero for every natural m.

**Definition 1.16 (pairedOperator).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.pairedOperator`

*Formalization.* `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.pairedOperator` (`✓ std3`).

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

The direct sum of the two-dimensional Fourier restrictions.

**Theorem 1.17 (paired nonzero semisimple).**

Lean statement: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.paired_nonzero_semisimple`

*Proof.* Machine-checked in Lean as `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.paired_nonzero_semisimple` (`✓ std3`). ∎

*Source.* Repository-derived.

*Acknowledgement.* Anna M. Barry, Panayotis G. Kevrekidis (2013). *Few-particle vortex cluster equilibria in Bose–Einstein condensates: existence and stability*. DOI: [10.1088/1751-8113/46/44/445001](https://doi.org/10.1088/1751-8113/46/44/445001). URL: <https://arxiv.org/abs/1306.1545v2>.

*Commentary.*

No two-dimensional off-diagonal restriction has a nontrivial nonzero Jordan chain. This controls generalized eigenspaces, not just polynomial roots.

## References

- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_factored`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.charpoly_folded`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.dipole_charpoly`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_add_one_ne_zero`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_fold`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.ell_shift`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_eq_iff`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_fibre_card`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.fold_le`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.gamma_zero_iff`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.mode_product`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.neutral_denominator_ne_zero`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.pairedOperator`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.paired_nonzero_semisimple`
- Truth anchor: `D5/S3/FluidDynamics/Vortices/AlternatingPolygonModes.square_charpoly`
- Dependency: [D5/S3/FluidDynamics/Vortices/AlternatingPolygonSpectrum](AlternatingPolygonSpectrum.md)
