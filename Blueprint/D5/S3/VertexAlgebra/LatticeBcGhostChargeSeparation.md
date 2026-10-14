# LatticeBcGhostChargeSeparation

## Abstract

Original-Q quartet prerequisites: LatticeBcGhostChargeSeparation

These are retained proofs from the accepted original-Q quartet source, not new mathematics produced by changing module names. The namespace remains D5.S3.VertexAlgebra.OriginalQQuartetSource. StatementSource.WithoutFormula renders declaration handles bound to the canonical scoped report, not displayed formula bodies; the source assumptions, proof bodies and noncomputable section are unchanged.

D is the original LatticeGeneratingFieldLocality.LatticeData, with arbitrary natural rank, integral symmetric Gram matrix and even diagonal. Carrier D is the finite-support sum over every integral charge of the actual complex oscillator polynomial space. State D is Carrier D tensor Fock Complex. The existing Fock, b, c, M, G, Q and J are used without replacement. No positivity, positive-energy cutoff, restricted charge spectrum, surrogate differential or assumed locality, Jacobi, spectrum or nilpotence is added. Isotropic and negative-norm charge sectors are not removed.

This retention establishes quartet prerequisites and per-mode identities, not a total K contraction, the cohomology of the full original Q, a physical no-ghost theorem, a string construction or AdS/CFT. Full-Q nilpotence is a separately previously accepted result outside this scoped graph, not imported or certified here. Wherever that separate route is invoked, both Gram-inverse equations and the rank-26 condition remain required; these are not premises of statements that do not use that route. The larger VOA/CFT/string/AdS goal remains active and open.

Native information-escape registration is unfinished under issue #15040. Mathematical kernel checking and scoped report binding do not imply declared_validated registration, frozen admission, CI, remote acceptance or independent canonical source/render approval.

oscillatorNormalSummand explicitly removes the summands with either current mode zero. The remaining statewise finite sum defines oscillatorSugawaraMode on the original charge carrier. The support argument is actual, not an assumed energy cutoff or formal divergent series.

For m nonzero and an actual charge alpha, sugawaraMode(H,m)(single(alpha,P))=a_complexCharge(alpha)(m)(single(alpha,P))+oscillatorSugawaraMode(H,m)(single(alpha,P)). The finite normal-order sum separates its two zero-current contributions, contracts each with H, and retains the oscillator remainder.

Both H*gramComplex(D)=1 and gramComplex(D)*H=1 are exact premises of inverseGram_charge_contractions and the charged separation theorem. No positivity, nonzero charge, isotropy, rank-26 assumption or m=0 separation is asserted. original_tensor_sugawara_charged_separation transports this exact result to M on the original State and is a consumed transport helper.

oscillatorNormalSummand_finite, normalSummand_finsum_split and original_sugawara_charged_separation are consumed bind-only helpers: support transport, finite-sum normalization and substitution of the existing inverse-Gram contractions respectively. ChargeSeparation earns no standalone new-content or module escape credit. First-admission and module escape remain unverified pending actual broader integration; the original proofs and hypotheses are retained unchanged.

**Definition 1.1 (oscillatorNormalSummand).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Theorem 1.2 (oscillatorNormalSummand finite).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand_finite`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand_finite` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only support-subset helper using the existing normalSummand_finite result and definition normalization, not standalone new mathematical content. Retained canonical consumers: D5.S3.VertexAlgebra.OriginalQQuartetSource.oscillatorSugawaraMode and D5.S3.VertexAlgebra.OriginalQQuartetSource.normalSummand_finsum_split.

**Definition 1.3 (oscillatorSugawaraMode).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorSugawaraMode`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorSugawaraMode` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Theorem 1.4 (chargeScalar expansion).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.chargeScalar_expansion`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.chargeScalar_expansion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: chosenH_original_chargeQuadratic, inverseGram_charge_contractions.

**Theorem 1.5 (inverseGram charge contractions).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.inverseGram_charge_contractions`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.inverseGram_charge_contractions` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: chosenH_original_chargeQuadratic, original_sugawara_charged_separation.

**Theorem 1.6 (normalSummand zero mode split).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_zero_mode_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_zero_mode_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: normalSummand_finsum_split.

**Theorem 1.7 (normalSummand finsum split).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_finsum_split`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_finsum_split` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only finite-sum splitting and normalization helper after normalSummand_zero_mode_split, not standalone new mathematical content. Retained canonical consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_sugawara_charged_separation.

**Theorem 1.8 (original sugawara charged separation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_sugawara_charged_separation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_sugawara_charged_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed bind-only helper substituting inverseGram_charge_contractions and normalSummand_finsum_split, then normalizing sums and scalars, not standalone new mathematical content. Both Gram-inverse equations and the nonzero-mode hypothesis are unchanged. Retained canonical consumer: D5.S3.VertexAlgebra.OriginalQQuartetSource.original_tensor_sugawara_charged_separation.

**Theorem 1.9 (original tensor sugawara charged separation).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_tensor_sugawara_charged_separation`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_tensor_sugawara_charged_separation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_adapted_M_nonzero.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.chargeScalar_expansion`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.inverseGram_charge_contractions`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_finsum_split`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.normalSummand_zero_mode_split`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_sugawara_charged_separation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.original_tensor_sugawara_charged_separation`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorNormalSummand_finite`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation.oscillatorSugawaraMode`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostQuartetCoordinates](LatticeBcGhostQuartetCoordinates.md)
- Dependency: [D5/S3/VertexAlgebra/LatticeSugawaraConformal](LatticeSugawaraConformal.md)
