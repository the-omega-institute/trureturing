# LatticeBcGhostChosenCharge

## Abstract

Original-Q quartet prerequisites: LatticeBcGhostChosenCharge

These are retained proofs from the accepted original-Q quartet source, not new mathematics produced by changing module names. The namespace remains D5.S3.VertexAlgebra.OriginalQQuartetSource. StatementSource.WithoutFormula renders declaration handles bound to the canonical scoped report, not displayed formula bodies; the source assumptions, proof bodies and noncomputable section are unchanged.

D is the original LatticeGeneratingFieldLocality.LatticeData, with arbitrary natural rank, integral symmetric Gram matrix and even diagonal. Carrier D is the finite-support sum over every integral charge of the actual complex oscillator polynomial space. State D is Carrier D tensor Fock Complex. The existing Fock, b, c, M, G, Q and J are used without replacement. No positivity, positive-energy cutoff, restricted charge spectrum, surrogate differential or assumed locality, Jacobi, spectrum or nilpotence is added. Isotropic and negative-norm charge sectors are not removed.

This retention establishes quartet prerequisites and per-mode identities, not a total K contraction, the cohomology of the full original Q, a physical no-ghost theorem, a string construction or AdS/CFT. Full-Q nilpotence is a separately previously accepted result outside this scoped graph, not imported or certified here. Wherever that separate route is invoked, both Gram-inverse equations and the rank-26 condition remain required; these are not premises of statements that do not use that route. The larger VOA/CFT/string/AdS goal remains active and open.

Native information-escape registration is unfinished under issue #15040. Mathematical kernel checking and scoped report binding do not imply declared_validated registration, frozen admission, CI, remote acceptance or independent canonical source/render approval.

For the actual integral charge alpha write a=complexCharge(alpha), p=<k,a>_G, h=(1/2)<a,a>_G and q=h/p. The chosen construction requires k null and p nonzero; it does not require h positive or nonzero. adaptedPartner l=p^(-1)a-h*p^(-2)k has <l,k>_G=1, <l,l>_G=0 and a=p*l+q*k. These are relations in the original Gram form, not a new matter or ghost model.

chosenH_original_chargeQuadratic identifies this h with the original chargeQuadratic using both Gram-inverse equations. For every nonzero mode the original M separates as p O_l(m)+q O_k(m)+the actual oscillator Sugawara remainder. Accordingly A_m-p d_m=q C(-m)O_k(m)+C(-m)(oscillatorSugawaraMode(H,m)(single(alpha,P)) tensor ghost)+(1/2)N_m on the original charged tensor.

original_Q_corrected_finsum proves the corresponding statewise finite sum for Q-Delta. Its zero-mode summand is exactly A(H,0), not discarded or replaced. Every nonzero summand is the preceding q-current, oscillator and N term. Both Gram inverse hypotheses, the null condition and p nonzero remain in its statement.

original_chosen_quartet_algebra only specializes the consumed quartet package after proving the adapted-partner relations. It has an actual accepted proof-path consumer in the preserved transient original_Q_polarized_coordinate_consumer, but no retained canonical consumer in these six modules. It earns no new mathematics credit; the retained original source remains protected and the final unconsumed conjunction itself is omitted from canonical delivery.

**Definition 1.1 (complexCharge).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.complexCharge`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.complexCharge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.2 (chosenP).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenP`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenP` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.3 (chosenH).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.4 (chosenQ).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenQ`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Definition 1.5 (adaptedPartner).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner`

*Formalization.* `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Retained original construction on the unchanged carrier.

**Theorem 1.6 (gramPair smul left).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: adaptedPartner_relations, gramPair_smul_right.

**Theorem 1.7 (gramPair smul right).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: adaptedPartner_relations, original_nonzero_charge_adapted_frame_exists.

**Theorem 1.8 (gramPair sub left).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_left`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_left` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: adaptedPartner_relations, gramPair_sub_right.

**Theorem 1.9 (gramPair sub right).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_right`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_right` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: adaptedPartner_relations.

**Theorem 1.10 (adaptedPartner relations).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner_relations`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner_relations` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: actualK_original, originalFixedReduced, original_Q_polarized_coordinate_consumer, original_adapted_M_nonzero, original_chosen_quartet_algebra, original_nonzero_charge_adapted_frame_exists.

**Theorem 1.11 (chosenH original chargeQuadratic).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH_original_chargeQuadratic`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH_original_chargeQuadratic` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: chosenH_signed_norm, original_Q_polarized_coordinate_consumer.

**Theorem 1.12 (O direction combination).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.O_direction_combination`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.O_direction_combination` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_adapted_M_nonzero.

**Theorem 1.13 (original adapted M nonzero).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_adapted_M_nonzero`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_adapted_M_nonzero` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_A_leading_piece.

**Theorem 1.14 (original A leading piece).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_A_leading_piece`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_A_leading_piece` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_Q_corrected_finsum, raisingOneAtom_nonzero_native.

**Theorem 1.15 (original Q corrected finsum).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_Q_corrected_finsum`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_Q_corrected_finsum` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Retained substantive original proof; canonical naming supplies no additional mathematical novelty.

**Theorem 1.16 (original chosen quartet algebra).**

Lean statement: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_chosen_quartet_algebra`

*Proof.* Machine-checked in Lean as `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_chosen_quartet_algebra` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Consumed normalization, transport or packaging helper, not a separately new mathematical result. Accepted source consumers: original_Q_polarized_coordinate_consumer.

## References

- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.O_direction_combination`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.adaptedPartner_relations`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenH_original_chargeQuadratic`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenP`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.chosenQ`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.complexCharge`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_left`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_smul_right`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_left`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.gramPair_sub_right`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_A_leading_piece`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_Q_corrected_finsum`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_adapted_M_nonzero`
- Truth anchor: `D5/S3/VertexAlgebra/LatticeBcGhostChosenCharge.original_chosen_quartet_algebra`
- Dependency: [D5/S3/VertexAlgebra/LatticeBcGhostChargeSeparation](LatticeBcGhostChargeSeparation.md)
