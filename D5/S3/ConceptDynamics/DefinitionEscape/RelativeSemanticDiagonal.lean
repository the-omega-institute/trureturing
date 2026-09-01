/- GID: D5/S3/ConceptDynamics/DefinitionEscape/RelativeSemanticDiagonal
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/DefinitionEscape/RelativeSemanticDiagonal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complete decoder catalogs yield diagonal targets outside the latent closure. -/

import D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois
import D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality

/- Library-search audit trail (2026-08-24):
   * `Lawvere.QualitativeEscape` proves ordinary catalog escape under
     self-application.
   * `BlindKernelObstruction` proves that a nonempty blind residual obstructs
     every finite or pointwise sublanguage.
   * `DefinitionKernelGalois` identifies semantic closure with factorization
     through a full language joint readout.
   * Repository search found no theorem showing that a complete decoder catalog
     produces a diagonal target whose defect is a nonempty language blind
     residual. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.DefinitionEscape.RelativeSemanticDiagonal

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.TargetRisk.RefinementRiskCostTradeoff
open D5.S3.ConceptDynamics.Restoration.TargetRecoveryCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.LatentAdequacyCriterion
open D5.S3.ConceptDynamics.DefinitionEscape.QuestionAlgebraDuality
open D5.S3.ConceptDynamics.DefinitionEscape.BlindKernelObstruction
open D5.S3.ConceptDynamics.DefinitionEscape.DefinitionKernelGalois

/-- A latent-relative diagonal evaluates the decoder listed at an address on
that address's latent coordinate and then applies a fixed-point-free twist. -/
def relativeSemanticDiagonal
    {Address Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output) :
    Concept Address Output :=
  fun address => twist (decoderCatalog address (latent address))

/-- The latent-relative diagonal differs from each listed decoded target at its
own address. -/
theorem relative_semantic_diagonal_ne_listed_decode
    {Address Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (address : Address) :
    relativeSemanticDiagonal twist latent decoderCatalog ≠
      decoderCatalog address ∘ latent := by
  intro equality
  apply fixedPointFree (decoderCatalog address (latent address))
  have pointwise := congrFun equality address
  unfold relativeSemanticDiagonal Function.comp at pointwise
  exact pointwise

/-- Therefore the diagonal target lies outside the entire listed decoded
catalog. -/
theorem relative_semantic_diagonal_not_mem_decoded_catalog
    {Address Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output) :
    relativeSemanticDiagonal twist latent decoderCatalog ∉
      Set.range (fun address => decoderCatalog address ∘ latent) := by
  rintro ⟨address, captured⟩
  exact relative_semantic_diagonal_ne_listed_decode
    twist latent decoderCatalog fixedPointFree address captured.symm

/-- If the catalog lists every decoder on the fixed latent coordinate, its
diagonal target cannot factor through that latent. -/
theorem relative_semantic_diagonal_target_inadequate_of_surjective
    {Address Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept Address Coordinate)
    (decoderCatalog : Address → Coordinate → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    ¬TargetAdequate latent
      (relativeSemanticDiagonal twist latent decoderCatalog) := by
  rintro ⟨decoder, factors⟩
  rcases complete decoder with ⟨address, catalogAtAddress⟩
  apply relative_semantic_diagonal_ne_listed_decode
    twist latent decoderCatalog fixedPointFree address
  rw [catalogAtAddress]
  exact factors

/-- The canonical semantic diagonal uses decoder space itself as its world. -/
def semanticDiagonal
    {Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept (Coordinate → Output) Coordinate) :
    Concept (Coordinate → Output) Output :=
  fun decoder => twist (decoder (latent decoder))

/-- No fixed latent on decoder space can be adequate for its own canonical
semantic diagonal. -/
theorem semantic_diagonal_target_inadequate
    {Coordinate Output : Type*}
    (twist : Output → Output)
    (latent : Concept (Coordinate → Output) Coordinate)
    (fixedPointFree : ∀ output, twist output ≠ output) :
    ¬TargetAdequate latent (semanticDiagonal twist latent) := by
  rintro ⟨decoder, factors⟩
  apply fixedPointFree (decoder (latent decoder))
  have pointwise := congrFun factors decoder
  unfold semanticDiagonal Function.comp at pointwise
  exact pointwise

/-- Every fixed latent has a concrete target outside its adequate-target
class. -/
theorem no_fixed_latent_is_universally_adequate
    {Coordinate Output : Type*}
    (twist : Output → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (latent : Concept (Coordinate → Output) Coordinate) :
    ∃ target : Concept (Coordinate → Output) Output,
      ¬TargetAdequate latent target :=
  ⟨semanticDiagonal twist latent,
    semantic_diagonal_target_inadequate twist latent fixedPointFree⟩

/-- Boolean negation gives a canonical question absent from the question
algebra of every fixed latent over Boolean decoders. -/
theorem boolean_semantic_diagonal_not_answerable
    {Coordinate : Type*}
    (latent : Concept (Coordinate → Bool) Coordinate) :
    semanticDiagonal (fun value : Bool => !value) latent ∉
      AnswerableQuestions latent := by
  change ¬TargetAdequate latent
    (semanticDiagonal (fun value : Bool => !value) latent)
  exact semantic_diagonal_target_inadequate
    (fun value : Bool => !value) latent (by decide)

/-- A complete decoder catalog over the full current-language readout produces
a target with a nonempty blind residual. The diagonal therefore witnesses a
representation boundary, rather than merely absence from one finite list. -/
theorem complete_catalog_diagonal_blindResidual_nonempty
    {X Current InputOutput Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (twist : Output → Output)
    (decoderCatalog :
      X → (Current × (Gamma → InputOutput)) → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    (blindResidual Gamma current
      (relativeSemanticDiagonal twist
        (languageExtension current
          (fun definition : Gamma => definition.1))
        decoderCatalog)).Nonempty := by
  let fullReadout :=
    languageExtension current
      (fun definition : Gamma => definition.1)
  let diagonalTarget :=
    relativeSemanticDiagonal twist fullReadout decoderCatalog
  have inadequate : ¬TargetAdequate fullReadout diagonalTarget := by
    exact relative_semantic_diagonal_target_inadequate_of_surjective
      twist fullReadout decoderCatalog fixedPointFree complete
  have fullDefect :
      (defectRelation fullReadout diagonalTarget).Nonempty := by
    apply (target_recovery_criterion fullReadout diagonalTarget).2.2.2.mp
    simpa only [TargetAdequate, Refines] using inadequate
  change
    (blindResidual Gamma current
      (relativeSemanticDiagonal twist
        (languageExtension current
          (fun definition : Gamma => definition.1))
        decoderCatalog)).Nonempty
  rw [← languageExtension_defect_eq_blindResidual]
  exact fullDefect

/-- The same diagonal target cannot be recovered from any finite selection of
the old definition language. -/
theorem complete_catalog_diagonal_no_finite_selection
    {X Current InputOutput Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (twist : Output → Output)
    (decoderCatalog :
      X → (Current × (Gamma → InputOutput)) → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog) :
    ¬finiteSelectionSufficient Gamma current
      (relativeSemanticDiagonal twist
        (languageExtension current
          (fun definition : Gamma => definition.1))
        decoderCatalog) := by
  have blind :=
    complete_catalog_diagonal_blindResidual_nonempty
      Gamma current twist decoderCatalog fixedPointFree complete
  exact
    ((blind_kernel_obstruction Gamma current
      (relativeSemanticDiagonal twist
        (languageExtension current
          (fun definition : Gamma => definition.1))
        decoderCatalog)).2 blind).2.2

/-- Even an arbitrary pointwise subfamily of the old language cannot recover
the complete-catalog diagonal target. -/
theorem complete_catalog_diagonal_obstructs_subfamily
    {X Current InputOutput Output : Type*} [Nonempty X]
    (Gamma : Set (Concept X InputOutput))
    (current : Concept X Current)
    (twist : Output → Output)
    (decoderCatalog :
      X → (Current × (Gamma → InputOutput)) → Output)
    (fixedPointFree : ∀ output, twist output ≠ output)
    (complete : Function.Surjective decoderCatalog)
    (Delta : Set Gamma) :
    ¬∃ recover : (Current × (Delta → InputOutput)) → Output,
      relativeSemanticDiagonal twist
          (languageExtension current
            (fun definition : Gamma => definition.1))
          decoderCatalog =
        recover ∘
          languageExtension current
            (fun definition : Delta => definition.1.1) := by
  have blind :=
    complete_catalog_diagonal_blindResidual_nonempty
      Gamma current twist decoderCatalog fixedPointFree complete
  exact
    ((blind_kernel_obstruction Gamma current
      (relativeSemanticDiagonal twist
        (languageExtension current
          (fun definition : Gamma => definition.1))
        decoderCatalog)).2 blind).2.1 Delta

/-- After effective-range normalization, the Boolean semantic diagonal creates
an operationally new Boolean question with no unused-coordinate hypothesis. -/
theorem boolean_semantic_diagonal_creates_effective_question
    {Coordinate : Type*}
    (latent : Concept (Coordinate → Bool) Coordinate) :
    ∃ question : (Coordinate → Bool) → Bool,
      (∃! answer : EffectiveCoordinate
          (conceptJoin latent
            (semanticDiagonal (fun value : Bool => !value) latent)) → Bool,
        question = answer ∘ effectiveReadout
          (conceptJoin latent
            (semanticDiagonal (fun value : Bool => !value) latent))) ∧
      ¬∃ answer : EffectiveCoordinate latent → Bool,
        question = answer ∘ effectiveReadout latent := by
  apply (target_inadequate_iff_effective_new_question
    latent (semanticDiagonal (fun value : Bool => !value) latent)).1
  exact semantic_diagonal_target_inadequate
    (fun value : Bool => !value) latent (by decide)

#print axioms relative_semantic_diagonal_target_inadequate_of_surjective
#print axioms complete_catalog_diagonal_blindResidual_nonempty
#print axioms complete_catalog_diagonal_no_finite_selection
#print axioms complete_catalog_diagonal_obstructs_subfamily

end D5.S3.ConceptDynamics.DefinitionEscape.RelativeSemanticDiagonal
