/- GID: D5/S3/VertexAlgebra/LatticeBcGhostCohomologyLocality
   generality: I
   mirror-B: none(waiver:evidence-not-specified-by-formal-manifest)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Preserved full-carrier quotient super-locality proof obligation for the original BRST charge. -/

import D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields

open LatticeGeneratingFieldLocality
open LatticeBcGhostBrstCharge (State Q)
open LatticeBcGhostNeutralCohomology (OriginalCycles OriginalBoundaries OriginalCohomology)
open LatticeBcGhostCohomologyModes
open scoped VertexOperator

variable (D : LatticeData) (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)

def cycleCommutator (exchange : ℂ) (left right vector : OriginalCycles D H) :
    ℤ → ℤ → OriginalCycles D H :=
  fun first second => cycleMode D H first left (cycleMode D H second right vector) -
    exchange • cycleMode D H second right (cycleMode D H first left vector)

theorem iterated_cycle_val (exchange : ℂ) (left right vector : OriginalCycles D H)
    (order : ℕ) (first second : ℤ) :
    (SuperFieldProducts.delta^[order] (cycleCommutator D H exchange left right vector)
      first second).val =
    (SuperFieldProducts.delta^[order]
      (SuperFieldProducts.superCommutator exchange
        (LatticeBcGhostTensorStateField.stateField D left.val)
        (LatticeBcGhostTensorStateField.stateField D right.val)) first second) vector.val := by
  induction order generalizing first second with
  | zero => rfl
  | succ order inductionHypothesis =>
      simp only [Function.iterate_succ_apply', SuperFieldProducts.delta,
        Submodule.coe_sub, LinearMap.sub_apply]
      rw [inductionHypothesis, inductionHypothesis]

theorem iterated_quotient_mk (exchange : ℂ) (left right vector : OriginalCycles D H)
    (order : ℕ) (first second : ℤ) :
    (SuperFieldProducts.delta^[order]
      (SuperFieldProducts.superCommutator exchange
        (field D H ((OriginalBoundaries D H).mkQ left))
        (field D H ((OriginalBoundaries D H).mkQ right))) first second)
      ((OriginalBoundaries D H).mkQ vector) =
    (OriginalBoundaries D H).mkQ
      (SuperFieldProducts.delta^[order] (cycleCommutator D H exchange left right vector) first second) := by
  induction order generalizing first second with
  | zero =>
      simp only [Function.iterate_zero_apply, SuperFieldProducts.superCommutator,
        field_mode, Module.End.mul_apply, LinearMap.sub_apply, LinearMap.smul_apply,
        cycleCommutator, product_mk, map_sub, map_smul]
  | succ order inductionHypothesis =>
      simp only [Function.iterate_succ_apply', SuperFieldProducts.delta, LinearMap.sub_apply]
      rw [inductionHypothesis, inductionHypothesis, map_sub]

theorem projected_superLocal (leftParity rightParity : ℕ) (left right : OriginalCycles D H) :
    SuperFieldProducts.SuperLocal leftParity rightParity
      (field D H ((OriginalBoundaries D H).mkQ (cycleParity D H leftParity left)))
      (field D H ((OriginalBoundaries D H).mkQ (cycleParity D H rightParity right))) := by
  obtain ⟨order, killed⟩ := LatticeBcGhostTensorLocality.homogeneous_superFieldLocal D
    leftParity rightParity (LatticeBcGhostTensorStateField.parityPart leftParity left.val)
      (LatticeBcGhostTensorStateField.parityPart rightParity right.val)
      (LatticeBcGhostTensorStateField.parityPart_mem leftParity left.val)
      (LatticeBcGhostTensorStateField.parityPart_mem rightParity right.val)
  refine ⟨order, ?_⟩
  funext first second
  apply LinearMap.ext
  intro vector
  obtain ⟨representative, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective vector
  rw [iterated_quotient_mk]
  have zero : SuperFieldProducts.delta^[order]
      (cycleCommutator D H (SuperFieldProducts.koszul leftParity rightParity)
        (cycleParity D H leftParity left) (cycleParity D H rightParity right) representative)
      first second = 0 := by
    apply Subtype.ext
    rw [iterated_cycle_val]
    change (SuperFieldProducts.delta^[order]
      (SuperFieldProducts.superCommutator (SuperFieldProducts.koszul leftParity rightParity)
        (LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.parityPart leftParity left.val))
        (LatticeBcGhostTensorStateField.stateField D
          (LatticeBcGhostTensorStateField.parityPart rightParity right.val))) first second)
      representative.val = 0
    have evaluated := congrArg (fun distribution : ℤ → ℤ → Module.End ℂ (State D) =>
      (distribution first second) representative.val) killed
    exact evaluated
  rw [zero, map_zero]
  rfl

theorem superLocal (leftParity rightParity : ℕ) (left right : OriginalCohomology D H)
    (leftFixed : parity D H leftParity left = left)
    (rightFixed : parity D H rightParity right = right) :
    SuperFieldProducts.SuperLocal leftParity rightParity (field D H left) (field D H right) := by
  obtain ⟨firstState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective left
  obtain ⟨secondState, rfl⟩ := (OriginalBoundaries D H).mkQ_surjective right
  rw [← leftFixed, ← rightFixed, parity_mk, parity_mk]
  exact projected_superLocal D H leftParity rightParity firstState secondState

#print axioms superLocal

end D5.S3.VertexAlgebra.LatticeBcGhostCohomologyFields
