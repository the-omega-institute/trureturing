import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
import Reg.Support.DependentFamily

/-! Source-owner registration for the native weighted-base threshold theorem. -/

namespace Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation

open _root_.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

universe u

abbrev signature : Signature where
  Params := Type u
  State E := Matroid E × (E → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ E := Matroid E × (E → ℝ)
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature (fun _ _ state => state) (fun e => nomatch e)

noncomputable def rejected : Realization signature.{u} :=
  realize signature (fun _ E state => (state.1, fun _ => 0)) (fun e => nomatch e)

def target {E : Type u} [Finite E] (M : Matroid E) (w : E → ℝ) : Prop :=
  (∃ B, M.IsBase B ∧
      ∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C) ∧
    ∀ B, M.IsBase B →
      ((∀ C, M.IsBase C → baseWeight w B ≤ baseWeight w C) ↔
        ∀ t : ℝ,
          (B ∩ lowerWeightSet M w t).ncard =
            (M.eRk (lowerWeightSet M w t)).toNat)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [Finite E] (M : Matroid E) (w : E → ℝ),
    (R.readout () E (M, w) = (M, w)) ∧
      target (R.readout () E (M, w)).1 (R.readout () E (M, w)).2

private theorem actual_law : arena.{u}.Law actual := by
  intro E _ M w
  refine ⟨rfl, ?_⟩
  change target M w
  simpa [target] using native_weighted_base_rank_saturation M w

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  letI : Fintype (ULift.{u} Unit) := inferInstance
  let M : Matroid (ULift.{u} Unit) := Matroid.emptyOn _
  let w : ULift.{u} Unit → ℝ := fun _ => 1
  have he := h M w
  have hw := congrArg (fun p => p.2 (0 : ULift.{u} Unit)) he.1
  norm_num [rejected, realize, w] at hw

noncomputable def source_registration : Registration arena.{u}
    (type_of% @native_weighted_base_rank_saturation.{u}) where
  actual := actual
  bridge := by
    constructor
    · intro h E _ M w
      change ((M, w) = (M, w)) ∧ target M w
      exact ⟨rfl, by simpa [target] using h M w⟩
    · intro h E _ M w
      have hh := (h M w).2
      change target M w at hh
      simpa [target] using hh
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨ULift.{u} Unit, (Matroid.emptyOn _, fun _ => 0),
      (Matroid.emptyOn _, fun _ => 1), ?_⟩
    intro h
    have hw := congrArg (fun p => p.2 (0 : ULift.{u} Unit)) h
    simpa [actual, realize] using hw

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_weighted_base_rank_saturation.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation.unit
  realizationName := `Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end Reg.D5.S3.Combinatorics.Matroids.NativeWeightedBaseRankSaturation
