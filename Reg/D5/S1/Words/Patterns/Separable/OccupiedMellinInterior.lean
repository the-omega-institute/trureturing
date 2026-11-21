import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ δ x => (16 * δ ^ (-(17/4:ℝ))) / x) (fun a => nomatch a)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {β δ : ℝ} (n L N : ℕ), 0 < n →
    0 ≤ β → β ≤ 3/4 → 0 < δ → δ ≤ 1 →
    δ ≤ (L : ℝ)/n → (N : ℝ)/n ≤ δ⁻¹ →
    (((L+N : ℕ) : ℝ)/n ≤ 1-δ ∨ 1+δ ≤ (L : ℝ)/n) →
    |(∫ t in ((L:ℝ)/n)..(((L+N:ℕ):ℝ)/n), sample β 0 t) -
        ∑ i ∈ Finset.range N, (1/(n:ℝ)) * sample β (2/(n:ℝ)) (((L+i:ℕ):ℝ)/n)| ≤
      R.readout () δ (n:ℝ)

private theorem rejected_law : ¬arena.Law rejected := by
  intro law
  have hf := law (β := 0) (δ := 1) 1 2 1
    (by decide) (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) (by norm_num) (Or.inr (by norm_num))
  change _ ≤ (-1:ℝ) at hf
  exact not_le_of_gt (lt_of_lt_of_le (by norm_num : (-1:ℝ) < 0) (abs_nonneg _)) hf

def family : Registration arena (type_of% @normalized_lattice_interior_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalized_lattice_interior_error, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨1, 1, 2, ?_⟩
    change (16:ℝ) * 1^(-(17/4:ℝ)) / 1 ≠ (16:ℝ) * 1^(-(17/4:ℝ)) / 2
    norm_num [Real.one_rpow]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@normalized_lattice_interior_error) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ δ x => (16 * δ ^ (-(17/4:ℝ))) / x)
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
