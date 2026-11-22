import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
import Reg.Support.DependentFamily

/-! The central lattice term of the global error budget varies with the mesh size. -/

namespace Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh

open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
open _root_.D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory
open scoped BigOperators

noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ r => 16 * r ^ (-(1 / 4 : ℝ))) (fun a => nomatch a)

private noncomputable def rejectedValue : ℝ :=
  -(64 * (1 / 4 : ℝ) ^ (3 / 2 : ℝ) + 112 * (1 / 4 : ℝ) ^ (1 / 4 : ℝ) +
    (32 * (1 / 4 : ℝ) ^ (-(17 / 4 : ℝ))) / 4 + 8 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) + 1)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => rejectedValue) (fun a => nomatch a)

abbrev arena : Arena where
  signature := signature
  Law Rmdl := ∀ {β : ℝ}, 0 ≤ β → β ≤ 3 / 4 → ∀ n K M : ℕ,
    0 < n → 0 < K → 2 * n < M → (M : ℝ) / n ≤ ((K : ℝ) / n)⁻¹ →
    let δ := (K : ℝ) / n
    let R := ((M - 1 : ℕ) : ℝ) / n
    Summable (fun i : ℕ => |sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)|) ∧
    IntegrableOn (sample β 0) (Set.Ioi 0) ∧
    |(∫ t in Set.Ioi (0 : ℝ), sample β 0 t) -
        (∑' i : ℕ, sample β (2 / (n : ℝ)) (((i + 1 : ℕ) : ℝ) / n)) / n| ≤
      64 * δ ^ (3 / 2 : ℝ) + 112 * δ ^ (1 / 4 : ℝ) + Rmdl.readout () () (n : ℝ) +
        (32 * δ ^ (-(17 / 4 : ℝ))) / n + 8 * R ^ (-(1 / 2 : ℝ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  have h := (law (β := 0) le_rfl (by norm_num) 4 1 9
    (by decide) (by decide) (by decide) (by norm_num)).2.2
  have h' : |(∫ t in Set.Ioi (0 : ℝ), sample 0 0 t) -
      (∑' i : ℕ, sample 0 (2 / ((4 : ℕ) : ℝ)) ((i + 1 : ℕ) / ((4 : ℕ) : ℝ))) /
        ((4 : ℕ) : ℝ)| ≤
    64 * (1 / 4 : ℝ) ^ (3 / 2 : ℝ) + 112 * (1 / 4 : ℝ) ^ (1 / 4 : ℝ) +
      rejectedValue + (32 * (1 / 4 : ℝ) ^ (-(17 / 4 : ℝ))) / 4 +
      8 * (2 : ℝ) ^ (-(1 / 2 : ℝ)) := by
    have EqR : (((9 - 1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ)) = 2 := by norm_num
    dsimp only at h
    change _ ≤ 64 * ((↑(1 : ℕ) : ℝ) / ↑(4 : ℕ)) ^ (3 / 2 : ℝ) +
      112 * ((↑(1 : ℕ) : ℝ) / ↑(4 : ℕ)) ^ (1 / 4 : ℝ) + rejectedValue +
      (32 * ((↑(1 : ℕ) : ℝ) / ↑(4 : ℕ)) ^ (-(17 / 4 : ℝ))) / ↑(4 : ℕ) +
      8 * (((9 - 1 : ℕ) : ℝ) / ↑(4 : ℕ)) ^ (-(1 / 2 : ℝ)) at h
    rw [EqR] at h
    simpa only [Nat.cast_one, Nat.cast_ofNat] using h
  have hb := (abs_nonneg _).trans h'
  dsimp [rejectedValue] at hb
  linarith only [hb]

def family : Registration arena (type_of% @global_mesh_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@global_mesh_error, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j hj => (hj (@Subsingleton.elim Unit _ j i)).elim,
    rfl, rejected_law⟩, fun a => nomatch a⟩
  dependence := by
    intro i
    refine ⟨(), 4, 8, ?_⟩
    change (16 : ℝ) * (4 : ℝ) ^ (-(1 / 4 : ℝ)) ≠
      16 * (8 : ℝ) ^ (-(1 / 4 : ℝ))
    exact (mul_lt_mul_of_pos_left
      (Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num))
      (by norm_num : (0 : ℝ) < 16)).ne'

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@global_mesh_error) (Realization signature) (Type) Unit where
  unitName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh.unit
  realizationName := `Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ r => 16 * r ^ (-(1 / 4 : ℝ)))
    (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "arg", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.Patterns.Separable.OccupiedMellinGlobalMesh
