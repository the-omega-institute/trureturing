import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
import Reg.Support.SingleDependentReadout

/-! Observe each coefficient in the three-column integrality law. -/

set_option linter.style.longLine false

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality

open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped BigOperators symmDiff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 3 → ℝ) (fun _ => Fin 3) (fun _ => ℝ)

private abbrev arena : Arena where
  signature := signature
  Law r := ∀ {n : ℕ} (rows : Finset (Finset (Fin n)))
    (center : Fin 3 ↪ Finset (Fin n)) (entry : Fin 3 → Finset (Fin n) → ℤ)
    (_hsign : ∀ j x, x ∈ rows → (center j ∆ x).card = 1 → entry j x = 1 ∨ entry j x = -1)
    (_hzero : ∀ j x, x ∈ rows → (center j ∆ x).card ≠ 1 → entry j x = 0)
    (_hsize : ∀ j, 4 ≤ (rows.filter (fun x => (center j ∆ x).card = 1)).card)
    (coeff : Fin 3 → ℝ)
    (_hrow : ∀ x ∈ rows, ∃ z : ℤ, (∑ j, (entry j x : ℝ) * coeff j) = 2 * (z : ℝ)),
    ∀ j, ∃ z : ℤ, r.readout () coeff j = 2 * (z : ℝ)

private def actual : Realization signature :=
  realize signature (fun _ coeff j => coeff j) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private def sampleCenter : Fin 3 ↪ Finset (Fin 4) where
  toFun j := {Fin.castLE (by decide : 3 ≤ 4) j}
  inj' := by
    intro j k h
    have h' : Fin.castLE (by decide : 3 ≤ 4) j = Fin.castLE (by decide : 3 ≤ 4) k :=
      Finset.singleton_injective h
    exact Fin.ext (congrArg (Fin.val : Fin 4 → ℕ) h')

private theorem sample_support : ∀ j,
    4 ≤ ((Finset.univ : Finset (Finset (Fin 4))).filter
      (fun x => (sampleCenter j ∆ x).card = 1)).card := by
  decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let rows : Finset (Finset (Fin 4)) := Finset.univ
  let entry (j : Fin 3) (x : Finset (Fin 4)) : ℤ :=
    if (sampleCenter j ∆ x).card = 1 then 1 else 0
  have hsign (j : Fin 3) (x : Finset (Fin 4)) (_hx : x ∈ rows)
      (hnear : (sampleCenter j ∆ x).card = 1) : entry j x = 1 ∨ entry j x = -1 := by
    simp [entry, hnear]
  have hzero (j : Fin 3) (x : Finset (Fin 4)) (_hx : x ∈ rows)
      (hfar : (sampleCenter j ∆ x).card ≠ 1) : entry j x = 0 := by
    simp [entry, hfar]
  have hrow (x : Finset (Fin 4)) (_hx : x ∈ rows) :
      ∃ z : ℤ, (∑ j, (entry j x : ℝ) * (0 : ℝ)) = 2 * (z : ℝ) := ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := h rows sampleCenter entry hsign hzero sample_support (fun _ => 0) hrow 0
  change (1 : ℝ) = 2 * (z : ℝ) at hz
  norm_cast at hz
  omega

def source_registration : Registration arena
    (type_of% @even_coefficients_of_three_cube_columns) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@even_coefficients_of_three_cube_columns, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity _ actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun j => if j = 0 then 0 else 1), 0, 1, ?_⟩
    change (if (0 : Fin 3) = 0 then 0 else 1 : ℝ) ≠ (if (1 : Fin 3) = 0 then 0 else 1)
    simp

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@even_coefficients_of_three_cube_columns) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality.unit
  realizationName :=
    `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ coeff j => coeff j) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
    definition := none
    coordinates := #[7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.HuangThreeColumnIntegrality
