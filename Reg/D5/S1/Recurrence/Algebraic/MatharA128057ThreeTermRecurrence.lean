import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence
import Reg.Support.DependentFamily
import Mathlib.Tactic.FinCases

/-! The entire normalized-root and inverse specification accompanies three coefficient observations. -/

namespace Reg.D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence

open _root_.D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature where
  Params := PowerSeries ℚ
  State _ := ℕ
  Role := Fin 3
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ S n => coeff n ((1 + X) * S⁻¹)) (fun e => nomatch e)

def changed (i : Fin 3) : Realization signature :=
  realize signature (fun j S n =>
    if j = i then coeff n ((1 + X) * S⁻¹) + 1 else coeff n ((1 + X) * S⁻¹))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∃! S : PowerSeries ℚ, constantCoeff S = 1 ∧ S ^ 2 = 1 + 4 * X ^ 2) ∧
    ∀ S : PowerSeries ℚ, constantCoeff S = 1 → S ^ 2 = 1 + 4 * X ^ 2 →
      constantCoeff S⁻¹ = 1 ∧ S * S⁻¹ = 1 ∧ S⁻¹ * S = 1 ∧
      let A := (1 + X) * S⁻¹
      let a : ℕ → ℚ := fun n => coeff n A
      ∀ n : ℕ, 2 ≤ n →
        (n : ℚ) * (5 * n - 9) * R.readout 0 S n + 4 * R.readout 1 S (n - 1) +
          4 * (5 * (n : ℚ) - 4) * (n - 2) * R.readout 2 S (n - 2) = 0

private theorem changed_law (i : Fin 3) : ¬ arena.Law (changed i) := by
  intro h
  obtain ⟨S, hS, _⟩ := result.1
  have hh := (h.2 S hS.1 hS.2).2.2.2 3 (by decide)
  have ha := (result.2 S hS.1 hS.2).2.2.2 3 (by decide)
  fin_cases i <;> simp +decide [changed, realize] at hh <;>
    norm_num at ha <;> linarith

def family : Registration arena (type_of% result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, changed 0, changed_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨changed i, ?_, ?_, changed_law i⟩
      · intro j hj
        funext S n
        simp [changed, actual, realize, hj]
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 2, ?_⟩
    change coeff 0 ((1 + X) * (1 : PowerSeries ℚ)⁻¹) ≠
      coeff 2 ((1 + X) * (1 : PowerSeries ℚ)⁻¹)
    norm_num [coeff_X]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    result (Realization signature) Type Unit where
  unitName := `Reg.D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence.auditUnit
  realizationName := `Reg.D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ S n => coeff n ((1 + X) * S⁻¹)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["arg", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
        stateBinder := 0, functionOperand := false
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false
        stateOperand := some #["arg"], booleanPredicate := false },
      { path := #["arg", "body", "body", "body", "arg", "arg", "arg", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
        stateBinder := 0, functionOperand := false
        stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end
end Reg.D5.S1.Recurrence.Algebraic.MatharA128057ThreeTermRecurrence
