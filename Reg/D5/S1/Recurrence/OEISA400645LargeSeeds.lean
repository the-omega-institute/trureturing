import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.OEISA400645LargeSeeds
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.OEISA400645LargeSeeds

open _root_.D5.S1.Recurrence.OEISA400645 (radicand limitingRatio)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Asymptotics Filter

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => (ℕ → ℝ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f g => f =O[atTop] g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the bounded absolute error. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    ∀ a : ℕ → ℕ, a 1 ≤ a 2 → a 2 ≤ a 3 → a 3 ≤ a 4 →
      (∀ n, 4 ≤ n → (a (n + 1) : ℤ) = round (Real.sqrt (radicand a n : ℝ))) →
      (∀ n, 4 ≤ n → 0 ≤ radicand a n) ∧
        (a 1 = a 4 ∧ a 4 ≤ 1 → ∀ n, 1 ≤ n → a n = a 1) ∧
        ((∃ c : ℝ, 0 < c ∧
            Q.readout () () (fun n => (a n : ℝ) - c * limitingRatio ^ n) (fun _ => (1 : ℝ)) ∧
            (fun n => (a (n + 1) : ℝ) / a n - limitingRatio) =O[atTop]
              (fun n => (limitingRatio ^ n)⁻¹)) ↔
          ¬ (a 1 = a 4 ∧ a 4 ≤ 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨⟨a, ha⟩, -⟩ := _root_.D5.S1.Recurrence.OEISA400645.result
  obtain ⟨h1, h2, h3, h4, hrec⟩ := ha
  have h := (hlaw a (by omega) (by omega) (by omega) (fun n hn => (hrec n hn).2)).2.2
  obtain ⟨_, _, hF, _⟩ := h.mpr (by omega)
  exact hF

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), fun _ => 0, fun _ => 1, ?_⟩
  intro h
  have hh := congrFun h (fun _ => 0)
  simp only [actual, realize] at hh
  have h0 : (fun _ : ℕ => (0 : ℝ)) =O[atTop] (fun _ : ℕ => (0 : ℝ)) := isBigO_zero _ _
  rw [hh, isBigO_zero_right_iff] at h0
  obtain ⟨n, hn⟩ := eventually_atTop.mp h0
  exact one_ne_zero (hn n le_rfl)

def family : Registration arena
    (type_of% (@_root_.D5.S1.Recurrence.OEISA400645LargeSeeds.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S1.Recurrence.OEISA400645LargeSeeds.result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.OEISA400645LargeSeeds.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.OEISA400645LargeSeeds.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.OEISA400645LargeSeeds.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f =O[atTop] g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Recurrence.OEISA400645LargeSeeds
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "body",
        "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S1.Recurrence.OEISA400645LargeSeeds
