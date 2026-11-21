import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Recurrence.Asymptotic.DominantRootForcing
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S1.Recurrence.Asymptotic.DominantRootForcing

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Polynomial Asymptotics Filter

set_option autoImplicit false
noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => (ℕ → ℝ) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f g => f =O[atTop] g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- The original statement is retained; the readout observes the remainder bound of the first
part. -/
abbrev arena : Arena where
  signature := signature
  Law Q :=
    (∀ (P : ℝ[X]) (R q : ℝ), P.rootMultiplicity R = 1 → 0 < q → q < |R| →
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < q) →
      ∀ b e : ℕ → ℝ,
      (∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j) →
      e =O[atTop] (fun j => q ^ j) →
      ∃ L : ℝ, Q.readout () () (fun j => b j - L * R ^ j) (fun j => q ^ j)) ∧
    (∀ (P : ℝ[X]) (R : ℝ), 1 < |R| → P.rootMultiplicity R = 1 →
      (∀ z : ℂ, (P.map (algebraMap ℝ ℂ)).IsRoot z → z ≠ (R : ℂ) → ‖z‖ < Real.sqrt |R|) →
      ∀ (b e : ℕ → ℝ) (L : ℝ),
      (∀ j, ∑ k ∈ Finset.range (P.natDegree + 1), P.coeff k * b (j + k) = e j) →
      (fun j => b j - L * R ^ j) =o[atTop] (fun j => R ^ j) →
      e =O[atTop] (fun j => Real.sqrt |R| ^ j) →
      (fun j => b j - L * R ^ j) =O[atTop] (fun j => Real.sqrt |R| ^ j))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hlaw
  obtain ⟨_, hL⟩ := hlaw.1 (X - C 2) 2 1 (rootMultiplicity_X_sub_C_self) one_pos (by norm_num)
    (fun z hz hne => by
      exfalso
      apply hne
      have : z - 2 = 0 := by simpa using hz
      rw [show ((2 : ℝ) : ℂ) = 2 by norm_num]
      linear_combination this)
    (fun _ => 0) (fun _ => 0) (fun j => by simp) (isBigO_zero _ _)
  exact hL

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
    (type_of% (@_root_.D5.S1.Recurrence.Asymptotic.DominantRootForcing.result))
    where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S1.Recurrence.Asymptotic.DominantRootForcing.result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S1.Recurrence.Asymptotic.DominantRootForcing.result)
    (Realization signature) Unit Unit where
  unitName := `D5.S1.Recurrence.Asymptotic.DominantRootForcing.result.__information_unit
  realizationName := `Reg.D5.S1.Recurrence.Asymptotic.DominantRootForcing.family
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
    owner := `D5.S1.Recurrence.Asymptotic.DominantRootForcing
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "body", "fn", "fn"]
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
end Reg.D5.S1.Recurrence.Asymptotic.DominantRootForcing
