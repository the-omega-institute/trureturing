import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Factorization.BoninShadowMarkoffPositivity
import Reg.Support.SingleDependentReadout

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Factorization.BoninShadowMarkoffPositivity

open _root_.D5.S3.Factorization.BoninShadowMarkoffPositivity

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ → ℚ, ℚ) (fun _ => ℕ) (fun _ => ℚ)

def actual : Realization signature :=
  realize signature (fun _ p n => p.1 n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (t : ℕ → ℚ) (k : ℚ) (hk : 3 ≤ k)
    (h0 : 0 < t 0) (h01 : t 0 < t 1) (h1 : t 1 ≤ k * t 0)
    (ht : ∀ n, t (n + 2) = k * t (n + 1) - t n),
    ∀ n, 0 < R.readout () ⟨t, k⟩ n ∧
      R.readout () ⟨t, k⟩ n < R.readout () ⟨t, k⟩ (n + 1) ∧
      R.readout () ⟨t, k⟩ (n + 1) ≤ k * R.readout () ⟨t, k⟩ n

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let t : ℕ → ℚ := fun n => (3 : ℚ) ^ n
  have hk : (3 : ℚ) ≤ 10 / 3 := by norm_num
  have h0 : 0 < t 0 := by norm_num [t]
  have h01 : t 0 < t 1 := by norm_num [t]
  have h1 : t 1 ≤ (10 / 3 : ℚ) * t 0 := by norm_num [t]
  have ht : ∀ n, t (n + 2) = (10 / 3 : ℚ) * t (n + 1) - t n := by
    intro n
    dsimp [t]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
    ring
  have hh := h t (10 / 3 : ℚ) hk h0 h01 h1 ht
  have hbad := hh 0
  change (0 : ℚ) < 0 ∧ _ at hbad
  linarith [hbad.1]

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨(fun n => (3 : ℚ) ^ n), 10 / 3⟩, 0, 1, ?_⟩
  change (3 : ℚ) ^ 0 ≠ (3 : ℚ) ^ 1
  norm_num

def source_registration : Registration arena (type_of% @real_recurrence_growth) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@real_recurrence_growth, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Factorization.BoninShadowMarkoffPositivity.real_recurrence_growth)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Factorization.BoninShadowMarkoffPositivity.unit
  realizationName := `Reg.D5.S3.Factorization.BoninShadowMarkoffPositivity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => p.1 n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Factorization.BoninShadowMarkoffPositivity
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Factorization.BoninShadowMarkoffPositivity
