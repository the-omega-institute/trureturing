import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Zeros.Jensen.PositiveThreeTermRootReality

open _root_.D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (Σ _ : ℕ, Σ _ : ℕ → ℝ, ℕ → ℂ) (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.im) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (q : ℕ) (z : ℂ) (c : ℕ → ℝ) (v : ℕ → ℂ),
    (∀ k, k + 2 ≤ q → 0 < c k) →
    v 0 ≠ 0 → v 1 = z * v 0 →
    (∀ k, k + 2 ≤ q →
      v (k + 2) = z * v (k + 1) - (c k : ℂ) * v k) →
    v q = 0 → R.readout () ⟨q, c, v⟩ z = 0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : ℕ → ℂ := fun k => if k = 0 then 1 else 0
  have hbad := h 1 0 (fun _ => 1) v
    (by intro k hk; omega) (by simp [v]) (by simp [v])
    (by intro k hk; omega) (by simp [v])
  change (1 : ℝ) = 0 at hbad
  norm_num at hbad

def evidence : Registration arena
    (type_of% (@finite_positive_three_term_zero_has_real_parameter)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_positive_three_term_zero_has_real_parameter,
    rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    change ObservationalDependence signature actual
    intro role
    refine ⟨⟨0, fun _ => 0, fun _ => 0⟩, 0, Complex.I, ?_⟩
    change (0 : ℂ).im ≠ Complex.I.im
    simp

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_positive_three_term_zero_has_real_parameter)
    (type_of% (realize signature (fun _ _ z => z.im) (fun e => nomatch e)))
    Type Unit := {
  unitName := `Reg.D5.S3.Zeros.Jensen.PositiveThreeTermRootReality.root_reality_unit
  realizationName := `Reg.D5.S3.Zeros.Jensen.PositiveThreeTermRootReality.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z.im) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℂ
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
    definition := none
    coordinates := #[0, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration

end Reg.D5.S3.Zeros.Jensen.PositiveThreeTermRootReality
