import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.MetricGeometry.ArithmeticHorizon
import Reg.Support.SingleDependentReadout

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.MetricGeometry.ArithmeticHorizon

namespace Reg.D5.S3.Observer.MetricGeometry.ArithmeticHorizon

universe u
noncomputable section

/-- One role, no anchors, and genuinely real observation states and outputs. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ ε => Real.arcsin ε) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -Real.pi) (fun e => nomatch e)

/-- Only the selected arcsin occurrence varies; the entire source telescope remains. -/
def arena : Arena where
  signature := signature
  Law obs := ∀ {S : Type u} [Fintype S]
    (G : S → S) (h : S → ℂ) (initial : S) (x : AddCircle (1 : ℝ))
    (α ε : ℝ) (_hα : Irrational α) (_hε : 0 < ε) (_hεh : ε < 1 / 2)
    (H : ℕ)
    (_accuracy : ∀ n : ℕ, n ≤ H →
      ‖h ((G^[n]) initial) -
        ((x + n • (α : AddCircle (1 : ℝ))).toCircle : ℂ)‖ ≤ ε),
    (H : ℝ) < Fintype.card S +
      (obs.readout () () ε / Real.pi) * Psi α (Fintype.card S)

/-- Direct application of the unchanged source theorem, including its universe. -/
theorem positiveLaw : arena.{u}.Law actual :=
  @_root_.D5.S3.Observer.MetricGeometry.ArithmeticHorizon.finite_predictor_horizon.{u}

/-- The concrete one-state counterexample needs only this one value of Psi. -/
theorem sqrt_two_psi_lower : (2 : ℝ) ≤ Psi (Real.sqrt 2) 1 := by
  have hδ : 0 < torusNorm (Real.sqrt 2) := by
    change 0 < ‖(Real.sqrt 2 : AddCircle (1 : ℝ))‖
    rw [AddCircle.norm_eq]
    simpa only [inv_one, one_mul, mul_one] using
      (abs_pos.mpr (sub_ne_zero.mpr
        (irrational_sqrt_two.ne_int (round (Real.sqrt 2)))))
  have hδhalf : torusNorm (Real.sqrt 2) ≤ 1 / 2 := by
    simpa only [torusNorm, abs_one] using
      (AddCircle.norm_le_half_period (1 : ℝ)
        (x := (Real.sqrt 2 : AddCircle (1 : ℝ))) (by norm_num))
  have hPsi : Psi (Real.sqrt 2) 1 = 1 / torusNorm (Real.sqrt 2) := by
    simp only [Psi, dif_pos (show 1 ≤ (1 : ℕ) from le_rfl),
      Finset.Icc_self, Finset.sup'_singleton, Nat.cast_one, one_mul]
  rw [hPsi]
  exact (le_div_iff₀ hδ).mpr (by linarith [hδhalf])

/-- The rejected constant fails already at horizon zero, in every source universe. -/
theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have accuracy : ∀ n : ℕ, n ≤ 0 →
      ‖(1 : ℂ) -
        (((0 : AddCircle (1 : ℝ)) + n •
          (Real.sqrt 2 : AddCircle (1 : ℝ))).toCircle : ℂ)‖ ≤ (1 / 4 : ℝ) := by
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst n
    norm_num
  have hbound := h (S := ULift.{u} Unit)
    id (fun _ => (1 : ℂ)) ⟨()⟩ (0 : AddCircle (1 : ℝ))
    (Real.sqrt 2) (1 / 4) irrational_sqrt_two
    (by norm_num) (by norm_num) 0 accuracy
  have hpi : -Real.pi / Real.pi = (-1 : ℝ) := by
    rw [neg_div, div_self Real.pi_ne_zero]
  have hbound' : (0 : ℝ) < 1 + (-1) * Psi (Real.sqrt 2) 1 := by
    simpa only [rejected, realize, Fintype.card_ulift, Fintype.card_unit,
      Nat.cast_zero, Nat.cast_one, hpi] using hbound
  linarith [sqrt_two_psi_lower]

/-- Reuse the public whole-family sensitivity theorem for one role and no anchors. -/
theorem sensitivity : Sensitivity arena.{u} actual :=
  Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law actual rejected rejected_law

/-- Both chosen observation states lie strictly between zero and one half. -/
theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), (1 / 8 : ℝ), (1 / 4 : ℝ), by
    change Real.arcsin (1 / 8) ≠ Real.arcsin (1 / 4)
    exact ne_of_lt (Real.arcsin_lt_arcsin
      (by norm_num) (by norm_num) (by norm_num))⟩

/-- Every mathematical field is supplied; the bridge is definitional equality. -/
def sourceRegistration : Registration arena.{u} (arena.Law actual) :=
  Registration.mk actual Iff.rfl
    ⟨positiveLaw, rejected, rejected_law⟩ sensitivity dependence


noncomputable def registration_1.{u_1} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Observer.MetricGeometry.ArithmeticHorizon.finite_predictor_horizon.{u_1})
    (type_of% (realize.{0,0,0,0,0} signature (fun _ _ ε => Real.arcsin ε) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Observer.MetricGeometry.ArithmeticHorizon.finite_predictor_horizon.__information_unit,
  realizationName := `Reg.D5.S3.Observer.MetricGeometry.ArithmeticHorizon.sourceRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u_1}⟩,
  objectArena := .source ⟨arena.{u_1}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u_1} ⟨sourceRegistration.{u_1}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize.{0,0,0,0,0} signature (fun _ _ ε => Real.arcsin ε) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.MetricGeometry.ArithmeticHorizon
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms sourceRegistration
#print axioms registration_1

end
end Reg.D5.S3.Observer.MetricGeometry.ArithmeticHorizon
