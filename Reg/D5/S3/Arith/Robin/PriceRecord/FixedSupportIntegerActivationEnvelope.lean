import D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

/-! Source-bound four-slot attempts observe the literal free q in the head
error, keeping every original hypothesis and every other q occurrence. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
open Real
open _root_.D5.S3.Arith.Robin.PriceRecord.OwnClockFixedSupport
open _root_.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Constructive
abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ _ q => q) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => -16) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Finset ℕ}, primeSupport S → ∀ {lam q : ℝ},
    0 < lam → 2 ≤ q → lam * q ^ 4 ≤ 1 →
    ∃ a : ℕ → ℕ, supportedAdmissible S a ∧
      linearCost S lam a ≤ activationSum S lam + secondActivationSum S lam +
        lam * R.readout () () q * (log (1 / lam) + 1) + 4 / q ^ 3
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, hcost⟩ := h (S := ∅) (by simp [primeSupport])
    (lam := 1 / 16) (q := 2) (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 ≤ log (16 : ℝ) := log_nonneg (by norm_num)
  norm_num [linearCost, activationSum, secondActivationSum, rejected, realize] at hcost
  linarith only [hcost, hlog]
def family : Registration arena (type_of% (@constructive_trial_vector)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@constructive_trial_vector, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@constructive_trial_vector) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope.constructive_trial_vector.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope.Constructive.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Constructive

namespace Envelope
abbrev signature : Signature.{0,0,0,0,0} :=
  _root_.Reg.Support.SingleDependentReadout.signature (Finset ℕ) (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature := realize signature
  (fun _ _ q => q) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ S q =>
    let lam := 1 / (theta S * log (theta S))
    let A := activationSum S lam + secondActivationSum S lam
    (integerInfimum S - A - 4 / q ^ 3 - 1) / (lam * (log (1 / lam) + 1)))
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {S : Finset ℕ}, primeSupport S → exp 1 < theta S →
    ∀ {r q : ℝ}, 0 < r → r ≤ 1 → 2 * log (theta S) * r ≤ 1 →
    2 ≤ q → (1 / (theta S * log (theta S))) * q ^ 4 ≤ 1 →
    let H := theta S
    let L := log H
    let lam := 1 / (H * L)
    let A := activationSum S lam + secondActivationSum S lam
    min r (A - 2 * lam * log (1 / lam) - 16 * L * r ^ 2) ≤ integerInfimum S ∧
      integerInfimum S ≤ A + lam * R.readout () S q * (log (1 / lam) + 1) + 4 / q ^ 3
private theorem rejected_law : ¬ arena.Law rejected := by
  let S : Finset ℕ := {65537}
  let H := theta S
  let L := log H
  let lam := 1 / (H * L)
  have hprime : primeSupport S := by norm_num [S, primeSupport]
  have hexp : exp (9 : ℝ) < 65537 := by
    have hp := pow_lt_pow_left₀ exp_one_lt_three (exp_pos 1).le (by decide : (9 : ℕ) ≠ 0)
    rw [show (9 : ℝ) = (9 : ℕ) * 1 by norm_num, exp_nat_mul]
    norm_num at hp ⊢
    linarith only [hp]
  have hH : 9 < H := by
    simpa [H, S, theta] using
      (lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 65537)).mpr hexp
  have hH0 : 0 < H := by linarith
  have hL : 2 < L := by
    have he2 : exp (2 : ℝ) < 9 := by
      have hp := pow_lt_pow_left₀ exp_one_lt_three (exp_pos 1).le (by decide : (2 : ℕ) ≠ 0)
      rw [show (2 : ℝ) = (2 : ℕ) * 1 by norm_num, exp_nat_mul]
      norm_num at hp ⊢
      exact hp
    exact (lt_log_iff_exp_lt hH0).mpr (he2.trans hH)
  have hL0 : 0 < L := by linarith
  have hlam : 0 < lam := by dsimp only [lam]; positivity
  have hlam1 : lam < 1 := by
    dsimp only [lam]
    apply (div_lt_one (mul_pos hH0 hL0)).mpr
    nlinarith only [hH, hL]
  have hT : 0 < log (1 / lam) + 1 := by
    have h := log_pos ((one_lt_div hlam).mpr hlam1)
    linarith only [h]
  have hr : 0 < 1 / (4 * L) := by positivity
  have hr1 : 1 / (4 * L) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 * L)).mpr
    linarith only [hL]
  have hrs : 2 * L * (1 / (4 * L)) ≤ 1 := by
    field_simp
    <;> nlinarith only [hL]
  have hquartic : lam * (2 : ℝ) ^ 4 ≤ 1 := by
    dsimp only [lam]
    rw [show (1 : ℝ) / (H * L) * 2 ^ 4 = 16 / (H * L) by ring]
    apply (div_le_one (mul_pos hH0 hL0)).mpr
    nlinarith only [hH, hL]
  intro h
  have hbad := (h hprime (exp_one_lt_three.trans (by linarith only [hH]))
    hr hr1 hrs (by norm_num : (2 : ℝ) ≤ 2) hquartic).2
  change integerInfimum S ≤ _ at hbad
  dsimp only [rejected, realize, actual, Realization.readout] at hbad
  change integerInfimum S ≤
    (activationSum S lam + secondActivationSum S lam) +
      lam * ((integerInfimum S - (activationSum S lam + secondActivationSum S lam) -
        4 / (2 : ℝ) ^ 3 - 1) / (lam * (log (1 / lam) + 1))) *
          (log (1 / lam) + 1) + 4 / (2 : ℝ) ^ 3 at hbad
  have heq : lam * ((integerInfimum S - (activationSum S lam + secondActivationSum S lam) -
      4 / (2 : ℝ) ^ 3 - 1) / (lam * (log (1 / lam) + 1))) *
        (log (1 / lam) + 1) =
      integerInfimum S - (activationSum S lam + secondActivationSum S lam) -
        4 / (2 : ℝ) ^ 3 - 1 := by
    field_simp
  rw [heq] at hbad
  linarith only [hbad]
def family : Registration arena (type_of% (@finite_integer_activation_envelope)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@finite_integer_activation_envelope, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨∅, 0, 1, ?_⟩
    change (0 : ℝ) ≠ 1
    norm_num
def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@finite_integer_activation_envelope) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope.finite_integer_activation_envelope.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope.Envelope.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Envelope

#print axioms Constructive.family
#print axioms Envelope.family
end Reg.D5.S3.Arith.Robin.PriceRecord.FixedSupportIntegerActivationEnvelope
