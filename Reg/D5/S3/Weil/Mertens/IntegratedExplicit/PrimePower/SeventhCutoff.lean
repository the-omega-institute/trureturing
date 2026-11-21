import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SeventhCutoff
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

/-! Source readouts of the finite Chebyshev cutoff and its normalized tail. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real LeanInformationAudit MeasureTheory Set
open _root_.D5.S3.Arith.Robin.CompleteMertensPeak (Q)
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimeOnlyTailCorrection (primeTail)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SeventhCutoff

open PrimePowerFifthCutoff (signature actual rejected correctedFamily)

abbrev finiteArena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t →
    |V.readout () () t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) + theta (t ^ (1 / 6 : ℝ)) - theta (t ^ (1 / 7 : ℝ))| ≤
      4 * log t * t ^ (1 / 9 : ℝ)

private theorem finite_rejected : ¬ finiteArena.Law rejected := by
  intro h
  have hbad := h (t := 2) (by norm_num)
  dsimp [rejected, realize] at hbad
  have hseven : theta ((2 : ℝ) ^ (1 / 7 : ℝ)) = 0 := by
    apply theta_eq_zero_iff.mpr
    simpa using rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1 / 7 : ℝ) < 1)
  rw [hseven, sub_zero] at hbad
  have hcancel :
      theta (2 : ℝ) + psi (2 ^ (1 / 2 : ℝ)) + psi (2 ^ (1 / 3 : ℝ)) +
        psi (2 ^ (1 / 5 : ℝ)) + (2 + 100) - theta 2 - psi (2 ^ (1 / 2 : ℝ)) -
        psi (2 ^ (1 / 3 : ℝ)) - psi (2 ^ (1 / 5 : ℝ)) =
        (102 : ℝ) := by ring
  rw [hcancel] at hbad
  have hbound : 4 * log 2 * (2 : ℝ) ^ (1 / 9 : ℝ) ≤ 8 := by
    have hlog : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (x := 2) (by norm_num)]
    have hpow : (2 : ℝ) ^ (1 / 9 : ℝ) ≤ 2 := rpow_le_self_of_one_le (by norm_num) (by norm_num)
    calc
      _ ≤ (4 : ℝ) * 1 * 2 := by gcongr
      _ = _ := by norm_num
  linarith only [theta_nonneg ((2 : ℝ) ^ (1 / 6 : ℝ)), le_abs_self
    ((102 : ℝ) + theta (2 ^ (1 / 6 : ℝ))), hbad.trans hbound]

def finiteFamily : Registration finiteArena
    (type_of% @abs_psi_sub_roots_add_theta_sixth_sub_seventh_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@abs_psi_sub_roots_add_theta_sixth_sub_seventh_le, rejected, finite_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    finiteArena.Law actual rejected finite_rejected
  dependence := correctedFamily.dependence

def finiteRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@abs_psi_sub_roots_add_theta_sixth_sub_seventh_le) (Realization signature) Unit Unit where
  unitName := .str ``abs_psi_sub_roots_add_theta_sixth_sub_seventh_le "__information_unit"
  realizationName := ``finiteFamily
  realizationSource := none
  generated := false
  arena := .source ⟨finiteArena⟩
  objectArena := .source ⟨finiteArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source finiteArena ⟨finiteFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SeventhCutoff
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev tailSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def tailActual : Realization tailSignature :=
  realize tailSignature (fun _ _ x => primeTail x) (fun e => nomatch e)

def tailConclusion (R : Realization tailSignature) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 5000 ^ (7 : ℝ) ≤ x →
    |Real.sqrt x * (Q x - R.readout () () x -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, Chebyshev.psi (t ^ (5 : ℝ)⁻¹) / t ^ 2)) +
      (6 / 5) * x ^ (-(1 / 3) : ℝ) - (7 / 6) * x ^ (-(5 / 14) : ℝ)| ≤
      C * x ^ (-(3 / 8) : ℝ)

abbrev tailArena : Arena :=
  ⟨tailSignature, fun R => RiemannHypothesis → tailConclusion R⟩

theorem tail_source_bridge :
    (type_of% @sixth_seventh_normalized) ↔ tailArena.Law tailActual := Iff.rfl

def tailAltered : Realization tailSignature :=
  realize tailSignature (fun _ _ x =>
    Q x - (∫ t in Ioi x, psi (t ^ (2 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, psi (t ^ (3 : ℝ)⁻¹) / t ^ 2) -
      (∫ t in Ioi x, psi (t ^ (5 : ℝ)⁻¹) / t ^ 2) +
      ((6 / 5) * x ^ (-(1 / 3) : ℝ) - (7 / 6) * x ^ (-(5 / 14) : ℝ) -
        x * x ^ (-(3 / 8) : ℝ)) / Real.sqrt x) (fun e => nomatch e)

theorem tail_altered_rejects : ¬ tailConclusion tailAltered := by
  rintro ⟨C, hC, h⟩
  let x : ℝ := max (5000 ^ (7 : ℝ)) (C + 1)
  have hx : 5000 ^ (7 : ℝ) ≤ x := le_max_left _ _
  have hCx : C < x := (lt_add_one C).trans_le (le_max_right _ _)
  have hx0 : 0 < x := hC.trans hCx
  have hbad := h x hx
  dsimp [tailAltered, realize] at hbad
  have hcancel (q a b c d e f s : ℝ) (hs : s ≠ 0) :
      s * (q - (q - a - b - c + (d - e - f) / s) - a - b - c) + d - e = f := by
    field_simp
    ring
  rw [hcancel _ _ _ _ _ _ _ _ (Real.sqrt_pos.mpr hx0).ne',
    abs_of_pos (mul_pos hx0 (rpow_pos_of_pos hx0 _))] at hbad
  exact (not_le_of_gt (mul_lt_mul_of_pos_right hCx (rpow_pos_of_pos hx0 _))) hbad

theorem tail_sensitivity_iff_rh : Sensitivity tailArena tailActual ↔ RiemannHypothesis := by
  constructor
  · intro hs
    obtain ⟨_, _, _, hrejected⟩ := hs.1 ()
    by_contra hn
    exact hrejected (fun h => (hn h).elim)
  · intro hRH
    exact _root_.Reg.Support.SingleDependentReadout.sensitivity tailArena.Law tailActual
      tailAltered (fun h => tail_altered_rejects (h hRH))

theorem tail_variation_iff_rh : Variation tailArena tailActual ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨_, _, hn⟩
    by_contra h
    exact hn (fun hr => (h hr).elim)
  · intro hRH
    exact ⟨sixth_seventh_normalized, tailAltered, fun h => tail_altered_rejects (h hRH)⟩

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SeventhCutoff
