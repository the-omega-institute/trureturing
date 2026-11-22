import D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.FifthExponents
import Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Chebyshev Real LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.FifthExponents

open Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePowerFifthCutoff
  (signature actual rejected correctedFamily)

abbrev sumArena : Arena where
  signature := signature
  Law V := ∀ {t : ℝ}, 2 ≤ t → ∀ {N : ℕ},
    ⌊log t / log 2⌋₊ ≤ N →
    V.readout () () t - theta t - psi (t ^ (1 / 2 : ℝ)) - psi (t ^ (1 / 3 : ℝ)) -
      psi (t ^ (1 / 5 : ℝ)) =
      ∑ k ∈ Finset.Icc 6 N, coefficient k * theta (t ^ (1 / (k : ℝ)))

private theorem sum_rejected : ¬ sumArena.Law rejected := by
  intro h
  have hN : ⌊log (2 : ℝ) / log 2⌋₊ ≤ 6 := by
    rw [div_self (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    norm_num
  have hbad := h (t := 2) (by norm_num) (N := 6) hN
  have hgood := psi_sub_roots_eq_sum (by norm_num : (2 : ℝ) ≤ 2) hN
  have hpsi : psi 2 = theta 2 := by
    have hb : ⌊log (2 : ℝ) / log 2⌋₊ ≤ 1 := by
      rw [div_self (log_pos (by norm_num : (1 : ℝ) < 2)).ne']
      norm_num
    simpa using psi_eq_theta_add_sum_theta' (by norm_num : (2 : ℝ) ≤ 2) hb
  have hz (d : ℝ) (hd : 0 < d) (hd' : d < 1) : psi ((2 : ℝ) ^ d) = 0 := by
    apply psi_eq_zero_iff.mpr
    simpa using rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hd'
  dsimp [rejected, realize] at hbad
  rw [hpsi, hz _ (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num),
    hz _ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num),
    hz _ (by norm_num : (0 : ℝ) < 1 / 5) (by norm_num)] at hgood
  linarith only [hbad, hgood]

def sumFamily : Registration sumArena (type_of% @psi_sub_roots_eq_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@psi_sub_roots_eq_sum, rejected, sum_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sumArena.Law actual rejected sum_rejected
  dependence := correctedFamily.dependence

def sumRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@psi_sub_roots_eq_sum) (Realization signature) Unit Unit where
  unitName := .str ``psi_sub_roots_eq_sum "__information_unit"
  realizationName := ``sumFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sumArena⟩
  objectArena := .source ⟨sumArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sumArena ⟨sumFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => psi t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.FifthExponents
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn",
        "arg", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.FifthExponents
