import D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment
import D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-bound registration of the coefficient in the actual mode-three residual bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator

open Filter LeanInformationAudit Real
open _root_.D5.S3.Arith.DiophantineApproximation.SimultaneousPhaseAlignment
  (simultaneous_dirichlet)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
  (eventually_mode_three_residual_bound)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualTwoFourCutoffCurvature (d actual_root_equation)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

noncomputable section

def actual : Realization signature :=
  realize signature (fun _ _ K => 2 * K + 6) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : ℝ} (_hK : 0 ≤ K),
    ∀ᶠ X : ℝ in atTop,
      let L := log X
      let x := L / d 2 X
      let t := d 3 X / d 2 X
      ∀ h m p : ℕ, 0 < h →
        |(h : ℝ) * x - m| ≤ K * exp (-(L / 15)) →
        |(h : ℝ) * t - p| ≤ K * exp (-(L / 15)) / L ^ 2 →
        h < m ∧ h < p ∧ 5 * p ≤ 8 * h ∧ (m : ℝ) ≤ 2 * (h : ℝ) * L ∧
        |(p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) -
            (h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤
          (R.readout () () K) * ((L ^ 2)⁻¹ * exp (-(L / 15)) + (h : ℝ) * exp (-(L / 3)))

private theorem source_bridge :
    (type_of% (@eventually_mode_three_residual_bound)) ↔ arena.Law actual := Iff.rfl

-- Both tolerances are chosen at the given X. The residual law allows every positive h.
private theorem exists_labels {x t ε δ : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t)
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ h m p : ℕ, 0 < h ∧ |(h : ℝ) * x - m| ≤ ε ∧ |(h : ℝ) * t - p| ≤ δ := by
  let tol : ℝ := min ε δ
  have htol : 0 < tol := lt_min hε hδ
  obtain ⟨Q, hQlt⟩ := exists_nat_gt (max 1 (1 / tol))
  have hQ : 1 ≤ Q := by
    exact_mod_cast (show (1 : ℝ) ≤ (Q : ℝ) from (le_max_left _ _).trans hQlt.le)
  have hQerr : 1 / (Q : ℝ) ≤ tol := calc
    _ ≤ 1 / (1 / tol) :=
      one_div_le_one_div_of_le (one_div_pos.mpr htol) ((le_max_right _ _).trans hQlt.le)
    _ = tol := by rw [one_div_div, div_one]
  let phase : Fin 2 → ℝ := fun i => if i = 0 then x else t
  obtain ⟨h, hh, _, happrox⟩ := simultaneous_dirichlet hQ phase
  obtain ⟨a, ha⟩ := happrox 0
  obtain ⟨b, hb⟩ := happrox 1
  have ha' : |(h : ℝ) * x - (a : ℝ)| ≤ 1 / (Q : ℝ) := by
    simpa only [phase, if_pos (rfl : (0 : Fin 2) = 0)] using ha
  have hb' : |(h : ℝ) * t - (b : ℝ)| ≤ 1 / (Q : ℝ) := by
    simpa only [phase, if_neg (show (1 : Fin 2) ≠ 0 by decide)] using hb
  have nat_error {y : ℝ} (hy : 0 ≤ y) (z : ℤ) :
      |(h : ℝ) * y - (z.natAbs : ℝ)| ≤ |(h : ℝ) * y - (z : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    simpa only [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg h) hy)] using
      abs_abs_sub_abs_le_abs_sub ((h : ℝ) * y) (z : ℝ)
  exact ⟨h, a.natAbs, b.natAbs, hh,
    (nat_error hx a).trans (ha'.trans (hQerr.trans (min_le_left _ _))),
    (nat_error ht b).trans (hb'.trans (hQerr.trans (min_le_right _ _)))⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hLaw
  have impossible : ∀ᶠ X : ℝ in atTop, False := by
    filter_upwards [hLaw (K := 1) zero_le_one,
      tendsto_log_atTop.eventually_gt_atTop 0,
      actual_root_equation (j := 2) (by norm_num),
      actual_root_equation (j := 3) (by norm_num)] with X hX hL hd₂ hd₃
    let L := log X
    let x := L / d 2 X
    let t := d 3 X / d 2 X
    have hLpos : 0 < L := hL
    have hx : 0 ≤ x := (div_pos hLpos hd₂.1).le
    have ht : 0 ≤ t := (div_pos hd₃.1 hd₂.1).le
    have hε : 0 < 1 * exp (-(L / 15)) := by positivity
    have hδ : 0 < 1 * exp (-(L / 15)) / L ^ 2 := by positivity
    obtain ⟨h, m, p, hh, hm, hp⟩ := exists_labels hx ht hε hδ
    obtain ⟨_, _, _, _, hResidual⟩ := hX h m p hh hm hp
    change |(p : ℝ) * log (2 * (m : ℝ) / ((m : ℝ) + h)) -
        (h : ℝ) * log (3 * (m : ℝ) / ((m : ℝ) + p))| ≤
      (-1 : ℝ) * ((L ^ 2)⁻¹ * exp (-(L / 15)) + (h : ℝ) * exp (-(L / 3))) at hResidual
    have hweight : 0 < (L ^ 2)⁻¹ * exp (-(L / 15)) + (h : ℝ) * exp (-(L / 3)) :=
      add_pos_of_nonneg_of_pos (mul_nonneg (inv_nonneg.mpr (sq_nonneg L)) (exp_pos _).le)
        (mul_pos (Nat.cast_pos.mpr hh) (exp_pos _))
    exact ((abs_nonneg _).trans hResidual).not_gt (mul_neg_of_neg_of_pos (by norm_num) hweight)
  obtain ⟨_, hFalse⟩ := impossible.exists
  exact hFalse

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change (2 : ℝ) * 1 + 6 ≠ 2 * 2 + 6
  norm_num

def family : Registration arena (type_of% (@eventually_mode_three_residual_bound)) where
  actual := actual
  bridge := source_bridge
  variation :=
    ⟨source_bridge.mp (@eventually_mode_three_residual_bound), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@eventually_mode_three_residual_bound) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator.eventually_mode_three_residual_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => 2 * K + 6) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
    definition := none
    coordinates := #[]
    readouts := #[{
      -- K and hK, then the eventual predicate and its X binder.
      -- Three lets, six binders, four right conjuncts, then the bound and its left factor.
      path := #["body", "body", "fn", "arg", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end
end Reg.D5.S3.Arith.Robin.PriceRecord.ActualModeThreeShortDenominator
