import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Reg.Support.SingleDependentReadout

/-! Source-bound observations for the scaled disk estimate, the global identity,
and the summability of the multiplicity weights. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Reg.D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Zeta23.WeilEF
open LeanInformationAudit Asymptotics Filter
open scoped Topology

namespace ScaledDisk

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ w => ‖w‖) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ w => ‖w‖ + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law L := ∀ {f : ℂ → ℂ} {R B : ℝ}
    (_hR : 0 < R) (_hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (_hf0 : f 0 ≠ 0)
    (_hB2 : 2 ≤ B) (_hfB : ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B * ‖f 0‖),
    ∃ Z : Finset ℂ, (↑Z : Set ℂ) = SetOfZeros (22 / 25 * R) f ∧
      ∀ s : ℂ, ‖s‖ ≤ R / 4 → f s ≠ 0 →
        L.readout () () ((logDeriv f s - logDeriv f 0) -
          ((∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ)) -
            ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (0 - ρ))) ≤
          179180000 * ‖s‖ * Real.log B / R ^ 2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨Z, _, hbound⟩ := h (f := fun _ => (1 : ℂ)) (R := 1) (B := 2)
    (by norm_num) (fun _ => analyticAt_const) one_ne_zero le_rfl (by intro w hw; norm_num)
  have hzero := hbound 0 (by norm_num) one_ne_zero
  norm_num [rejected, realize] at hzero

def family : Registration arena (type_of% (@logDeriv_partial_fraction_disk_centered)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logDeriv_partial_fraction_disk_centered, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro _
    refine ⟨(), (0 : ℂ), (1 : ℂ), ?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    rw [norm_zero, norm_one]
    exact zero_ne_one

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@logDeriv_partial_fraction_disk_centered) (Realization signature) Unit Unit where
  unitName := `Zeta23.WeilEF.logDeriv_partial_fraction_disk_centered.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion.ScaledDisk.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion
    definition := none
    coordinates := #[]
    -- The norm function applied to the centered remainder on the left of the bound.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end ScaledDisk

namespace GlobalIdentity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℂ → ℂ) (fun _ => ℂ) (fun _ => ℂ)

def actual : Realization signature :=
  realize signature (fun _ f s => logDeriv f s - logDeriv f 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ f s => (logDeriv f s - logDeriv f 0) + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law L := ∀ {f : ℂ → ℂ} {B : ℝ → ℝ}
    (_hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (_hf0 : f 0 ≠ 0)
    (_hB : ∀ᶠ R in atTop, 2 ≤ B R ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B R * ‖f 0‖)
    (_hgrowth : (fun R : ℝ => Real.log (B R)) =o[atTop] (fun R : ℝ => R ^ 2))
    (_hweight : Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
      (analyticOrderNatAt f (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2))
    (s : ℂ) (_hfs : f s ≠ 0),
    let k : ℂ → ℂ := fun ρ => (analyticOrderNatAt f ρ : ℂ) * ((s - ρ)⁻¹ + ρ⁻¹)
    Summable (fun ρ : {ρ : ℂ // f ρ = 0} => ‖k ρ‖) ∧
      L.readout () f s = ∑' ρ : {ρ : ℂ // f ρ = 0}, k ρ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  letI : IsEmpty {ρ : ℂ // (1 : ℂ) = 0} := ⟨fun ρ => one_ne_zero ρ.property⟩
  have hB : ∀ᶠ R : ℝ in atTop, 2 ≤ (2 : ℝ) ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖(1 : ℂ)‖ ≤ 2 * ‖(1 : ℂ)‖ := by
    exact .of_forall fun _ => ⟨le_rfl, by intro w hw; norm_num⟩
  have hgrowth : (fun _ : ℝ => Real.log 2) =o[atTop] (fun R : ℝ => R ^ 2) := by
    exact (isLittleO_const_id_atTop (Real.log 2)).comp_tendsto
      (tendsto_pow_atTop (α := ℝ) (n := 2) (by decide))
  have hbad := (h (f := fun _ => (1 : ℂ)) (B := fun _ => 2)
    (fun _ => analyticAt_const) one_ne_zero hB hgrowth summable_empty 0 one_ne_zero).2
  apply (one_ne_zero : (1 : ℂ) ≠ 0)
  simpa only [rejected, realize, sub_self, zero_add, tsum_empty] using hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  let f : ℂ → ℂ := fun z => z + 1
  refine ⟨f, 0, 1, ?_⟩
  change logDeriv f 0 - logDeriv f 0 ≠ logDeriv f 1 - logDeriv f 0
  have hlog (z : ℂ) : logDeriv f z = 1 / (z + 1) := by
    rw [logDeriv_apply]
    change deriv (fun w : ℂ => id w + 1) z / (z + 1) = _
    rw [deriv_add_const, deriv_id]
  rw [hlog 0, hlog 1, zero_add, div_one, sub_self]
  intro heq
  have htwo : (1 + 1 : ℂ) ≠ 0 := by norm_num
  have hone := (div_eq_iff htwo).mp (sub_eq_zero.mp heq.symm)
  norm_num at hone

def family : Registration arena (type_of% (@logDeriv_global_zero_expansion)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@logDeriv_global_zero_expansion, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@logDeriv_global_zero_expansion) (Realization signature) Unit Unit where
  unitName := `Zeta23.WeilEF.logDeriv_global_zero_expansion.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion.GlobalIdentity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion
    definition := none
    coordinates := #[0]
    -- Cross the let k binder, then select the left side of the equality.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "arg", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end GlobalIdentity

namespace DyadicWeights

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    (ℂ → ℂ) (fun f => {ρ : ℂ // f ρ = 0}) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ f ρ =>
    (analyticOrderNatAt f (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law L := ∀ {f : ℂ → ℂ} {B : ℝ → ℝ}
    (_hfa : ∀ z : ℂ, AnalyticAt ℂ f z) (_hf0 : f 0 ≠ 0)
    (_hB : ∀ᶠ R in atTop, 2 ≤ B R ∧
      ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖f w‖ ≤ B R * ‖f 0‖)
    (_hdyadic : Summable (fun n : ℕ =>
      Real.log (B ((2 : ℝ) ^ (n + 2) / (22 / 25))) / ((2 : ℝ) ^ (n + 1)) ^ 2)),
    Summable (fun ρ : {ρ : ℂ // f ρ = 0} => L.readout () f ρ)

private theorem cosineEnvelope : ∀ᶠ R : ℝ in atTop, 2 ≤ Real.exp R ∧
    ∀ w : ℂ, ‖w‖ ≤ 24 / 25 * R → ‖Complex.cos w‖ ≤ Real.exp R * ‖Complex.cos 0‖ := by
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  refine ⟨by linarith [Real.add_one_le_exp R], ?_⟩
  intro w hw
  have hIm : |w.im| ≤ R := (Complex.abs_im_le_norm w).trans (hw.trans (by linarith))
  have hpos := Real.exp_le_exp.mpr (abs_le.mp hIm).2
  have hneg := Real.exp_le_exp.mpr (show -w.im ≤ R by linarith [(abs_le.mp hIm).1])
  rw [Complex.cos_zero, norm_one, mul_one, Complex.cos, norm_div, Complex.norm_two]
  have hsum := norm_add_le (Complex.exp (w * Complex.I)) (Complex.exp (-w * Complex.I))
  rw [Complex.norm_exp_mul_I, Complex.norm_exp_mul_I, Complex.neg_im, neg_neg] at hsum
  linarith

private theorem cosineDyadic : Summable (fun n : ℕ =>
    Real.log (Real.exp ((2 : ℝ) ^ (n + 2) / (22 / 25))) / ((2 : ℝ) ^ (n + 1)) ^ 2) := by
  have hGeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (hGeom.mul_left (25 / 22)).congr ?_
  intro n
  symm
  rw [Real.log_exp, pow_add (2 : ℝ) n 2, pow_succ (2 : ℝ) n, one_div_pow]
  have hpow : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp [hpow] <;> ring

private def cosineZero (n : ℕ) : {ρ : ℂ // Complex.cos ρ = 0} :=
  ⟨((Real.pi / 2 + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ), by
    rw [← Complex.ofReal_cos, Real.cos_add_nat_mul_two_pi, Real.cos_pi_div_two,
      Complex.ofReal_zero]⟩

private theorem cosineZero_injective : Function.Injective cosineZero := by
  intro m n h
  have heq : Real.pi / 2 + (m : ℝ) * (2 * Real.pi) =
      Real.pi / 2 + (n : ℝ) * (2 * Real.pi) :=
    Complex.ofReal_injective (congrArg Subtype.val h)
  have hcast : (m : ℝ) = (n : ℝ) :=
    mul_right_cancel₀ (show (2 * Real.pi) ≠ 0 by positivity) (add_left_cancel heq)
  exact_mod_cast hcast

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hs : Summable (fun _ : {ρ : ℂ // Complex.cos ρ = 0} => (1 : ℝ)) :=
    h (f := Complex.cos) (B := Real.exp) (fun _ => Complex.analyticAt_cos)
      (by simp) cosineEnvelope cosineDyadic
  let _ := Infinite.of_injective cosineZero cosineZero_injective
  let _ := Finite.of_summable_const zero_lt_one hs
  exact not_finite {ρ : ℂ // Complex.cos ρ = 0}

private theorem cosineOrder (ρ : {ρ : ℂ // Complex.cos ρ = 0}) :
    analyticOrderNatAt Complex.cos (ρ : ℂ) = 1 := by
  have hd : deriv Complex.cos (ρ : ℂ) ≠ 0 := by
    rw [Complex.deriv_cos, neg_ne_zero]
    intro hsin
    have h := Complex.sin_sq_add_cos_sq (x := (ρ : ℂ))
    rw [hsin, ρ.property] at h
    norm_num at h
  have horder := Complex.analyticAt_cos.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    ρ.property hd
  simp [analyticOrderNatAt, horder]

private theorem cosineZero_norm (n : ℕ) :
    ‖(cosineZero n : ℂ)‖ = Real.pi / 2 + (n : ℝ) * (2 * Real.pi) := by
  change ‖((Real.pi / 2 + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ)‖ = _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨Complex.cos, cosineZero 0, cosineZero 1, ?_⟩
  change (analyticOrderNatAt Complex.cos (cosineZero 0 : ℂ) : ℝ) / ‖(cosineZero 0 : ℂ)‖ ^ 2 ≠
    (analyticOrderNatAt Complex.cos (cosineZero 1 : ℂ) : ℝ) / ‖(cosineZero 1 : ℂ)‖ ^ 2
  simp only [cosineOrder, cosineZero_norm, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, one_mul]
  have h0 : 0 < Real.pi / 2 := by positivity
  have h1 : Real.pi / 2 < Real.pi / 2 + 2 * Real.pi := by linarith [Real.pi_pos]
  have hsq := pow_lt_pow_left₀ h1 h0.le (by decide : (2 : ℕ) ≠ 0)
  exact (div_lt_div_of_pos_left zero_lt_one (sq_pos_of_pos h0) hsq).ne.symm

def family : Registration arena (type_of% (@summable_zero_multiplicity_div_norm_sq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@summable_zero_multiplicity_div_norm_sq, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@summable_zero_multiplicity_div_norm_sq) (Realization signature) Unit Unit where
  unitName := `Zeta23.WeilEF.summable_zero_multiplicity_div_norm_sq.audit
  realizationName := `Reg.D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion.DyadicWeights.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion
    definition := none
    coordinates := #[0]
    -- The summand lambda has a state in the zero subtype determined by f.
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end DyadicWeights

end Reg.D5.S3.Weil.ZetaExplicit.GlobalZeroExpansion
