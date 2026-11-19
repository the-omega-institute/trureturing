import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.MobiusDyadicEnergy
import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for the cumulative and individual Möbius shell quotients. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators Topology
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.ForwardKernel.KappaGap (zeroAbscissa)
open _root_.D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
open _root_.D5.S3.Weil.Mertens.MobiusDyadicEnergy
  (K mobiusDyadicShellEnergy signed_dyadic_eventual_prefix_lower_bound)
open _root_.D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
  (exists_nontrivial_zero_re_ge_half)

namespace Reg.D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℝ)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2 * zeroAbscissa) (fun e => nomatch e)

private theorem logQuotient_pos {n : ℕ} {x : ℝ} (hn : 0 < n) (hx : 0 < x) :
    0 < Real.log (1 + x) / ((n : ℝ) * Real.log 2) :=
  div_pos (Real.log_pos (by linarith only [hx]))
    (mul_pos (Nat.cast_pos.mpr hn) (Real.log_pos (by norm_num)))

private theorem exists_shell_prefix_gt (B : ℝ) :
    ∃ N : ℕ, 0 < N ∧ B < ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k := by
  obtain ⟨ρ, hρ, hβ⟩ := exists_nontrivial_zero_re_ge_half
  obtain ⟨c, hc, N₀, hlower⟩ := signed_dyadic_eventual_prefix_lower_bound hβ hρ.2.2 hρ.1
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htime : Tendsto (fun N : ℕ => (N : ℝ) * Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hlog
  obtain ⟨N, hN, hlarge⟩ :=
    ((eventually_ge_atTop (max N₀ 1)).and (htime.eventually_gt_atTop (B / c))).exists
  let U : ℝ := (N : ℝ) * Real.log 2
  have hU : 0 ≤ U := mul_nonneg (Nat.cast_nonneg N) hlog.le
  have hK : U ≤ K ρ.re U := by
    have he : IntervalIntegrable (fun t : ℝ => Real.exp ((2 * ρ.re - 1) * t)) volume 0 U :=
      (by fun_prop : Continuous (fun t : ℝ => Real.exp ((2 * ρ.re - 1) * t))).intervalIntegrable _ _
    have hm : (∫ _t in (0 : ℝ)..U, (1 : ℝ)) ≤
        ∫ t in (0 : ℝ)..U, Real.exp ((2 * ρ.re - 1) * t) := by
      apply intervalIntegral.integral_mono_on hU intervalIntegrable_const he
      intro t ht
      have hp : 0 ≤ (2 * ρ.re - 1) * t := mul_nonneg (by linarith only [hβ]) ht.1
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hp
    simpa only [K, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one] using hm
  have hstrict : B < c * U := by
    rw [mul_comm c]
    exact (div_lt_iff₀ hc).mp hlarge
  exact ⟨N, (le_max_right N₀ 1).trans hN,
    hstrict.trans_le ((mul_le_mul_of_nonneg_left hK hc.le).trans
      (hlower N ((le_max_left N₀ 1).trans hN)))⟩

private theorem exists_pos_shell : ∃ k : ℕ, 1 ≤ k ∧ 0 < mobiusDyadicShellEnergy k := by
  by_contra h
  have hzero (k : ℕ) (hk : 1 ≤ k) : mobiusDyadicShellEnergy k = 0 :=
    le_antisymm (le_of_not_gt (fun hpos => h ⟨k, hk, hpos⟩))
      (integral_nonneg (fun _ => sq_nonneg _))
  have hprefix (N : ℕ) :
      (∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) ≤ mobiusDyadicShellEnergy 0 := by
    induction N with
    | zero =>
      rw [Finset.sum_range_zero]
      exact integral_nonneg (fun _ => sq_nonneg _)
    | succ N ih =>
      rw [Finset.sum_range_succ]
      cases N with
      | zero => simp
      | succ N =>
        rw [hzero (N + 1) (Nat.succ_pos N), add_zero]
        exact ih
  obtain ⟨N, _, hlarge⟩ := exists_shell_prefix_gt (mobiusDyadicShellEnergy 0)
  exact (not_lt_of_ge (hprefix N)) hlarge

namespace Cumulative

def actual : Realization signature :=
  realize signature (fun _ _ N =>
    Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
      ((N : ℝ) * Real.log 2)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Tendsto (fun N : ℕ => R.readout () () N) atTop (𝓝 (2 * zeroAbscissa - 1))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change Tendsto (fun _ : ℕ => 2 * zeroAbscissa) atTop (𝓝 (2 * zeroAbscissa - 1)) at h
  have heq : 2 * zeroAbscissa = 2 * zeroAbscissa - 1 :=
    tendsto_nhds_unique tendsto_const_nhds h
  linarith only [heq]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨N, hN, hsum⟩ := exists_shell_prefix_gt 0
  refine ⟨(), 0, N, ?_⟩
  change Real.log (1 + ∑ k ∈ Finset.range 0, mobiusDyadicShellEnergy k) /
    (((0 : ℕ) : ℝ) * Real.log 2) ≠
      Real.log (1 + ∑ k ∈ Finset.range N, mobiusDyadicShellEnergy k) /
        ((N : ℝ) * Real.log 2)
  simpa only [Nat.cast_zero, zero_mul, div_zero] using (logQuotient_pos hN hsum).ne

def evidence : Registration arena (type_of% @tendsto_log_one_add_sum_mobiusDyadicShellEnergy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨tendsto_log_one_add_sum_mobiusDyadicShellEnergy, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    tendsto_log_one_add_sum_mobiusDyadicShellEnergy (Realization signature) (ℕ → ℝ) Unit where
  unitName := `D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit.tendsto_log_one_add_sum_mobiusDyadicShellEnergy.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit.Cumulative.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
    definition := none
    coordinates := #[]
    -- The body of the sequence argument of Tendsto.
    readouts := #[{
      path := #["fn", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Cumulative

namespace Individual

def actual : Realization signature :=
  realize signature (fun _ _ k =>
    Real.log (1 + mobiusDyadicShellEnergy k) / ((k : ℝ) * Real.log 2)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := Filter.limsup (fun k : ℕ => R.readout () () k) atTop = 2 * zeroAbscissa - 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change Filter.limsup (fun _ : ℕ => 2 * zeroAbscissa) atTop = 2 * zeroAbscissa - 1 at h
  rw [Filter.limsup_const] at h
  linarith only [h]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨k, hk, hpos⟩ := exists_pos_shell
  have hk₀ : 0 < k := hk
  refine ⟨(), 0, k, ?_⟩
  change Real.log (1 + mobiusDyadicShellEnergy 0) / (((0 : ℕ) : ℝ) * Real.log 2) ≠
    Real.log (1 + mobiusDyadicShellEnergy k) / ((k : ℝ) * Real.log 2)
  simpa only [Nat.cast_zero, zero_mul, div_zero] using (logQuotient_pos hk₀ hpos).ne

def evidence : Registration arena (type_of% @limsup_log_one_add_mobiusDyadicShellEnergy) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨limsup_log_one_add_mobiusDyadicShellEnergy, rejected, rejected_law⟩
  sensitivity :=
    _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    limsup_log_one_add_mobiusDyadicShellEnergy (Realization signature) (ℕ → ℝ) Unit where
  unitName := `D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit.limsup_log_one_add_mobiusDyadicShellEnergy.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit.Individual.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
    definition := none
    coordinates := #[]
    -- The body of the sequence argument of limsup on the left of Eq.
    readouts := #[{
      path := #["fn", "arg", "fn", "arg", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Individual

#print axioms Cumulative.evidence
#print axioms Individual.evidence

end Reg.D5.S3.Weil.Mertens.MobiusDyadicGrowthLimit
