/- GID: D5/S3/Weil/Mertens/MobiusDyadicEnergy/Kernel
   generality: I
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite arithmetic convolution and its zero transform for the signed Möbius energy proof. -/

import D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence
import D5.S3.Arith.MoebiusLogarithmic.ReciprocalBound
import D5.S3.Weil.Mertens.IntegratedExplicit.OriginalSignedJ
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic
import D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin
import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MobiusCausalKernel

open Set MeasureTheory
open scoped BigOperators

open D5.S3.Weil.ZetaPntBounds.MobiusPartialSumL2Divergence

/-- The actual arithmetic kernel, used only on nonnegative times. -/
def a (t : ℝ) : ℝ :=
  Real.exp (-t / 2) *
    (1 - Int.fract (Real.exp t) + ∫ u in (0 : ℝ)..t, Int.fract (Real.exp u))

/-- The existing literal weighted Mobius partial sum in logarithmic time. -/
def h (t : ℝ) : ℝ := Real.exp (t / 2) * mobiusPartialSum (Real.exp t)

private def b (t : ℝ) : ℝ :=
  1 - Int.fract (Real.exp t) + ∫ u in (0 : ℝ)..t, Int.fract (Real.exp u)

private def cutoff (T : ℝ) : Finset ℕ := Finset.Ioc 0 ⌊Real.exp T⌋₊

private def ramp (c T : ℝ) : ℝ := if c ≤ T then T - c else 0

private def pair (T : ℝ) (k n : ℕ) (u : ℝ) : ℝ :=
  if Real.log (n : ℝ) ≤ u ∧ u ≤ T - Real.log (k : ℝ) then
    (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) *
      Real.exp (T / 2 - u) * (1 - u + Real.log (n : ℝ))
  else 0

private lemma cutoff_mono {s T : ℝ} (hsT : s ≤ T) : cutoff s ⊆ cutoff T := by
  intro n hn
  exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
    (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono (Real.exp_le_exp.mpr hsT))⟩

private lemma log_mem_cutoff {T : ℝ} {n : ℕ} (hn : n ∈ cutoff T) :
    Real.log (n : ℝ) ∈ Icc 0 T := by
  have hn0 : 0 < n := (Finset.mem_Ioc.mp hn).1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine ⟨Real.log_natCast_nonneg n, (Real.log_le_iff_le_exp hnR).mpr ?_⟩
  exact (Nat.le_floor_iff (Real.exp_pos T).le).mp (Finset.mem_Ioc.mp hn).2

/-- Fixed-horizon expansion, valid also when s is negative. -/
private lemma cutoff_sum (f : ℕ → ℝ) {s T : ℝ} (hsT : s ≤ T) :
    (∑ n ∈ cutoff T, if Real.log (n : ℝ) ≤ s then f n else 0) =
      ∑ n ∈ cutoff s, f n := by
  classical
  have he : (cutoff T).filter (fun n : ℕ => Real.log (n : ℝ) ≤ s) = cutoff s := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnT, hns⟩ := Finset.mem_filter.mp hn
      have hn0 : 0 < n := (Finset.mem_Ioc.mp hnT).1
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      exact Finset.mem_Ioc.mpr ⟨hn0,
        (Nat.le_floor_iff (Real.exp_pos s).le).mpr
          ((Real.log_le_iff_le_exp hnR).mp hns)⟩
    · intro hn
      exact Finset.mem_filter.mpr ⟨cutoff_mono hsT hn, (log_mem_cutoff hn).2⟩
  rw [← Finset.sum_filter, he]

private lemma floor_exp_sum {s T : ℝ} (hsT : s ≤ T) :
    (⌊Real.exp s⌋₊ : ℝ) =
      ∑ n ∈ cutoff T, if Real.log (n : ℝ) ≤ s then (1 : ℝ) else 0 := by
  rw [cutoff_sum (fun _ => 1) hsT]
  simp [cutoff]

private lemma mobius_finite {s T : ℝ} (hsT : s ≤ T) :
    mobiusPartialSum (Real.exp s) =
      ∑ k ∈ cutoff T, if Real.log (k : ℝ) ≤ s then
        (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) else 0 := by
  rw [cutoff_sum (fun k => (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)) hsT]
  have he : Finset.Icc 1 ⌊Real.exp s⌋₊ = cutoff s := by
    ext n
    simp only [cutoff, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  simp only [mobiusPartialSum, he]

private lemma step_integrable (c T : ℝ) :
    IntervalIntegrable (fun u : ℝ => if c ≤ u then (1 : ℝ) else 0) volume 0 T := by
  have he : (fun u : ℝ => if c ≤ u then (1 : ℝ) else 0) =
      (Ici c).indicator (fun _ => (1 : ℝ)) := by
    ext u
    simp [Set.indicator]
  rw [he]
  exact OriginalSignedJ.indicator_tail_integrable intervalIntegrable_const c

private lemma integral_step {c T : ℝ} (hc : 0 ≤ c) (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T, if c ≤ u then (1 : ℝ) else 0) = ramp c T := by
  by_cases hcT : c ≤ T
  · have he := OriginalSignedJ.integral_indicator_tail
      (g := fun _ : ℝ => (1 : ℝ)) hc hcT
    simpa [Set.indicator, ramp, hcT] using he
  · have he : (∫ u in (0 : ℝ)..T, if c ≤ u then (1 : ℝ) else 0) =
        ∫ _u in (0 : ℝ)..T, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT] at hu
      exact ite_eq_right (by linarith [hu.2])
    simp [he, ramp, hcT]

private lemma floor_exp_integrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => (⌊Real.exp u⌋₊ : ℝ)) volume 0 T := by
  have hi := IntervalIntegrable.sum (cutoff T)
    (fun n _ => step_integrable (Real.log (n : ℝ)) T)
  apply hi.congr
  intro u hu
  rw [uIoc_of_le hT] at hu
  simpa only [Finset.sum_apply, Finset.sum_fn] using (floor_exp_sum hu.2).symm

private lemma integral_floor_exp {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T, (⌊Real.exp u⌋₊ : ℝ)) =
      ∑ n ∈ cutoff T, (T - Real.log (n : ℝ)) := by
  calc
    _ = ∫ u in (0 : ℝ)..T,
        ∑ n ∈ cutoff T, if Real.log (n : ℝ) ≤ u then (1 : ℝ) else 0 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT] at hu
      exact floor_exp_sum hu.2
    _ = ∑ n ∈ cutoff T,
        ∫ u in (0 : ℝ)..T, if Real.log (n : ℝ) ≤ u then (1 : ℝ) else 0 :=
      intervalIntegral.integral_finsetSum (fun n _ => step_integrable _ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [integral_step (log_mem_cutoff hn).1 hT, ramp,
        ite_eq_left (log_mem_cutoff hn).2]

private lemma fract_exp_eq (u : ℝ) :
    Int.fract (Real.exp u) = Real.exp u - (⌊Real.exp u⌋₊ : ℝ) := by
  rw [Int.fract, natCast_floor_eq_intCast_floor (Real.exp_pos u).le]

/-- Local integrability used in converting the defining fractional-part
integral to finite arithmetic pulses. -/
private lemma fract_exp_intervalIntegrable {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (fun u : ℝ => Int.fract (Real.exp u)) volume 0 T := by
  simpa only [fract_exp_eq] using
    (Real.continuous_exp.intervalIntegrable 0 T).sub (floor_exp_integrable hT)

private lemma b_floor_form {T : ℝ} (hT : 0 ≤ T) :
    b T = (⌊Real.exp T⌋₊ : ℝ) -
      ∫ u in (0 : ℝ)..T, (⌊Real.exp u⌋₊ : ℝ) := by
  have hi : (∫ u in (0 : ℝ)..T, (⌊Real.exp u⌋₊ : ℝ)) =
      (Real.exp T - 1) - ∫ u in (0 : ℝ)..T, Int.fract (Real.exp u) := by
    calc
      _ = ∫ u in (0 : ℝ)..T, Real.exp u - Int.fract (Real.exp u) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        rw [fract_exp_eq]
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub (Real.continuous_exp.intervalIntegrable 0 T)
          (fract_exp_intervalIntegrable hT), integral_exp, Real.exp_zero]
  unfold b
  linarith [fract_exp_eq T]

private lemma b_finite {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    b s = ∑ n ∈ cutoff T, if Real.log (n : ℝ) ≤ s then
      1 - s + Real.log (n : ℝ) else 0 := by
  rw [cutoff_sum (fun n => 1 - s + Real.log (n : ℝ)) hsT,
    b_floor_form hs, integral_floor_exp hs]
  have hc : (⌊Real.exp s⌋₊ : ℝ) = ∑ _n ∈ cutoff s, (1 : ℝ) := by
    simp [cutoff]
  rw [hc, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The fixed cutoff still uses exactly the frozen floor cancellation;
the extra terms vanish because their quotient has natural floor zero. -/
private lemma floor_cancellation_fixed {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
      (⌊Real.exp s / (k : ℝ)⌋₊ : ℝ)) = 1 := by
  have hsub : cutoff s ⊆ cutoff T := cutoff_mono hsT
  have he : (∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
      (⌊Real.exp s / (k : ℝ)⌋₊ : ℝ)) =
      ∑ k ∈ cutoff s, (ArithmeticFunction.moebius k : ℝ) *
        (⌊Real.exp s / (k : ℝ)⌋₊ : ℝ) := by
    symm
    apply Finset.sum_subset hsub
    intro k hkT hks
    have hk0 : 0 < k := (Finset.mem_Ioc.mp hkT).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hnk : ¬k ≤ ⌊Real.exp s⌋₊ := by
      intro hk
      exact hks (Finset.mem_Ioc.mpr ⟨hk0, hk⟩)
    have hsk : Real.exp s < (k : ℝ) := by
      by_contra hnot
      exact hnk ((Nat.le_floor_iff (Real.exp_pos s).le).mpr (le_of_not_gt hnot))
    have hq : Real.exp s / (k : ℝ) < 1 :=
      (div_lt_iff₀ hkR).mpr (by simpa using hsk)
    simp [Nat.floor_eq_zero.mpr hq]
  rw [he]
  exact D5.S3.Arith.MoebiusLogarithmic.floor_cancellation
    (by simpa using Real.exp_le_exp.mpr hs)

private lemma arithmetic_steps {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
      ∑ n ∈ cutoff T,
        if Real.log (k : ℝ) + Real.log (n : ℝ) ≤ s then (1 : ℝ) else 0) = 1 := by
  have he (k : ℕ) (hk : k ∈ cutoff T) :
      (∑ n ∈ cutoff T,
        if Real.log (k : ℝ) + Real.log (n : ℝ) ≤ s then (1 : ℝ) else 0) =
        (⌊Real.exp s / (k : ℝ)⌋₊ : ℝ) := by
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    have hshift : s - Real.log (k : ℝ) ≤ T := by
      linarith [(log_mem_cutoff hk).1]
    have hexp : Real.exp (s - Real.log (k : ℝ)) = Real.exp s / (k : ℝ) := by
      rw [Real.exp_sub, Real.exp_log hk0]
    rw [← hexp, floor_exp_sum hshift]
    apply Finset.sum_congr rfl
    intro n _
    have hc : (Real.log (k : ℝ) + Real.log (n : ℝ) ≤ s) ↔
        Real.log (n : ℝ) ≤ s - Real.log (k : ℝ) := by constructor <;> intro hle <;> linarith
    simp only [hc]
  calc
    _ = ∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
        (⌊Real.exp s / (k : ℝ)⌋₊ : ℝ) :=
      Finset.sum_congr rfl (fun k hk => congrArg
        (fun v : ℝ => (ArithmeticFunction.moebius k : ℝ) * v) (he k hk))
    _ = 1 := floor_cancellation_fixed hs hsT

/-- Actual finite arithmetic: all positive integer pairs at every real
horizon, collapsed using the frozen Mobius--floor identity. -/
private lemma arithmetic_ramps {T : ℝ} (hT : 0 ≤ T) :
    (∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
      ∑ n ∈ cutoff T, ramp (Real.log (k : ℝ) + Real.log (n : ℝ)) T) = T := by
  have hi (k : ℕ) : IntervalIntegrable
      (fun u : ℝ => ∑ n ∈ cutoff T,
        if Real.log (k : ℝ) + Real.log (n : ℝ) ≤ u then (1 : ℝ) else 0)
      volume 0 T := by
    simpa only [Finset.sum_apply, Finset.sum_fn] using
      IntervalIntegrable.sum (cutoff T) (fun n _ =>
        step_integrable (Real.log (k : ℝ) + Real.log (n : ℝ)) T)
  have hi_sum : (∫ u in (0 : ℝ)..T,
      ∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
        ∑ n ∈ cutoff T,
          if Real.log (k : ℝ) + Real.log (n : ℝ) ≤ u then (1 : ℝ) else 0) =
      ∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
        ∑ n ∈ cutoff T, ramp (Real.log (k : ℝ) + Real.log (n : ℝ)) T := by
    rw [intervalIntegral.integral_finsetSum
      (fun k _ => (hi k).const_mul (ArithmeticFunction.moebius k : ℝ))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum (fun n _ => step_integrable _ _)]
    congr 1
    apply Finset.sum_congr rfl
    intro n hn
    exact integral_step
      (add_nonneg (log_mem_cutoff hk).1 (log_mem_cutoff hn).1) hT
  have hi_one : (∫ u in (0 : ℝ)..T,
      ∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
        ∑ n ∈ cutoff T,
          if Real.log (k : ℝ) + Real.log (n : ℝ) ≤ u then (1 : ℝ) else 0) = T := by
    calc
      _ = ∫ _u in (0 : ℝ)..T, (1 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hT] at hu
        exact arithmetic_steps hu.1 hu.2
      _ = T := by simp
  exact hi_sum.symm.trans hi_one

private lemma pair_integrable (T : ℝ) (k n : ℕ) :
    IntervalIntegrable (pair T k n) volume 0 T := by
  let f : ℝ → ℝ := fun u => (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) *
    Real.exp (T / 2 - u) * (1 - u + Real.log (n : ℝ))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have hh : IntervalIntegrable ((Iic (T - Real.log (k : ℝ))).indicator f)
      volume 0 T :=
    intervalIntegrable_iff.mpr ((hf.intervalIntegrable 0 T).def'.indicator measurableSet_Iic)
  convert OriginalSignedJ.indicator_tail_integrable hh (Real.log (n : ℝ)) using 1
  ext u
  by_cases hn : Real.log (n : ℝ) ≤ u <;>
    by_cases hk : u ≤ T - Real.log (k : ℝ) <;>
    simp [pair, Set.indicator, hn, hk, f]

/-- The finite pair integral includes equality of both endpoints. -/
private lemma integral_pair {T : ℝ} {k n : ℕ}
    (hk : k ∈ cutoff T) (hn : n ∈ cutoff T) :
    (∫ u in (0 : ℝ)..T, pair T k n u) =
      (ArithmeticFunction.moebius k : ℝ) * Real.exp (-T / 2) *
        ramp (Real.log (k : ℝ) + Real.log (n : ℝ)) T := by
  let α : ℝ := Real.log (n : ℝ)
  let β : ℝ := T - Real.log (k : ℝ)
  let c : ℝ := (ArithmeticFunction.moebius k : ℝ) / (k : ℝ)
  let f : ℝ → ℝ := fun u => c * Real.exp (T / 2 - u) * (1 - u + α)
  have hα : α ∈ Icc 0 T := log_mem_cutoff hn
  have hβ : β ∈ Icc 0 T := by
    have h := log_mem_cutoff hk
    dsimp [β]
    constructor <;> linarith [h.1, h.2]
  by_cases hab : α ≤ β
  · have hp : pair T k n = (Ici α).indicator ((Iic β).indicator f) := by
      ext u
      change (if α ≤ u ∧ u ≤ β then f u else 0) = _
      by_cases hnu : α ≤ u <;> by_cases hku : u ≤ β <;>
        simp [Set.indicator, hnu, hku]
    have hcut : (∫ u in (0 : ℝ)..T, pair T k n u) = ∫ u in α..β, f u := by
      rw [hp, OriginalSignedJ.integral_indicator_tail hα.1 hα.2]
      exact intervalIntegral.integral_indicator (f := f) ⟨hab, hβ.2⟩
    let F : ℝ → ℝ := fun u => c * (Real.exp (T / 2 - u) * (u - α))
    have hd (u : ℝ) : HasDerivAt F (f u) u := by
      convert ((((hasDerivAt_const u (T / 2)).sub (hasDerivAt_id u)).exp).mul
        ((hasDerivAt_id u).sub_const α)).const_mul c using 1 <;>
        dsimp [F, f] <;> ring
    have hf : Continuous f := by dsimp [f]; fun_prop
    have hprim : (∫ u in α..β, f u) = F β - F α :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
        (hf.intervalIntegrable α β)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast (Finset.mem_Ioc.mp hk).1
    have he : Real.exp (T / 2 - β) = (k : ℝ) * Real.exp (-T / 2) := by
      rw [show T / 2 - β = Real.log (k : ℝ) + (-T / 2) by dsimp [β]; ring,
        Real.exp_add, Real.exp_log hk0]
    have hcT : Real.log (k : ℝ) + Real.log (n : ℝ) ≤ T := by
      change Real.log (n : ℝ) ≤ T - Real.log (k : ℝ) at hab
      linarith
    rw [hcut, hprim, ramp, ite_eq_left hcT]
    dsimp [F]
    rw [he]
    dsimp [c, α, β]
    field_simp [hk0.ne'] <;> ring
  · have hcT : ¬Real.log (k : ℝ) + Real.log (n : ℝ) ≤ T := by
      change ¬Real.log (n : ℝ) ≤ T - Real.log (k : ℝ) at hab
      linarith
    have hz : pair T k n = fun _ => 0 := by
      ext u
      apply ite_eq_right
      rintro ⟨hnu, hku⟩
      exact hab (hnu.trans hku)
    simp [hz, ramp, hcT]

private lemma integrand_finite {T u : ℝ} (hu : u ∈ Icc 0 T) :
    a u * h (T - u) = ∑ k ∈ cutoff T, ∑ n ∈ cutoff T, pair T k n u := by
  have hTuT : T - u ≤ T := by linarith [hu.1]
  have he : Real.exp (-u / 2) * Real.exp ((T - u) / 2) =
      Real.exp (T / 2 - u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    a u * h (T - u) = Real.exp (T / 2 - u) *
        (mobiusPartialSum (Real.exp (T - u)) * b u) := by
      change (Real.exp (-u / 2) * b u) *
        (Real.exp ((T - u) / 2) * mobiusPartialSum (Real.exp (T - u))) = _
      rw [← he]
      ring
    _ = Real.exp (T / 2 - u) *
        ((∑ k ∈ cutoff T, if Real.log (k : ℝ) ≤ T - u then
          (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) else 0) *
        (∑ n ∈ cutoff T, if Real.log (n : ℝ) ≤ u then
          1 - u + Real.log (n : ℝ) else 0)) := by
      rw [mobius_finite hTuT, b_finite hu.1 hu.2]
    _ = ∑ k ∈ cutoff T, ∑ n ∈ cutoff T,
        Real.exp (T / 2 - u) *
          ((if Real.log (k : ℝ) ≤ T - u then
            (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) else 0) *
          (if Real.log (n : ℝ) ≤ u then 1 - u + Real.log (n : ℝ) else 0)) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro n _
      have hc : (u ≤ T - Real.log (k : ℝ)) ↔
          Real.log (k : ℝ) ≤ T - u := by constructor <;> intro hle <;> linarith
      by_cases hk : Real.log (k : ℝ) ≤ T - u <;>
        by_cases hn : Real.log (n : ℝ) ≤ u <;>
        simp [pair, hc, hk, hn] <;> ring

/-- The requested identity for the literal kernel and literal Mobius sum,
at every nonnegative real time. -/
theorem causal_identity {T : ℝ} (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T, a u * h (T - u)) = T * Real.exp (-T / 2) := by
  calc
    _ = ∫ u in (0 : ℝ)..T, ∑ k ∈ cutoff T, ∑ n ∈ cutoff T, pair T k n u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hT] at hu
      exact integrand_finite hu
    _ = ∑ k ∈ cutoff T, ∑ n ∈ cutoff T, ∫ u in (0 : ℝ)..T, pair T k n u := by
      rw [intervalIntegral.integral_finsetSum (fun k _ => by
        simpa only [Finset.sum_apply, Finset.sum_fn] using IntervalIntegrable.sum (cutoff T)
          (fun n _ => pair_integrable T k n))]
      apply Finset.sum_congr rfl
      intro k _
      exact intervalIntegral.integral_finsetSum (fun n _ => pair_integrable T k n)
    _ = ∑ k ∈ cutoff T, ∑ n ∈ cutoff T,
        (ArithmeticFunction.moebius k : ℝ) * Real.exp (-T / 2) *
          ramp (Real.log (k : ℝ) + Real.log (n : ℝ)) T := by
      apply Finset.sum_congr rfl
      intro k hk
      exact Finset.sum_congr rfl (fun n hn => integral_pair hk hn)
    _ = Real.exp (-T / 2) *
        (∑ k ∈ cutoff T, (ArithmeticFunction.moebius k : ℝ) *
          ∑ n ∈ cutoff T, ramp (Real.log (k : ℝ) + Real.log (n : ℝ)) T) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = T * Real.exp (-T / 2) := by rw [arithmetic_ramps hT]; ring

end MobiusCausalKernel

namespace MobiusKernelLaplace

open Set MeasureTheory

open D5.S3.Weil.ZetaPntBounds.NymanFractionalMellin


private def r (t : ℝ) : ℝ := Int.fract (Real.exp t)

private def exponential (p : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (-p * (t : ℂ))

private def fractionalWeighted (p : ℂ) (t : ℝ) : ℂ :=
  (r t : ℂ) * exponential p t

private def primitiveWeighted (p : ℂ) (t : ℝ) : ℂ :=
  exponential p t * ((∫ u in (0 : ℝ)..t, r u : ℝ) : ℂ)

private def fractionalMellinIntegrand (p : ℂ) (x : ℝ) : ℂ :=
  ((Int.fract (1 / x : ℝ) : ℝ) : ℂ) * (x : ℂ) ^ (p - 1)

private lemma decay_hasDeriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
  simpa only [Pi.neg_apply, id_eq, mul_neg, mul_one] using ((hasDerivAt_id t).neg.exp)

private lemma decay_injOn :
    InjOn (fun t : ℝ => Real.exp (-t)) (Ioi (0 : ℝ)) := by
  intro x _ y _ h
  have hxy : -x = -y := Real.exp_injective h
  linarith

private lemma decay_image :
    (fun t : ℝ => Real.exp (-t)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨Real.exp_pos _, Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr ht)⟩
  · intro hx
    refine ⟨-Real.log x, neg_pos.mpr (Real.log_neg hx.1 hx.2), ?_⟩
    simpa only [neg_neg] using Real.exp_log hx.1

/-- The literal Jacobian pullback; no branch choice is made at a complex base. -/
private lemma decay_pullback (p : ℂ) (t : ℝ) :
    (abs (-Real.exp (-t)) : ℝ) • fractionalMellinIntegrand p (Real.exp (-t)) =
      fractionalWeighted p t := by
  have hrec : 1 / Real.exp (-t) = Real.exp t := by
    simp only [Real.exp_neg, one_div, inv_inv]
  have hlog : Complex.log (Real.exp (-t) : ℂ) = (-t : ℝ) := by
    rw [← Complex.ofReal_log (Real.exp_pos (-t)).le, Real.log_exp]
  have hpow : (Real.exp (-t) : ℂ) ^ (p - 1) =
      Complex.exp (-(t : ℂ) * (p - 1)) := by
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (-t))), hlog, Complex.ofReal_neg]
  rw [abs_neg, abs_of_pos (Real.exp_pos _), Complex.real_smul]
  change (Real.exp (-t) : ℂ) *
    (((Int.fract (1 / Real.exp (-t) : ℝ) : ℝ) : ℂ) * (Real.exp (-t) : ℂ) ^ (p - 1)) = _
  rw [hrec, hpow, Complex.ofReal_exp, Complex.ofReal_neg]
  calc
    _ = (r t : ℂ) * (Complex.exp (-(t : ℂ)) *
        Complex.exp (-(t : ℂ) * (p - 1))) := by dsimp [r]; ring
    _ = (r t : ℂ) * Complex.exp (-p * (t : ℂ)) := by
      rw [← Complex.exp_add]
      congr 2
      ring
    _ = fractionalWeighted p t := rfl

/-- Actual L1 is transported from the existing bounded fractional Mellin L1 theorem. -/
private lemma fractionalWeighted_integrable {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fractionalWeighted p) (Ioi (0 : ℝ)) := by
  have hi : IntegrableOn (fractionalMellinIntegrand p) (Ioo (0 : ℝ) 1) := by
    unfold fractionalMellinIntegrand
    exact fractionalMellin_integrableOn 1 p hp
  have hchange := integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := fun t : ℝ => Real.exp (-t))
    (f' := fun t : ℝ => -Real.exp (-t)) measurableSet_Ioi
    (fun t _ => (decay_hasDeriv t).hasDerivWithinAt) decay_injOn
    (fractionalMellinIntegrand p)
  rw [decay_image] at hchange
  simpa only [decay_pullback] using hchange.mp hi

private lemma fractionalWeighted_integral {p : ℂ} (hp : 0 < p.re) (hp1 : p ≠ 1) :
    (∫ t in Ioi (0 : ℝ), fractionalWeighted p t) =
      1 / (p - 1) - riemannZeta p / p := by
  have hchange := integral_image_eq_integral_abs_deriv_smul
    (s := Ioi (0 : ℝ)) (f := fun t : ℝ => Real.exp (-t))
    (f' := fun t : ℝ => -Real.exp (-t)) measurableSet_Ioi
    (fun t _ => (decay_hasDeriv t).hasDerivWithinAt) decay_injOn
    (fractionalMellinIntegrand p)
  rw [decay_image] at hchange
  simp only [decay_pullback] at hchange
  calc
    _ = ∫ x in Ioo (0 : ℝ) 1, fractionalMellinIntegrand p x := hchange.symm
    _ = _ := bd_mellin_base_case_proved p hp hp1

private lemma exponential_integrable {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (exponential p) (Ioi (0 : ℝ)) := by
  exact integrableOn_exp_mul_complex_Ioi
    (a := -p) (by simpa only [Complex.neg_re, neg_lt_zero] using hp) 0

private lemma exponential_integral {p : ℂ} (hp : 0 < p.re) :
    (∫ t in Ioi (0 : ℝ), exponential p t) = 1 / p := by
  simpa [exponential] using integral_exp_mul_complex_Ioi
    (a := -p) (by simpa only [Complex.neg_re, neg_lt_zero] using hp) (0 : ℝ)

/-- The bounded measurable fractional part is integrable on every finite positive interval. -/
private lemma fractional_intervalIntegrable {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u : ℝ => (r u : ℂ)) volume 0 t := by
  have hm : Measurable (fun u : ℝ => (r u : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp Real.continuous_exp.measurable.fract
  have hi : IntegrableOn (fun u : ℝ => (r u : ℂ)) (Ioc (0 : ℝ) t) := by
    refine Measure.integrableOn_of_bounded
      (show volume (Ioc (0 : ℝ) t) ≠ ⊤ from measure_Ioc_lt_top.ne)
      hm.aestronglyMeasurable (M := 1) ?_
    filter_upwards with u
    change ‖((Int.fract (Real.exp u) : ℝ) : ℂ)‖ ≤ (1 : ℝ)
    simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg (Real.exp u))]
      using (Int.fract_lt_one (Real.exp u)).le
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le ht).mpr hi

/-- Finite factoring, with actual interval integrability supplied before integration. -/
private lemma convolution_inner (p : ℂ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable
      (fun u : ℝ => fractionalWeighted p u * exponential p (t - u)) volume 0 t ∧
    (∫ u in (0 : ℝ)..t, fractionalWeighted p u * exponential p (t - u)) =
      primitiveWeighted p t := by
  have hpoint (u : ℝ) :
      fractionalWeighted p u * exponential p (t - u) = exponential p t * (r u : ℂ) := by
    dsimp only [fractionalWeighted, exponential]
    rw [mul_assoc, ← Complex.exp_add]
    have he : -p * (u : ℂ) + -p * ((t - u : ℝ) : ℂ) = -p * (t : ℂ) := by
      push_cast
      ring
    rw [he, mul_comm]
  have hi : IntervalIntegrable (fun u : ℝ => exponential p t * (r u : ℂ)) volume 0 t :=
    (fractional_intervalIntegrable ht).const_mul _
  refine ⟨hi.congr (fun u _ => (hpoint u).symm), ?_⟩
  calc
    _ = ∫ u in (0 : ℝ)..t, exponential p t * (r u : ℂ) :=
      intervalIntegral.integral_congr (fun u _ => hpoint u)
    _ = exponential p t * ∫ u in (0 : ℝ)..t, (r u : ℂ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = primitiveWeighted p t := by
      rw [intervalIntegral.integral_ofReal]
      rfl

/-- Mathlib's positive convolution is zero outside Ioi 0; equality is used only inside it. -/
private lemma primitiveWeighted_integrable {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (primitiveWeighted p) (Ioi (0 : ℝ)) := by
  have hc : Integrable
      (posConvolution (fractionalWeighted p) (exponential p)
        (ContinuousLinearMap.mul ℝ ℂ) volume) volume :=
    integrable_posConvolution (fractionalWeighted_integrable hp)
      (exponential_integrable hp) (ContinuousLinearMap.mul ℝ ℂ)
  apply hc.integrableOn.congr_fun _ measurableSet_Ioi
  intro t ht
  rw [posConvolution, indicator_of_mem ht]
  simp only [ContinuousLinearMap.mul_apply']
  exact (convolution_inner p ht.le).2

private lemma primitiveWeighted_integral {p : ℂ} (hp : 0 < p.re) :
    (∫ t in Ioi (0 : ℝ), primitiveWeighted p t) =
      (∫ t in Ioi (0 : ℝ), fractionalWeighted p t) / p := by
  have hf := fractionalWeighted_integrable hp
  have hg := exponential_integrable hp
  have hc := integral_posConvolution hf hg (ContinuousLinearMap.mul ℝ ℂ)
  simp only [ContinuousLinearMap.mul_apply'] at hc
  calc
    _ = ∫ t in Ioi (0 : ℝ),
        ∫ u in (0 : ℝ)..t, fractionalWeighted p u * exponential p (t - u) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      exact (convolution_inner p ht.le).2.symm
    _ = (∫ t in Ioi (0 : ℝ), fractionalWeighted p t) *
        (∫ t in Ioi (0 : ℝ), exponential p t) := hc
    _ = _ := by rw [exponential_integral hp]; ring

/-- Algebra for the supplied literal real a; no arithmetic causal theorem is invoked. -/
private lemma actual_integrand_split (z : ℂ) (t : ℝ) :
    (MobiusCausalKernel.a t : ℂ) * Complex.exp (-z * (t : ℂ)) =
      exponential (z + 1 / 2) t - fractionalWeighted (z + 1 / 2) t +
        primitiveWeighted (z + 1 / 2) t := by
  have he : (Real.exp (-t / 2) : ℂ) * Complex.exp (-z * (t : ℂ)) =
      exponential (z + 1 / 2) t := by
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    dsimp only [exponential]
    congr 1
    push_cast
    ring
  change ((Real.exp (-t / 2) *
    (1 - r t + ∫ u in (0 : ℝ)..t, r u) : ℝ) : ℂ) *
      Complex.exp (-z * (t : ℂ)) = _
  rw [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_one]
  calc
    _ = ((Real.exp (-t / 2) : ℂ) * Complex.exp (-z * (t : ℂ))) *
        (1 - (r t : ℂ) + ((∫ u in (0 : ℝ)..t, r u : ℝ) : ℂ)) := by ring
    _ = _ := by rw [he]; dsimp only [fractionalWeighted, primitiveWeighted]; ring

private lemma shifted_re_pos {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    0 < (z + 1 / 2 : ℂ).re := by
  have he : (z + 1 / 2 : ℂ).re = z.re + (1 / 2 : ℝ) := by simp
  rw [he]
  linarith

/-- Actual Bochner/Lebesgue absolute integrability, including z=1/2. -/
private theorem integrableOn_actual_kernel {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re) :
    IntegrableOn
      (fun t : ℝ => (MobiusCausalKernel.a t : ℂ) * Complex.exp (-z * (t : ℂ)))
      (Ioi (0 : ℝ)) := by
  have hp := shifted_re_pos hz
  have hi := ((exponential_integrable hp).sub
    (fractionalWeighted_integrable hp)).add (primitiveWeighted_integrable hp)
  apply hi.congr_fun _ measurableSet_Ioi
  intro t _
  exact (actual_integrand_split z t).symm

/-- The exact transform, only on the nonpole domain p=z+1/2. -/
private theorem actual_kernel_laplace {z : ℂ} (hz : -(1 / 2 : ℝ) < z.re)
    (hzpole : z ≠ (1 / 2 : ℂ)) :
    (∫ t in Ioi (0 : ℝ),
      (MobiusCausalKernel.a t : ℂ) * Complex.exp (-z * (t : ℂ))) =
      (((z + 1 / 2) - 1) * riemannZeta (z + 1 / 2)) / (z + 1 / 2) ^ 2 := by
  have hp := shifted_re_pos hz
  have hp0 : z + (1 / 2 : ℂ) ≠ 0 := by
    intro h
    rw [h] at hp
    norm_num at hp
  have hp1 : z + (1 / 2 : ℂ) ≠ 1 := by
    intro h
    apply hzpole
    linear_combination h
  have he := exponential_integrable hp
  have hf := fractionalWeighted_integrable hp
  have hprim := primitiveWeighted_integrable hp
  have hsplit :
      (fun t : ℝ => (MobiusCausalKernel.a t : ℂ) * Complex.exp (-z * (t : ℂ))) =
        (fun t : ℝ => exponential (z + 1 / 2) t - fractionalWeighted (z + 1 / 2) t +
          primitiveWeighted (z + 1 / 2) t) := funext (actual_integrand_split z)
  rw [hsplit]
  rw [integral_add (f := fun t => exponential (z + 1 / 2) t - fractionalWeighted (z + 1 / 2) t) (he.sub hf) hprim,
    integral_sub (f := exponential (z + 1 / 2)) he hf,
    exponential_integral hp, primitiveWeighted_integral hp]
  simp only [fractionalWeighted_integral hp hp1]
  generalize (z + (1 / 2 : ℂ)) = p at hp0 hp1 ⊢
  field_simp [hp0, sub_ne_zero.mpr hp1]
  ring

/-- True integrability and vanishing for every actual nonpole zero
in Re rho>0. In particular rho=0 is excluded by the strict real-part condition. -/
private theorem at_zero {rho : ℂ} (hpos : 0 < rho.re) (hpole : rho ≠ 1)
    (hzero : riemannZeta rho = 0) :
    IntegrableOn
      (fun t : ℝ => (MobiusCausalKernel.a t : ℂ) *
        Complex.exp (-(rho - 1 / 2) * (t : ℂ))) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), (MobiusCausalKernel.a t : ℂ) *
      Complex.exp (-(rho - 1 / 2) * (t : ℂ))) = 0 := by
  have hz : -(1 / 2 : ℝ) < (rho - 1 / 2 : ℂ).re := by
    have he : (rho - 1 / 2 : ℂ).re = rho.re - (1 / 2 : ℝ) := by simp
    rw [he]
    linarith
  have hzpole : rho - (1 / 2 : ℂ) ≠ 1 / 2 := by
    intro h
    apply hpole
    linear_combination h
  refine ⟨integrableOn_actual_kernel hz, ?_⟩
  simpa only [sub_add_cancel, hzero, mul_zero, zero_div] using
    actual_kernel_laplace hz hzpole

/-- The requested actual nontrivial-zero input, without RH,
a simple-zero premise, or any assumption about a transform of h. -/
theorem at_nontrivial_zero {rho : ℂ} (hhalf : (1 / 2 : ℝ) ≤ rho.re)
    (hlt : rho.re < 1) (hzero : riemannZeta rho = 0) :
    IntegrableOn
      (fun t : ℝ => (MobiusCausalKernel.a t : ℂ) *
        Complex.exp (-(rho - 1 / 2) * (t : ℂ))) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), (MobiusCausalKernel.a t : ℂ) *
      Complex.exp (-(rho - 1 / 2) * (t : ℂ))) = 0 := by
  apply at_zero (by linarith) _ hzero
  intro h
  rw [h] at hlt
  norm_num at hlt

end MobiusKernelLaplace
