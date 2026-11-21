/- GID: D5/S1/Recurrence/Residue/OEISA194767ReciprocalSum
   generality: I
   mirror-B: D5/B/S1/Recurrence/Residue/OEISA194767ReciprocalSum
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: [mathlib/module/Mathlib.Analysis.SpecialFunctions.Integrals.Basic]
   utility: none
   digest: The A194767 fourth-diagonal denominators have reciprocal sum 1 + log 3 - π/(3√3). -/

import D5.S1.Recurrence.Residue.OEISA194767SecondKindDiagonal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! The reciprocal sum of the fourth-diagonal denominators of the A194767 array. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Recurrence.Residue.OEISA194767ReciprocalSum

open D5.S1.Recurrence.Residue.OEISA194767SecondKindDiagonal
open Real intervalIntegral Filter Topology

private noncomputable def q (x : ℝ) : ℝ := x ^ 2 + x + 1

private theorem q_pos (x : ℝ) : 0 < q x := by unfold q; nlinarith [sq_nonneg (x + 1 / 2)]

private noncomputable def F (x : ℝ) : ℝ :=
  Real.log (q x) / 2 - arctan ((2 * x + 1) / √3) / √3

private theorem hF (x : ℝ) : HasDerivAt F (x / q x) x := by
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hq : HasDerivAt q (2 * x + 1) x := by
    unfold q
    have := ((hasDerivAt_pow 2 x).add (hasDerivAt_id x)).add_const 1
    convert this using 1; simp; ring
  have hl := (hq.log (q_pos x).ne').div_const 2
  have ha : HasDerivAt (fun x : ℝ => (2 * x + 1) / √3) (2 / √3) x := by
    have := (((hasDerivAt_id x).const_mul 2).add_const 1).div_const √3
    convert this using 1 <;> simp
  have hat := ha.arctan.div_const √3
  unfold F
  convert hl.sub hat using 1
  have hqx := q_pos x
  have key : 1 + ((2 * x + 1) / √3) ^ 2 = 4 * q x / 3 := by
    rw [div_pow, hs]; unfold q; ring
  rw [key]
  field_simp
  rw [hs]
  ring

private theorem integral_I : ∫ x in (0 : ℝ)..1, x / q x = Real.log 3 / 2 - π / (6 * √3) := by
  have hc : Continuous fun x : ℝ => x / q x :=
    continuous_id.div (by unfold q; fun_prop) (fun x => (q_pos x).ne')
  rw [integral_eq_sub_of_hasDerivAt (fun x _ => hF x) (hc.intervalIntegrable _ _)]
  have h3 : (0 : ℝ) < √3 := by positivity
  have hs : √3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have e1 : (2 * (1 : ℝ) + 1) / √3 = tan (π / 3) := by
    rw [tan_pi_div_three]; field_simp; rw [hs]; norm_num
  have e0 : (2 * (0 : ℝ) + 1) / √3 = tan (π / 6) := by rw [tan_pi_div_six]; norm_num
  unfold F
  rw [e1, e0, arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos]),
    arctan_tan (by linarith [pi_pos]) (by linarith [pi_pos])]
  unfold q
  norm_num
  field_simp
  ring

private noncomputable def E (N : ℕ) : ℝ := ∫ x in (0 : ℝ)..1, x ^ (3 * N + 1) / q x

private theorem cont_pow_div (n : ℕ) : Continuous fun x : ℝ => x ^ n / q x :=
  (continuous_pow n).div (by unfold q; fun_prop) (fun x => (q_pos x).ne')

private theorem E_step (N : ℕ) : E N - E (N + 1) = 1 / (3 * N + 2) - 1 / (3 * N + 3) := by
  unfold E
  rw [← integral_sub ((cont_pow_div _).intervalIntegrable _ _)
    ((cont_pow_div _).intervalIntegrable _ _)]
  have h : ∀ x : ℝ, x ^ (3 * N + 1) / q x - x ^ (3 * (N + 1) + 1) / q x =
      x ^ (3 * N + 1) - x ^ (3 * N + 2) := by
    intro x
    have := (q_pos x).ne'
    field_simp
    unfold q
    ring
  simp_rw [h]
  rw [integral_sub (intervalIntegrable_pow _) (intervalIntegrable_pow _), integral_pow,
    integral_pow]
  push_cast
  norm_num
  ring

private theorem T_eq (N : ℕ) : ∑ k ∈ Finset.range N, (1 / (3 * (k : ℝ) + 2) - 1 / (3 * k + 3)) =
    (Real.log 3 / 2 - π / (6 * √3)) - E N := by
  induction N with
  | zero =>
    rw [← integral_I]; unfold E; simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, ← E_step N]
    ring

private theorem E_nonneg (N : ℕ) : 0 ≤ E N :=
  integral_nonneg zero_le_one fun x hx => div_nonneg (pow_nonneg hx.1 _) (q_pos x).le

private theorem E_le (N : ℕ) : E N ≤ 1 / (3 * N + 2) := by
  have h : E N ≤ ∫ x in (0 : ℝ)..1, x ^ (3 * N + 1) :=
    integral_mono_on zero_le_one ((cont_pow_div _).intervalIntegrable _ _)
      (intervalIntegrable_pow _) fun x hx => by
        have h1 : 1 ≤ q x := by unfold q; nlinarith [hx.1]
        exact div_le_self (pow_nonneg hx.1 _) h1
  rw [integral_pow] at h
  push_cast at h
  norm_num at h
  convert h using 2; ring

private theorem E_tendsto : Tendsto E atTop (𝓝 0) := by
  have h : Tendsto (fun N : ℕ => 1 / (3 * (N : ℝ) + 2)) atTop (𝓝 0) := by
    apply tendsto_const_nhds.div_atTop
    exact tendsto_atTop_add_const_right _ _
      (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h E_nonneg E_le

/-- The reciprocal sum of the fourth-diagonal denominators of the A194767 second-kind array:
`∑_{m ≥ 0} 1 / d_m = 1 + log 3 - π / (3 √3)`. -/
theorem result :
    HasSum (fun m => (1 : ℝ) / d m) (1 + Real.log 3 - π / (3 * √3)) := by
  have hd := OEISA194767SecondKindDiagonal.result.2.2.1
  set S : ℕ → ℝ := fun n => ∑ m ∈ Finset.range n, (1 : ℝ) / d m with hS
  have hblock : ∀ N, S (3 * N) = 1 - 1 / (3 * N + 1) +
      2 * ∑ k ∈ Finset.range N, (1 / (3 * (k : ℝ) + 2) - 1 / (3 * k + 3)) := by
    intro N
    induction N with
    | zero => simp [hS]
    | succ N ih =>
      obtain ⟨h0, h1, h2⟩ := hd N
      simp only [hS] at ih ⊢
      rw [show 3 * (N + 1) = 3 * N + 2 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ, h0, h1, h2]
      push_cast
      field_simp
      ring
  have hL : Tendsto (fun N => S (3 * N)) atTop (𝓝 (1 + Real.log 3 - π / (3 * √3))) := by
    simp_rw [hblock, T_eq]
    have h1 : Tendsto (fun N : ℕ => 1 / (3 * (N : ℝ) + 1)) atTop (𝓝 0) := by
      apply tendsto_const_nhds.div_atTop
      exact tendsto_atTop_add_const_right _ _
        (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub h1).add
      ((tendsto_const_nhds (x := Real.log 3 / 2 - π / (6 * √3))).sub E_tendsto |>.const_mul 2)
    convert this using 2
    have : (0 : ℝ) < √3 := by positivity
    field_simp
    ring
  have hnn : ∀ m, (0 : ℝ) ≤ 1 / d m := fun m => by positivity
  have hmono : Monotone S := fun a b hab =>
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) (fun i _ _ => hnn i)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hdiv : Tendsto (fun n : ℕ => n / 3) atTop atTop := Nat.tendsto_div_const_atTop (by norm_num)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le (hL.comp hdiv)
    ((hL.comp (tendsto_add_atTop_nat 1)).comp hdiv) (fun n => hmono ?_) (fun n => hmono ?_)
  · simp only; omega
  · simp only; omega

end D5.S1.Recurrence.Residue.OEISA194767ReciprocalSum
