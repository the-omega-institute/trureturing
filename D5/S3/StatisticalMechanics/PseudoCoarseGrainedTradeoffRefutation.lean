/- GID: D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim; result=D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result; claim=D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim
   digest: A positive cyclic chain violates the pseudo-coarse-grained trade-off bound. -/

import D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation

set_option linter.style.header false
set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.whitespace false

namespace D5.S3.StatisticalMechanics.PseudoCoarseGrainedTradeoffRefutation

open scoped BigOperators
open MarkovMpembaTripletRefutation (generator)
open D5.S3.Divergence.ClassicalDPI (klDivergence)

noncomputable def binarySteadyState (x y k τ : ℝ) : ℝ :=
  x + (y - x) / (1 - Real.exp (-(k * τ)))

def claim : Prop :=
  ∀ (n : ℕ) (a : Fin n → Fin n → ℝ) (u : Fin n → ℝ)
    (p : ℝ → Fin n → ℝ) (τ : ℝ) (ω : Finset (Fin n)),
    (∀ i j, i ≠ j → 0 < a i j) →
    (∀ i, 0 < u i) → (∑ i, u i) = 1 → (generator a).mulVec u = 0 →
    (∀ t, HasDerivAt p ((generator a).mulVec (p t)) t) → 0 < τ →
    (∀ i, 0 < p 0 i) → (∑ i, p 0 i) = 1 → (∀ i, 0 < p τ i) →
    ω.Nonempty → ωᶜ.Nonempty →
    let x := ∑ i ∈ ω, p 0 i
    let y := ∑ i ∈ ω, p τ i
    let k := -(generator a).trace
    let s := binarySteadyState x y k τ
    0 < s → s < 1 →
    klDivergence ![x, 1 - x] ![s, 1 - s] -
        klDivergence ![y, 1 - y] ![s, 1 - s] ≤
      klDivergence (p 0) u - klDivergence (p τ) u

private noncomputable def rates : Fin 3 → Fin 3 → ℝ :=
  !![0, 1/100, 1; 1, 0, 1/100; 1/100, 1, 0]
private noncomputable def uniform : Fin 3 → ℝ := ![1/3, 1/3, 1/3]
private noncomputable def mode_a : Fin 3 → ℝ := ![2, -1, -1]
private noncomputable def mode_b : Fin 3 → ℝ := ![0, Real.sqrt 3, -Real.sqrt 3]
private noncomputable def α : ℝ := 303/200
private noncomputable def β : ℝ := 99 * Real.sqrt 3 / 200
private noncomputable def time : ℝ := Real.pi / β
private noncomputable def residual : ℝ := Real.exp (-(α * time))
private noncomputable def trajectory (t : ℝ) : Fin 3 → ℝ :=
  uniform + (1/12 * Real.exp (-(α*t))) •
    (Real.cos (β*t) • mode_a + Real.sin (β*t) • mode_b)

private theorem rates_positive : ∀ i j, i ≠ j → 0 < rates i j := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num [rates.eq_1] at *

private theorem stationary : (generator rates).mulVec uniform = 0 := by
  ext i
  unfold Matrix.mulVec dotProduct
  fin_cases i <;>
    simp only [Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, uniform.eq_1, Fin.sum_univ_succ]

private theorem mode_action :
    (generator rates).mulVec mode_a = -α • mode_a + β • mode_b ∧
    (generator rates).mulVec mode_b = -β • mode_a - α • mode_b := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  constructor <;> ext i <;> unfold Matrix.mulVec dotProduct
  all_goals fin_cases i <;>
    simp only [Fin.sum_univ_succ] <;>
    simp only [generator.eq_1] <;>
    norm_num [rates.eq_1, mode_a.eq_1, mode_b.eq_1, α.eq_1, β.eq_1,
      Fin.sum_univ_succ] <;> nlinarith

private theorem trajectory_deriv (t : ℝ) :
    HasDerivAt trajectory ((generator rates).mulVec (trajectory t)) t := by
  obtain ⟨ha, hb⟩ := mode_action
  rw [trajectory.eq_1, Matrix.mulVec_add, Matrix.mulVec_smul, stationary,
    Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, ha, hb, zero_add]
  apply hasDerivAt_pi.mpr
  intro i
  have he := (((hasDerivAt_id t).const_mul α).neg.exp).const_mul (1/12 : ℝ)
  have hc := ((hasDerivAt_id t).const_mul β).cos.mul_const (mode_a i)
  have hs := ((hasDerivAt_id t).const_mul β).sin.mul_const (mode_b i)
  convert (he.mul (hc.add hs)).const_add (uniform i) using 1 <;>
    simp only [trajectory.eq_1, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
      Pi.mul_apply, Pi.neg_apply, id_eq, smul_eq_mul]; ring

private theorem endpoints :
    trajectory 0 = ![1/2, 1/4, 1/4] ∧
    trajectory time = ![(2-residual)/6, (4+residual)/12, (4+residual)/12] := by
  have hβ : β ≠ 0 := by unfold β; positivity
  have ht : β * time = Real.pi := by rw [time.eq_1]; field_simp
  constructor
  · ext i
    fin_cases i <;> norm_num [trajectory.eq_1, uniform.eq_1, mode_a.eq_1, mode_b.eq_1]
  · ext i
    fin_cases i <;>
      simp [trajectory.eq_1, ht, Real.cos_pi, Real.sin_pi, ← residual.eq_1,
        uniform.eq_1, mode_a.eq_1, mode_b.eq_1] <;> ring

private theorem time_bounds : 0 < time ∧ 0 < residual ∧ residual < 1/4 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hs0 := Real.sqrt_nonneg (3 : ℝ)
  have hslo : (17/10 : ℝ) < Real.sqrt 3 := by nlinarith
  have hβ : 0 < β := by unfold β; positivity
  have ht : 0 < time := div_pos Real.pi_pos hβ
  have ha : α*time = 101 * Real.sqrt 3 * Real.pi / 99 := by
    unfold α time β
    field_simp
    nlinarith
  have hlo : 3 < α*time := by
    rw [ha]
    have hm := mul_lt_mul hslo Real.pi_gt_three.le (by norm_num : (0 : ℝ) < 3) hs0
    nlinarith
  refine ⟨ht, Real.exp_pos _, ?_⟩
  have he : 4 < Real.exp (α*time) := by
    have := Real.add_one_le_exp (α*time)
    linarith
  rw [residual.eq_1, Real.exp_neg]
  simpa using (inv_lt_inv₀ (Real.exp_pos (α*time)) (by norm_num : (0 : ℝ) < 4)).2 he

private theorem total_rate : -(generator rates).trace = 303/100 := by
  unfold Matrix.trace
  simp only [Matrix.diag_apply, Fin.sum_univ_succ]
  simp only [generator.eq_1]
  norm_num [rates.eq_1, Fin.sum_univ_succ]

private theorem steady_formula :
    binarySteadyState (1/2) ((2-residual)/6) (303/100) time =
      (2-3*residual)/(6*(1-residual)) := by
  have hr := time_bounds.2.2
  have h1 : 1-residual ≠ 0 := by linarith
  have he : Real.exp (-((303/100)*time)) = residual^2 := by
    rw [residual.eq_1, pow_two, ← Real.exp_add]
    congr 1
    unfold α
    ring
  have hd : 1-residual^2 ≠ 0 := by
    have hp := time_bounds.2.1
    nlinarith
  rw [binarySteadyState.eq_1, he]
  field_simp [hd, h1]
  ring

private theorem steady_bounds (r : ℝ) (hr : 0 < r) (hb : r < 1/4) :
    0 < (2-3*r)/(6*(1-r)) ∧ (2-3*r)/(6*(1-r)) < 1/3 := by
  have hd : 0 < 6*(1-r) := by linarith
  exact ⟨div_pos (by linarith) hd, (div_lt_iff₀ hd).2 (by linarith)⟩

private theorem split_divergence (z : ℝ) :
    klDivergence ![z, (1-z)/2, (1-z)/2] uniform =
      klDivergence ![z, 1-z] ![1/3, 1-1/3] := by
  rw [klDivergence, klDivergence]
  simp only [Fin.sum_univ_succ, uniform.eq_1, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.cons_val_fin_one, Fin.isValue]
  have he : (1-z)/2/(1/3) = (1-z)/(1-1/3) := by ring
  rw [he]
  ring

private theorem reference_change (x y s : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (hs : 0 < s) (hs1 : s < 1) :
    (klDivergence ![x, 1-x] ![1/3, 1-1/3] -
      klDivergence ![y, 1-y] ![1/3, 1-1/3]) -
    (klDivergence ![x, 1-x] ![s, 1-s] -
      klDivergence ![y, 1-y] ![s, 1-s]) =
    (x-y) * Real.log (2*s/(1-s)) := by
  rw [klDivergence, klDivergence, klDivergence, klDivergence]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hx' : 1-x ≠ 0 := ne_of_gt (sub_pos.mpr hx1)
  have hy' : 1-y ≠ 0 := ne_of_gt (sub_pos.mpr hy1)
  have hs' : 1-s ≠ 0 := ne_of_gt (sub_pos.mpr hs1)
  rw [Real.log_div hx.ne' (by norm_num : (1/3 : ℝ) ≠ 0),
    Real.log_div hx' (by norm_num : (1-1/3 : ℝ) ≠ 0),
    Real.log_div hy.ne' (by norm_num : (1/3 : ℝ) ≠ 0),
    Real.log_div hy' (by norm_num : (1-1/3 : ℝ) ≠ 0),
    Real.log_div hx.ne' hs.ne', Real.log_div hx' hs',
    Real.log_div hy.ne' hs.ne', Real.log_div hy' hs',
    Real.log_div (mul_ne_zero (by norm_num) hs.ne') hs',
    Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne']
  norm_num only [show (1-1/3 : ℝ) = 2/3 by norm_num]
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0),
    Real.log_div one_ne_zero (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]
  ring

private theorem strict_violation (r : ℝ) (hr : 0 < r) (hb : r < 1/4) :
    klDivergence ![1/2, 1/4, 1/4] uniform -
      klDivergence ![(2-r)/6, (4+r)/12, (4+r)/12] uniform <
    klDivergence ![1/2, 1-1/2] ![(2-3*r)/(6*(1-r)), 1-(2-3*r)/(6*(1-r))] -
      klDivergence ![(2-r)/6, 1-(2-r)/6]
        ![(2-3*r)/(6*(1-r)), 1-(2-3*r)/(6*(1-r))] := by
  obtain ⟨hs, hs3⟩ := steady_bounds r hr hb
  have hs1 : (2-3*r)/(6*(1-r)) < 1 := hs3.trans (by norm_num)
  have hy : 0 < (2-r)/6 := by linarith
  have hy1 : (2-r)/6 < 1 := by linarith
  have hq : ![(2-r)/6, (4+r)/12, (4+r)/12] =
      (![(2-r)/6, (1-(2-r)/6)/2, (1-(2-r)/6)/2] : Fin 3 → ℝ) := by
    ext i
    fin_cases i <;> norm_num <;> ring
  have hp : ![1/2, 1/4, 1/4] =
      (![1/2, (1-1/2)/2, (1-1/2)/2] : Fin 3 → ℝ) := by norm_num
  rw [hp, hq, split_divergence, split_divergence]
  have he := reference_change (1/2) ((2-r)/6) ((2-3*r)/(6*(1-r)))
    (by norm_num) (by norm_num) hy hy1 hs hs1
  have hratio : 2*((2-3*r)/(6*(1-r)))/(1-(2-3*r)/(6*(1-r))) =
      (4-6*r)/(4-3*r) := by
    have h1 : 0 < 1-r := by linarith
    have h4 : 0 < 4-r*3 := by linarith
    have hd : 0 < 1-(2-3*r)/(6*(1-r)) := sub_pos.mpr hs1
    field_simp (disch := first | positivity | linarith)
    ring
  rw [hratio] at he
  have hl : Real.log ((4-6*r)/(4-3*r)) < 0 :=
    Real.log_neg (div_pos (by linarith) (by linarith))
      ((div_lt_one (by linarith)).2 (by linarith))
  have hm : (1/2-(2-r)/6)*Real.log ((4-6*r)/(4-3*r)) < 0 :=
    mul_neg_of_pos_of_neg (by linarith) hl
  linarith

theorem result : ¬ claim := by
  intro h
  obtain ⟨ht, hr, hb⟩ := time_bounds
  obtain ⟨hp, hq⟩ := endpoints
  obtain ⟨hs, hs3⟩ := steady_bounds residual hr hb
  have hs1 : (2-3*residual)/(6*(1-residual)) < 1 := hs3.trans (by norm_num)
  have hu : ∀ i, 0 < uniform i := by
    intro i
    fin_cases i <;> norm_num [uniform.eq_1]
  have hun : (∑ i, uniform i) = 1 := by
    norm_num [uniform.eq_1, Fin.sum_univ_succ]
  have hp0 : ∀ i, 0 < trajectory 0 i := by
    rw [hp]
    intro i
    fin_cases i <;> norm_num
  have hpn : (∑ i, trajectory 0 i) = 1 := by
    rw [hp]
    norm_num [Fin.sum_univ_succ]
  have hqt : ∀ i, 0 < trajectory time i := by
    rw [hq]
    intro i
    fin_cases i <;> norm_num <;> linarith
  have hc : ({0} : Finset (Fin 3))ᶜ.Nonempty := by
    exact ⟨1, by simp⟩
  have hh := h 3 rates uniform trajectory time {0} rates_positive hu hun stationary
    trajectory_deriv ht hp0 hpn hqt (Finset.singleton_nonempty 0) hc
  simp only [Finset.sum_singleton] at hh
  rw [hp, hq, total_rate] at hh
  norm_num only [Matrix.cons_val_zero] at hh
  rw [steady_formula] at hh
  apply (not_le_of_gt (strict_violation residual hr hb))
  convert hh hs hs1 using 1; norm_num

end D5.S3.StatisticalMechanics.PseudoCoarseGrainedTradeoffRefutation
