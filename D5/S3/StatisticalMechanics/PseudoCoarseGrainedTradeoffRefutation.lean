/- GID: D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim; result=D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.result; claim=D5/S3/StatisticalMechanics/PseudoCoarseGrainedTradeoffRefutation.claim
   digest: A positive three-state cyclic chain violates the pseudo-coarse-grained trade-off bound. -/

import D5.S3.StatisticalMechanics.MarkovMpembaTripletRefutation
import D5.S3.Divergence.ClassicalDPI

set_option autoImplicit false

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
  sorry

private theorem stationary : (generator rates).mulVec uniform = 0 := by
  sorry

private theorem mode_action :
    (generator rates).mulVec mode_a = -α • mode_a + β • mode_b ∧
    (generator rates).mulVec mode_b = -β • mode_a - α • mode_b := by
  sorry

private theorem trajectory_deriv (t : ℝ) :
    HasDerivAt trajectory ((generator rates).mulVec (trajectory t)) t := by
  sorry

private theorem endpoints :
    trajectory 0 = ![1/2, 1/4, 1/4] ∧
    trajectory time = ![(2-residual)/6, (4+residual)/12, (4+residual)/12] := by
  sorry

private theorem time_bounds : 0 < time ∧ 0 < residual ∧ residual < 1/4 := by
  sorry

private theorem total_rate : -(generator rates).trace = 303/100 := by
  sorry

private theorem steady_formula :
    binarySteadyState (1/2) ((2-residual)/6) (303/100) time =
      (2-3*residual)/(6*(1-residual)) := by
  sorry

private theorem steady_bounds (r : ℝ) (hr : 0 < r) (hb : r < 1/4) :
    0 < (2-3*r)/(6*(1-r)) ∧ (2-3*r)/(6*(1-r)) < 1 := by
  sorry

private theorem split_divergence (z : ℝ) :
    klDivergence ![z, (1-z)/2, (1-z)/2] uniform =
      klDivergence ![z, 1-z] ![1/3, 1-1/3] := by
  sorry

private theorem reference_change (x y s : ℝ)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1)
    (hs : 0 < s) (hs1 : s < 1) :
    (klDivergence ![x, 1-x] ![1/3, 1-1/3] -
      klDivergence ![y, 1-y] ![1/3, 1-1/3]) -
    (klDivergence ![x, 1-x] ![s, 1-s] -
      klDivergence ![y, 1-y] ![s, 1-s]) =
    (x-y) * Real.log (2*s/(1-s)) := by
  sorry

private theorem strict_violation (r : ℝ) (hr : 0 < r) (hb : r < 1/4) :
    klDivergence ![1/2, 1/4, 1/4] uniform -
      klDivergence ![(2-r)/6, (4+r)/12, (4+r)/12] uniform <
    klDivergence ![1/2, 1-1/2] ![(2-3*r)/(6*(1-r)), 1-(2-3*r)/(6*(1-r))] -
      klDivergence ![(2-r)/6, 1-(2-r)/6]
        ![(2-3*r)/(6*(1-r)), 1-(2-3*r)/(6*(1-r))] := by
  sorry

theorem result : ¬ claim := by
  intro h
  obtain ⟨ht, hr, hb⟩ := time_bounds
  obtain ⟨hp, hq⟩ := endpoints
  obtain ⟨hs, hs1⟩ := steady_bounds residual hr hb
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
  exact (not_le_of_gt (strict_violation residual hr hb)) (hh hs hs1)

end D5.S3.StatisticalMechanics.PseudoCoarseGrainedTradeoffRefutation
