/- GID: D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.claim; result=D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.result; claim=D5/S3/StatisticalMechanics/CrossCorrelationActivityBoundRefutation.claim
   digest: A hexagon with an equilibrium clique refutes the general-network activity bound. -/

import D5.S3.TotalVariation.CycleSingleCutMinimax

set_option autoImplicit false
set_option maxRecDepth 3000

namespace D5.S3.StatisticalMechanics.CrossCorrelationActivityBoundRefutation

open scoped BigOperators

noncomputable def flux {N : ℕ} (w : Fin N → Fin N → ℝ) (p : Fin N → ℝ)
    (m n : Fin N) : ℝ := if m = n then 0 else w m n * p n

noncomputable def activity {N : ℕ} (w : Fin N → Fin N → ℝ) (p : Fin N → ℝ) : ℝ :=
  ∑ m, ∑ n, flux w p m n

noncomputable def entropyRate {N : ℕ} (w : Fin N → Fin N → ℝ) (p : Fin N → ℝ) : ℝ :=
  ∑ m, ∑ n, if 0 < flux w p m n then
    flux w p m n * Real.log (flux w p m n / flux w p n m) else 0

noncomputable def scaleRatio {N : ℕ} (w : Fin N → Fin N → ℝ) (p : Fin N → ℝ) : ℝ :=
  let s := {x : ℝ | ∃ m n, x = flux w p m n ∧ 0 < x}
  sSup s / sInf s

noncomputable def asym {N : ℕ} (w : Fin N → Fin N → ℝ) (p a b : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ m, ∑ n, (a n * b m - a m * b n) * flux w p m n

noncomputable def diffusion {N : ℕ} (w : Fin N → Fin N → ℝ) (p a : Fin N → ℝ) : ℝ :=
  (1 / 2) * ∑ m, ∑ n, (a m - a n)^2 * flux w p m n

def IsStationaryNetwork {N : ℕ} (w : Fin N → Fin N → ℝ) (p : Fin N → ℝ) : Prop :=
  (∀ m n, 0 ≤ w m n) ∧
  (∀ m n, w m n ≠ 0 ↔ w n m ≠ 0) ∧
  D5.S3.TotalVariation.CycleSingleCutMinimax.Probability p ∧
  (∀ m, ∑ n, w m n * p n = (∑ k, w k m) * p m)

def claim : Prop :=
  ∀ (N : ℕ), 3 ≤ N → ∀ (w : Fin N → Fin N → ℝ) (p a b : Fin N → ℝ),
    IsStationaryNetwork w p → (∃ m n, 0 < flux w p m n) →
    0 < diffusion w p a * diffusion w p b →
    |asym w p a b| / Real.sqrt (diffusion w p a * diffusion w p b) ≤
      scaleRatio w p / Real.tan (Real.pi / N) *
        Real.sqrt (entropyRate w p / (2 * activity w p))

private def hex : Finset (Fin 16 × Fin 16) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (5, 0)}

private def clique : Finset (Fin 16 × Fin 16) :=
  {(0, 6), (0, 7), (0, 8), (0, 9), (0, 10), (0, 11), (0, 12), (0, 13),
    (0, 14), (0, 15), (6, 7), (6, 8), (6, 9), (6, 10), (6, 11), (6, 12),
    (6, 13), (6, 14), (6, 15), (7, 8), (7, 9), (7, 10), (7, 11), (7, 12),
    (7, 13), (7, 14), (7, 15), (8, 9), (8, 10), (8, 11), (8, 12), (8, 13),
    (8, 14), (8, 15), (9, 10), (9, 11), (9, 12), (9, 13), (9, 14), (9, 15),
    (10, 11), (10, 12), (10, 13), (10, 14), (10, 15), (11, 12), (11, 13), (11, 14),
    (11, 15), (12, 13), (12, 14), (12, 15), (13, 14), (13, 15), (14, 15)}

private def support : Finset (Fin 16 × Fin 16) :=
  (hex ∪ hex.image Prod.swap) ∪ (clique ∪ clique.image Prod.swap)

private noncomputable def rates (m n : Fin 16) : ℝ :=
  if n.val < 6 ∧ m.val = (n.val + 1) % 6 then 201/200
  else if m.val < 6 ∧ n.val = (m.val + 1) % 6 then 199/200
  else if m ≠ n ∧ (m.val = 0 ∨ 6 ≤ m.val) ∧ (n.val = 0 ∨ 6 ≤ n.val) then 1 else 0

private noncomputable def prob (_ : Fin 16) : ℝ := 1/16

private noncomputable def obsA : Fin 16 → ℝ :=
  ![1, 1/2, -1/2, -1, -1/2, 1/2,
    999/1000, 998/1000, 997/1000, 996/1000, 995/1000,
    994/1000, 993/1000, 992/1000, 991/1000, 990/1000]

private noncomputable def obsB : Fin 16 → ℝ :=
  ![0, Real.sqrt 3/2, Real.sqrt 3/2, 0, -Real.sqrt 3/2, -Real.sqrt 3/2,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

private theorem hex_mem : ∀ m n : Fin 16,
    (m, n) ∈ hex ↔ m.val < 6 ∧ n.val = (m.val + 1) % 6 := by decide

private theorem clique_mem : ∀ m n : Fin 16,
    (m, n) ∈ clique ↔ m < n ∧ (m.val = 0 ∨ 6 ≤ m.val) ∧
      (n.val = 0 ∨ 6 ≤ n.val) := by decide

private theorem rates_zero (m n : Fin 16) (h : (m, n) ∉ support) : rates m n = 0 := by
  have hm : (m, n) ∉ hex ∧ (n, m) ∉ hex ∧
      (m, n) ∉ clique ∧ (n, m) ∉ clique := by
    simpa [support.eq_1, and_assoc,
      and_comm, and_left_comm] using h
  rw [hex_mem] at hm
  rw [hex_mem] at hm
  rw [clique_mem] at hm
  rw [clique_mem] at hm
  simp only [rates.eq_1, if_neg hm.2.1, if_neg hm.1]
  split_ifs with hc
  · exfalso
    rcases lt_or_gt_of_ne hc.1 with hlt | hgt
    · exact hm.2.2.1 ⟨hlt, hc.2⟩
    · exact hm.2.2.2 ⟨hgt, hc.2.2, hc.2.1⟩
  · rfl

private theorem edge_sum (f : Fin 16 → Fin 16 → ℝ)
    (hz : ∀ m n, rates m n = 0 → f m n = 0) :
    ∑ m, ∑ n, f m n =
      (∑ e ∈ hex, (f e.1 e.2 + f e.2 e.1)) +
      ∑ e ∈ clique, (f e.1 e.2 + f e.2 e.1) := by
  change (∑ m, ∑ n, (fun e : Fin 16 × Fin 16 => f e.1 e.2) (m, n)) = _
  rw [← Fintype.sum_prod_type (fun e : Fin 16 × Fin 16 => f e.1 e.2)]
  calc
    ∑ e : Fin 16 × Fin 16, f e.1 e.2 = ∑ e ∈ support, f e.1 e.2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ support)
      intro e _ he
      exact hz e.1 e.2 (rates_zero e.1 e.2 he)
    _ = _ := by
      rw [support.eq_1, Finset.sum_union (by decide),
        Finset.sum_union (by decide), Finset.sum_union (by decide)]
      simp only [Finset.sum_image, Prod.swap_injective.injOn,
        Finset.sum_add_distrib, Prod.fst_swap, Prod.snd_swap]

private theorem diagonal_zero (m : Fin 16) : rates m m = 0 := by
  fin_cases m <;> norm_num [rates.eq_1]

private theorem flux_value (m n : Fin 16) : flux rates prob m n = rates m n / 16 := by
  by_cases h : m = n
  · subst n
    simp [flux.eq_1, diagonal_zero]
  · simp only [flux.eq_1, if_neg h, prob.eq_1, div_eq_mul_inv, one_mul]

set_option maxHeartbeats 2000000 in
private theorem stationary : IsStationaryNetwork rates prob := by
  refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro m n
    unfold rates
    split_ifs <;> norm_num
  · intro m n
    fin_cases m <;> fin_cases n <;> norm_num [rates.eq_1]
  · intro m
    norm_num [prob.eq_1]
  · norm_num [prob.eq_1, Fin.sum_univ_succ]
  · intro m
    fin_cases m <;> norm_num [rates.eq_1, prob.eq_1, Fin.sum_univ_succ, Fin.succ, Fin.ofNat, Fin.mk.injEq]

set_option maxHeartbeats 2000000 in
private theorem activity_value : activity rates prob = 61/8 := by
  unfold activity
  rw [edge_sum _ (by intro m n h; simp only [flux_value, h, zero_div])]
  simp (disch := decide) only [hex.eq_1, clique.eq_1, Finset.sum_insert, Finset.sum_singleton]
  norm_num [Fin.ext_iff, flux_value, rates.eq_1]

set_option maxHeartbeats 2000000 in
private theorem entropy_value : entropyRate rates prob =
    (3/800) * Real.log (201/199) := by
  have log_reverse : Real.log (199/201 : ℝ) = -Real.log (201/199) := by
    rw [show (199/201 : ℝ) = (201/199)⁻¹ by norm_num, Real.log_inv]
  unfold entropyRate
  rw [edge_sum _ (by intro m n h; simp only [flux_value, h, zero_div, lt_self_iff_false, if_false])]
  simp (disch := decide) only [hex.eq_1, clique.eq_1, Finset.sum_insert, Finset.sum_singleton]
  norm_num [Fin.ext_iff, flux_value, rates.eq_1, log_reverse]
  ring

set_option maxHeartbeats 2000000 in
private theorem asym_value : asym rates prob obsA obsB = 3 * Real.sqrt 3 / 3200 := by
  unfold asym
  rw [edge_sum _ (by intro m n h; simp only [flux_value, h, zero_div, mul_zero])]
  simp (disch := decide) only [hex.eq_1, clique.eq_1, Finset.sum_insert, Finset.sum_singleton]
  simp only [obsA.eq_1, obsB.eq_1]
  dsimp only [Matrix.cons_val]
  norm_num [Fin.ext_iff, flux_value, rates.eq_1]
  ring

set_option maxHeartbeats 2000000 in
private theorem diffusion_a_value : diffusion rates prob obsA = 300121/1600000 := by
  unfold diffusion
  rw [edge_sum _ (by intro m n h; simp only [flux_value, h, zero_div, mul_zero])]
  simp (disch := decide) only [hex.eq_1, clique.eq_1, Finset.sum_insert, Finset.sum_singleton]
  simp only [obsA.eq_1]
  dsimp only [Matrix.cons_val]
  norm_num [Fin.ext_iff, flux_value, rates.eq_1]

set_option maxHeartbeats 2000000 in
private theorem diffusion_b_value : diffusion rates prob obsB = 3/16 := by
  unfold diffusion
  rw [edge_sum _ (by intro m n h; simp only [flux_value, h, zero_div, mul_zero])]
  simp (disch := decide) only [hex.eq_1, clique.eq_1, Finset.sum_insert, Finset.sum_singleton]
  simp only [obsB.eq_1]
  dsimp only [Matrix.cons_val]
  norm_num [Fin.ext_iff, flux_value, rates.eq_1]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

private theorem flux_bounds (m n : Fin 16) (h : 0 < flux rates prob m n) :
    199/3200 ≤ flux rates prob m n ∧ flux rates prob m n ≤ 201/3200 := by
  rw [flux_value] at h ⊢
  simp only [rates.eq_1] at h ⊢
  split_ifs at h ⊢ <;> norm_num at *

private theorem ratio_value : scaleRatio rates prob = 201/199 := by
  have hmax : IsGreatest {x : ℝ | ∃ m n, x = flux rates prob m n ∧ 0 < x}
      (201/3200) := by
    refine ⟨⟨1, 0, ?_, by norm_num⟩, ?_⟩
    · norm_num [flux_value, rates.eq_1]
    · rintro x ⟨m, n, rfl, hx⟩
      exact (flux_bounds m n hx).2
  have hmin : IsLeast {x : ℝ | ∃ m n, x = flux rates prob m n ∧ 0 < x}
      (199/3200) := by
    refine ⟨⟨0, 1, ?_, by norm_num⟩, ?_⟩
    · norm_num [flux_value, rates.eq_1]
    · rintro x ⟨m, n, rfl, hx⟩
      exact (flux_bounds m n hx).1
  simp only [scaleRatio.eq_1]
  rw [hmax.csSup_eq, hmin.csInf_eq]
  norm_num

private theorem numerical_violation :
    ¬ (|3 * Real.sqrt 3 / 3200| /
      Real.sqrt ((300121/1600000) * (3/16)) ≤
    (201/199) / Real.tan (Real.pi / 16) *
      Real.sqrt (((3/800) * Real.log (201/199)) / (2 * (61/8)))) := by
  have tangent_lower : (3 : ℝ)/16 < Real.tan (Real.pi / 16) := by
    exact lt_trans (by linarith [Real.pi_gt_three])
      (Real.lt_tan (by positivity) (by linarith [Real.pi_pos]))
  have tangent_pos : 0 < Real.tan (Real.pi / 16) := by linarith
  have gamma_pos : 0 ≤ (201/199 : ℝ) / Real.tan (Real.pi / 16) := by positivity
  have gamma_bound : (201/199 : ℝ) / Real.tan (Real.pi / 16) < 1072/199 := by
    apply (div_lt_iff₀ tangent_pos).2
    nlinarith
  have log_bound : Real.log (201/199 : ℝ) < 2/199 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 201/199)
      (by norm_num : (201/199 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have log_nonneg : 0 ≤ Real.log (201/199 : ℝ) :=
    le_of_lt (Real.log_pos (by norm_num))
  have left_square : (|3 * Real.sqrt 3 / 3200| /
      Real.sqrt ((300121/1600000) * (3/16)))^2 = (45/600242 : ℝ) := by
    norm_num [div_pow, mul_pow, Real.sq_sqrt, sq_abs]
  have right_square :
      ((201/199) / Real.tan (Real.pi / 16) *
        Real.sqrt (((3/800) * Real.log (201/199)) / (2 * (61/8))))^2 =
      ((201/199) / Real.tan (Real.pi / 16))^2 *
        (3/12200 * Real.log (201/199)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  have gamma_square : ((201/199 : ℝ) / Real.tan (Real.pi / 16))^2 < (1072/199)^2 := by
    nlinarith
  have right_bound : ((201/199 : ℝ) / Real.tan (Real.pi / 16))^2 *
      (3/12200 * Real.log (201/199)) < (1072/199)^2 * (3/12200 * (2/199)) := by
    calc
      _ ≤ (1072/199 : ℝ)^2 * (3/12200 * Real.log (201/199)) :=
        mul_le_mul_of_nonneg_right gamma_square.le (by positivity)
      _ < _ := mul_lt_mul_of_pos_left (by nlinarith) (by norm_num)
  intro h
  have squared := mul_self_le_mul_self (by positivity :
    (0 : ℝ) ≤ |3 * Real.sqrt 3 / 3200| /
      Real.sqrt ((300121/1600000) * (3/16))) h
  rw [← sq, ← sq, left_square, right_square] at squared
  norm_num at right_bound
  linarith

theorem result : ¬ claim := by
  intro h
  have positive_flux : ∃ m n, 0 < flux rates prob m n := by
    exact ⟨1, 0, by norm_num [flux_value, rates.eq_1]⟩
  have positive_diffusion : 0 < diffusion rates prob obsA * diffusion rates prob obsB := by
    rw [diffusion_a_value, diffusion_b_value]
    norm_num
  have bound := h 16 (by decide) rates prob obsA obsB stationary
    positive_flux positive_diffusion
  rw [asym_value, diffusion_a_value, diffusion_b_value, ratio_value,
    entropy_value, activity_value] at bound
  exact numerical_violation bound

end D5.S3.StatisticalMechanics.CrossCorrelationActivityBoundRefutation
