/- GID: D5/S3/Estimation/TimeArrow/NativeRowCountTail
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRowCountTail
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exponential tail budgets for actual compensated departure counts. -/

import D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Estimation.TimeArrow.NativeRowCountTail
noncomputable section

private theorem path_fourth_moment {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hLM : (L : ℝ) / M ≤ 1 / 45) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) .path, probability r .path S o *
      (4 : ℝ) ^ (count .path o i 1 + count .path o i (-1))) ≤
        3 * Real.exp (3 * (L : ℝ)) := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb : |b r S (.inl i)| ≤ 1 := by
    rw [abs_le]
    simp only [b]
    split_ifs <;> constructor <;> linarith
  let η : ℝ := 3 / (2 * M)
  have hη : 0 ≤ η := by dsimp [η]; positivity
  have hη1 : η ≤ 1 / 4 := by
    dsimp [η]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * M)).mpr
    have hh : (6 : ℝ) ≤ M := by exact_mod_cast hM6
    linarith
  have hA : driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) =
      (3 : ℂ) / (2 * M) := by norm_num [driftA, tiltU, tiltV]
  have hB : driftB r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) =
      ((b r S (.inl i) : ℂ) * 3) / (2 * M) := by norm_num [driftB, tiltU, tiltV]
  have hAn : ‖driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)‖ ≤ η := by
    rw [hA, norm_div, norm_mul, Complex.norm_natCast]
    norm_num [η, abs_of_pos hM]
  have hBn : ‖driftB r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)‖ ≤ η := by
    rw [hB, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_natCast]
    norm_num
    exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hTη : ((2 * M * L : ℕ) : ℝ) * η ^ 2 = (9 / 2) * ((L : ℝ) / M) := by
    dsimp [η]
    push_cast
    field_simp
    <;> ring
  have hT : ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 1 / 10 := by
    rw [hTη]
    nlinarith
  have hh := actual_marked_path_pgf_poisson_envelope hq hqm hr hr1 hc1 S
    (Or.inl rfl) (fun _ : Fin 1 => i) (fun a b _ => Subsingleton.elim a b)
    (fun _ => 4) (fun _ => 4) hη hη1 hAn hBn hT
  let Z : ℝ := ∑ o : Obs M (2 * M * L) .path, probability r .path S o *
      (4 : ℝ) ^ (count .path o i 1 + count .path o i (-1))
  have hZ : actualPGF r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)
      (2 * M * L) = (Z : ℂ) := by
    simp [actualPGF, Z, pow_add]
  have htA : ((2 * M * L : ℕ) : ℂ) *
      driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) = (3 * (L : ℝ) : ℝ) := by
    rw [hA]
    push_cast
    field_simp
    <;> ring
  have htre : ((2 * M * L : ℕ) : ℝ) *
      (driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)).re = 3 * (L : ℝ) := by
    have he := congrArg Complex.re htA
    simpa using he
  rw [hZ, htA, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, htre] at hh
  have hcoef : 20 * ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 2 := by
    nlinarith
  have he := hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
  have hu := (abs_le.mp he).2
  change Z ≤ _
  linarith

private theorem pair_fourth_moment {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) .pair, probability r .pair S o *
      (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1))) ≤
        Real.exp (3 * (L : ℝ)) := by
  classical
  have hM : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hlaw := finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 Experiment.pair
  have hrow := (hlaw.1 S).1.2
  let g := fun p : Vertex M × Vertex M => if p.1 = .inl i then (4 : ℝ) else 1
  have hedge (x y : Vertex M) :
      (if x = .inl i ∧ chi y = 1 then (4 : ℝ) else 1) *
        (if x = .inl i ∧ chi y = -1 then (4 : ℝ) else 1) = g (x, y) := by
    cases y <;> by_cases hx : x = .inl i <;> norm_num [g, chi, hx]
  have hcount (o : Obs M (2 * M * L) .pair) :
      (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), g (o k) := by
    rw [pow_add]
    have hp : (4 : ℝ) ^ count .pair o i 1 =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = 1 then 4 else 1 := by
      simp [prod_ite, prod_const, count, edges]
      rfl
    have hm : (4 : ℝ) ^ count .pair o i (-1) =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = -1 then 4 else 1 := by
      simp [prod_ite, prod_const, count, edges]
      rfl
    rw [hp, hm, ← prod_mul_distrib]
    exact prod_congr rfl fun k _ => hedge _ _
  let K := fun p : Vertex M × Vertex M =>
    (2 * (M : ℝ))⁻¹ * transition r S p.1 p.2 * g p
  have hsum : (∑ p : Vertex M × Vertex M, K p) = 1 + 3 / (2 * M) := by
    rw [Fintype.sum_prod_type]
    have hx (x : Vertex M) : (∑ y : Vertex M, K (x, y)) =
        (2 * (M : ℝ))⁻¹ * (if x = .inl i then 4 else 1) := by
      dsimp [K, g]
      calc
        _ = ((2 * (M : ℝ))⁻¹ * (if x = .inl i then 4 else 1)) *
            ∑ y : Vertex M, transition r S x y := by
          rw [mul_sum]
          apply sum_congr rfl
          intro y _
          ring
        _ = _ := by rw [hrow x, mul_one]
    simp_rw [hx]
    rw [← mul_sum]
    have he : (∑ x : Vertex M, if x = .inl i then (4 : ℝ) else 1) = 2 * M + 3 := by
      have hh (x : Vertex M) : (if x = .inl i then (4 : ℝ) else 1) =
          1 + if x = .inl i then 3 else 0 := by split_ifs <;> norm_num
      simp_rw [hh]
      simp [sum_add_distrib, Fintype.card_sum, Fintype.card_fin]
      ring
    rw [he]
    field_simp
    <;> ring
  have hmass (o : Obs M (2 * M * L) .pair) :
      probability r .pair S o * (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), K (o k) := by
    rw [hcount]
    simp [probability, K, prod_mul_distrib]
  simp_rw [hmass]
  change (∑ o : Fin (2 * M * L) → Vertex M × Vertex M, ∏ k, K (o k)) ≤ _
  rw [← Fintype.prod_sum (fun (_ : Fin (2 * M * L)) p => K p)]
  simp_rw [hsum]
  simp only [prod_const, card_univ, Fintype.card_fin]
  calc
    (1 + 3 / (2 * (M : ℝ))) ^ (2 * M * L) ≤
        (Real.exp (3 / (2 * M))) ^ (2 * M * L) :=
      pow_le_pow_left₀ (by positivity)
        (by simpa only [add_comm] using Real.add_one_le_exp (3 / (2 * (M : ℝ)))) _
    _ = Real.exp (3 * (L : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
      <;> ring

/-- An exponential budget holds under each original complete-history law.
The path estimate retains adjacent visits and all terminal coordinates. -/
theorem native_row_count_tail {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hL : 1 ≤ L) (hLM : (L : ℝ) / M ≤ 1 / 45)
    (e : Experiment) (i : Fin M) :
    (∑ o : Obs M (2 * M * L) e,
      if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) ≤
        Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hp := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S
  have hmgf : (∑ o : Obs M (2 * M * L) e, probability r e S o *
      (4 : ℝ) ^ (count e o i 1 + count e o i (-1))) ≤ 3 * Real.exp (3 * (L : ℝ)) := by
    cases e
    · exact (pair_fourth_moment r S hq hqm hr hr1 hc1 i).trans
        (by nlinarith [Real.exp_pos (3 * (L : ℝ))])
    · exact path_fourth_moment r S hq hqm hr hr1 hc1 hM6 hLM i
  have hmarkov : (4 : ℝ) ^ (8 * L) *
      (∑ o : Obs M (2 * M * L) e,
        if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) ≤
      ∑ o : Obs M (2 * M * L) e, probability r e S o *
        (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro o _
    split_ifs with ho
    · have hh : (4 : ℝ) ^ (8 * L) ≤
          (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) :=
        pow_le_pow_right₀ (by norm_num) (by omega)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (hp o)
    · simp only [mul_zero]
      exact mul_nonneg (hp o) (pow_nonneg (by norm_num) _)
  have h3 : 3 ≤ Real.exp (3 * (L : ℝ)) := by
    have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hh := Real.add_one_le_exp (3 * (L : ℝ))
    linarith
  have hb : 3 * Real.exp (3 * (L : ℝ)) ≤ Real.exp (6 * (L : ℝ)) := by
    rw [show 6 * (L : ℝ) = 3 * L + 3 * L by ring, Real.exp_add]
    exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
  have hpow : (4 : ℝ) ^ (8 * L) = Real.exp (8 * (L : ℝ) * Real.log 4) := by
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
  have htotal := hmarkov.trans (hmgf.trans hb)
  rw [hpow] at htotal
  calc
    _ ≤ Real.exp (6 * (L : ℝ)) / Real.exp (8 * (L : ℝ) * Real.log 4) :=
      (le_div_iff₀ (Real.exp_pos _)).mpr (by simpa only [mul_comm] using htotal)
    _ = _ := by rw [← Real.exp_sub]; congr 1; ring

/-- A single all-row cutoff preserves all original rows and pays the union
budget, uniformly in the true support and in the experiment. -/
theorem native_all_row_count_cut {M q L : ℕ} (r : ℝ) (S : Support M q)
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (hM6 : 6 ≤ M)
    (hL : 1 ≤ L) (hLM : (L : ℝ) / M ≤ 1 / 45) (e : Experiment) :
    (∑ o : Obs M (2 * M * L) e,
      if ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
      then probability r e S o else 0) ≥
        1 - (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have law := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1
  have hp := law.1 S
  have hsum := law.2 S
  have hpoint (o : Obs M (2 * M * L) e) :
      (if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
       then probability r e S o else 0) ≤
        ∑ i : Fin M, if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := by
    by_cases ho : ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
    · rw [if_neg (not_not.mpr ho)]
      apply sum_nonneg
      intro i _
      split_ifs <;> [exact hp o; exact le_rfl]
    · rw [if_pos ho]
      push_neg at ho
      obtain ⟨i, hi⟩ := ho
      have hh := single_le_sum (f := fun j : Fin M =>
        if 8 * L < count e o j 1 + count e o j (-1) then probability r e S o else 0)
        (fun j _ => by split_ifs <;> [exact hp o; exact le_rfl]) (mem_univ i)
      simpa only [if_pos hi] using hh
  have hbad : (∑ o : Obs M (2 * M * L) e,
      if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
      then probability r e S o else 0) ≤
        (M : ℝ) * Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
    calc
      _ ≤ ∑ o : Obs M (2 * M * L) e, ∑ i : Fin M,
          if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := sum_le_sum fun o _ => hpoint o
      _ = ∑ i : Fin M, ∑ o : Obs M (2 * M * L) e,
          if 8 * L < count e o i 1 + count e o i (-1)
          then probability r e S o else 0 := sum_comm
      _ ≤ ∑ _i : Fin M, Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) :=
        sum_le_sum fun i _ => native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i
      _ = _ := by simp
  have hpartition :
      (∑ o : Obs M (2 * M * L) e,
        if ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
        then probability r e S o else 0) +
      (∑ o : Obs M (2 * M * L) e,
        if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
        then probability r e S o else 0) = 1 := by
    rw [← sum_add_distrib, ← hsum]
    apply sum_congr rfl
    intro o _
    split_ifs <;> simp_all only [not_true_eq_false, not_false_eq_true,
      add_zero, zero_add]
  linarith

end
end D5.S3.Estimation.TimeArrow.NativeRowCountTail
