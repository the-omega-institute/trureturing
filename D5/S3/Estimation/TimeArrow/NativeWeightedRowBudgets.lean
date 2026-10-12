/- GID: D5/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeWeightedRowBudgets
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite native row transfer restores both actual and reference tails. -/
import D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative
import D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative
set_option autoImplicit false
set_option relaxedAutoImplicit false
open D5.S3.Estimation.TimeArrow.NativeSignalConditionalFiber
open D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
set_option backward.isDefEq.respectTransparency false
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
    rw [abs_le]; simp only [b]
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
    rw [hA, norm_div, norm_mul, Complex.norm_natCast]; norm_num [η, abs_of_pos hM]
  have hBn : ‖driftB r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)‖ ≤ η := by
    rw [hB, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_natCast]
    norm_num; exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hTη : ((2 * M * L : ℕ) : ℝ) * η ^ 2 = (9 / 2) * ((L : ℝ) / M) := by
    dsimp [η]
    push_cast
    field_simp <;> ring
  have hT : ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 1 / 10 := by
    rw [hTη]; nlinarith
  have hh := actual_marked_path_pgf_poisson_envelope hq hqm hr hr1 hc1 S
    (Or.inl rfl) (fun _ : Fin 1 => i) (fun a b _ => Subsingleton.elim a b)
    (fun _ => 4) (fun _ => 4) hη hη1 hAn hBn hT
  let Z : ℝ := ∑ o : Obs M (2 * M * L) .path, probability r .path S o * (4 : ℝ) ^ (count .path o i 1 + count .path o i (-1))
  have hZ : actualPGF r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)
      (2 * M * L) = (Z : ℂ) := by simp [actualPGF, Z, pow_add]
  have htA : ((2 * M * L : ℕ) : ℂ) *
      driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4) = (3 * (L : ℝ) : ℝ) := by
    rw [hA]
    push_cast
    field_simp <;> ring
  have htre : ((2 * M * L : ℕ) : ℝ) *
      (driftA r S (fun _ : Fin 1 => i) (fun _ => 4) (fun _ => 4)).re = 3 * (L : ℝ) := by
    have he := congrArg Complex.re htA
    simpa using he
  rw [hZ, htA, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, htre] at hh
  have hcoef : 20 * ((2 * M * L : ℕ) : ℝ) * η ^ 2 ≤ 2 := by nlinarith
  have he := hh.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le)
  have hu := (abs_le.mp he).2
  change Z ≤ _; linarith
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
  have hedge (x y : Vertex M) : (if x = .inl i ∧ chi y = 1 then (4 : ℝ) else 1) *
        (if x = .inl i ∧ chi y = -1 then (4 : ℝ) else 1) = g (x, y) := by
    cases y <;> by_cases hx : x = .inl i <;> norm_num [g, chi, hx]
  have hcount (o : Obs M (2 * M * L) .pair) : (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), g (o k) := by
    rw [pow_add]
    have hp : (4 : ℝ) ^ count .pair o i 1 =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = 1 then 4 else 1 := by simp [prod_ite, prod_const, count, edges]
    have hm : (4 : ℝ) ^ count .pair o i (-1) =
        ∏ k : Fin (2 * M * L), if (o k).1 = .inl i ∧ chi (o k).2 = -1 then 4 else 1 := by
      simp [prod_ite, prod_const, count, edges]
    rw [hp, hm, ← prod_mul_distrib]; exact prod_congr rfl fun k _ => hedge _ _
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
      simp [sum_add_distrib, Fintype.card_sum, Fintype.card_fin]; ring
    rw [he]
    field_simp <;> ring
  have hmass (o : Obs M (2 * M * L) .pair) : probability r .pair S o * (4 : ℝ) ^ (count .pair o i 1 + count .pair o i (-1)) =
        ∏ k : Fin (2 * M * L), K (o k) := by
    rw [hcount]; simp [probability, K, prod_mul_distrib]
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
      field_simp <;> ring
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
    · exact (pair_fourth_moment r S hq hqm hr hr1 hc1 i).trans (by nlinarith [Real.exp_pos (3 * (L : ℝ))])
    · exact path_fourth_moment r S hq hqm hr hr1 hc1 hM6 hLM i
  have hmarkov : (4 : ℝ) ^ (8 * L) * (∑ o : Obs M (2 * M * L) e,
        if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) ≤
      ∑ o : Obs M (2 * M * L) e, probability r e S o *
        (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) := by
    rw [mul_sum]
    apply sum_le_sum
    intro o _
    split_ifs with ho
    · have hh : (4 : ℝ) ^ (8 * L) ≤ (4 : ℝ) ^ (count e o i 1 + count e o i (-1)) := pow_le_pow_right₀ (by norm_num) (by omega)
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (hp o)
    · simp only [mul_zero]
      exact mul_nonneg (hp o) (pow_nonneg (by norm_num) _)
  have h3 : 3 ≤ Real.exp (3 * (L : ℝ)) := by
    have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hh := Real.add_one_le_exp (3 * (L : ℝ))
    linarith
  have hb : 3 * Real.exp (3 * (L : ℝ)) ≤ Real.exp (6 * (L : ℝ)) := by
    rw [show 6 * (L : ℝ) = 3 * L + 3 * L by ring, Real.exp_add]; exact mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
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
  have hpoint (o : Obs M (2 * M * L) e) : (if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
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
  have hbad : (∑ o : Obs M (2 * M * L) e, if ¬∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
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
  have hpartition : (∑ o : Obs M (2 * M * L) e, if ∀ i : Fin M, count e o i 1 + count e o i (-1) ≤ 8 * L
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
namespace D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
noncomputable section
/-- The reference mass uses the native compensated row drift. -/
def rowReference {M q : ℕ} (S : Support M q) (r : ℝ) (L : ℕ)
    (i : Fin M) (c : ℕ × ℕ) : ℝ :=
  (Real.exp (-((L : ℝ) * (1 + b r S (.inl i)) / 2)) *
      ((L : ℝ) * (1 + b r S (.inl i)) / 2) ^ c.1 / c.1.factorial) *
    (Real.exp (-((L : ℝ) * (1 - b r S (.inl i)) / 2)) *
      ((L : ℝ) * (1 - b r S (.inl i)) / 2) ^ c.2 / c.2.factorial)
/-- A deterministic row function restricted to a finite count set. -/
def truncatedRow {M s : ℕ} (e : Experiment) (D : Finset (ℕ × ℕ))
    (g : Fin M → ℕ × ℕ → ℝ) (i : Fin M) (o : Obs M s e) : ℝ :=
  ∑ c ∈ D, if count e o i 1 = c.1 ∧ count e o i (-1) = c.2 then g i c else 0
theorem reference_pos {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (c : ℕ × ℕ) : 0 < rowReference S r L i c := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb : -(1 - κ) ≤ b r S (.inl i) ∧ b r S (.inl i) ≤ 1 - κ := by
    simp only [b]
    split_ifs <;> constructor <;> linarith
  have hp : 0 < (L : ℝ) * (1 + b r S (.inl i)) / 2 := div_pos (mul_pos hLpos (by linarith [hb.1])) (by norm_num)
  have hm : 0 < (L : ℝ) * (1 - b r S (.inl i)) / 2 := div_pos (mul_pos hLpos (by linarith [hb.2])) (by norm_num)
  unfold rowReference; exact mul_pos (div_pos (mul_pos (Real.exp_pos _) (pow_pos hp _)) (by positivity))
    (div_pos (mul_pos (Real.exp_pos _) (pow_pos hm _)) (by positivity))
private theorem multiply_relative {P Q δ : ℝ} (hQ : 0 < Q)
    (h : |P / Q - 1| ≤ δ) : |P - Q| ≤ δ * Q := by
  have he : P - Q = (P / Q - 1) * Q := by field_simp
  rw [he, abs_mul, abs_of_pos hQ]; exact mul_le_mul_of_nonneg_right h hQ.le
private theorem native_point_transfer (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ →
        ∀ (S : Support M q) (e : Experiment) (i : Fin M) (c : ℕ × ℕ),
          (c.1 : ℝ) ≤ 8 * L → (c.2 : ℝ) ≤ 8 * L →
          (|((∑ o : Obs M (2 * M * L) e,
              if count e o i 1 = c.1 ∧ count e o i (-1) = c.2
              then probability r e S o else 0) - rowReference S r L i c)| ≤
            (A * (L : ℝ) ^ 2 / M) * rowReference S r L i c) ∧
          ∀ (j : Fin M) (d : ℕ × ℕ), i ≠ j →
            (d.1 : ℝ) ≤ 8 * L → (d.2 : ℝ) ≤ 8 * L →
            |((∑ o : Obs M (2 * M * L) e,
                if (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ∧
                   (count e o j 1 = d.1 ∧ count e o j (-1) = d.2)
                then probability r e S o else 0) -
              rowReference S r L i c * rowReference S r L j d)| ≤
              (A * (L : ℝ) ^ 3 / M) *
                (rowReference S r L i c * rowReference S r L j d) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := actual_marked_count_poisson_relative κ 8 hκ hκ1 (by norm_num)
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c hc1 hc2
  have hQc := reference_pos S r κ hκ hr hrκ hcκ hL i c
  constructor
  · have hh := h M q L 1 r hMM hq hqm hr hrκ hcκ hL hLη (Or.inl rfl) S (fun _ => i) (fun a b _ => Subsingleton.elim a b)
      (fun _ => c.1) (fun _ => c.2) (fun _ => ⟨hc1, hc2⟩) e
    simp only [Fin.prod_univ_one, Fin.forall_fin_one] at hh; exact multiply_relative hQc hh
  · intro j d hij hd1 hd2
    let m : Fin 2 → Fin M := ![i, j]
    have hm : Function.Injective m := by
      intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact False.elim (hij hab)
      · exact False.elim (hij hab.symm)
      · rfl
    have hn : ∀ a : Fin 2, ((![c.1, d.1] a : ℕ) : ℝ) ≤ 8 * L ∧
        ((![c.2, d.2] a : ℕ) : ℝ) ≤ 8 * L := by
      intro a; fin_cases a
      · exact ⟨hc1, hc2⟩
      · exact ⟨hd1, hd2⟩
    have hh := h M q L 2 r hMM hq hqm hr hrκ hcκ hL hLη (Or.inr rfl) S m hm ![c.1, d.1] ![c.2, d.2] hn e
    simp only [Fin.prod_univ_two, Fin.forall_fin_two, m, Matrix.cons_val_zero, Matrix.cons_val_one] at hh
    exact multiply_relative (mul_pos hQc (reference_pos S r κ hκ hr hrκ hcκ hL j d)) hh
private theorem weighted_relative_sum {α : Type*} (D : Finset α)
    (P Q g : α → ℝ) (δ : ℝ) (hg : ∀ c ∈ D, 0 ≤ g c)
    (h : ∀ c ∈ D, |P c - Q c| ≤ δ * Q c) :
    |(∑ c ∈ D, g c * P c) - ∑ c ∈ D, g c * Q c| ≤
      δ * ∑ c ∈ D, g c * Q c := by
  rw [← sum_sub_distrib]
  calc
    |∑ c ∈ D, (g c * P c - g c * Q c)| ≤
        ∑ c ∈ D, |g c * P c - g c * Q c| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ D, δ * (g c * Q c) := by
      apply sum_le_sum
      intro c hc
      rw [← mul_sub, abs_mul, abs_of_nonneg (hg c hc)]
      simpa only [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left (h c hc) (hg c hc)
    _ = δ * ∑ c ∈ D, g c * Q c := (mul_sum ..).symm
private theorem truncated_bounds {M s : ℕ} (e : Experiment)
    (D : Finset (ℕ × ℕ)) (g : Fin M → ℕ × ℕ → ℝ)
    (hg : ∀ i c, c ∈ D → 0 ≤ g i c ∧ g i c ≤ 1)
    (i : Fin M) (o : Obs M s e) :
    0 ≤ truncatedRow e D g i o ∧ truncatedRow e D g i o ≤ 1 := by
  classical
  let c := (count e o i 1, count e o i (-1))
  have hi : truncatedRow e D g i o = if c ∈ D then g i c else 0 := by
    unfold truncatedRow
    simp_rw [show ∀ d : ℕ × ℕ,
      (count e o i 1 = d.1 ∧ count e o i (-1) = d.2) ↔ d = c by
      intro d; simp [c, Prod.ext_iff, eq_comm]]
    simp
  rw [hi]
  split_ifs with hc
  · exact hg i c hc
  · norm_num
private theorem truncated_expectation {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (D : Finset (ℕ × ℕ)) (g : Fin M → ℕ × ℕ → ℝ) (i : Fin M) :
    (∑ o : Obs M s e, probability r e S o * truncatedRow e D g i o) =
      ∑ c ∈ D, g i c * (∑ o : Obs M s e,
        if count e o i 1 = c.1 ∧ count e o i (-1) = c.2
        then probability r e S o else 0) := by
  classical
  simp only [truncatedRow, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  apply sum_congr rfl
  intro o _
  split_ifs <;> ring
private theorem truncated_product_expectation {M q s : ℕ} (S : Support M q) (r : ℝ)
    (e : Experiment) (D : Finset (ℕ × ℕ)) (g : Fin M → ℕ × ℕ → ℝ) (i j : Fin M) :
    (∑ o : Obs M s e, probability r e S o *
        (truncatedRow e D g i o * truncatedRow e D g j o)) =
      ∑ c ∈ D, ∑ d ∈ D, (g i c * g j d) * (∑ o : Obs M s e,
        if (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ∧
           (count e o j 1 = d.1 ∧ count e o j (-1) = d.2)
        then probability r e S o else 0) := by
  classical
  have he (o : Obs M s e) : probability r e S o * (truncatedRow e D g i o * truncatedRow e D g j o) =
      ∑ c ∈ D, ∑ d ∈ D, probability r e S o *
        ((if count e o i 1 = c.1 ∧ count e o i (-1) = c.2 then g i c else 0) *
          (if count e o j 1 = d.1 ∧ count e o j (-1) = d.2 then g j d else 0)) := by
    unfold truncatedRow
    rw [sum_mul]
    simp_rw [mul_sum]
  simp_rw [he, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro c _
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro o _
  by_cases hi : count e o i 1 = c.1 ∧ count e o i (-1) = c.2 <;>
    by_cases hj : count e o j 1 = d.1 ∧ count e o j (-1) = d.2 <;>
    simp [hi, hj] <;> ring
private theorem finite_weighted_moments {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (I : Finset ι) (p : Ω → ℝ) (X : ι → Ω → ℝ) (a : ι → ℝ)
    (δ₁ δ₂ : ℝ) (hp : ∀ o, 0 ≤ p o) (hsum : ∑ o, p o = 1)
    (ha : ∀ i ∈ I, 0 ≤ a i)
    (hX : ∀ i ∈ I, ∀ o, 0 ≤ X i o ∧ X i o ≤ 1)
    (hδ₁ : δ₁ ≤ 1 / 2) (hδ₂ : 0 ≤ δ₂) (hδ : δ₁ ≤ δ₂)
    (hmean : ∀ i ∈ I, |(∑ o, p o * X i o) - a i| ≤ δ₁ * a i)
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      (∑ o, p o * (X i o * X j o)) ≤ (1 + δ₂) * (a i * a j)) :
    |(∑ o, p o * ∑ i ∈ I, X i o) - ∑ i ∈ I, a i| ≤ δ₁ * ∑ i ∈ I, a i ∧
    (∑ o, p o * ((∑ i ∈ I, X i o) - ∑ i ∈ I, a i) ^ 2) ≤
      (3 / 2) * (∑ i ∈ I, a i) + 3 * δ₂ * (∑ i ∈ I, a i) ^ 2 := by
  classical
  let A := ∑ i ∈ I, a i
  let Z := fun o => ∑ i ∈ I, X i o
  let E := fun f : Ω → ℝ => ∑ o, p o * f o
  have hA : 0 ≤ A := sum_nonneg ha
  have hEZ : E Z = ∑ i ∈ I, E (X i) := by
    dsimp [E, Z]
    simp_rw [mul_sum]
    rw [sum_comm]
  have hm : |E Z - A| ≤ δ₁ * A := by
    rw [hEZ]
    dsimp [A]
    rw [← sum_sub_distrib]; exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hmean).trans_eq (mul_sum ..).symm)
  have hmlo : (1 - δ₁) * A ≤ E Z := by
    have := (abs_le.mp hm).1
    nlinarith
  have hmhi : E Z ≤ (1 + δ₁) * A := by
    have := (abs_le.mp hm).2
    nlinarith
  have hproduct (i : ι) (hi : i ∈ I) (j : ι) (hj : j ∈ I) : E (fun o => X i o * X j o) ≤
        (if i = j then E (X i) else 0) + (1 + δ₂) * (a i * a j) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hd : E (fun o => X i o * X i o) ≤ E (X i) := by
        apply sum_le_sum
        intro o _
        apply mul_le_mul_of_nonneg_left _ (hp o)
        nlinarith [(hX i hi o).1, (hX i hi o).2]
      exact hd.trans (le_add_of_nonneg_right (mul_nonneg (by linarith) (mul_nonneg (ha i hi) (ha i hi))))
    · rw [if_neg hij, zero_add]
      exact hpair i hi j hj hij
  have hsecond : E (fun o => (Z o) ^ 2) ≤ E Z + (1 + δ₂) * A ^ 2 := by
    have he : E (fun o => (Z o) ^ 2) =
        ∑ i ∈ I, ∑ j ∈ I, E (fun o => X i o * X j o) := by
      dsimp [E, Z]; simp only [pow_two, sum_mul, mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro i _
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      apply sum_congr rfl
      intro o _
      ring
    rw [he]
    calc
      (∑ i ∈ I, ∑ j ∈ I, E (fun o => X i o * X j o)) ≤
          ∑ i ∈ I, ∑ j ∈ I,
            ((if i = j then E (X i) else 0) + (1 + δ₂) * (a i * a j)) :=
        sum_le_sum fun i hi => sum_le_sum fun j hj => hproduct i hi j hj
      _ = E Z + (1 + δ₂) * A ^ 2 := by
        simp only [sum_add_distrib]
        have hi (i : ι) (hi : i ∈ I) : (∑ j ∈ I, if i = j then E (X i) else 0) =
            E (X i) := by simp [← eq_comm, hi]
        rw [sum_congr rfl hi, ← hEZ]
        congr 1
        dsimp [A]
        simp_rw [← mul_sum, ← sum_mul]
        ring
  have hcenter : E (fun o => (Z o - A) ^ 2) =
      E (fun o => (Z o) ^ 2) - 2 * A * E Z + A ^ 2 := by
    dsimp [E]
    calc
      (∑ o, p o * (Z o - A) ^ 2) =
          ∑ o, (p o * (Z o) ^ 2 - 2 * A * (p o * Z o) + p o * A ^ 2) := by
        apply sum_congr rfl
        intro o _
        ring
      _ = _ := by rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hsum, one_mul]
  refine ⟨hm, ?_⟩
  change E (fun o => (Z o - A) ^ 2) ≤ (3 / 2) * A + 3 * δ₂ * A ^ 2
  rw [hcenter]
  have hlow := mul_le_mul_of_nonneg_left hmlo (show 0 ≤ 2 * A by positivity)
  have hlin := mul_le_mul_of_nonneg_right hδ₁ hA
  have hquad := mul_le_mul_of_nonneg_right hδ (sq_nonneg A)
  nlinarith
/-- The native relative point laws give finite weighted moments without a
count-box cardinality loss or an independence assumption on actual rows. -/
theorem native_truncated_weighted_moments (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M))
          (D : Finset (ℕ × ℕ)) (g : Fin M → ℕ × ℕ → ℝ),
          (∀ c ∈ D, (c.1 : ℝ) ≤ 8 * L ∧ (c.2 : ℝ) ≤ 8 * L) →
          (∀ i c, c ∈ D → 0 ≤ g i c ∧ g i c ≤ 1) →
          let a := fun i => ∑ c ∈ D, g i c * rowReference S r L i c
          let Z := fun o : Obs M (2 * M * L) e => ∑ i ∈ I, truncatedRow e D g i o
          (|(∑ o, probability r e S o * Z o) - ∑ i ∈ I, a i| ≤
            (A * (L : ℝ) ^ 2 / M) * ∑ i ∈ I, a i) ∧
          ((∑ o, probability r e S o * (Z o - ∑ i ∈ I, a i) ^ 2) ≤
            (3 / 2) * (∑ i ∈ I, a i) +
              3 * (A * (L : ℝ) ^ 3 / M) * (∑ i ∈ I, a i) ^ 2) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_point_transfer κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I D g hD hg
  let a := fun i => ∑ c ∈ D, g i c * rowReference S r L i c
  let δ₁ := A * (L : ℝ) ^ 2 / M
  let δ₂ := A * (L : ℝ) ^ 3 / M
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have hlaw := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1
  have hp : ∀ o : Obs M (2 * M * L) e, 0 ≤ probability r e S o := hlaw.1 S
  have hsum : (∑ o : Obs M (2 * M * L) e, probability r e S o) = 1 := hlaw.2 S
  have ha (i : Fin M) : 0 ≤ a i := by
    apply sum_nonneg
    intro c hc
    exact mul_nonneg (hg i c hc).1 (reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hδ₂ : 0 ≤ δ₂ := by dsimp [δ₂]; positivity
  have hδ : δ₁ ≤ δ₂ := by
    have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have hpow : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := by nlinarith [sq_nonneg (L : ℝ)]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA.le) (by positivity)
  have hm (i : Fin M) :
      |(∑ o : Obs M (2 * M * L) e,
        probability r e S o * truncatedRow e D g i o) - a i| ≤ δ₁ * a i := by
    rw [truncated_expectation]
    apply weighted_relative_sum D _ _ (g i) δ₁ (fun c hc => (hg i c hc).1)
    intro c hc
    exact (h M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c (hD c hc).1 (hD c hc).2).1
  have hpair (i j : Fin M) (hij : i ≠ j) : (∑ o : Obs M (2 * M * L) e, probability r e S o *
        (truncatedRow e D g i o * truncatedRow e D g j o)) ≤
        (1 + δ₂) * (a i * a j) := by
    rw [truncated_product_expectation]
    have hb : ∀ c ∈ D, ∀ d ∈ D, (∑ o : Obs M (2 * M * L) e, if (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ∧
             (count e o j 1 = d.1 ∧ count e o j (-1) = d.2)
          then probability r e S o else 0) ≤
            (1 + δ₂) * (rowReference S r L i c * rowReference S r L j d) := by
      intro c hc d hd
      have hh := (abs_le.mp ((h M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c
        (hD c hc).1 (hD c hc).2).2 j d hij (hD d hd).1 (hD d hd).2)).2
      dsimp [δ₂]; nlinarith
    calc
      _ ≤ ∑ c ∈ D, ∑ d ∈ D, (g i c * g j d) *
          ((1 + δ₂) * (rowReference S r L i c * rowReference S r L j d)) :=
        sum_le_sum fun c hc => sum_le_sum fun d hd =>
          mul_le_mul_of_nonneg_left (hb c hc d hd)
            (mul_nonneg (hg i c hc).1 (hg j d hd).1)
      _ = (1 + δ₂) * (a i * a j) := by
        dsimp [a]
        rw [sum_mul]
        simp_rw [mul_sum]
        apply sum_congr rfl
        intro c _
        apply sum_congr rfl
        intro d _
        ring
  exact finite_weighted_moments I (probability r e S) (truncatedRow e D g) a δ₁ δ₂ hp hsum (fun i _ => ha i)
    (fun i _ o => truncated_bounds e D g hg i o) hsmall hδ₂ hδ
    (fun i _ => hm i) (fun i _ j _ hij => hpair i j hij)
end
end D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
open D5.S3.Estimation.TimeArrow.NativeRowCountTail
namespace D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
noncomputable section
/-- All nonnegative count pairs inside the original all-row cutoff. -/
def countBox (L : ℕ) : Finset (ℕ × ℕ) :=
  ((range (8 * L + 1)).product (range (8 * L + 1))).filter fun c => c.1 + c.2 ≤ 8 * L
private theorem mem_countBox (L : ℕ) (c : ℕ × ℕ) :
    c ∈ countBox L ↔ c.1 + c.2 ≤ 8 * L := by
  rcases c with ⟨a, b⟩
  simp only [countBox, mem_filter, Finset.product_eq_sprod, Finset.mem_product, mem_range]; omega
private theorem reference_exponential_sum {M q L : ℕ} (S : Support M q) (r κ z : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L) (hz : 0 ≤ z) (i : Fin M) :
    HasSum (fun c : ℕ × ℕ => z ^ (c.1 + c.2) * rowReference S r L i c)
      (Real.exp ((z - 1) * (L : ℝ))) := by
  let a := (L : ℝ) * (1 + b r S (.inl i)) / 2
  let d := (L : ℝ) * (1 - b r S (.inl i)) / 2
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hb : -(1 - κ) ≤ b r S (.inl i) ∧ b r S (.inl i) ≤ 1 - κ := by
    simp only [b]
    split_ifs <;> constructor <;> linarith
  have ha : 0 ≤ a := by dsimp [a]; nlinarith [hb.1]
  have hd : 0 ≤ d := by dsimp [d]; nlinarith [hb.2]
  let f := fun n : ℕ => Real.exp (-a) * (z * a) ^ n / n.factorial
  let g := fun n : ℕ => Real.exp (-d) * (z * d) ^ n / n.factorial
  have hf : HasSum f (Real.exp ((z - 1) * a)) := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (z * a)).mul_left (Real.exp (-a))
    simpa only [f, mul_div_assoc, ← Real.exp_add, show -a + z * a = (z - 1) * a by ring, ← Real.exp_eq_exp_ℝ] using hh
  have hg : HasSum g (Real.exp ((z - 1) * d)) := by
    have hh := (NormedSpace.expSeries_div_hasSum_exp (z * d)).mul_left (Real.exp (-d))
    simpa only [g, mul_div_assoc, ← Real.exp_add, show -d + z * d = (z - 1) * d by ring, ← Real.exp_eq_exp_ℝ] using hh
  have hfg := hf.mul hg (hf.summable.mul_of_nonneg hg.summable
    (fun n => by dsimp [f]; positivity) (fun n => by dsimp [g]; positivity))
  have he (c : ℕ × ℕ) : f c.1 * g c.2 = z ^ (c.1 + c.2) * rowReference S r L i c := by
    dsimp [f, g, rowReference, a, d]
    rw [pow_add, mul_pow, mul_pow]; ring
  have hsum : a + d = (L : ℝ) := by dsimp [a, d]; ring
  simpa only [he, ← Real.exp_add, ← mul_add, hsum] using hfg
private theorem reference_weighted_tail {M q L : ℕ} (S : Support M q) (r κ : ℝ)
    (hκ : 0 < κ) (hr : 0 < r) (hrκ : r ≤ 1 - κ)
    (hcκ : compensation M q r ≤ 1 - κ) (hL : 1 ≤ L)
    (i : Fin M) (g : ℕ × ℕ → ℝ) (hg : ∀ c, 0 ≤ g c ∧ g c ≤ 1) :
    Summable (fun c => g c * rowReference S r L i c) ∧
      0 ≤ (∑' c, g c * rowReference S r L i c) -
        ∑ c ∈ countBox L, g c * rowReference S r L i c ∧
      (∑' c, g c * rowReference S r L i c) -
        (∑ c ∈ countBox L, g c * rowReference S r L i c) ≤
          Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
  classical
  let Q := rowReference S r L i
  have hQ (c : ℕ × ℕ) : 0 ≤ Q c :=
    (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hQs : Summable Q := by
    simpa only [one_pow, one_mul, sub_self, zero_mul, Real.exp_zero] using
      (reference_exponential_sum S r κ 1 hκ hr hrκ hcκ hL (by norm_num) i).summable
  let f := fun c => g c * Q c
  have hf0 : ∀ c, 0 ≤ f c := fun c => mul_nonneg (hg c).1 (hQ c)
  have hfQ : ∀ c, f c ≤ Q c := fun c => by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hg c).2 (hQ c)
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hfQ hQs
  let tail := fun c => if c ∈ countBox L then (0 : ℝ) else f c
  have ht0 : ∀ c, 0 ≤ tail c := by intro c; dsimp [tail]; split_ifs <;> [exact le_rfl; exact hf0 c]
  have htf : ∀ c, tail c ≤ f c := by intro c; dsimp [tail]; split_ifs <;> simp [hf0]
  have ht : Summable tail := Summable.of_nonneg_of_le ht0 htf hf
  have hsplit : (∑' c, f c) - (∑ c ∈ countBox L, f c) = ∑' c, tail c := by
    have hpart : (fun c => if c ∈ countBox L then f c else 0) + tail = f := by funext c; dsimp [tail]; split_ifs <;> simp
    have hfin : Summable (fun c => if c ∈ countBox L then f c else 0) :=
      summable_of_ne_finset_zero (s := countBox L) (by intro c hc; simp [hc])
    have he := hfin.tsum_add ht
    change (∑' c, ((fun c => if c ∈ countBox L then f c else 0) + tail) c) = _ at he
    rw [hpart] at he
    have hefin : (∑' c, if c ∈ countBox L then f c else 0) = ∑ c ∈ countBox L, f c := by
      rw [tsum_eq_sum (s := countBox L) (fun c hc => if_neg hc)]; exact sum_congr rfl fun c hc => if_pos hc
    rw [hefin] at he; linarith
  have hmgf := reference_exponential_sum S r κ 4 hκ hr hrκ hcκ hL (by norm_num) i
  have hdom (c : ℕ × ℕ) : tail c ≤
      ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (c.1 + c.2) * Q c) := by
    by_cases hc : c ∈ countBox L
    · dsimp [tail]; rw [if_pos hc]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (hQ c))
    · have hn : 8 * L < c.1 + c.2 := by
        have := (mem_countBox L c).not.mp hc; omega
      have hp : (4 : ℝ) ^ (8 * L) ≤ (4 : ℝ) ^ (c.1 + c.2) := pow_le_pow_right₀ (by norm_num) (by omega)
      dsimp [tail]; rw [if_neg hc]
      apply (hfQ c).trans
      have he : Q c = ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (8 * L) * Q c) := by field_simp
      calc
        Q c = _ := he
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (hQ c)) (by positivity)
  have hbound : (∑' c, tail c) ≤ ((4 : ℝ) ^ (8 * L))⁻¹ * Real.exp (3 * (L : ℝ)) := by
    calc
      _ ≤ ∑' c, ((4 : ℝ) ^ (8 * L))⁻¹ * ((4 : ℝ) ^ (c.1 + c.2) * Q c) :=
        ht.tsum_le_tsum hdom (hmgf.summable.mul_left _)
      _ = _ := by rw [tsum_mul_left, hmgf.tsum_eq]; norm_num
  have hpow : (4 : ℝ) ^ (8 * L) = Real.exp (8 * (L : ℝ) * Real.log 4) := by
    conv_lhs => rw [show (4 : ℝ) = Real.exp (Real.log 4) from (Real.exp_log (by norm_num)).symm]
    rw [← Real.exp_nat_mul]
    push_cast
    congr 1
  have hexp : ((4 : ℝ) ^ (8 * L))⁻¹ * Real.exp (3 * (L : ℝ)) ≤
      Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ))) := by
    rw [hpow, ← Real.exp_neg, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hLn : (0 : ℝ) ≤ L := by positivity
    nlinarith
  refine ⟨hf, ?_, ?_⟩
  · change 0 ≤ (∑' c, f c) - ∑ c ∈ countBox L, f c
    rw [hsplit]; exact tsum_nonneg ht0
  · change (∑' c, f c) - (∑ c ∈ countBox L, f c) ≤ _
    rw [hsplit]; exact hbound.trans hexp
private theorem truncatedRow_countBox {M s : ℕ} (e : Experiment)
    (L : ℕ) (g : Fin M → ℕ × ℕ → ℝ) (i : Fin M) (o : Obs M s e) :
    truncatedRow e (countBox L) g i o =
      if count e o i 1 + count e o i (-1) ≤ 8 * L
      then g i (count e o i 1, count e o i (-1)) else 0 := by
  classical
  unfold truncatedRow
  simp_rw [show ∀ c : ℕ × ℕ,
    (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ↔
      c = (count e o i 1, count e o i (-1)) by
    intro c; simp [Prod.ext_iff, eq_comm]]
  simp [mem_countBox]
set_option maxHeartbeats 800000 in
-- The complete-row estimate combines finite moments with two restored tails.
/-- Restoring both tails yields a complete native weighted-row second
moment, with the same reference sum and every original row retained. -/
theorem native_full_weighted_moments (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M))
          (g : Fin M → ℕ × ℕ → ℝ),
          (∀ i c, 0 ≤ g i c ∧ g i c ≤ 1) →
          let a := fun i => ∑' c, g i c * rowReference S r L i c
          let Z := fun o : Obs M (2 * M * L) e =>
            ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
          let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (|(∑ o, probability r e S o * Z o) - ∑ i ∈ I, a i| ≤
            (A * (L : ℝ) ^ 2 / M) * (∑ i ∈ I, a i) + 2 * I.card * ζ) ∧
          ((∑ o, probability r e S o * (Z o - ∑ i ∈ I, a i) ^ 2) ≤
            3 * (∑ i ∈ I, a i) +
              8 * (A * (L : ℝ) ^ 3 / M) * (∑ i ∈ I, a i) ^ 2 +
              10 * (I.card : ℝ) ^ 2 * ζ) := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_truncated_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg
  let a := fun i => ∑' c, g i c * rowReference S r L i c
  let ad := fun i => ∑ c ∈ countBox L, g i c * rowReference S r L i c
  let B := ∑ i ∈ I, a i
  let Bd := ∑ i ∈ I, ad i
  let Z := fun o : Obs M (2 * M * L) e => ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
  let Zd := fun o : Obs M (2 * M * L) e => ∑ i ∈ I, truncatedRow e (countBox L) g i o
  let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
  let n : ℝ := I.card
  let δ₁ := A * (L : ℝ) ^ 2 / M
  let δ₂ := A * (L : ℝ) ^ 3 / M
  let E := fun f : Obs M (2 * M * L) e → ℝ => ∑ o, probability r e S o * f o
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  have law := (finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1
  have hp := law.1 S
  have hsum := law.2 S
  have hz0 : 0 ≤ ζ := (Real.exp_pos _).le
  have hz1 : ζ ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hl4 : 1 ≤ Real.log (4 : ℝ) := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]; linarith [Real.log_two_gt_d9]
    have hLn : (0 : ℝ) ≤ L := by positivity
    nlinarith
  have hδ1 : 0 ≤ δ₁ := by dsimp [δ₁]; positivity
  have hδ2 : 0 ≤ δ₂ := by dsimp [δ₂]; positivity
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have htail (i : Fin M) := reference_weighted_tail S r κ hκ hr hrκ hcκ hL i (g i) (hg i)
  have ha (i : Fin M) : 0 ≤ a i := tsum_nonneg fun c => mul_nonneg (hg i c).1
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have had (i : Fin M) : 0 ≤ ad i := sum_nonneg fun c _ => mul_nonneg (hg i c).1
      (D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer.reference_pos S r κ hκ hr hrκ hcκ hL i c).le
  have hBB : 0 ≤ B - Bd ∧ B - Bd ≤ n * ζ := by
    have he : B - Bd = ∑ i ∈ I, (a i - ad i) := by dsimp [B, Bd]; rw [sum_sub_distrib]
    rw [he]
    refine ⟨sum_nonneg (fun i _ => (htail i).2.1), ?_⟩
    calc
      _ ≤ ∑ _i ∈ I, ζ := sum_le_sum fun i _ => (htail i).2.2
      _ = n * ζ := by simp [n]
  have hB : 0 ≤ B := sum_nonneg fun i _ => ha i
  have hBd : 0 ≤ Bd := sum_nonneg fun i _ => had i
  have hBdB : Bd ≤ B := by linarith [hBB.1]
  have hD (c : ℕ × ℕ) (hc : c ∈ countBox L) :
      (c.1 : ℝ) ≤ 8 * L ∧ (c.2 : ℝ) ≤ 8 * L := by
    have hh := (mem_countBox L c).mp hc
    constructor
    · exact_mod_cast (show c.1 ≤ 8 * L by omega)
    · exact_mod_cast (show c.2 ≤ 8 * L by omega)
  have hm := h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall S e I (countBox L) g hD (fun i c _ => hg i c)
  have hdz (i : Fin M) (o : Obs M (2 * M * L) e) : 0 ≤ g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o ∧
      g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o ≤
        if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0 := by
    rw [truncatedRow_countBox]
    by_cases ho : count e o i 1 + count e o i (-1) ≤ 8 * L
    · rw [if_pos ho, if_neg (by omega)]
      simp
    · rw [if_neg ho, if_pos (by omega), sub_zero]
      exact hg i _
  have hZdiff (o : Obs M (2 * M * L) e) : 0 ≤ Z o - Zd o := by
    dsimp [Z, Zd]; rw [← sum_sub_distrib]; exact sum_nonneg fun i _ => (hdz i o).1
  have hEZdiff : 0 ≤ E Z - E Zd ∧ E Z - E Zd ≤ n * ζ := by
    have he : E Z - E Zd = ∑ i ∈ I, E (fun o =>
        g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o) := by
      dsimp [E, Z, Zd]
      rw [← sum_sub_distrib]
      simp_rw [← mul_sub, ← sum_sub_distrib, mul_sum]
      rw [sum_comm]
    refine ⟨?_, ?_⟩
    · dsimp [E]
      rw [← sum_sub_distrib]
      apply sum_nonneg
      intro o _
      rw [← mul_sub]; exact mul_nonneg (hp o) (hZdiff o)
    · rw [he]
      calc
        _ ≤ ∑ _i ∈ I, ζ := by
          apply sum_le_sum
          intro i _
          have hh := native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i
          apply le_trans _ hh
          apply sum_le_sum
          intro o _
          have ht := mul_le_mul_of_nonneg_left (hdz i o).2 (hp o)
          dsimp [E]
          split_ifs at ht ⊢ <;> simpa using ht
        _ = n * ζ := by simp [n]
  have hD2 : E (fun o => (Z o - Zd o) ^ 2) ≤ n ^ 2 * ζ := by
    have hpw (o : Obs M (2 * M * L) e) : (Z o - Zd o) ^ 2 ≤
        n * ∑ i ∈ I, if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0 := by
      have hs := sq_sum_le_card_mul_sum_sq (s := I) (f := fun i =>
        g i (count e o i 1, count e o i (-1)) - truncatedRow e (countBox L) g i o)
      dsimp [Z, Zd]
      rw [← sum_sub_distrib]
      apply hs.trans
      apply mul_le_mul_of_nonneg_left _ hn
      apply sum_le_sum
      intro i _
      have hh := hdz i o
      split_ifs at hh ⊢ <;> nlinarith only [hh.1, hh.2]
    calc
      _ ≤ E (fun o => n * ∑ i ∈ I,
          if 8 * L < count e o i 1 + count e o i (-1) then (1 : ℝ) else 0) :=
        sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (hpw o) (hp o)
      _ = n * ∑ i ∈ I, (∑ o : Obs M (2 * M * L) e,
          if 8 * L < count e o i 1 + count e o i (-1) then probability r e S o else 0) := by
        dsimp [E]
        simp_rw [mul_sum]
        simp_rw [show ∀ o : Obs M (2 * M * L) e, ∀ v : ℝ,
          probability r e S o * (n * v) = n * (probability r e S o * v) by intro o v; ring]
        rw [sum_comm]
        apply sum_congr rfl
        intro i _
        apply sum_congr rfl
        intro o _
        split_ifs <;> ring
      _ ≤ n * (n * ζ) := mul_le_mul_of_nonneg_left
        ((sum_le_sum fun i _ => native_row_count_tail r S hq hqm hr hr1 hc1 hM6 hL hLM e i).trans_eq
          (by simp [n, ζ])) hn
      _ = n ^ 2 * ζ := by ring
  refine ⟨?_, ?_⟩
  · change |E Z - B| ≤ δ₁ * B + 2 * n * ζ
    have hmd : |E Zd - Bd| ≤ δ₁ * Bd := hm.1
    have hb := abs_le.mp hmd
    have hmono := mul_le_mul_of_nonneg_left hBdB hδ1
    apply abs_le.mpr
    constructor <;> linarith only [hb.1, hb.2, hmono, hBB.1, hBB.2, hEZdiff.1, hEZdiff.2, mul_nonneg hn hz0]
  · change E (fun o => (Z o - B) ^ 2) ≤ 3 * B + 8 * δ₂ * B ^ 2 + 10 * n ^ 2 * ζ
    have hpt (o : Obs M (2 * M * L) e) : (Z o - B) ^ 2 ≤
        2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2 := by
      have hh := hZdiff o
      nlinarith only [sq_nonneg ((Zd o - Bd) - ((Z o - Zd o) - (B - Bd))), mul_nonneg hh hBB.1]
    have he := sum_le_sum (fun o (_ : o ∈ univ) => mul_le_mul_of_nonneg_left (hpt o) (hp o))
    have hexp : E (fun o => 2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2) =
        2 * E (fun o => (Zd o - Bd) ^ 2) + 2 * E (fun o => (Z o - Zd o) ^ 2) +
          2 * (B - Bd) ^ 2 := by
      dsimp [E]
      simp_rw [mul_add]
      rw [sum_add_distrib, sum_add_distrib]
      simp_rw [show ∀ o : Obs M (2 * M * L) e, ∀ v : ℝ,
        probability r e S o * (2 * v) = 2 * (probability r e S o * v) by intro o v; ring]
      rw [← mul_sum, ← mul_sum, ← mul_sum, ← sum_mul, hsum, one_mul]
    change E (fun o => (Z o - B) ^ 2) ≤ E (fun o =>
      2 * (Zd o - Bd) ^ 2 + 2 * (Z o - Zd o) ^ 2 + 2 * (B - Bd) ^ 2) at he
    rw [hexp] at he
    have hsq : Bd ^ 2 ≤ B ^ 2 := by nlinarith only [hBd, hB, hBdB]
    have hmono := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 3 * δ₂ by positivity)
    have hbq : (B - Bd) ^ 2 ≤ n ^ 2 * ζ := by
      have hh := mul_self_le_mul_self hBB.1 hBB.2
      have hh2 := mul_le_mul_of_nonneg_left hz1 hz0
      have hh3 := mul_le_mul_of_nonneg_left hh2 (sq_nonneg n)
      nlinarith only [hh, hh3]
    have hmd : E (fun o => (Zd o - Bd) ^ 2) ≤ (3 / 2) * Bd + 3 * δ₂ * Bd ^ 2 := hm.2
    nlinarith only [he, hmd, hmono, hBdB, hD2, hbq, mul_nonneg hδ2 (sq_nonneg B), mul_nonneg (sq_nonneg n) hz0]
theorem finite_square_markov {Ω : Type*} [Fintype Ω] (p X : Ω → ℝ)
    (a h B : ℝ) (hp : ∀ o, 0 ≤ p o) (hh : 0 < h)
    (hB : (∑ o, p o * (X o - a) ^ 2) ≤ B) :
    (∑ o, if h < |X o - a| then p o else 0) ≤ B / h ^ 2 := by
  classical
  apply (le_div_iff₀ (sq_pos_of_pos hh)).mpr
  rw [sum_mul]
  apply le_trans _ hB
  apply sum_le_sum
  intro o _
  split_ifs with ho
  · have ht := mul_self_le_mul_self hh.le ho.le
    have hs : h ^ 2 ≤ (X o - a) ^ 2 := by simpa only [← pow_two, sq_abs] using ht
    exact mul_le_mul_of_nonneg_left hs (hp o)
  · simp only [zero_mul]
    exact mul_nonneg (hp o) (sq_nonneg _)
/-- Complete native deterministic row-function deviations follow from the
full weighted second moment, with both restored tails in the same budget. -/
theorem native_full_weighted_deviation (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) :
    ∃ (A : ℝ) (M₀ : ℕ) (η₀ : ℝ), 0 < A ∧ 1 ≤ M₀ ∧ 0 < η₀ ∧
      ∀ (M q L : ℕ) (r : ℝ), M₀ ≤ M → 1 ≤ q → q < M →
        0 < r → r ≤ 1 - κ → compensation M q r ≤ 1 - κ →
        1 ≤ L → (L : ℝ) / M ≤ η₀ → A * (L : ℝ) ^ 2 / M ≤ 1 / 2 →
        6 ≤ M → (L : ℝ) / M ≤ 1 / 45 →
        ∀ (S : Support M q) (e : Experiment) (I : Finset (Fin M))
          (g : Fin M → ℕ × ℕ → ℝ),
          (∀ i c, 0 ≤ g i c ∧ g i c ≤ 1) → ∀ h : ℝ, 0 < h →
          let B := ∑ i ∈ I, ∑' c, g i c * rowReference S r L i c
          let Z := fun o : Obs M (2 * M * L) e =>
            ∑ i ∈ I, g i (count e o i 1, count e o i (-1))
          let ζ := Real.exp (-((8 * Real.log 4 - 6) * (L : ℝ)))
          (∑ o, if h < |Z o - B| then probability r e S o else 0) ≤
            (3 * B + 8 * (A * (L : ℝ) ^ 3 / M) * B ^ 2 +
              10 * (I.card : ℝ) ^ 2 * ζ) / h ^ 2 := by
  classical
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ := native_full_weighted_moments κ hκ hκ1
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg t ht
  have hr1 : r < 1 := by linarith
  have hc : 0 ≤ compensation M q r := by unfold compensation; positivity
  have hc1 : compensation M q r < 1 := by linarith
  exact finite_square_markov _ _ _ t _ ((finite_support_bayes (s := 2 * M * L) hq hqm hr hr1 hc hc1 e).2.1.1 S) ht
    (h M q L r hMM hq hqm hr hrκ hcκ hL hLη hsmall hM6 hLM S e I g hg).2
end
end D5.S3.Estimation.TimeArrow.NativeWeightedRowBudgets
namespace D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
noncomputable section
open scoped Classical in
theorem finite_environment_anchor_budget {Ω E : Type*} [Fintype Ω] [DecidableEq E]
    (env : Ω → E) (p : Ω → ℝ) (G C : Ω → Prop) [DecidablePred G] [DecidablePred C]
    (hp : ∀ o, 0 ≤ p o)
    (htail : ∀ z, G z →
      (∑ y : Ω, if env y = env z ∧ ¬C y then p y else 0) ≤
        1/16 * ∑ y : Ω, if env y = env z then p y else 0) :
    (∑ y : Ω, if ¬∃ z, env z = env y ∧ G z ∧ C z then p y else 0) ≤
      16/15 * ∑ y : Ω, if ¬G y then p y else 0 := by
  classical
  let A := fun η : E => ∃ z, env z = η ∧ G z ∧ C z
  let F := (univ : Finset Ω).image env
  have hη (η : E) : (∑ y ∈ univ.filter (fun y => env y = η), if ¬A η then p y else 0) ≤
      16/15 * ∑ y ∈ univ.filter (fun y => env y = η), if ¬G y then p y else 0 := by
    let T := univ.filter fun y => env y = η
    have hbad0 : 0 ≤ ∑ y ∈ T, if ¬G y then p y else 0 :=
      sum_nonneg fun y _ => by split_ifs <;> first | exact hp y | positivity
    by_cases hA : A η
    · simp only [hA, not_true_eq_false, if_false, sum_const_zero]
      exact mul_nonneg (by norm_num) hbad0
    · by_cases hG : ∃ z, env z = η ∧ G z
      · obtain ⟨z,hz,hGz⟩ := hG
        have ht := htail z hGz
        rw [hz] at ht
        have hgoodtail : (∑ y ∈ T, if G y then p y else 0) ≤
            ∑ y : Ω, if env y = η ∧ ¬C y then p y else 0 := by
          rw [sum_filter]
          apply sum_le_sum
          intro y _
          by_cases he : env y = η <;> by_cases hg : G y
          · have hc : ¬C y := fun hy => hA ⟨y,he,hg,hy⟩
            simp [he,hg,hc]
          · by_cases hc : C y <;> simp [he,hg,hc,hp y]
          · simp [he,hg]
          · simp [he,hg]
        have hpart : (∑ y ∈ T, if G y then p y else 0) +
            (∑ y ∈ T, if ¬G y then p y else 0) = ∑ y ∈ T, p y := by
          rw [← sum_add_distrib]
          apply sum_congr rfl
          intro y _
          by_cases hg : G y <;> simp [hg]
        have htot : (∑ y : Ω, if env y = η then p y else 0) = ∑ y ∈ T, p y := (sum_filter _ _).symm
        rw [htot] at ht; simp only [hA, not_false_eq_true, if_true]
        dsimp only [T] at hpart hgoodtail ht; linarith only [hpart, hgoodtail, ht]
      · have hn (y : Ω) (hy : y ∈ T) : ¬G y := by
          intro hg
          exact hG ⟨y,(mem_filter.mp hy).2,hg⟩
        simp only [hA, not_false_eq_true, if_true]
        have he : (∑ y ∈ T, if ¬G y then p y else 0) = ∑ y ∈ T, p y := sum_congr rfl fun y hy => if_pos (hn y hy)
        change (∑ y ∈ T, p y) ≤ 16/15 * ∑ y ∈ T, if ¬G y then p y else 0
        rw [he]
        have hh := sum_nonneg (s := T) fun y _ => hp y
        linarith only [hh]
  calc
    _ = ∑ η ∈ F, ∑ y ∈ univ.filter (fun y => env y = η), if ¬A η then p y else 0 := by
      rw [← sum_fiberwise_of_maps_to (fun y (_ : y ∈ (univ : Finset Ω)) =>
        mem_image_of_mem env (mem_univ y)) (fun y => if ¬A (env y) then p y else 0)]
      apply sum_congr rfl
      intro η _
      apply sum_congr rfl
      intro y hy
      rw [(mem_filter.mp hy).2]
    _ ≤ ∑ η ∈ F, 16/15 * ∑ y ∈ univ.filter (fun y => env y = η), if ¬G y then p y else 0 :=
      sum_le_sum fun η _ => hη η
    _ = _ := by
      rw [← mul_sum, sum_fiberwise_of_maps_to (fun y (_ : y ∈ (univ : Finset Ω)) =>
        mem_image_of_mem env (mem_univ y))]
end
end D5.S3.Estimation.TimeArrow.NativeEnvironmentAnchors
