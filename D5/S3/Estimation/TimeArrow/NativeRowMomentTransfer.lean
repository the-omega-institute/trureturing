/- GID: D5/S3/Estimation/TimeArrow/NativeRowMomentTransfer
   generality: G
   mirror-B: D5/B/S3/Estimation/TimeArrow/NativeRowMomentTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Native one- and two-row relative laws control deterministic weighted row moments. -/

import D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative

open scoped BigOperators
open Finset
open D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open D5.S3.Estimation.TimeArrow.ActualMarkedCountPoissonRelative

set_option autoImplicit false
set_option relaxedAutoImplicit false

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
  have hp : 0 < (L : ℝ) * (1 + b r S (.inl i)) / 2 :=
    div_pos (mul_pos hLpos (by linarith [hb.1])) (by norm_num)
  have hm : 0 < (L : ℝ) * (1 - b r S (.inl i)) / 2 :=
    div_pos (mul_pos hLpos (by linarith [hb.2])) (by norm_num)
  unfold rowReference
  exact mul_pos
    (div_pos (mul_pos (Real.exp_pos _) (pow_pos hp _)) (by positivity))
    (div_pos (mul_pos (Real.exp_pos _) (pow_pos hm _)) (by positivity))

private theorem multiply_relative {P Q δ : ℝ} (hQ : 0 < Q)
    (h : |P / Q - 1| ≤ δ) : |P - Q| ≤ δ * Q := by
  have he : P - Q = (P / Q - 1) * Q := by field_simp
  rw [he, abs_mul, abs_of_pos hQ]
  exact mul_le_mul_of_nonneg_right h hQ.le

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
  obtain ⟨A, M₀, η₀, hA, hM₀, hη₀, h⟩ :=
    actual_marked_count_poisson_relative κ 8 hκ hκ1 (by norm_num)
  refine ⟨A, M₀, η₀, hA, hM₀, hη₀, ?_⟩
  intro M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c hc1 hc2
  have hQc := reference_pos S r κ hκ hr hrκ hcκ hL i c
  constructor
  · have hh := h M q L 1 r hMM hq hqm hr hrκ hcκ hL hLη (Or.inl rfl)
      S (fun _ => i) (fun a b _ => Subsingleton.elim a b)
      (fun _ => c.1) (fun _ => c.2) (fun _ => ⟨hc1, hc2⟩) e
    simp only [Fin.prod_univ_one, Fin.forall_fin_one] at hh
    exact multiply_relative hQc hh
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
    have hh := h M q L 2 r hMM hq hqm hr hrκ hcκ hL hLη (Or.inr rfl)
      S m hm ![c.1, d.1] ![c.2, d.2] hn e
    simp only [Fin.prod_univ_two, Fin.forall_fin_two, m,
      Matrix.cons_val_zero, Matrix.cons_val_one] at hh
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
      simpa only [mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (h c hc) (hg c hc)
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
  have he (o : Obs M s e) : probability r e S o *
      (truncatedRow e D g i o * truncatedRow e D g j o) =
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
    rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans
      ((sum_le_sum hmean).trans_eq (mul_sum ..).symm)
  have hmlo : (1 - δ₁) * A ≤ E Z := by
    have := (abs_le.mp hm).1
    nlinarith
  have hmhi : E Z ≤ (1 + δ₁) * A := by
    have := (abs_le.mp hm).2
    nlinarith
  have hproduct (i : ι) (hi : i ∈ I) (j : ι) (hj : j ∈ I) :
      E (fun o => X i o * X j o) ≤
        (if i = j then E (X i) else 0) + (1 + δ₂) * (a i * a j) := by
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      have hd : E (fun o => X i o * X i o) ≤ E (X i) := by
        apply sum_le_sum
        intro o _
        apply mul_le_mul_of_nonneg_left _ (hp o)
        nlinarith [(hX i hi o).1, (hX i hi o).2]
      exact hd.trans (le_add_of_nonneg_right
        (mul_nonneg (by linarith) (mul_nonneg (ha i hi) (ha i hi))))
    · rw [if_neg hij, zero_add]
      exact hpair i hi j hj hij
  have hsecond : E (fun o => (Z o) ^ 2) ≤ E Z + (1 + δ₂) * A ^ 2 := by
    have he : E (fun o => (Z o) ^ 2) =
        ∑ i ∈ I, ∑ j ∈ I, E (fun o => X i o * X j o) := by
      dsimp [E, Z]
      simp only [pow_two, sum_mul, mul_sum]
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
      _ = _ := by
        rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← sum_mul, hsum, one_mul]
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
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hA.le) (by positivity)
  have hm (i : Fin M) :
      |(∑ o : Obs M (2 * M * L) e,
        probability r e S o * truncatedRow e D g i o) - a i| ≤ δ₁ * a i := by
    rw [truncated_expectation]
    apply weighted_relative_sum D _ _ (g i) δ₁ (fun c hc => (hg i c hc).1)
    intro c hc
    exact (h M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c
      (hD c hc).1 (hD c hc).2).1
  have hpair (i j : Fin M) (hij : i ≠ j) :
      (∑ o : Obs M (2 * M * L) e, probability r e S o *
        (truncatedRow e D g i o * truncatedRow e D g j o)) ≤
        (1 + δ₂) * (a i * a j) := by
    rw [truncated_product_expectation]
    have hb : ∀ c ∈ D, ∀ d ∈ D,
        (∑ o : Obs M (2 * M * L) e,
          if (count e o i 1 = c.1 ∧ count e o i (-1) = c.2) ∧
             (count e o j 1 = d.1 ∧ count e o j (-1) = d.2)
          then probability r e S o else 0) ≤
            (1 + δ₂) * (rowReference S r L i c * rowReference S r L j d) := by
      intro c hc d hd
      have hh := (abs_le.mp ((h M q L r hMM hq hqm hr hrκ hcκ hL hLη S e i c
        (hD c hc).1 (hD c hc).2).2 j d hij (hD d hd).1 (hD d hd).2)).2
      dsimp [δ₂]
      nlinarith
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
  exact finite_weighted_moments I (probability r e S)
    (truncatedRow e D g) a δ₁ δ₂ hp hsum (fun i _ => ha i)
    (fun i _ o => truncated_bounds e D g hg i o) hsmall hδ₂ hδ
    (fun i _ => hm i) (fun i _ j _ hij => hpair i j hij)

end
end D5.S3.Estimation.TimeArrow.NativeRowMomentTransfer
