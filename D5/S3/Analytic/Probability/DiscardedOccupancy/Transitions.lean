/- GID: D5/S3/Analytic/Probability/DiscardedOccupancy/Transitions
   generality: G
   mirror-B: D5/B/S3/Analytic/Probability/DiscardedOccupancy/Transitions
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The conditional bin-hit probability yields exact occupancy moment recursions and a linear variance lower bound. -/

import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic

open scoped BigOperators Topology
open Finset Filter MeasureTheory ProbabilityTheory

namespace DiscardedOccupancy

noncomputable section

abbrev History (n j : ℕ) := Fin j → Option (Fin n)

def throwMass (n : ℕ) (p : ℝ) : Option (Fin n) → ℝ
  | none => 1 - p
  | some _ => p / n

def wordMass (n : ℕ) (p : ℝ) {j : ℕ} (ω : History n j) : ℝ :=
  ∏ i, throwMass n p (ω i)

def insertThrow {n : ℕ} (s : Finset (Fin n)) : Option (Fin n) → Finset (Fin n)
  | none => s
  | some x => insert x s

def occupied (n : ℕ) : (j : ℕ) → History n j → Finset (Fin n)
  | 0, _ => ∅
  | j + 1, ω => insertThrow (occupied n j (Fin.init ω)) (ω (Fin.last j))

def count (n j : ℕ) (ω : History n j) : ℕ := (occupied n j ω).card

def average {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (f : History n j → E) : E :=
  ∑ ω, wordMass n p ω • f ω

def expect {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (f : ℕ → E) : E :=
  average n p j (fun ω => f (count n j ω))

def q (n : ℕ) (p x : ℝ) : ℝ := p * (1 - x / n)

def a (n : ℕ) (p : ℝ) : ℝ := 1 - p / n

def v (n : ℕ) (p x : ℝ) : ℝ := q n p x * (1 - q n p x)

private theorem count_le_time (n j : ℕ) (ω : History n j) : count n j ω ≤ j := by
  induction j with
  | zero => simp [count, occupied]
  | succ j ih =>
    change (insertThrow (occupied n j (Fin.init ω)) (ω (Fin.last j))).card ≤ j + 1
    have h := ih (Fin.init ω)
    change (occupied n j (Fin.init ω)).card ≤ j at h
    cases ω (Fin.last j) with
    | none => exact h.trans (Nat.le_succ _)
    | some i => exact (Finset.card_insert_le _ _).trans (Nat.succ_le_succ h)

private theorem count_le_bins (n j : ℕ) (ω : History n j) : count n j ω ≤ n := by
  simpa [count] using (occupied n j ω).card_le_univ

theorem wordMass_nonneg {n : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {j : ℕ} (ω : History n j) : 0 ≤ wordMass n p ω := by
  apply Finset.prod_nonneg
  intro i _
  cases ω i <;> simp [throwMass, sub_nonneg.mpr hp']
  exact div_nonneg hp (Nat.cast_nonneg n)

private theorem average_succ {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (f : History n (j + 1) → E) :
    average n p (j + 1) f =
      average n p j (fun ω => ∑ b, throwMass n p b • f (Fin.snoc ω b)) := by
  classical
  unfold average
  let e : History n j × Option (Fin n) ≃ History n (j + 1) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ : Fin (j + 1) => Option (Fin n)))
  have hw (ω : History n j) (b : Option (Fin n)) :
      wordMass n p (Fin.snoc ω b) = wordMass n p ω * throwMass n p b := by
    simp [wordMass, Fin.prod_univ_castSucc]
  calc
    _ = ∑ x : History n j × Option (Fin n),
        wordMass n p (Fin.snoc x.1 x.2) • f (Fin.snoc x.1 x.2) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [hw, Finset.smul_sum, smul_smul]

private lemma throw_step {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (hn : 0 < n) (p : ℝ) (s : Finset (Fin n)) (f : ℕ → E) :
    (∑ b, throwMass n p b • f (insertThrow s b).card) =
      (1 - q n p s.card) • f s.card + q n p s.card • f (s.card + 1) := by
  classical
  rw [Fintype.sum_option]
  simp only [throwMass, insertThrow]
  have h : ∀ b : Fin n, (insert b s).card = if b ∈ s then s.card else s.card + 1 := by
    intro b
    split_ifs with hb
    · rw [insert_eq_of_mem hb]
    · exact card_insert_of_notMem hb
  simp_rw [h, apply_ite f, smul_ite]
  rw [Finset.sum_ite]
  simp only [filter_mem_eq_inter, univ_inter, sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, ← add_assoc, ← add_smul]
  have hcard : (Finset.univ.filter fun b : Fin n => b ∉ s).card = n - s.card := by
    have he : (Finset.univ.filter fun b : Fin n => b ∉ s) = Finset.univ \ s := by
      ext b
      simp
    rw [he, card_sdiff]
    simp
  rw [hcard, Nat.cast_sub (by simpa using s.card_le_univ : s.card ≤ n)]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h1 : 1 - p + (s.card : ℝ) * (p / n) = 1 - q n p s.card := by
    unfold q
    ring
  have h2 : ((n : ℝ) - s.card) * (p / n) = q n p s.card := by
    unfold q
    field_simp
  rw [h1, h2]

theorem expect_succ {E : Type*} [AddCommMonoid E] [Module ℝ E]
    {n : ℕ} (hn : 0 < n) (p : ℝ) (j : ℕ) (f : ℕ → E) :
    expect n p (j + 1) f =
      expect n p j (fun x => (1 - q n p x) • f x + q n p x • f (x + 1)) := by
  unfold expect
  rw [average_succ]
  congr 1
  funext ω
  simpa [count, occupied, Fin.init_snoc, Fin.snoc_last] using
    throw_step hn p (occupied n j ω) f

theorem expect_congr {E : Type*} [AddCommMonoid E] [Module ℝ E] {n j : ℕ} {p : ℝ}
    {f g : ℕ → E} (h : ∀ x, x ≤ j → x ≤ n → f x = g x) :
    expect n p j f = expect n p j g := by
  apply Finset.sum_congr rfl
  intro ω _
  exact congrArg (fun r => wordMass n p ω • r)
    (h _ (count_le_time n j ω) (count_le_bins n j ω))

theorem expect_zero_time {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (f : ℕ → E) : expect n p 0 f = f 0 := by
  simp [expect, average, wordMass, count, occupied]

theorem expect_const {E : Type*} [AddCommMonoid E] [Module ℝ E] {n : ℕ}
    (hn : 0 < n) (p : ℝ) (j : ℕ) (c : E) : expect n p j (fun _ => c) = c := by
  induction j with
  | zero => exact expect_zero_time n p _
  | succ j ih =>
    rw [expect_succ hn]
    convert ih using 2
    funext x
    rw [← add_smul, sub_add_cancel, one_smul]

theorem expect_add {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (f g : ℕ → E) :
    expect n p j (fun x => f x + g x) = expect n p j f + expect n p j g := by
  simp only [expect, average, smul_add, Finset.sum_add_distrib]

theorem expect_smul {E : Type*} [AddCommMonoid E] [Module ℝ E] (n : ℕ) (p : ℝ)
    (j : ℕ) (c : ℝ) (f : ℕ → E) :
    expect n p j (fun x => c • f x) = c • expect n p j f := by
  simp only [expect, average, Finset.smul_sum]
  exact Finset.sum_congr rfl (fun ω _ => smul_comm (wordMass n p ω) c _)

theorem expect_mono {n j : ℕ} {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) {f g : ℕ → ℝ}
    (h : ∀ x, x ≤ j → x ≤ n → f x ≤ g x) : expect n p j f ≤ expect n p j g := by
  apply Finset.sum_le_sum
  intro ω _
  exact mul_le_mul_of_nonneg_left (h _ (count_le_time n j ω) (count_le_bins n j ω))
    (wordMass_nonneg hp hp' ω)

theorem q_bounds {n : ℕ} {p x : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x) (hx' : x ≤ n) :
    0 ≤ q n p x ∧ q n p x ≤ p := by
  have hb : x / n ≤ 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (div_le_one (by exact_mod_cast hn)).2 hx'
  exact ⟨mul_nonneg hp (sub_nonneg.mpr hb),
    mul_le_of_le_one_right hp (by have := div_nonneg hx (Nat.cast_nonneg n); linarith)⟩

theorem a_bounds {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ a n p ∧ a n p ≤ 1 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact ⟨sub_nonneg.mpr ((div_le_one hn').2 (hp'.trans hn1)),
    sub_le_self _ (div_nonneg hp hn'.le)⟩

def mean (n : ℕ) (p : ℝ) (j : ℕ) : ℝ := expect n p j fun x => (x : ℝ)

def variance (n : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  expect n p j fun x => ((x : ℝ) - mean n p j) ^ 2

theorem mean_bounds {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (j : ℕ) :
    0 ≤ mean n p j ∧ mean n p j ≤ n := by
  constructor
  · rw [← expect_const hn p j (0 : ℝ)]
    exact expect_mono hp hp' (fun x _ _ => Nat.cast_nonneg x)
  · rw [← expect_const hn p j (n : ℝ)]
    exact expect_mono hp hp' (fun x _ h => by exact_mod_cast h)

theorem mean_succ {n : ℕ} (hn : 0 < n) (p : ℝ) (j : ℕ) :
    mean n p (j + 1) = a n p * mean n p j + p := by
  unfold mean
  rw [expect_succ hn]
  have h (x : ℕ) :
      (1 - q n p x) • (x : ℝ) + q n p x • ((x + 1 : ℕ) : ℝ) =
        a n p • (x : ℝ) + p := by
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, a, q]
    ring
  simp_rw [h]
  rw [expect_add, expect_smul, expect_const hn, smul_eq_mul]

private theorem variance_succ {n : ℕ} (hn : 0 < n) (p : ℝ) (j : ℕ) :
    variance n p (j + 1) =
      a n p ^ 2 * variance n p j + expect n p j (fun x => v n p x) := by
  unfold variance
  rw [expect_succ hn, mean_succ hn]
  have h (x : ℕ) :
      (1 - q n p x) • ((x : ℝ) - (a n p * mean n p j + p)) ^ 2 +
          q n p x • (((x + 1 : ℕ) : ℝ) - (a n p * mean n p j + p)) ^ 2 =
        a n p ^ 2 • ((x : ℝ) - mean n p j) ^ 2 + v n p x := by
    simp only [smul_eq_mul, Nat.cast_add, Nat.cast_one, q, a, v]
    ring
  simp_rw [h]
  rw [expect_add, expect_smul, smul_eq_mul]

theorem variance_nonneg {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) : 0 ≤ variance n p j := by
  rw [← expect_const hn p j (0 : ℝ)]
  exact expect_mono hp hp' (fun _ _ _ => sq_nonneg _)

theorem v_bounds {n : ℕ} {p x : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hx : 0 ≤ x) (hx' : x ≤ n) : 0 ≤ v n p x ∧ v n p x ≤ 1 := by
  have ⟨hq0, hqp⟩ := q_bounds hp hx hx'
  have hq1 := hqp.trans hp'
  exact ⟨mul_nonneg hq0 (sub_nonneg.mpr hq1),
    (mul_le_of_le_one_right hq0 (sub_le_self _ hq0)).trans hq1⟩

theorem variance_le_time {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (j : ℕ) : variance n p j ≤ j := by
  induction j with
  | zero => simp [variance, mean, expect_zero_time]
  | succ j ih =>
    have hab := a_bounds hn hp hp'
    have hs : a n p ^ 2 ≤ 1 := pow_le_one₀ hab.1 hab.2
    have hv : expect n p j (fun x => v n p x) ≤ 1 := by
      rw [← expect_const hn p j (1 : ℝ)]
      exact expect_mono hp hp' (fun x _ hx => (v_bounds hp hp' (Nat.cast_nonneg x)
        (by exact_mod_cast hx)).2)
    have hmul := mul_le_of_le_one_left (variance_nonneg hn hp hp' j) hs
    rw [variance_succ hn, Nat.cast_succ]
    linarith

theorem weighted_variance {n : ℕ} (hn : 0 < n) (p : ℝ) (m : ℕ) :
    variance n p m =
      ∑ j ∈ range m, (a n p ^ (m - (j + 1))) ^ 2 * expect n p j (fun x => v n p x) := by
  induction m with
  | zero => simp [variance, mean, expect_zero_time]
  | succ m ih =>
    rw [variance_succ hn, ih, Finset.sum_range_succ, Nat.sub_self, pow_zero, one_pow,
      one_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : m + 1 - (j + 1) = m - (j + 1) + 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [hj', pow_succ]
    ring

private theorem weight_lower {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    {j : ℕ} (hj : j ≤ n) : 1 - p ≤ a n p ^ j := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 := (a_bounds hn hp hp').1
  unfold a at h0
  have hb := one_add_mul_le_pow (by linarith [h0] : -2 ≤ -(p / n)) j
  have he : 1 + -(p / n) = a n p := by unfold a; ring
  rw [he] at hb
  have hj' : (j : ℝ) ≤ n := by exact_mod_cast hj
  have hm := mul_le_mul_of_nonneg_right hj' (div_nonneg hp hn'.le)
  have hd : (n : ℝ) * (p / n) = p := by field_simp
  rw [hd] at hm
  linarith

private theorem early_q_bounds {n j x : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p)
    (hj : j < n / 2) (hx : x ≤ j) : p / 2 ≤ q n p x ∧ q n p x ≤ p := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : 2 * x ≤ n := by omega
  have h2' : (2 : ℝ) * x ≤ n := by exact_mod_cast h2
  have hx' : (x : ℝ) ≤ n := by linarith
  refine ⟨?_, (q_bounds hp (Nat.cast_nonneg x) hx').2⟩
  have hh : (x : ℝ) / n ≤ 1 / 2 := (div_le_iff₀ hn').2 (by linarith)
  have := mul_le_mul_of_nonneg_left (show 1 / 2 ≤ 1 - (x : ℝ) / n by linarith) hp
  unfold q
  linarith

theorem variance_lower {n : ℕ} (hn : 0 < n) {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (n / 2 : ℕ) * (p * (1 - p) ^ 3 / 2) ≤ variance n p (n - 1) := by
  rw [weighted_variance hn]
  let c : ℝ := p * (1 - p) ^ 3 / 2
  have hsub : range (n / 2) ⊆ range (n - 1) := range_mono (by omega)
  have hnonneg (j : ℕ) : 0 ≤ expect n p j (fun x => v n p x) := by
    rw [← expect_const hn p j (0 : ℝ)]
    exact expect_mono hp hp' (fun x _ hx => (v_bounds hp hp' (Nat.cast_nonneg x)
      (by exact_mod_cast hx)).1)
  calc
    _ = ∑ _j ∈ range (n / 2), c := by simp [c, nsmul_eq_mul]
    _ ≤ ∑ j ∈ range (n / 2),
        (a n p ^ (n - 1 - (j + 1))) ^ 2 * expect n p j (fun x => v n p x) := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' := mem_range.mp hj
      have hw := weight_lower hn hp hp' (show n - 1 - (j + 1) ≤ n by omega)
      have hc : p / 2 * (1 - p) ≤ expect n p j (fun x => v n p x) := by
        rw [← expect_const hn p j (p / 2 * (1 - p))]
        apply expect_mono hp hp'
        intro x hx _
        have ⟨hl, hu⟩ := early_q_bounds hn hp hj' hx
        exact mul_le_mul hl (by linarith) (sub_nonneg.mpr hp') (by linarith)
      calc
        c = (1 - p)^2 * (p / 2 * (1 - p)) := by dsimp [c]; ring
        _ ≤ _ := mul_le_mul (pow_le_pow_left₀ (sub_nonneg.mpr hp') hw 2) hc
          (by positivity) (sq_nonneg _)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (by
      intro j _ _
      exact mul_nonneg (sq_nonneg _) (hnonneg j))

end
end DiscardedOccupancy
