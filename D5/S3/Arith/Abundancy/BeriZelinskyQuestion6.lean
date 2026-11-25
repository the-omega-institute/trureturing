/- GID: D5/S3/Arith/Abundancy/BeriZelinskyQuestion6
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/BeriZelinskyQuestion6
   mirror-E: none(waiver:symbolic-asymptotic-theorem)
   anchors: []
   utility: none
   digest: Norton threshold lengths and the reciprocal-square perturbation. -/

import D5.S3.Weil.Mertens.Third
import D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail
import D5.S3.Arith.OmegaGreedyPermutation
import D5.S3.Arith.Robin.GoldenResidualFive
import D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Strict prime-product crossings and their logarithmic errors. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Filter Real
open scoped Topology BigOperators
open D5.S3.Arith.OmegaGreedyPermutation (prime)
open D5.S3.Arith.Robin.GoldenResidualFive (eulerFactor)

namespace D5.S3.Arith.Abundancy.BeriZelinskyQuestion6

/-- The factor in the definition of KS. -/
def ksFactor (q : ℕ) : ℝ := eulerFactor q + 1 / (q : ℝ) ^ 2

/-- The logarithmic Norton weight. -/
def weight (q : ℕ) : ℝ := log (eulerFactor q)

/-- The logarithmic increment contributed by the KS perturbation. -/
def perturbation (q : ℕ) : ℝ := log (1 + ((q : ℝ) - 1) / (q : ℝ) ^ 3)

/-- The source's product over k consecutive primes, starting at its index n. -/
def nortonProduct (n k : ℕ) : ℝ :=
  ∏ i ∈ Ico (n - 1) (n - 1 + k), eulerFactor (prime i)

/-- The corresponding perturbed product. -/
def ksProduct (n k : ℕ) : ℝ :=
  ∏ i ∈ Ico (n - 1) (n - 1 + k), ksFactor (prime i)

/-- The least positive length giving a strict crossing of alpha. -/
def aAlpha (α : ℝ) (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ α < nortonProduct n k}

/-- Norton's threshold at alpha = 2. -/
def a (n : ℕ) : ℕ := aAlpha 2 n

/-- The least positive length for the strict perturbed crossing of two. -/
def KS (n : ℕ) : ℕ := sInf {k : ℕ | 1 ≤ k ∧ 2 < ksProduct n k}

private lemma nthPrime_prime (i : ℕ) : (prime i).Prime := Nat.prime_nth_prime i

private lemma eulerFactor_pos {q : ℕ} (hq : q.Prime) : 0 < eulerFactor q := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  exact div_pos (by linarith) (by linarith)

private lemma eulerFactor_gt_one {q : ℕ} (hq : q.Prime) : 1 < eulerFactor q := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  exact (lt_div_iff₀ (by linarith : 0 < (q : ℝ) - 1)).mpr (by linarith)

private lemma weight_pos {q : ℕ} (hq : q.Prime) : 0 < weight q :=
  log_pos (eulerFactor_gt_one hq)

private lemma weight_bounds {q : ℕ} (hq : q.Prime) :
    1 / (q : ℝ) ≤ weight q ∧ weight q ≤ 2 / (q : ℝ) := by
  have h := ZelinskyZhangDoublePrimitive.log_bounds hq.two_le
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  refine ⟨h.1, h.2.trans ?_⟩
  apply (div_le_div_iff₀ hq1 hq0).mpr
  linarith

private lemma ksFactor_log {q : ℕ} (hq : q.Prime) :
    log (ksFactor q) = weight q + perturbation q := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (q : ℝ) ≠ 0 := by linarith
  have hq1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have heq : ksFactor q =
      eulerFactor q * (1 + ((q : ℝ) - 1) / (q : ℝ) ^ 3) := by
    dsimp [ksFactor, eulerFactor]
    field_simp
  rw [heq, log_mul (eulerFactor_pos hq).ne' (by positivity)]
  rfl

private lemma perturbation_bounds {q : ℕ} (hq : q.Prime) :
    1 / (4 * (q : ℝ) ^ 2) ≤ perturbation q ∧
      perturbation q ≤ 1 / (q : ℝ) ^ 2 := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq0 : (0 : ℝ) < q := by linarith
  let x : ℝ := ((q : ℝ) - 1) / (q : ℝ) ^ 3
  have hx0 : 0 ≤ x := div_nonneg (by linarith) (by positivity)
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) ^ 3)).mpr
    nlinarith [sq_nonneg ((q : ℝ) - 1)]
  have hxl : 1 / (2 * (q : ℝ) ^ 2) ≤ x := by
    dsimp [x]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_pos_of_pos hq0]
  have hxu : x ≤ 1 / (q : ℝ) ^ 2 := by
    dsimp [x]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (q : ℝ)]
  have hxhalf : x / 2 ≤ log (1 + x) := by
    have hl := le_log_one_add_of_nonneg hx0
    have hden : 0 < x + 2 := by linarith
    have hcomp : x / 2 ≤ 2 * x / (x + 2) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith
    exact hcomp.trans hl
  constructor
  · change _ ≤ log (1 + x)
    have heq : 1 / (4 * (q : ℝ) ^ 2) = (1 / (2 * (q : ℝ) ^ 2)) / 2 := by
      ring
    rw [heq]
    exact (div_le_div_of_nonneg_right hxl (by norm_num)).trans hxhalf
  · change log (1 + x) ≤ _
    have h := log_le_sub_one_of_pos (by linarith : 0 < 1 + x)
    linarith

private lemma log_nortonProduct (n k : ℕ) :
    log (nortonProduct n k) =
      ∑ i ∈ Ico (n - 1) (n - 1 + k), weight (prime i) := by
  exact log_prod (fun i _ => (eulerFactor_pos (nthPrime_prime i)).ne')

private lemma log_ksProduct (n k : ℕ) :
    log (ksProduct n k) =
      ∑ i ∈ Ico (n - 1) (n - 1 + k),
        (weight (prime i) + perturbation (prime i)) := by
  rw [ksProduct, log_prod (fun i _ => by
    have hp := eulerFactor_pos (nthPrime_prime i)
    dsimp [ksFactor]
    positivity)]
  exact sum_congr rfl (fun i _ => ksFactor_log (nthPrime_prime i))

private lemma norton_sum_nth_prime_lt (f : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ range k, f (Nat.nth Nat.Prime i)) =
      ∑ q ∈ (range (Nat.nth Nat.Prime k)).filter Nat.Prime, f q := by
  classical
  induction k with
  | zero =>
    have hz : (range 2).filter Nat.Prime = ∅ := by decide
    simp [Nat.nth_prime_zero_eq_two, hz]
  | succ k ih =>
    rw [sum_range_succ,
      Nat.filter_range_nth_eq_insert_of_infinite Nat.infinite_setOfPred_prime k,
      sum_insert (by simp)]
    rw [← ih]
    ring

private lemma norton_sum_nth_prime_le (f : ℕ → ℝ) (k : ℕ) :
    (∑ i ∈ range (k + 1), f (Nat.nth Nat.Prime i)) =
      ∑ q ∈ (Ioc 0 (Nat.nth Nat.Prime k)).filter Nat.Prime, f q := by
  classical
  have hset : (Ioc 0 (Nat.nth Nat.Prime k)).filter Nat.Prime =
      insert (Nat.nth Nat.Prime k)
        ((range (Nat.nth Nat.Prime k)).filter Nat.Prime) := by
    ext q
    simp only [mem_filter, mem_Ioc, mem_insert, mem_range]
    grind [Nat.Prime.pos, Nat.prime_nth_prime]
  rw [sum_range_succ, norton_sum_nth_prime_lt, hset, sum_insert (by simp)]
  ring

private lemma norton_weight_eq_neg_log {q : ℕ} (hq : q.Prime) :
    Real.log ((q : ℝ) / (q - 1)) = -Real.log (1 - 1 / (q : ℝ)) := by
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have heq : 1 - 1 / (q : ℝ) = ((q : ℝ) - 1) / q := by
    field_simp
  rw [heq, ← Real.log_inv, inv_div]

private lemma norton_prefix_mertens_bound :
    ∃ C : ℝ, ∀ k : ℕ,
      |(∑ i ∈ range (k + 1),
          Real.log ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1))) -
        (Real.log (Real.log (Nat.nth Nat.Prime k)) +
          Real.eulerMascheroniConstant)| ≤
        C / Real.log (Nat.nth Nat.Prime k) := by
  classical
  obtain ⟨C, hC⟩ := Mertens.E₃.abs_le
  refine ⟨C, fun k => ?_⟩
  have hp : (2 : ℝ) ≤ Nat.nth Nat.Prime k := by
    exact_mod_cast (Nat.prime_nth_prime k).two_le
  have hsum : (∑ i ∈ range (k + 1),
      Real.log ((Nat.nth Nat.Prime i : ℝ) / (Nat.nth Nat.Prime i - 1))) =
      -(∑ q ∈ (Ioc 0 (Nat.nth Nat.Prime k)).filter Nat.Prime,
        Real.log (1 - 1 / (q : ℝ))) := by
    rw [norton_sum_nth_prime_le (fun q => log ((q : ℝ) / (q - 1))),
      ← sum_neg_distrib]
    apply sum_congr rfl
    intro q hq
    exact norton_weight_eq_neg_log (mem_filter.mp hq).2
  calc
    _ = |-(Mertens.E₃ (Nat.nth Nat.Prime k : ℝ))| := by
      rw [hsum]
      unfold Mertens.E₃
      rw [Nat.floor_natCast]
      congr 1
      ring
    _ = |Mertens.E₃ (Nat.nth Nat.Prime k : ℝ)| := abs_neg _
    _ ≤ _ := hC _ hp

private def weightPrefix (k : ℕ) : ℝ := ∑ i ∈ range k, weight (prime i)

private lemma weightPrefix_diverges : Tendsto weightPrefix atTop atTop := by
  obtain ⟨C, hC⟩ := norton_prefix_mertens_bound
  have hp : Tendsto (fun k : ℕ => (prime k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop
  have hl := Real.tendsto_log_atTop.comp hp
  apply tendsto_atTop.2
  intro b
  filter_upwards [hl.eventually_ge_atTop C,
    (Real.tendsto_log_atTop.comp hl).eventually_ge_atTop
      (b - eulerMascheroniConstant + 2)] with k hk hb
  have hLP : 0 < log (prime k : ℝ) :=
    log_pos (by exact_mod_cast (nthPrime_prime k).one_lt)
  have he : |weightPrefix (k + 1) -
      (log (log (prime k)) + eulerMascheroniConstant)| ≤ 1 :=
    (hC k).trans ((div_le_one hLP).mpr hk)
  have hw : weight (prime k) ≤ 1 := (weight_bounds (nthPrime_prime k)).2.trans
    ((div_le_one (by exact_mod_cast (nthPrime_prime k).pos)).mpr
      (by exact_mod_cast (nthPrime_prime k).two_le))
  have hs : weightPrefix (k + 1) = weightPrefix k + weight (prime k) :=
    sum_range_succ _ _
  simp only [Function.comp_apply] at hb
  linarith [(abs_le.mp he).1]

private lemma nortonProduct_pos (n k : ℕ) : 0 < nortonProduct n k :=
  prod_pos (fun i _ => eulerFactor_pos (nthPrime_prime i))

private lemma nortonProduct_le_ksProduct (n k : ℕ) :
    nortonProduct n k ≤ ksProduct n k := by
  apply Finset.prod_le_prod₀
  · intro i _
    exact (eulerFactor_pos (nthPrime_prime i)).le
  · intro i _
    dsimp [ksFactor]
    exact le_add_of_nonneg_right (by positivity)

private lemma log_nortonProduct_prefix (n k : ℕ) :
    log (nortonProduct n k) = weightPrefix (n - 1 + k) - weightPrefix (n - 1) := by
  rw [log_nortonProduct, sum_Ico_eq_sub (fun i => weight (prime i)) (by omega)]
  rfl

private lemma norton_crossing_exists (α : ℝ) (n : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ α < nortonProduct n k := by
  have htail : Tendsto (fun k => log (nortonProduct n k)) atTop atTop := by
    simp_rw [log_nortonProduct_prefix]
    have ht : Tendsto (fun k : ℕ => n - 1 + k) atTop atTop := by
      simpa only [Nat.add_comm] using tendsto_add_atTop_nat (n - 1)
    simpa only [sub_eq_add_neg, Function.comp_apply] using
      tendsto_atTop_add_const_right atTop (-weightPrefix (n - 1))
        (weightPrefix_diverges.comp ht)
  obtain ⟨k, hk⟩ := eventually_atTop.mp (htail.eventually_gt_atTop (log (max α 1)))
  refine ⟨max k 1, le_max_right _ _, ?_⟩
  have h := hk (max k 1) (le_max_left _ _)
  have hm : 0 < max α 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  exact (le_max_left α 1).trans_lt
    ((log_lt_log_iff hm (nortonProduct_pos _ _)).mp h)

private lemma aAlpha_spec (α : ℝ) (n : ℕ) :
    1 ≤ aAlpha α n ∧ α < nortonProduct n (aAlpha α n) :=
  csInf_mem (norton_crossing_exists α n)

private lemma aAlpha_minimal {α : ℝ} (hα : 1 < α) (n k : ℕ)
    (hk : k < aAlpha α n) : nortonProduct n k ≤ α := by
  by_contra h
  have hcross : α < nortonProduct n k := lt_of_not_ge h
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    simp [hkz, nortonProduct] at hcross
    linarith
  have hle : aAlpha α n ≤ k := csInf_le' ⟨hk1, hcross⟩
  omega

private lemma ks_crossing_exists (n : ℕ) :
    ∃ k : ℕ, 1 ≤ k ∧ 2 < ksProduct n k := by
  obtain ⟨k, hk, hcross⟩ := norton_crossing_exists 2 n
  exact ⟨k, hk, hcross.trans_le (nortonProduct_le_ksProduct n k)⟩

private lemma KS_spec (n : ℕ) : 1 ≤ KS n ∧ 2 < ksProduct n (KS n) :=
  csInf_mem (ks_crossing_exists n)

private lemma KS_le_a (n : ℕ) : KS n ≤ a n := by
  apply csInf_le'
  exact ⟨(aAlpha_spec 2 n).1,
    (aAlpha_spec 2 n).2.trans_le (nortonProduct_le_ksProduct n (a n))⟩

private lemma perturbation_sum_le {r t : ℕ} (_hrt : r ≤ t) :
    (∑ i ∈ Finset.Ico r t, perturbation (prime i)) ≤
      2 / (prime r : ℝ) := by
  classical
  let P : ℕ := prime r
  let g : ℕ → ℕ := fun i => prime i - P
  have hmono : Monotone prime := by
    change Monotone (Nat.nth Nat.Prime)
    exact (Nat.nth_strictMono Nat.infinite_setOfPred_prime).monotone
  have hP : 1 ≤ P := by
    exact (Nat.prime_nth_prime r).one_lt.le
  have hadd (i : ℕ) (hi : i ∈ Finset.Ico r t) : g i + P = prime i := by
    exact Nat.sub_add_cancel (hmono (Finset.mem_Ico.mp hi).1)
  have hinj : Set.InjOn g (Finset.Ico r t) := by
    intro i hi j hj hij
    apply (Nat.nth_strictMono Nat.infinite_setOfPred_prime).injective
    change prime i = prime j
    rw [← hadd i hi, ← hadd j hj, hij]
  have hs0 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hs : Summable (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + (P : ℝ)) ^ 2) := by
    simpa only [Nat.cast_add] using (summable_nat_add_iff P).mpr hs0
  calc
    _ ≤ ∑ i ∈ Finset.Ico r t, (1 : ℝ) / (prime i : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (perturbation_bounds (Nat.prime_nth_prime i)).2
    _ = ∑ j ∈ (Finset.Ico r t).image g,
        (1 : ℝ) / ((j : ℝ) + (P : ℝ)) ^ 2 := by
      rw [Finset.sum_image hinj]
      apply Finset.sum_congr rfl
      intro i hi
      have hc := congrArg (fun k : ℕ => (k : ℝ)) (hadd i hi)
      push_cast at hc
      rw [hc]
    _ ≤ ∑' j : ℕ, (1 : ℝ) / ((j : ℝ) + (P : ℝ)) ^ 2 :=
      Summable.sum_le_tsum _ (fun _ _ => by positivity) hs
    _ ≤ 2 / (P : ℝ) :=
      Mertens.sum_one_div_sq_le (by exact_mod_cast hP)
    _ = _ := rfl

private lemma norton_log_endpoint_of_loglog_error
    {α K P Q : ℝ} (hα : 1 < α) (_hK : 0 ≤ K)
    (hP : 2 ≤ P) (hPQ : P ≤ Q) (hlog : K ≤ Real.log P)
    (herror : |Real.log (Real.log Q) - Real.log (Real.log P) - Real.log α| ≤
      K / Real.log P) :
    |Real.log Q - α * Real.log P| ≤ 2 * α * K := by
  have hα0 : 0 < α := by linarith
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := hP0.trans_le hPQ
  have hLP : 0 < Real.log P := Real.log_pos (by linarith)
  have hLQ : 0 < Real.log Q := Real.log_pos (by linarith)
  let e : ℝ := Real.log (Real.log Q) - Real.log (Real.log P) - Real.log α
  have he : |e| ≤ K / Real.log P := herror
  have he1 : |e| ≤ 1 := he.trans
    ((div_le_iff₀ hLP).mpr (by simpa using hlog))
  have hexact : Real.log Q = α * Real.log P * Real.exp e := by
    calc
      Real.log Q = Real.exp (Real.log (Real.log Q)) := (Real.exp_log hLQ).symm
      _ = Real.exp (e + Real.log α + Real.log (Real.log P)) := by
        congr 1
        dsimp [e]
        ring
      _ = α * Real.log P * Real.exp e := by
        rw [Real.exp_add, Real.exp_add, Real.exp_log hα0, Real.exp_log hLP]
        ring
  calc
    |Real.log Q - α * Real.log P| =
        |α * Real.log P * (Real.exp e - 1)| := by
      rw [hexact]
      congr 1
      ring
    _ = (α * Real.log P) * |Real.exp e - 1| := by
      rw [abs_mul, abs_of_pos (mul_pos hα0 hLP)]
    _ ≤ (α * Real.log P) * (2 * |e|) :=
      mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le he1)
        (mul_pos hα0 hLP).le
    _ ≤ (α * Real.log P) * (2 * (K / Real.log P)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left he (by norm_num)) (mul_pos hα0 hLP).le
    _ = 2 * α * K := by
      field_simp [hLP.ne']

private lemma norton_endpoint_bounds_of_log_error
    {α D P Q : ℝ} (hP : 0 < P) (hQ : 0 < Q)
    (herror : |Real.log Q - α * Real.log P| ≤ D) :
    Real.exp (-D) * P ^ α ≤ Q ∧ Q ≤ Real.exp D * P ^ α := by
  obtain ⟨hl, hu⟩ := abs_le.mp herror
  constructor
  · calc
      Real.exp (-D) * P ^ α = Real.exp (-D + Real.log P * α) := by
        rw [Real.rpow_def_of_pos hP, Real.exp_add]
      _ ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Q := Real.exp_log hQ
  · calc
      Q = Real.exp (Real.log Q) := (Real.exp_log hQ).symm
      _ ≤ Real.exp (D + Real.log P * α) := Real.exp_le_exp.mpr (by nlinarith)
      _ = Real.exp D * P ^ α := by
        rw [Real.rpow_def_of_pos hP, Real.exp_add]

private lemma crossing_excess (α : ℝ) (hα : 1 < α) (n : ℕ) :
    0 < log (nortonProduct n (aAlpha α n)) - log α ∧
      log (nortonProduct n (aAlpha α n)) - log α ≤
        weight (prime (n - 1 + aAlpha α n - 1)) := by
  have hk := (aAlpha_spec α n).1
  have hα0 : 0 < α := by linarith
  have hcross := (log_lt_log_iff hα0
    (nortonProduct_pos n (aAlpha α n))).mpr (aAlpha_spec α n).2
  have hprev := log_le_log (nortonProduct_pos n (aAlpha α n - 1))
    (aAlpha_minimal hα n (aAlpha α n - 1) (by omega))
  have hrec : log (nortonProduct n (aAlpha α n)) =
      log (nortonProduct n (aAlpha α n - 1)) +
        weight (prime (n - 1 + aAlpha α n - 1)) := by
    simp only [log_nortonProduct_prefix]
    have hi : n - 1 + aAlpha α n =
        (n - 1 + aAlpha α n - 1) + 1 := by omega
    have hi' : n - 1 + (aAlpha α n - 1) =
        n - 1 + aAlpha α n - 1 := by omega
    have hs : weightPrefix (n - 1 + aAlpha α n) =
        weightPrefix (n - 1 + aAlpha α n - 1) +
          weight (prime (n - 1 + aAlpha α n - 1)) := by
      conv_lhs => rw [hi]
      exact sum_range_succ _ _
    rw [hs, hi']
    ring
  exact ⟨sub_pos.mpr hcross, by linarith⟩

private lemma starting_prime_tendsto :
    Tendsto (fun n : ℕ => (prime (n - 1) : ℝ)) atTop atTop := by
  exact tendsto_natCast_atTop_atTop.comp
    (((Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop).comp
      (tendsto_sub_atTop_nat 1))

private lemma prefix_errors :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      |weightPrefix k - (log (log (prime k)) + eulerMascheroniConstant)| ≤
        C / log (prime k) ∧
      |weightPrefix (k + 1) -
          (log (log (prime k)) + eulerMascheroniConstant)| ≤
        C / log (prime k) := by
  obtain ⟨C, hC⟩ := norton_prefix_mertens_bound
  refine ⟨|C| + 2, by positivity, fun k => ?_⟩
  have hlog : 0 < log (prime k : ℝ) :=
    log_pos (by exact_mod_cast (nthPrime_prime k).one_lt)
  have hi : |weightPrefix (k + 1) -
      (log (log (prime k)) + eulerMascheroniConstant)| ≤
      |C| / log (prime k) :=
    (hC k).trans (div_le_div_of_nonneg_right (le_abs_self C) hlog.le)
  have hw := (weight_bounds (nthPrime_prime k)).2.trans
    (div_le_div_of_nonneg_left (by norm_num) hlog
      (log_le_self (by exact_mod_cast (nthPrime_prime k).pos.le)))
  constructor
  · have heq : weightPrefix k -
        (log (log (prime k)) + eulerMascheroniConstant) =
        (weightPrefix (k + 1) -
          (log (log (prime k)) + eulerMascheroniConstant)) -
            weight (prime k) := by
      simp only [weightPrefix, sum_range_succ]
      ring
    rw [heq]
    have hh := abs_sub (weightPrefix (k + 1) -
      (log (log (prime k)) + eulerMascheroniConstant)) (weight (prime k))
    rw [abs_of_pos (weight_pos (nthPrime_prime k))] at hh
    calc
      _ ≤ |C| / log (prime k) + 2 / log (prime k) :=
        hh.trans (add_le_add hi hw)
      _ = _ := by ring
  · exact hi.trans (div_le_div_of_nonneg_right (by linarith) hlog.le)

private lemma block_loglog_error {C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ k : ℕ,
      |weightPrefix k - (log (log (prime k)) + eulerMascheroniConstant)| ≤
        C / log (prime k) ∧
      |weightPrefix (k + 1) -
          (log (log (prime k)) + eulerMascheroniConstant)| ≤
        C / log (prime k))
    (n k : ℕ) (hk : 1 ≤ k) :
    |log (nortonProduct n k) -
        (log (log (prime (n - 1 + k - 1))) -
          log (log (prime (n - 1))))| ≤
      2 * C / log (prime (n - 1)) := by
  let s := n - 1
  let t := n - 1 + k - 1
  have hst : s ≤ t := by dsimp [s, t]; omega
  have hPQ : (prime s : ℝ) ≤ prime t := by
    exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime hst)
  have hP0 : (0 : ℝ) < prime s := by
    exact_mod_cast (nthPrime_prime s).pos
  have hLP : 0 < log (prime s : ℝ) :=
    log_pos (by exact_mod_cast (nthPrime_prime s).one_lt)
  have hlogs := log_le_log hP0 hPQ
  have he₁ := (herr s).1
  have he₂ := (herr t).2
  have he₂' := he₂.trans (div_le_div_of_nonneg_left hC hLP hlogs)
  have hi : n - 1 + k = t + 1 := by dsimp [t]; omega
  rw [log_nortonProduct_prefix, hi]
  change |(weightPrefix (t + 1) - weightPrefix s) -
      (log (log (prime t)) - log (log (prime s)))| ≤
    2 * C / log (prime s)
  calc
    _ = |(weightPrefix (t + 1) -
          (log (log (prime t)) + eulerMascheroniConstant)) -
        (weightPrefix s -
          (log (log (prime s)) + eulerMascheroniConstant))| := by
      congr 1
      ring
    _ ≤ |weightPrefix (t + 1) -
          (log (log (prime t)) + eulerMascheroniConstant)| +
        |weightPrefix s -
          (log (log (prime s)) + eulerMascheroniConstant)| := abs_sub _ _
    _ ≤ C / log (prime s) + C / log (prime s) := add_le_add he₂' he₁
    _ = _ := by ring

private lemma endpoint_bounds_of_product_log_error
    (α : ℝ) (hα : 1 < α) (L : ℝ) (hL : 0 ≤ L) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ T : ℝ,
      ∀ n k : ℕ, 1 ≤ k → T ≤ log (prime (n - 1) : ℝ) →
        |log (nortonProduct n k) - log α| ≤
          L / log (prime (n - 1)) →
        c * (prime (n - 1) : ℝ) ^ α ≤
          (prime (n - 1 + k - 1) : ℝ) ∧
        (prime (n - 1 + k - 1) : ℝ) ≤
          C * (prime (n - 1) : ℝ) ^ α := by
  obtain ⟨B, hB, herrors⟩ := prefix_errors
  let K : ℝ := 2 * B + L
  let D : ℝ := 2 * α * K
  refine ⟨exp (-D), exp D, exp_pos _, exp_pos _, K, ?_⟩
  intro n k hk hlog hprod
  have hblock := block_loglog_error hB herrors n k hk
  have hP : (2 : ℝ) ≤ prime (n - 1) := by
    exact_mod_cast (nthPrime_prime (n - 1)).two_le
  have hPQ : (prime (n - 1) : ℝ) ≤ prime (n - 1 + k - 1) := by
    exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime
      (show n - 1 ≤ n - 1 + k - 1 by omega))
  have herr : |log (log (prime (n - 1 + k - 1))) -
      log (log (prime (n - 1))) - log α| ≤
        K / log (prime (n - 1)) := by
    calc
      _ = |(log (nortonProduct n k) - log α) -
          (log (nortonProduct n k) -
            (log (log (prime (n - 1 + k - 1))) -
              log (log (prime (n - 1)))))| := by
        congr 1
        ring
      _ ≤ |log (nortonProduct n k) - log α| +
          |log (nortonProduct n k) -
            (log (log (prime (n - 1 + k - 1))) -
              log (log (prime (n - 1))))| := abs_sub _ _
      _ ≤ L / log (prime (n - 1)) +
          2 * B / log (prime (n - 1)) := add_le_add hprod hblock
      _ = _ := by dsimp [K]; ring
  have hlogerr := norton_log_endpoint_of_loglog_error hα
    (by dsimp [K]; positivity) hP hPQ hlog herr
  exact norton_endpoint_bounds_of_log_error (by linarith)
    (lt_of_lt_of_le (by linarith) hPQ) hlogerr

/-- Norton endpoints have the power scale prescribed by the threshold. -/
theorem norton_endpoint_bounds (α : ℝ) (hα : 1 < α) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (prime (n - 1) : ℝ) ^ α ≤
          (prime (n - 1 + aAlpha α n - 1) : ℝ) ∧
        (prime (n - 1 + aAlpha α n - 1) : ℝ) ≤
          C * (prime (n - 1) : ℝ) ^ α := by
  obtain ⟨c, C, hc, hC, T, hT⟩ :=
    endpoint_bounds_of_product_log_error α hα 2 (by norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  have hlogtop := Real.tendsto_log_atTop.comp starting_prime_tendsto
  filter_upwards [hlogtop.eventually_ge_atTop T] with n hn
  have hk := (aAlpha_spec α n).1
  have hLP : 0 < log (prime (n - 1) : ℝ) :=
    log_pos (by exact_mod_cast (nthPrime_prime (n - 1)).one_lt)
  have hPQ : (prime (n - 1) : ℝ) ≤
      prime (n - 1 + aAlpha α n - 1) := by
    exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime
      (show n - 1 ≤ n - 1 + aAlpha α n - 1 by omega))
  have hexcess := crossing_excess α hα n
  have hw := (weight_bounds
    (nthPrime_prime (n - 1 + aAlpha α n - 1))).2
  have hwp : weight (prime (n - 1 + aAlpha α n - 1)) ≤
      2 / log (prime (n - 1) : ℝ) := by
    exact hw.trans (div_le_div_of_nonneg_left (by norm_num) hLP
      ((log_le_self (by positivity)).trans hPQ))
  apply hT n (aAlpha α n) hk hn
  rw [abs_of_pos hexcess.1]
  exact hexcess.2.trans hwp

private lemma weightPrefix_monotone : Monotone weightPrefix := by
  intro j k hjk
  apply sum_le_sum_of_subset_of_nonneg (range_mono hjk)
  intro i _ _
  exact (weight_pos (nthPrime_prime i)).le

/-- The shared interval cancels, leaving a positive-power lower bound for the
number of primes added at the upper end. -/
theorem norton_adjacent_cancellation (α : ℝ) (hα : 1 < α) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n in atTop,
      c * (prime (n - 1) : ℝ) ^ (α - 1) ≤
        (aAlpha α (n + 1) : ℝ) - aAlpha α n + 1 := by
  obtain ⟨c, C, hc, _hC, hend⟩ := norton_endpoint_bounds α hα
  have hPtop : Tendsto (fun n : ℕ => (prime (n - 1) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      ((Nat.nth_strictMono Nat.infinite_setOfPred_prime).tendsto_atTop.comp
        (tendsto_sub_atTop_nat 1))
  have hpower := (tendsto_rpow_atTop (by linarith : 0 < α - 1)).comp hPtop
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [hend, hpower.eventually (eventually_ge_atTop (4 / c)),
    eventually_ge_atTop 1] with n hnend hnlarge hn
  let P : ℝ := prime (n - 1)
  let e : ℕ := n - 1 + aAlpha α n
  let e' : ℕ := n + aAlpha α (n + 1)
  let Q : ℝ := prime (e - 1)
  have hP0 : 0 < P := by
    dsimp [P]
    exact_mod_cast (nthPrime_prime (n - 1)).pos
  have hQ0 : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (nthPrime_prime (e - 1)).pos
  have hQlower : c * P ^ α ≤ Q := hnend.1
  have hlarge : 4 ≤ c * P ^ (α - 1) := by
    have hh := (div_le_iff₀ hc).mp hnlarge
    simpa only [mul_comm, Function.comp_apply, P] using hh
  have hpow : P ^ α = P ^ (α - 1) * P := by
    calc
      P ^ α = P ^ ((α - 1) + 1) := by congr 1; ring
      _ = P ^ (α - 1) * P := by rw [Real.rpow_add hP0, Real.rpow_one]
  have hQfour : 4 * P ≤ Q := by
    rw [hpow, ← mul_assoc] at hQlower
    exact (mul_le_mul_of_nonneg_right hlarge hP0.le).trans hQlower
  have hsmall : 2 / Q ≤ 1 / (2 * P) := by
    apply (div_le_div_iff₀ hQ0 (by positivity : 0 < 2 * P)).mpr
    linarith
  have hshift : weightPrefix n =
      weightPrefix (n - 1) + weight (prime (n - 1)) := by
    simpa only [weightPrefix, Nat.sub_add_cancel hn] using
      sum_range_succ (fun i => weight (prime i)) (n - 1)
  have hold := log_nortonProduct_prefix n (aAlpha α n)
  change log (nortonProduct n (aAlpha α n)) =
    weightPrefix e - weightPrefix (n - 1) at hold
  have hnext := log_nortonProduct_prefix (n + 1) (aAlpha α (n + 1))
  simp only [Nat.add_sub_cancel] at hnext
  change log (nortonProduct (n + 1) (aAlpha α (n + 1))) =
    weightPrefix e' - weightPrefix n at hnext
  have hcancel : weightPrefix e' - weightPrefix e =
      weight (prime (n - 1)) +
        (log (nortonProduct (n + 1) (aAlpha α (n + 1))) - log α) -
        (log (nortonProduct n (aAlpha α n)) - log α) := by
    linarith
  have hnew := (crossing_excess α hα (n + 1)).1
  have hupper : log (nortonProduct n (aAlpha α n)) - log α ≤ 2 / Q :=
    (crossing_excess α hα n).2.trans (weight_bounds (nthPrime_prime (e - 1))).2
  have hweight : 1 / P ≤ weight (prime (n - 1)) :=
    (weight_bounds (nthPrime_prime (n - 1))).1
  have hhalf : 1 / P = 2 * (1 / (2 * P)) := by ring
  have hlower : 1 / (2 * P) ≤ weightPrefix e' - weightPrefix e := by
    linarith
  have hpos : 0 < weightPrefix e' - weightPrefix e :=
    lt_of_lt_of_le (one_div_pos.mpr (by positivity)) hlower
  have he : e ≤ e' := by
    by_contra h
    have hm := weightPrefix_monotone (le_of_lt (lt_of_not_ge h))
    linarith
  have hsum : weightPrefix e' - weightPrefix e =
      ∑ i ∈ Ico e e', weight (prime i) := by
    rw [sum_Ico_eq_sub (fun i => weight (prime i)) he]
    rfl
  have hsumupper : weightPrefix e' - weightPrefix e ≤
      ((e' - e : ℕ) : ℝ) * (2 / Q) := by
    rw [hsum]
    calc
      _ ≤ ∑ _i ∈ Ico e e', 2 / Q := by
        apply sum_le_sum
        intro i hi
        have hqi : prime (e - 1) ≤ prime i :=
          Nat.nth_monotone Nat.infinite_setOfPred_prime (by
            have := (mem_Ico.mp hi).1
            omega)
        exact (weight_bounds (nthPrime_prime i)).2.trans
          (div_le_div_of_nonneg_left (by norm_num) hQ0 (by dsimp [Q]; exact_mod_cast hqi))
      _ = _ := by simp
  let D : ℝ := ((e' - e : ℕ) : ℝ)
  have hD : D = (aAlpha α (n + 1) : ℝ) - aAlpha α n + 1 := by
    dsimp [D]
    rw [Nat.cast_sub he]
    dsimp [e, e']
    rw [Nat.cast_add, Nat.cast_add, Nat.cast_sub hn, Nat.cast_one]
    ring
  have hinterval : 1 / (2 * P) ≤ 2 * D / Q := by
    calc
      _ ≤ weightPrefix e' - weightPrefix e := hlower
      _ ≤ D * (2 / Q) := hsumupper
      _ = _ := by ring
  have hmul := (le_div_iff₀ hQ0).mp hinterval
  have hmul' := mul_le_mul_of_nonneg_right hmul (by positivity : 0 ≤ 2 * P)
  have heq : 1 / (2 * P) * Q * (2 * P) = Q := by
    field_simp [hP0.ne']
  rw [heq] at hmul'
  have hfinal : c / 4 * P ^ (α - 1) ≤ D := by
    rw [hpow, ← mul_assoc] at hQlower
    have hcancelP : c * P ^ (α - 1) ≤ 4 * D := by
      apply (mul_le_mul_iff_left₀ hP0).mp
      nlinarith
    nlinarith
  simpa only [P, hD] using hfinal

private lemma ksProduct_pos (n k : ℕ) : 0 < ksProduct n k := by
  apply prod_pos
  intro i _
  have h := eulerFactor_pos (nthPrime_prime i)
  dsimp [ksFactor]
  positivity

private lemma KS_minimal (n k : ℕ) (hk : k < KS n) : ksProduct n k ≤ 2 := by
  by_contra h
  have hcross : 2 < ksProduct n k := lt_of_not_ge h
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hkz : k = 0 := by omega
    simp [hkz, ksProduct] at hcross
  have hle : KS n ≤ k := csInf_le' ⟨hk1, hcross⟩
  omega

private lemma ks_crossing_excess (n : ℕ) :
    0 < log (ksProduct n (KS n)) - log 2 ∧
      log (ksProduct n (KS n)) - log 2 ≤
        weight (prime (n - 1 + KS n - 1)) +
          perturbation (prime (n - 1 + KS n - 1)) := by
  have hk := (KS_spec n).1
  have hc := (log_lt_log_iff (by norm_num : (0 : ℝ) < 2)
    (ksProduct_pos n (KS n))).mpr (KS_spec n).2
  have hp := log_le_log (ksProduct_pos n (KS n - 1))
    (KS_minimal n (KS n - 1) (by omega))
  have hr : log (ksProduct n (KS n)) = log (ksProduct n (KS n - 1)) +
      (weight (prime (n - 1 + KS n - 1)) +
        perturbation (prime (n - 1 + KS n - 1))) := by
    rw [log_ksProduct, log_ksProduct]
    have hi : n - 1 + KS n = (n - 1 + KS n - 1) + 1 := by omega
    have hi' : n - 1 + (KS n - 1) = n - 1 + KS n - 1 := by omega
    rw [hi']
    conv_lhs => rw [hi, sum_Ico_succ_top (by omega)]
  exact ⟨sub_pos.mpr hc, by linarith⟩

private lemma ks_log_error (n : ℕ) :
    |log (nortonProduct n (KS n)) - log 2| ≤
      5 / log (prime (n - 1) : ℝ) := by
  let P : ℝ := prime (n - 1)
  let B : ℝ := prime (n - 1 + KS n - 1)
  have hP : 2 ≤ P := by dsimp [P]; exact_mod_cast (nthPrime_prime (n - 1)).two_le
  have hB : P ≤ B := by
    dsimp [P, B, prime]
    exact_mod_cast (Nat.nth_monotone Nat.infinite_setOfPred_prime
      (show n - 1 ≤ n - 1 + KS n - 1 by have := (KS_spec n).1; omega))
  have hE := perturbation_sum_le (r := n - 1) (t := n - 1 + KS n) (by omega)
  have hE0 : 0 ≤ ∑ i ∈ Ico (n - 1) (n - 1 + KS n),
      perturbation (prime i) := by
    apply sum_nonneg
    intro i _
    exact (by positivity : 0 ≤ 1 / (4 * (prime i : ℝ) ^ 2)).trans
      (perturbation_bounds (nthPrime_prime i)).1
  have he := ks_crossing_excess n
  have hw := (weight_bounds (nthPrime_prime (n - 1 + KS n - 1))).2
  have hd := (perturbation_bounds (nthPrime_prime (n - 1 + KS n - 1))).2
  have hb0 : 0 < B := by linarith
  have hp0 : 0 < P := by linarith
  have hsmall : 1 / B ^ 2 ≤ 1 / P := by
    apply one_div_le_one_div_of_le hp0
    nlinarith
  have hw' : 2 / B ≤ 2 / P := div_le_div_of_nonneg_left (by norm_num) hp0 hB
  have hsum : log (ksProduct n (KS n)) = log (nortonProduct n (KS n)) +
      ∑ i ∈ Ico (n - 1) (n - 1 + KS n), perturbation (prime i) := by
    rw [log_ksProduct, log_nortonProduct, sum_add_distrib]
  change _ ≤ 2 / P at hE
  have hupper : log (ksProduct n (KS n)) - log 2 ≤ 3 / P := by
    calc
      _ ≤ _ := he.2
      _ ≤ 2 / B + 1 / B ^ 2 := add_le_add hw hd
      _ ≤ 2 / P + 1 / P := add_le_add hw' hsmall
      _ = _ := by ring
  have herr : |log (nortonProduct n (KS n)) - log 2| ≤ 5 / P := by
    apply abs_le.mpr
    have hnonneg : 0 ≤ 1 / P := by positivity
    simp only [div_eq_mul_inv] at hE hupper hnonneg ⊢
    constructor <;> linarith [he.1]
  exact herr.trans (div_le_div_of_nonneg_left (by norm_num)
    (log_pos (by linarith)) (log_le_self hp0.le))

private lemma ks_endpoint_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c * (prime (n - 1) : ℝ) ^ 2 ≤
          (prime (n - 1 + KS n - 1) : ℝ) ∧
        (prime (n - 1 + KS n - 1) : ℝ) ≤
          C * (prime (n - 1) : ℝ) ^ 2 := by
  obtain ⟨c, C, hc, hC, T, hT⟩ :=
    endpoint_bounds_of_product_log_error 2 (by norm_num) 5 (by norm_num)
  refine ⟨c, C, hc, hC, ?_⟩
  have hlogtop := Real.tendsto_log_atTop.comp starting_prime_tendsto
  filter_upwards [hlogtop.eventually_ge_atTop T] with n hn
  simpa only [Real.rpow_two] using hT n (KS n) (KS_spec n).1 hn (ks_log_error n)

private lemma finite_prime_square_sum_le_indexed (r t : ℕ) (hrt : r < t) :
    (∑ q ∈ (Finset.Ioc (prime r) (prime (t - 1))).filter Nat.Prime,
      (1 : ℝ) / (q : ℝ) ^ 2) ≤
      ∑ i ∈ Finset.Ico r t, (1 : ℝ) / (prime i : ℝ) ^ 2 := by
  classical
  let A := (Finset.Ioc (prime r) (prime (t - 1))).filter Nat.Prime
  let f : ℕ → ℕ := Nat.count Nat.Prime
  have hmono : StrictMono prime := by
    change StrictMono (Nat.nth Nat.Prime)
    exact Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have hrecover (q : ℕ) (hq : q ∈ A) : prime (f q) = q :=
    Nat.nth_count (Finset.mem_filter.mp hq).2
  have hinj : Set.InjOn f A := by
    intro q hq v hv hqv
    have heq := congrArg prime hqv
    rwa [hrecover q hq, hrecover v hv] at heq
  have hmem : A.image f ⊆ Finset.Ico r t := by
    intro i hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hi
    have hqI := Finset.mem_Ioc.mp (Finset.mem_filter.mp hq).1
    have hrq : r < f q := hmono.lt_iff_lt.mp (by
      rw [hrecover q hq]
      exact hqI.1)
    have hqt : f q ≤ t - 1 := hmono.le_iff_le.mp (by
      rw [hrecover q hq]
      exact hqI.2)
    exact Finset.mem_Ico.mpr ⟨hrq.le, by omega⟩
  change (∑ q ∈ A, (1 : ℝ) / (q : ℝ) ^ 2) ≤ _
  apply Finset.sum_le_sum_of_injOn f hinj hmem
  · intro q hq
    rw [hrecover q hq]
  · intro i _hi _hout
    positivity

private lemma perturbation_sum_eventually_lower (S : ℕ → ℕ)
    (hS : ∀ n, n - 1 < S n) {c : ℝ} (hc : 0 < c)
    (hB : ∀ᶠ n in Filter.atTop,
      c * (prime (n - 1) : ℝ) ^ 2 ≤ (prime (S n - 1) : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ n in Filter.atTop,
      d / ((prime (n - 1) : ℝ) * Real.log (prime (n - 1))) ≤
        ∑ i ∈ Finset.Ico (n - 1) (S n), perturbation (prime i) := by
  classical
  obtain ⟨C, hC, Y, hY, htail⟩ :=
    D5.S3.Arith.Robin.PriceRecord.PrimeSquareTail.prime_square_tail_uniform
      (1 / 2) (by norm_num)
  refine ⟨1 / 8, by norm_num, ?_⟩
  have hlarge : ∀ᶠ n in Filter.atTop,
      max Y (C / c) ≤ (prime (n - 1) : ℝ) :=
    starting_prime_tendsto.eventually_ge_atTop _
  filter_upwards [hB, hlarge] with n hBn hPn
  let P : ℝ := prime (n - 1)
  let B : ℝ := prime (S n - 1)
  change c * P ^ 2 ≤ B at hBn
  change max Y (C / c) ≤ P at hPn
  have hYP : Y ≤ P := (le_max_left _ _).trans hPn
  have hP1 : 1 < P := hY.trans_le hYP
  have hP0 : 0 < P := by linarith
  have hlog : 0 < Real.log P := Real.log_pos hP1
  have hscale : 0 < P * Real.log P := mul_pos hP0 hlog
  have hCdiv : C / c ≤ P := (le_max_right _ _).trans hPn
  have hCpc : C ≤ c * P := by
    simpa only [mul_comm] using (div_le_iff₀ hc).mp hCdiv
  have hCPB : C * P ≤ B := by
    calc
      _ ≤ (c * P) * P := mul_le_mul_of_nonneg_right hCpc hP0.le
      _ = c * P ^ 2 := by ring
      _ ≤ B := hBn
  have hh := htail P B hYP hCPB
  dsimp only [P, B] at hh
  simp only [Nat.floor_natCast] at hh
  let Q : ℝ := ∑ q ∈
    (Finset.Ioc (prime (n - 1)) (prime (S n - 1))).filter Nat.Prime,
      (1 : ℝ) / (q : ℝ) ^ 2
  have hhalf : (1 / 2 : ℝ) ≤ P * Real.log P * Q := by
    have hl := (abs_lt.mp hh).1
    change -(1 / 2 : ℝ) < P * Real.log P * Q - 1 at hl
    linarith
  have hsquare := finite_prime_square_sum_le_indexed (n - 1) (S n) (hS n)
  change Q ≤ _ at hsquare
  have hterm :
      (∑ i ∈ Finset.Ico (n - 1) (S n), (1 : ℝ) / (prime i : ℝ) ^ 2) ≤
        4 * ∑ i ∈ Finset.Ico (n - 1) (S n), perturbation (prime i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    have hp : (0 : ℝ) < prime i := by
      exact_mod_cast (Nat.prime_nth_prime i).pos
    have hp2 : 0 < (prime i : ℝ) ^ 2 := sq_pos_of_pos hp
    have hl := (perturbation_bounds (Nat.prime_nth_prime i)).1
    have hl' : 1 ≤ perturbation (prime i) * (4 * (prime i : ℝ) ^ 2) :=
      (div_le_iff₀ (by positivity)).mp hl
    apply (div_le_iff₀ hp2).mpr
    nlinarith only [hl']
  have hmass := hhalf.trans
    (mul_le_mul_of_nonneg_left (hsquare.trans hterm) hscale.le)
  change (1 / 8 : ℝ) / (P * Real.log P) ≤ _
  apply (div_le_iff₀ hscale).mpr
  nlinarith only [hmass]

theorem result : Tendsto (fun n => (a n : ℤ) - KS n) atTop atTop := by
  obtain ⟨c, C, hc, hC, hend⟩ := ks_endpoint_bounds
  obtain ⟨d, hd, hE⟩ := perturbation_sum_eventually_lower
    (fun n => n - 1 + KS n)
    (fun n => by have hk := (KS_spec n).1; omega) hc
    (hend.mono (fun _ hn => hn.1))
  let P : ℕ → ℝ := fun n => prime (n - 1)
  have hzero : Tendsto (fun n => log (P n) / P n) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp starting_prime_tendsto
  have hpos : ∀ᶠ n in atTop, 0 < log (P n) / P n := by
    apply Eventually.of_forall
    intro n
    have hp : (1 : ℝ) < P n := by dsimp [P]; exact_mod_cast (nthPrime_prime (n - 1)).one_lt
    exact div_pos (log_pos hp) (by linarith)
  have hquot : Tendsto (fun n => P n / log (P n)) atTop atTop := by
    simpa only [Function.comp_def, inv_div] using
      tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩)
  apply (tendsto_intCast_atTop_iff (R := ℝ)).mp
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [hend, hE,
    hquot.eventually_ge_atTop ((2 * b + 3) / (d * c))] with n hn hEn hqn
  let eA := n - 1 + a n
  let eB := n - 1 + KS n
  let B : ℝ := prime (eB - 1)
  let D : ℝ := (a n : ℝ) - KS n
  let E : ℝ := ∑ i ∈ Ico (n - 1) eB, perturbation (prime i)
  have hle := KS_le_a n
  have he : eB ≤ eA := by dsimp [eA, eB]; omega
  have hB2 : 2 ≤ B := by dsimp [B]; exact_mod_cast (nthPrime_prime (eB - 1)).two_le
  have hB0 : 0 < B := by linarith
  have hP2 : 2 ≤ P n := by dsimp [P]; exact_mod_cast (nthPrime_prime (n - 1)).two_le
  have hP0 : 0 < P n := by linarith
  have hlog : 0 < log (P n) := log_pos (by linarith)
  have hD : ((eA - eB : ℕ) : ℝ) = D := by
    rw [Nat.cast_sub he]
    dsimp [eA, eB, D]
    push_cast
    ring
  have hsum : (∑ i ∈ Ico eB eA, weight (prime i)) ≤ D * (2 / B) := by
    have hu : (∑ i ∈ Ico eB eA, weight (prime i)) ≤
        ∑ _i ∈ Ico eB eA, 2 / B := by
      apply sum_le_sum
      intro i hi
      have hqi : prime (eB - 1) ≤ prime i :=
        Nat.nth_monotone Nat.infinite_setOfPred_prime (by
          have hi' := (mem_Ico.mp hi).1
          omega)
      exact (weight_bounds (nthPrime_prime i)).2.trans
        (div_le_div_of_nonneg_left (by norm_num) hB0 (by dsimp [B]; exact_mod_cast hqi))
    simpa only [sum_const, nsmul_eq_mul, Nat.card_Ico, hD] using hu
  have hlogs : log (nortonProduct n (a n)) - log (nortonProduct n (KS n)) =
      ∑ i ∈ Ico eB eA, weight (prime i) := by
    rw [log_nortonProduct_prefix, log_nortonProduct_prefix,
      sum_Ico_eq_sub (fun i => weight (prime i)) he]
    change weightPrefix eA - weightPrefix (n - 1) -
      (weightPrefix eB - weightPrefix (n - 1)) = weightPrefix eA - weightPrefix eB
    ring
  have hsq : 1 / B ^ 2 ≤ 1 / B :=
    one_div_le_one_div_of_le hB0 (by nlinarith)
  have hu := (ks_crossing_excess n).2
  have hw := (weight_bounds (nthPrime_prime (eB - 1))).2
  have hp := (perturbation_bounds (nthPrime_prime (eB - 1))).2
  change weight (prime (eB - 1)) ≤ 2 / B at hw
  change perturbation (prime (eB - 1)) ≤ 1 / B ^ 2 at hp
  have huB : log (ksProduct n (KS n)) - log 2 ≤ 3 / B := by
    change _ ≤ weight (prime (eB - 1)) + perturbation (prime (eB - 1)) at hu
    have hh := hu.trans (add_le_add hw (hp.trans hsq))
    convert hh using 1 <;> ring
  have hidentity : log (ksProduct n (KS n)) =
      log (nortonProduct n (KS n)) + E := by
    rw [log_ksProduct, log_nortonProduct, sum_add_distrib]
  have hA := (crossing_excess 2 (by norm_num) n).1
  change 0 < log (nortonProduct n (a n)) - log 2 at hA
  have hEU : E ≤ (2 * D + 3) / B := by
    rw [← hlogs] at hsum
    have hh : E ≤ D * (2 / B) + 3 / B := by
      linarith only [hidentity, hsum, huB, hA]
    convert hh using 1 <;> ring
  change d / (P n * log (P n)) ≤ E at hEn
  have hineq := (div_le_div_iff₀ (mul_pos hP0 hlog) hB0).mp (hEn.trans hEU)
  have hBl : c * P n ^ 2 ≤ B := hn.1
  have hineq' : d * c * P n ≤ (2 * D + 3) * log (P n) := by
    apply (mul_le_mul_iff_left₀ hP0).mp
    nlinarith only [hineq, mul_le_mul_of_nonneg_left hBl hd.le]
  have hupper := (div_le_iff₀ hlog).mpr hineq'
  have hbig : 2 * b + 3 ≤ d * c * (P n / log (P n)) := by
    simpa only [mul_comm] using (div_le_iff₀ (mul_pos hd hc)).mp hqn
  have heq : d * c * (P n / log (P n)) = d * c * P n / log (P n) := by ring
  rw [heq] at hbig
  simp only [Int.cast_sub, Int.cast_natCast]
  change b ≤ D
  linarith only [hupper, hbig]

end D5.S3.Arith.Abundancy.BeriZelinskyQuestion6
