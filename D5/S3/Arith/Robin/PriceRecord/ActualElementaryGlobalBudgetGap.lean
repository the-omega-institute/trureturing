/- GID: D5/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PriceRecord/ActualElementaryGlobalBudgetGap
   mirror-E: none(waiver:general-asymptotic-analysis)
   anchors: []
   utility: none
   digest: Greatest feasible global optimizer and exact full original two-layer deletion and budget restrictions. -/

import D5.S3.Arith.Robin.ActualGlobalBracketing
import D5.S3.Arith.GoldenResource.GoldenResourceSupremum
import D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-
SOURCE PREPARATION ONLY: UNCOMPILED N0 OPEN.

The integer C below is constructed from the finite set of actual global
optimizers in [1,m]. Neither its existence nor its optimality is an endpoint
assumption. The proof inserts EACH omitted weak layer, with no bound on the
number of equality primes. All objectives are the literal project objective.

The c-canonical convention is exactly optimalLayerCount c 2, equivalently
(strictInteger c).factorization 2 at positive c. Equality layers are excluded
from that strict prefix and included in the full original tail with zero loss.
The occupied bad layer k may be anywhere in the original valuation interval.

The original bank modes 2,3,4,5,6,8,9,12, both directions, prescribed b/delta,
all fees, full payment, Robin/5040 and RH remain OPEN. No Six Exponentials or
tie-cardinality supplier is imported or assumed. No native check is claimed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap

open Finset
open scoped BigOperators
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenLocalThreshold
open D5.S3.Arith.GoldenResourceObjectiveFactorization
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.GoldenResource.GoldenResourceSupremum
open D5.S3.Arith.GoldenResource.FirstLayerMarginalAntitone
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.Robin.ActualTwoPriceDefect
open D5.S3.Arith.Robin.ActualGlobalBracketing

/-- Own-clock price, with the original integer's logarithm. -/
def ownPrice (m : ℕ) : ℝ :=
  1 / (Real.log (m : ℝ) * Real.log (Real.log (m : ℝ)))

/-- All original two-layers after the actual STRICT c-canonical cutoff. -/
def original2tail (m : ℕ) (c : ℝ) : Finset ℕ :=
  Icc (optimalLayerCount c 2 + 1) (m.factorization 2)

def h2 (m : ℕ) (c : ℝ) : ℝ :=
  ((m.factorization 2 - optimalLayerCount c 2 : ℕ) : ℝ) * Real.log 2

def J2 (m : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ original2tail m c, (c - goldenLayerMarginal 2 j) * Real.log 2

def ordinary2tailReward (m : ℕ) (c : ℝ) : ℝ :=
  ∑ j ∈ original2tail m c, goldenLayerMarginal 2 j * Real.log 2

/-- The actual positive integer obtained by deleting the ENTIRE original tail. -/
def deleted2tailInteger (m : ℕ) (c : ℝ) : ℕ :=
  m / 2 ^ (m.factorization 2 - optimalLayerCount c 2)

/-- Actual natural-order maximality, including every omitted equality prime. -/
structure GlobalBudgetGap (s : ℝ) (m C : ℕ) : Prop where
  positive : 1 ≤ C
  strict_le : strictInteger s ≤ C
  below : C < m
  weak_above : m < maximalInteger s
  global : IsGoldenResourceOptimal s C
  greatest : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsGoldenResourceOptimal s n → n ≤ C
  divides_weak : C ∣ maximalInteger s
  omitted_exists : ∃ q : ℕ, q.Prime ∧ C.factorization q < (maximalInteger s).factorization q
  gap_pos : 0 < Real.log ((m : ℝ) / C)
  omitted : ∀ q : ℕ, q.Prime →
    C.factorization q < (maximalInteger s).factorization q →
    goldenLayerMarginal q (C.factorization q + 1) = s ∧
    IsGoldenResourceOptimal s (q * C) ∧ m < q * C ∧
    Real.log ((m : ℝ) / C) < Real.log (q : ℝ) ∧
    s * (q : ℝ) * Real.log (q : ℝ) < 1
  exponential_bound :
    s * Real.log ((m : ℝ) / C) * Real.exp (Real.log ((m : ℝ) / C)) < 1

private theorem marginal_antitone {p i j : ℕ} (hp : p.Prime)
    (hi : 1 ≤ i) (hij : i ≤ j) :
    goldenLayerMarginal p j ≤ goldenLayerMarginal p i := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact (golden_layer_strict_decrease hp hi hlt).le

private theorem gap_positive {m C : ℕ} (hC : 1 ≤ C) (hCm : C < m) :
    0 < Real.log ((m : ℝ) / C) := by
  apply Real.log_pos
  exact (one_lt_div (by exact_mod_cast (show 0 < C by omega))).mpr
    (by exact_mod_cast hCm)

private theorem price_bound_of_zero {s : ℝ} {C q : ℕ} (hq : q.Prime)
    (hzero : goldenLayerMarginal q (C.factorization q + 1) = s) :
    s * (q : ℝ) * Real.log (q : ℝ) < 1 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hfirst : s ≤ goldenLayerMarginal q 1 := by
    rw [← hzero]
    exact marginal_antitone hq le_rfl (by omega)
  rw [golden_layer_marginal_one_eq_log_one_add_inv hq] at hfirst
  have hslog : s * Real.log (q : ℝ) ≤ Real.log (1 + 1 / (q : ℝ)) :=
    (le_div_iff₀ hlog).mp hfirst
  have hinv : 0 < 1 / (q : ℝ) := one_div_pos.mpr hq0
  have hloglt : Real.log (1 + 1 / (q : ℝ)) < 1 / (q : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos
      (show 0 < 1 + 1 / (q : ℝ) by linarith)
      (show 1 + 1 / (q : ℝ) ≠ 1 by linarith)
    linarith
  calc
    s * (q : ℝ) * Real.log (q : ℝ) = (s * Real.log (q : ℝ)) * q := by ring
    _ ≤ Real.log (1 + 1 / (q : ℝ)) * q := mul_le_mul_of_nonneg_right hslog hq0.le
    _ < (1 / (q : ℝ)) * q := mul_lt_mul_of_pos_right hloglt hq0
    _ = 1 := one_div_mul_cancel hq0.ne'

private theorem omitted_prime_step {s : ℝ} (hs : 0 < s) {m C q : ℕ}
    (hC : 1 ≤ C) (hCm : C < m) (hglobal : IsGoldenResourceOptimal s C)
    (hgreatest : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsGoldenResourceOptimal s n → n ≤ C)
    (hq : q.Prime) (hmiss : C.factorization q < (maximalInteger s).factorization q) :
    goldenLayerMarginal q (C.factorization q + 1) = s ∧
    IsGoldenResourceOptimal s (q * C) ∧ m < q * C ∧
    Real.log ((m : ℝ) / C) < Real.log (q : ℝ) ∧
    s * (q : ℝ) * Real.log (q : ℝ) < 1 := by
  have hupper := ((golden_resource_optimal_iff_layer_thresholds hs hC).mp hglobal).1 q hq
  have hlower : s ≤ goldenLayerMarginal q (C.factorization q + 1) :=
    (weak_layer_iff hs hq (by omega)).mp (by omega)
  have hzero : goldenLayerMarginal q (C.factorization q + 1) = s :=
    le_antisymm hupper hlower
  have heq : goldenResourceObjective s (q * C) = goldenResourceObjective s C := by
    simpa only [mul_comm] using golden_resource_objective_eq_of_layer_price s hC hq hzero
  have hnew : IsGoldenResourceOptimal s (q * C) := by
    intro n hn
    rw [heq]
    exact hglobal n hn
  have hnewpos : 1 ≤ q * C := by nlinarith [hq.two_le]
  have hCnew : C < q * C := by nlinarith [hq.two_le]
  have hmnew : m < q * C := by
    apply lt_of_not_ge
    intro hfeasible
    have hle := hgreatest (q * C) hnewpos hfeasible hnew
    omega
  have hC0 : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hgap : Real.log ((m : ℝ) / C) < Real.log (q : ℝ) := by
    apply Real.log_lt_log (div_pos hm0 hC0)
    apply (div_lt_iff₀ hC0).mpr
    exact_mod_cast hmnew
  exact ⟨hzero, hnew, hmnew, hgap, price_bound_of_zero hq hzero⟩

/-- Substantive adjacent-optimizer construction at ANY actual bracket price.
No existence, maximality, tie enumeration or prime-count premise for C occurs. -/
theorem greatest_feasible_global_gap {s : ℝ} (hs : 0 < s) {m : ℕ}
    (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s)
    (hnot : ¬ IsGoldenResourceOptimal s m) :
    ∃ C : ℕ, GlobalBudgetGap s m C := by
  classical
  let S := (Icc 1 m).filter (IsGoldenResourceOptimal s)
  have hS : S.Nonempty := by
    refine ⟨strictInteger s, mem_filter.mpr ⟨mem_Icc.mpr ⟨strictInteger_pos hs, hA⟩, ?_⟩⟩
    exact strict_is_optimal hs
  obtain ⟨C, hCS, hmax⟩ := S.exists_max_image id hS
  obtain ⟨hCI, hglobal⟩ := mem_filter.mp hCS
  obtain ⟨hC, hCmle⟩ := mem_Icc.mp hCI
  have hgreatest : ∀ n : ℕ, 1 ≤ n → n ≤ m → IsGoldenResourceOptimal s n → n ≤ C := by
    intro n hn hnm hnopt
    exact hmax n (mem_filter.mpr ⟨mem_Icc.mpr ⟨hn, hnm⟩, hnopt⟩)
  have hCm : C < m := by
    by_contra hnotlt
    have heq : C = m := by omega
    exact hnot (heq ▸ hglobal)
  have hmD : m < maximalInteger s := by
    by_contra hnotlt
    have heq : m = maximalInteger s := by omega
    exact hnot (heq.symm ▸ (maximalInteger_spec hs).2.2.1)
  have hCD : C < maximalInteger s := hCm.trans hmD
  have hex : ∃ q : ℕ, q.Prime ∧ C.factorization q < (maximalInteger s).factorization q := by
    obtain ⟨q, hq⟩ := Nat.exists_factorization_lt_of_lt (by omega : C ≠ 0) hCD
    refine ⟨q, ?_, hq⟩
    by_contra hnp
    simp only [Nat.factorization_eq_zero_of_not_prime _ hnp] at hq
    omega
  have hsteps (q : ℕ) (hq : q.Prime)
      (hmiss : C.factorization q < (maximalInteger s).factorization q) :=
    omitted_prime_step hs hC hCm hglobal hgreatest hq hmiss
  have hy := gap_positive hC hCm
  have hexp : s * Real.log ((m : ℝ) / C) * Real.exp (Real.log ((m : ℝ) / C)) < 1 := by
    obtain ⟨q, hq, hmiss⟩ := hex
    obtain ⟨_, _, _, hlog, hbound⟩ := hsteps q hq hmiss
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
    have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos (by exact_mod_cast hq.one_lt)
    have he : Real.exp (Real.log ((m : ℝ) / C)) < q := by
      simpa only [Real.exp_log hq0] using Real.exp_lt_exp.mpr hlog
    have hprod : Real.log ((m : ℝ) / C) * Real.exp (Real.log ((m : ℝ) / C)) <
        Real.log (q : ℝ) * q := by
      calc
        _ < Real.log (q : ℝ) * Real.exp (Real.log ((m : ℝ) / C)) :=
          mul_lt_mul_of_pos_right hlog (Real.exp_pos _)
        _ < Real.log (q : ℝ) * q := mul_lt_mul_of_pos_left he hqlog
    calc
      _ = s * (Real.log ((m : ℝ) / C) * Real.exp (Real.log ((m : ℝ) / C))) := by ring
      _ < s * (Real.log (q : ℝ) * q) := mul_lt_mul_of_pos_left hprod hs
      _ = s * (q : ℝ) * Real.log (q : ℝ) := by ring
      _ < 1 := hbound
  refine ⟨C, {
    positive := hC
    strict_le := hgreatest _ (strictInteger_pos hs) hA (strict_is_optimal hs)
    below := hCm
    weak_above := hmD
    global := hglobal
    greatest := hgreatest
    divides_weak := ((maximalInteger_spec hs).2.2.2 C hC hglobal).1
    omitted_exists := hex
    gap_pos := hy
    omitted := hsteps
    exponential_bound := hexp }⟩

/- Finite interval telescope. This is consumed by the ACTUAL integer deletion,
and later by the ordinary-reward bound; it is not an assumed tail identity. -/
private theorem local_interval_telescope {p : ℕ} (hp : p.Prime) (t : ℝ) (a r : ℕ) :
    goldenPrimeLocalObjective t p (a + r) - goldenPrimeLocalObjective t p a =
      ∑ j ∈ Icc (a + 1) (a + r), (goldenLayerMarginal p j - t) * Real.log p := by
  have hsplit : Icc 1 (a + r) = Icc 1 a ∪ Icc (a + 1) (a + r) := by
    ext j
    simp only [mem_Icc, mem_union]
    omega
  have hdisjoint : Disjoint (Icc 1 a) (Icc (a + 1) (a + r)) := by
    apply disjoint_left.mpr
    intro j hj htail
    simp only [mem_Icc] at hj htail
    omega
  have hfull := local_eq_layer_sum t hp (a + r)
  have hprefix := local_eq_layer_sum t hp a
  rw [hsplit, sum_union hdisjoint] at hfull
  calc
    goldenPrimeLocalObjective t p (a + r) - goldenPrimeLocalObjective t p a =
        ((∑ j ∈ Icc 1 a, Real.log p * (goldenLayerMarginal p j - t)) +
          (∑ j ∈ Icc (a + 1) (a + r),
            Real.log p * (goldenLayerMarginal p j - t))) -
          (∑ j ∈ Icc 1 a, Real.log p * (goldenLayerMarginal p j - t)) := by
      rw [hfull, hprefix]
    _ = ∑ j ∈ Icc (a + 1) (a + r),
        Real.log p * (goldenLayerMarginal p j - t) := by ring
    _ = ∑ j ∈ Icc (a + 1) (a + r),
        (goldenLayerMarginal p j - t) * Real.log p := by
      apply sum_congr rfl
      intro j _
      ring

private theorem delete_prime_power_tail {m p a : ℕ} (hm : 1 ≤ m)
    (hp : p.Prime) (ha : a ≤ m.factorization p) (t : ℝ) :
    let r := m.factorization p - a
    let n := m / p ^ r
    1 ≤ n ∧ n.factorization p = a ∧ n * p ^ r = m ∧
    goldenResourceObjective t m - goldenResourceObjective t n =
      ∑ j ∈ Icc (a + 1) (m.factorization p),
        (goldenLayerMarginal p j - t) * Real.log p := by
  classical
  dsimp only
  let r := m.factorization p - a
  let n := m / p ^ r
  have hm0 : m ≠ 0 := by omega
  have hd : p ^ r ∣ m := (hp.pow_dvd_iff_le_factorization hm0).mpr (by dsimp [r]; omega)
  have hnp : 1 ≤ n := Nat.div_pos (Nat.le_of_dvd (by omega) hd) (pow_pos hp.pos _)
  have hmul : n * p ^ r = m := Nat.div_mul_cancel hd
  have hfac : n.factorization p = a := by
    dsimp [n]
    rw [Nat.factorization_div hd, Finsupp.tsub_apply,
      hp.factorization_pow, Finsupp.single_eq_same]
    dsimp [r]
    omega
  have hother (q : ℕ) (hqp : q ≠ p) : n.factorization q = m.factorization q := by
    dsimp [n]
    rw [Nat.factorization_div hd, Finsupp.tsub_apply, hp.factorization_pow]
    simp [hqp, Ne.symm hqp]
  let S := insert p (m.primeFactors ∪ n.primeFactors)
  have hmsub : m.primeFactors ⊆ S := subset_union_left.trans (subset_insert _ _)
  have hnsub : n.primeFactors ⊆ S := subset_union_right.trans (subset_insert _ _)
  have hdelta : goldenResourceObjective t m - goldenResourceObjective t n =
      goldenPrimeLocalObjective t p (m.factorization p) - goldenPrimeLocalObjective t p a := by
    rw [golden_resource_objective_sum_on t hm S hmsub,
      golden_resource_objective_sum_on t hnp S hnsub, ← sum_sub_distrib]
    rw [sum_eq_single p]
    · rw [hfac]
    · intro q _ hqp
      rw [hother q hqp, sub_self]
    · intro hpnot
      exact (hpnot (mem_insert_self _ _)).elim
  refine ⟨hnp, hfac, hmul, ?_⟩
  rw [hdelta]
  have har : a + r = m.factorization p := by dsimp [r]; omega
  simpa only [har] using local_interval_telescope hp t a r

private theorem tail_card (m : ℕ) (c : ℝ) :
    (original2tail m c).card = m.factorization 2 - optimalLayerCount c 2 := by
  simp only [original2tail, Nat.card_Icc]
  omega

/-- Exact full-tail telescope at EVERY comparison price t, including mu and s.
The hypotheses concern the original integer and its actual canonical cutoff. -/
theorem full_original2tail_deletion_identity {m : ℕ} (hm : 1 ≤ m) {c : ℝ}
    (ha : optimalLayerCount c 2 ≤ m.factorization 2) (t : ℝ) :
    1 ≤ deleted2tailInteger m c ∧
    (deleted2tailInteger m c).factorization 2 = optimalLayerCount c 2 ∧
    deleted2tailInteger m c * 2 ^ (m.factorization 2 - optimalLayerCount c 2) = m ∧
    goldenResourceObjective t m - goldenResourceObjective t (deleted2tailInteger m c) =
      (c - t) * h2 m c - J2 m c := by
  obtain ⟨hn, hfac, hmul, hdelta⟩ := delete_prime_power_tail hm Nat.prime_two ha t
  refine ⟨hn, hfac, hmul, ?_⟩
  rw [hdelta]
  change (∑ j ∈ original2tail m c, (goldenLayerMarginal 2 j - t) * Real.log 2) =
    (c - t) * h2 m c - J2 m c
  have hterm : (∑ j ∈ original2tail m c, (goldenLayerMarginal 2 j - t) * Real.log 2) =
      ∑ j ∈ original2tail m c,
        ((c - t) * Real.log 2 - (c - goldenLayerMarginal 2 j) * Real.log 2) := by
    apply sum_congr rfl
    intro j _
    ring
  rw [hterm, sum_sub_distrib, sum_const, tail_card, nsmul_eq_mul]
  dsimp only [h2, J2]
  ring

private theorem tail_layer_nonnegative {c : ℝ} (hc : 0 < c) {m j : ℕ}
    (hj : j ∈ original2tail m c) :
    0 ≤ (c - goldenLayerMarginal 2 j) * Real.log 2 := by
  obtain ⟨haj, _⟩ := mem_Icc.mp hj
  have hj1 : 1 ≤ j := by omega
  have hnot : ¬ c < goldenLayerMarginal 2 j := by
    intro hactive
    have hjle := (strict_layer_iff hc Nat.prime_two hj1).mpr hactive
    rw [strictInteger_counts hc] at hjle
    omega
  exact mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot)) (Real.log_pos (by norm_num)).le

private theorem original_tail_record_data {m k : ℕ} (hm : 1 ≤ m) {c mu : ℝ}
    (hc : 0 < c) (hk : 1 ≤ k) (hkv : k ≤ m.factorization 2)
    (hbad : goldenLayerMarginal 2 k < c)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m) :
    optimalLayerCount c 2 < m.factorization 2 ∧
    0 < h2 m c ∧ 0 < J2 m c ∧
    1 ≤ deleted2tailInteger m c ∧ deleted2tailInteger m c < m ∧
    J2 m c < (c - mu) * h2 m c ∧ mu < c := by
  have hak : optimalLayerCount c 2 < k := by
    apply lt_of_not_ge
    intro hka
    have hactive := (strict_layer_iff hc Nat.prime_two hk).mp
      (by rw [strictInteger_counts hc]; exact hka)
    linarith
  have hav : optimalLayerCount c 2 < m.factorization 2 := hak.trans_le hkv
  have hh : 0 < h2 m c := by
    unfold h2
    exact mul_pos (by exact_mod_cast (show 0 < m.factorization 2 - optimalLayerCount c 2 by omega))
      (Real.log_pos (by norm_num))
  have hJ : 0 < J2 m c := by
    apply sum_pos' (fun j hj => tail_layer_nonnegative hc hj)
    exact ⟨k, mem_Icc.mpr ⟨by omega, hkv⟩,
      mul_pos (sub_pos.mpr hbad) (Real.log_pos (by norm_num))⟩
  obtain ⟨hn, _, hmul, hdelta⟩ := full_original2tail_deletion_identity hm hav.le mu
  have hr : 0 < m.factorization 2 - optimalLayerCount c 2 := by omega
  have hpow : 2 ≤ (2 : ℕ) ^ (m.factorization 2 - optimalLayerCount c 2) := by
    let r := m.factorization 2 - optimalLayerCount c 2
    change 2 ≤ 2 ^ r
    rw [show r = (r - 1) + 1 by dsimp [r]; omega, pow_succ]
    have hp : 0 < (2 : ℕ) ^ (r - 1) := by positivity
    omega
  have hnm : deleted2tailInteger m c < m := by nlinarith
  have hstrict := hrecord (deleted2tailInteger m c) (by omega) hnm
  have hrec : J2 m c < (c - mu) * h2 m c := by linarith
  have hmc : mu < c := by
    have hpos : 0 < (c - mu) * h2 m c := hJ.trans hrec
    exact sub_pos.mp ((mul_pos_iff_of_pos_right hh).mp hpos)
  exact ⟨hav, hh, hJ, hn, hnm, hrec, hmc⟩

private theorem objective_price_difference (mu s : ℝ) {m C : ℕ}
    (hm : 1 ≤ m) (hC : 1 ≤ C) :
    goldenResourceObjective s C - goldenResourceObjective s m =
      goldenResourceObjective mu C - goldenResourceObjective mu m +
        (s - mu) * Real.log ((m : ℝ) / C) := by
  rw [Real.log_div (by exact_mod_cast (show m ≠ 0 by omega))
    (by exact_mod_cast (show C ≠ 0 by omega))]
  simp only [goldenResourceObjective]
  ring

private theorem omitted_prime_lt_clock {m q : ℕ} {s : ℝ}
    (hT : 1 < Real.log (m : ℝ)) (hsc : ownPrice m ≤ s)
    (hq : q.Prime) (hbound : s * (q : ℝ) * Real.log (q : ℝ) < 1) :
    (q : ℝ) < Real.log (m : ℝ) := by
  let T := Real.log (m : ℝ)
  have hT0 : 0 < T := by dsimp [T]; linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT
  have hden : 0 < T * Real.log T := mul_pos hT0 hlogT
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hq0 : (0 : ℝ) < q := by linarith
  have hqlog : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hsmall : (1 / (T * Real.log T)) * ((q : ℝ) * Real.log (q : ℝ)) < 1 := by
    have hle := mul_le_mul_of_nonneg_right hsc (mul_pos hq0 hqlog).le
    dsimp only [ownPrice] at hle
    change 1 / (T * Real.log T) * ((q : ℝ) * Real.log (q : ℝ)) ≤
      s * ((q : ℝ) * Real.log (q : ℝ)) at hle
    exact hle.trans_lt (by nlinarith only [hbound])
  have hqT : (q : ℝ) * Real.log (q : ℝ) < T * Real.log T := by
    have hdiv : ((q : ℝ) * Real.log (q : ℝ)) / (T * Real.log T) < 1 := by
      simpa only [one_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hsmall
    simpa only [one_mul] using (div_lt_iff₀ hden).mp hdiv
  have he : Real.exp (-1 : ℝ) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show (-1 : ℝ) ≤ 0 by norm_num)
  change (q : ℝ) < T
  by_contra hnq
  have hTq : T ≤ (q : ℝ) := le_of_not_gt hnq
  have hmono := Real.mul_log_strictMonoOn.monotoneOn
    (he.trans hT.le) (he.trans hq1.le) hTq
  exact (not_lt_of_ge hmono) hqT

private theorem two_geometric_numerator_pos (n : ℕ) :
    0 < 1 - (2 : ℝ)⁻¹ ^ (n + 1) := by
  exact sub_pos.mpr (pow_lt_one₀ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1) (by omega : n + 1 ≠ 0))

private theorem two_geometric_full_numerator_pos (n : ℕ) :
    0 < 2 - (2 : ℝ)⁻¹ ^ n := by
  have heq : 2 - (2 : ℝ)⁻¹ ^ n = 2 * (1 - (2 : ℝ)⁻¹ ^ (n + 1)) := by
    rw [pow_succ]
    norm_num <;> ring
  rw [heq]
  exact mul_pos (by norm_num) (two_geometric_numerator_pos n)

/-- Exact ordinary reward of the SAME full tail. The right side is the
literal log((2-2^(-v))/(2-2^(-a))), with inverse natural powers. -/
theorem full_original2tail_reward_telescope {m : ℕ} {c : ℝ}
    (ha : optimalLayerCount c 2 ≤ m.factorization 2) :
    ordinary2tailReward m c =
      Real.log ((2 - (2 : ℝ)⁻¹ ^ (m.factorization 2)) /
        (2 - (2 : ℝ)⁻¹ ^ (optimalLayerCount c 2))) := by
  have ht := local_interval_telescope Nat.prime_two 0 (optimalLayerCount c 2)
    (m.factorization 2 - optimalLayerCount c 2)
  rw [show optimalLayerCount c 2 + (m.factorization 2 - optimalLayerCount c 2) =
    m.factorization 2 by omega] at ht
  have hlocal : ordinary2tailReward m c =
      goldenPrimeLocalObjective 0 2 (m.factorization 2) -
        goldenPrimeLocalObjective 0 2 (optimalLayerCount c 2) := by
    simpa only [ordinary2tailReward, original2tail, sub_zero] using ht.symm
  rw [hlocal]
  simp only [goldenPrimeLocalObjective, zero_mul, sub_zero]
  have hv := two_geometric_numerator_pos (m.factorization 2)
  have hc := two_geometric_numerator_pos (optimalLayerCount c 2)
  calc
    _ = Real.log (1 - (2 : ℝ)⁻¹ ^ (m.factorization 2 + 1)) -
        Real.log (1 - (2 : ℝ)⁻¹ ^ (optimalLayerCount c 2 + 1)) := by
      rw [Real.log_div hv.ne' (by norm_num : (1 : ℝ) - (2 : ℝ)⁻¹ ≠ 0),
        Real.log_div hc.ne' (by norm_num : (1 : ℝ) - (2 : ℝ)⁻¹ ≠ 0)]
      ring
    _ = _ := by
      rw [← Real.log_div hv.ne' hc.ne']
      congr 1
      apply (div_eq_div_iff hc.ne' (two_geometric_full_numerator_pos _).ne').mpr
      rw [pow_succ, pow_succ]
      norm_num <;> ring

private theorem reward_deficit_identity (m : ℕ) (c : ℝ) :
    ordinary2tailReward m c = c * h2 m c - J2 m c := by
  have hsum : ordinary2tailReward m c + J2 m c =
      ∑ _j ∈ original2tail m c, c * Real.log 2 := by
    rw [ordinary2tailReward, J2, ← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    ring
  rw [sum_const, tail_card, nsmul_eq_mul] at hsum
  dsimp only [h2]
  nlinarith only [hsum]

/-- The full ordinary reward is smaller than twice the first tail reward,
and hence smaller than 2*c*log 2. No layer is dropped from U2, h2 or J2. -/
theorem full_original2tail_reward_bound {m : ℕ} {c : ℝ} (hc : 0 < c)
    (ha : optimalLayerCount c 2 ≤ m.factorization 2) :
    ordinary2tailReward m c <
        2 * (goldenLayerMarginal 2 (optimalLayerCount c 2 + 1) * Real.log 2) ∧
      ordinary2tailReward m c < 2 * c * Real.log 2 := by
  let a := optimalLayerCount c 2
  let v := m.factorization 2
  let x : ℝ := (2 : ℝ)⁻¹ ^ (a + 1)
  let z : ℝ := (2 : ℝ)⁻¹ ^ (v + 1)
  let R : ℝ := (1 - x / 2) / (1 - x)
  have hx : 0 < x := pow_pos (by norm_num) _
  have hd : 0 < 1 - x := two_geometric_numerator_pos a
  have hz : 0 < z := pow_pos (by norm_num) _
  have hv : 0 < 1 - z := two_geometric_numerator_pos v
  have htel : ordinary2tailReward m c = Real.log ((1 - z) / (1 - x)) := by
    rw [full_original2tail_reward_telescope ha]
    change Real.log ((2 - (2 : ℝ)⁻¹ ^ v) / (2 - (2 : ℝ)⁻¹ ^ a)) = _
    congr 1
    apply (div_eq_div_iff (two_geometric_full_numerator_pos a).ne' hd.ne').mpr
    dsimp only [x, z]
    rw [pow_succ, pow_succ]
    norm_num <;> ring
  have hfirst : Real.log ((1 - z) / (1 - x)) < Real.log (1 / (1 - x)) := by
    apply Real.log_lt_log (div_pos hv hd)
    exact div_lt_div_of_pos_right (by linarith : 1 - z < 1) hd
  have hsquare : 1 - x < (1 - x / 2) ^ 2 := by nlinarith [sq_pos_of_pos hx]
  have hsqratio : 1 / (1 - x) < R ^ 2 := by
    have hdiv := div_lt_div_of_pos_right hsquare (pow_pos hd 2)
    have heq : (1 - x) / (1 - x) ^ 2 = 1 / (1 - x) := by
      field_simp [hd.ne'] <;> ring
    rw [heq] at hdiv
    simpa only [R, div_pow] using hdiv
  have hsecond := Real.log_lt_log (one_div_pos.mpr hd) hsqratio
  rw [Real.log_pow] at hsecond
  have hnext : goldenLayerMarginal 2 (a + 1) * Real.log 2 = Real.log R := by
    unfold goldenLayerMarginal
    rw [div_mul_cancel₀ _ (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
    congr 1
    dsimp only [R, x]
    rw [pow_succ]
    norm_num <;> ring
  have hU : ordinary2tailReward m c <
      2 * (goldenLayerMarginal 2 (a + 1) * Real.log 2) := by
    rw [htel, hnext]
    linarith
  have hnextle : goldenLayerMarginal 2 (a + 1) ≤ c := by
    apply le_of_not_gt
    intro hactive
    have hcount := (strict_layer_iff hc Nat.prime_two (by omega : 1 ≤ a + 1)).mpr hactive
    rw [strictInteger_counts hc] at hcount
    change a + 1 ≤ a at hcount
    omega
  have hle : 2 * (goldenLayerMarginal 2 (a + 1) * Real.log 2) ≤ 2 * c * Real.log 2 := by
    have ht := mul_le_mul_of_nonneg_right hnextle
      (show 0 ≤ 2 * Real.log (2 : ℝ) by positivity)
    nlinarith only [ht]
  exact ⟨hU, hU.trans_le hle⟩

/-- Full original-tail restrictions, with no bank-occupancy premise. -/
structure FullTailBudgetRestriction (mu s : ℝ) (m C : ℕ) : Prop where
  canonical_tail_nonempty : optimalLayerCount (ownPrice m) 2 < m.factorization 2
  tail_volume_pos : 0 < h2 m (ownPrice m)
  tail_loss_pos : 0 < J2 m (ownPrice m)
  original_price_below : mu < ownPrice m
  bracket_price_above : mu < s
  deletion_positive : 1 ≤ deleted2tailInteger m (ownPrice m)
  deletion_below : deleted2tailInteger m (ownPrice m) < m
  original_record_budget : J2 m (ownPrice m) < (ownPrice m - mu) * h2 m (ownPrice m)
  stronger_budget : J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m) <
    (s - mu) * Real.log ((m : ℝ) / C)
  ratio_monotone : J2 m (ownPrice m) / (ownPrice m - mu) ≤
    (J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m)) / (s - mu)
  stronger_ratio : (J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m)) / (s - mu) <
    Real.log ((m : ℝ) / C)
  forbidden_lower : J2 m (ownPrice m) / (ownPrice m - mu) < Real.log ((m : ℝ) / C)
  forbidden_upper : Real.log ((m : ℝ) / C) < Real.log (Real.log (m : ℝ))
  every_omitted_below_clock : ∀ q : ℕ, q.Prime →
    C.factorization q < (maximalInteger s).factorization q →
    (q : ℝ) < Real.log (m : ℝ) ∧ Real.log (q : ℝ) < Real.log (Real.log (m : ℝ))
  ordinary_reward_bound : ordinary2tailReward m (ownPrice m) < 2 * ownPrice m * Real.log 2
  tail_length_bound : h2 m (ownPrice m) < Real.log ((m : ℝ) / C) + 2 * Real.log 2
  tail_power_bound :
    (2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2) < 4 * Real.log (m : ℝ)

/-- Main full original2-tail endpoint at ANY actual bracket s >= c.
The strict original mu-record is over ALL positive strict predecessors.
Only the original occupied bad layer is required; no U != empty is needed. -/
theorem full_original2tail_forbidden_budget {m k : ℕ} (hm : 1 ≤ m)
    (hT : 1 < Real.log (m : ℝ)) {mu s : ℝ} (hmu : 0 < mu)
    (hrecord : ∀ n : ℕ, 0 < n → n < m →
      goldenResourceObjective mu n < goldenResourceObjective mu m)
    (hk : 1 ≤ k) (hkv : k ≤ m.factorization 2)
    (hbad : goldenLayerMarginal 2 k < ownPrice m)
    (hs : 0 < s) (hA : strictInteger s ≤ m) (hD : m ≤ maximalInteger s)
    (hsc : ownPrice m ≤ s) :
    ∃ C : ℕ, GlobalBudgetGap s m C ∧ FullTailBudgetRestriction mu s m C := by
  have hc : 0 < ownPrice m :=
    one_div_pos.mpr (mul_pos (by linarith : 0 < Real.log (m : ℝ)) (Real.log_pos hT))
  obtain ⟨hav, hh, hJ, hn, hnm, hrec, hmc⟩ :=
    original_tail_record_data hm hc hk hkv hbad hrecord
  have hsmu : mu < s := hmc.trans_le hsc
  have hdelete := (full_original2tail_deletion_identity hm hav.le s).2.2.2
  have hnot : ¬ IsGoldenResourceOptimal s m := by
    intro hopt
    have hcomp := hopt (deleted2tailInteger m (ownPrice m)) hn
    have hnonpos := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hsc) hh.le
    linarith
  obtain ⟨C, hgap⟩ := greatest_feasible_global_gap hs hA hD hnot
  have hlower : J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m) ≤
      goldenResourceObjective s C - goldenResourceObjective s m := by
    have hcomp := hgap.global (deleted2tailInteger m (ownPrice m)) hn
    linarith
  have hupper : goldenResourceObjective s C - goldenResourceObjective s m <
      (s - mu) * Real.log ((m : ℝ) / C) := by
    have hstrict := hrecord C (by have := hgap.positive; omega) hgap.below
    rw [objective_price_difference mu s hm hgap.positive]
    linarith
  have hstrong := hlower.trans_lt hupper
  have hratio : J2 m (ownPrice m) / (ownPrice m - mu) ≤
      (J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m)) / (s - mu) := by
    apply (div_le_div_iff₀ (sub_pos.mpr hmc) (sub_pos.mpr hsmu)).mpr
    have hprod := mul_nonneg (sub_nonneg.mpr hsc) (sub_pos.mpr hrec).le
    nlinarith only [hprod]
  have hstrongratio :
      (J2 m (ownPrice m) + (s - ownPrice m) * h2 m (ownPrice m)) / (s - mu) <
        Real.log ((m : ℝ) / C) := by
    apply (div_lt_iff₀ (sub_pos.mpr hsmu)).mpr
    simpa only [mul_comm] using hstrong
  have hclock : ∀ q : ℕ, q.Prime →
      C.factorization q < (maximalInteger s).factorization q →
      (q : ℝ) < Real.log (m : ℝ) ∧ Real.log (q : ℝ) < Real.log (Real.log (m : ℝ)) := by
    intro q hq hmiss
    have hbound := (hgap.omitted q hq hmiss).2.2.2.2
    have hqT := omitted_prime_lt_clock hT hsc hq hbound
    exact ⟨hqT, Real.log_lt_log (by exact_mod_cast hq.pos) hqT⟩
  have hlast : Real.log ((m : ℝ) / C) < Real.log (Real.log (m : ℝ)) := by
    obtain ⟨q, hq, hmiss⟩ := hgap.omitted_exists
    exact ((hgap.omitted q hq hmiss).2.2.2.1).trans (hclock q hq hmiss).2
  have hreward := (full_original2tail_reward_bound hc hav.le).2
  have hreward_s : ordinary2tailReward m (ownPrice m) < 2 * s * Real.log 2 := by
    apply hreward.trans_le
    have ht := mul_le_mul_of_nonneg_right hsc
      (show 0 ≤ 2 * Real.log (2 : ℝ) by positivity)
    nlinarith only [ht]
  have hlength : h2 m (ownPrice m) < Real.log ((m : ℝ) / C) + 2 * Real.log 2 := by
    have hU := reward_deficit_identity m (ownPrice m)
    have hmuy := mul_pos hmu hgap.gap_pos
    have hmul : s * h2 m (ownPrice m) <
        s * (Real.log ((m : ℝ) / C) + 2 * Real.log 2) := by
      nlinarith only [hstrong, hreward_s, hU, hmuy]
    exact (mul_lt_mul_left hs).mp hmul
  have hpower : (2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2) <
      4 * Real.log (m : ℝ) := by
    have hT0 : 0 < Real.log (m : ℝ) := by linarith
    have hlogpow :
        Real.log ((2 : ℝ) ^ (m.factorization 2 - optimalLayerCount (ownPrice m) 2)) =
          h2 m (ownPrice m) := by
      rw [Real.log_pow]
      rfl
    have hlog4 : Real.log (4 * Real.log (m : ℝ)) =
        Real.log (Real.log (m : ℝ)) + 2 * Real.log 2 := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT0.ne']
      have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num, Nat.cast_ofNat] using Real.log_pow (2 : ℝ) 2
      rw [h4]
      ring
    apply (Real.log_lt_log_iff (by positivity) (mul_pos (by norm_num) hT0)).mp
    rw [hlogpow, hlog4]
    linarith
  refine ⟨C, hgap, {
    canonical_tail_nonempty := hav
    tail_volume_pos := hh
    tail_loss_pos := hJ
    original_price_below := hmc
    bracket_price_above := hsmu
    deletion_positive := hn
    deletion_below := hnm
    original_record_budget := hrec
    stronger_budget := hstrong
    ratio_monotone := hratio
    stronger_ratio := hstrongratio
    forbidden_lower := hratio.trans_lt hstrongratio
    forbidden_upper := hlast
    every_omitted_below_clock := hclock
    ordinary_reward_bound := hreward
    tail_length_bound := hlength
    tail_power_bound := hpower }⟩

/- These commands are for the owning tree's LATER native run. They have not
been executed in this source-preparation packet. -/
#print axioms greatest_feasible_global_gap
#print axioms full_original2tail_deletion_identity
#print axioms full_original2tail_reward_telescope
#print axioms full_original2tail_forbidden_budget

end D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap
