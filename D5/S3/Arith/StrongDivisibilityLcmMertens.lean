/- GID: D5/S3/Arith/StrongDivisibilityLcmMertens
   generality: G
   mirror-B: D5/B/S3/Arith/StrongDivisibilityLcmMertens
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.NumberTheory.ArithmeticFunction.Moebius]
   utility: none
   digest: A positive strong divisibility sequence has an exact prefix-lcm logarithm as a Mertens dilation. -/

import D5.S3.Factorization.PrimePowers.FiniteCompatibleCrt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Arith.StrongDivisibilityLcmMertens

open Finset
open scoped BigOperators

/- The reconstruction by successive prefix-lcm quotients is classical:
   Andrzej Nowicki, Strong divisibility and lcm-sequences, arXiv:1310.2416v1,
   Theorem 2.1, PDF p. 4. The positive-natural version removes unit ambiguity.
   The projection induction below is a new Lean implementation, using the
   existing repository gcd/lcm distributor at its original public source.
   Additive Möbius inversion and finite convolution are Mathlib suppliers.
   The final log/Mertens identity is a consequence, not new mathematics. -/

private def prefixLcm (u : ℕ → ℕ) (N : ℕ) : ℕ := (Ioc 0 N).lcm u

private def lcmQuotient (u : ℕ → ℕ) (n : ℕ) : ℕ :=
  prefixLcm u n / prefixLcm u (n - 1)

private theorem prefixLcm_zero (u : ℕ → ℕ) : prefixLcm u 0 = 1 := by
  simp [prefixLcm]

private theorem prefixLcm_pos (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < u n) (N : ℕ) : 0 < prefixLcm u N := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun n hn => (hpos n (mem_Ioc.mp hn).1).ne')

private theorem prefixLcm_succ (u : ℕ → ℕ) (K : ℕ) :
    prefixLcm u (K + 1) = Nat.lcm (u (K + 1)) (prefixLcm u K) := by
  unfold prefixLcm
  rw [← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le K), Finset.lcm_insert]
  rfl

private theorem prefixLcm_dvd_succ (u : ℕ → ℕ) (K : ℕ) :
    prefixLcm u K ∣ prefixLcm u (K + 1) := by
  rw [prefixLcm_succ]
  exact Nat.dvd_lcm_right _ _

private theorem prefixLcm_step (u : ℕ → ℕ) (K : ℕ) :
    prefixLcm u (K + 1) = prefixLcm u K * lcmQuotient u (K + 1) := by
  dsimp [lcmQuotient]
  exact (Nat.mul_div_cancel' (prefixLcm_dvd_succ u K)).symm

private theorem lcmQuotient_pos (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < u n) (n : ℕ) (hn : 0 < n) :
    0 < lcmQuotient u n := by
  obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := prefixLcm_pos u hpos (K + 1)
  rw [prefixLcm_step] at h
  by_contra hq
  have heq := Nat.eq_zero_of_not_pos hq
  rw [heq, mul_zero] at h
  exact (lt_irrefl 0) h

private theorem strong_dvd (u : ℕ → ℕ)
    (hstrong : ∀ a b : ℕ, 0 < a → 0 < b →
      Nat.gcd (u a) (u b) = u (Nat.gcd a b))
    (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (hab : a ∣ b) : u a ∣ u b := by
  apply Nat.gcd_eq_left_iff_dvd.mp
  rw [hstrong a b ha hb, Nat.gcd_eq_left hab]

/- When c divides a, the new lcm multiplier contributes the same multiplier
   to gcd(a, b). This is the divisible branch of the projection induction. -/
private theorem gcd_lcm_quotient_step
    (hdistrib : ∀ a b c : ℕ, Nat.gcd (Nat.lcm a b) c =
      Nat.lcm (Nat.gcd a c) (Nat.gcd b c))
    (a b c A : ℕ) (hb : 0 < b) (hc : 0 < c) (hca : c ∣ a)
    (hA : Nat.lcm c b = b * A) :
    Nat.gcd a (Nat.lcm c b) = Nat.gcd a b * A := by
  let r := Nat.gcd b c
  let g := Nat.gcd a b
  have hr : 0 < r := Nat.gcd_pos_of_pos_right b hc
  have hAr : A * r = c := by
    apply (Nat.mul_left_cancel_iff hb).mp
    calc
      b * (A * r) = r * Nat.lcm b c := by rw [Nat.lcm_comm b c, hA]; ring
      _ = b * c := Nat.gcd_mul_lcm b c
  have hgr : Nat.gcd g c = r := by
    dsimp [g, r]
    rw [Nat.gcd_right_comm, Nat.gcd_eq_right hca, Nat.gcd_comm]
  have hlg : Nat.lcm c g = g * A := by
    apply (Nat.mul_right_cancel_iff hr).mp
    calc
      Nat.lcm c g * r = g * c := by
        rw [← hgr, Nat.lcm_comm c g, mul_comm, Nat.gcd_mul_lcm]
      _ = g * (A * r) := by rw [hAr]
      _ = g * A * r := by ring
  rw [Nat.gcd_comm a, hdistrib, Nat.gcd_eq_left hca, Nat.gcd_comm b a]
  exact hlg

/- Live prefix projection: each quotient contributes precisely when its
   positive index divides the tested positive index. -/
private theorem gcd_prefix_projection (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < u n)
    (hstrong : ∀ a b : ℕ, 0 < a → 0 < b →
      Nat.gcd (u a) (u b) = u (Nat.gcd a b))
    (hdistrib : ∀ a b c : ℕ, Nat.gcd (Nat.lcm a b) c =
      Nat.lcm (Nat.gcd a c) (Nat.gcd b c)) :
    ∀ K n : ℕ, 0 < n → Nat.gcd (u n) (prefixLcm u K) =
      ∏ d ∈ Ioc 0 K, if d ∣ n then lcmQuotient u d else 1 := by
  intro K
  induction K with
  | zero => intro n hn; simp [prefixLcm_zero]
  | succ K ih =>
    intro n hn
    rw [prod_Ioc_succ_top (Nat.zero_le K)]
    by_cases hd : K + 1 ∣ n
    · rw [if_pos hd, ← ih n hn, prefixLcm_succ]
      apply gcd_lcm_quotient_step hdistrib
        (u n) (prefixLcm u K) (u (K + 1)) (lcmQuotient u (K + 1))
        (prefixLcm_pos u hpos K) (hpos _ (Nat.succ_pos K))
        (strong_dvd u hstrong _ _ (Nat.succ_pos K) hn hd)
      exact (prefixLcm_succ u K).symm.trans (prefixLcm_step u K)
    · rw [if_neg hd, mul_one, ← ih n hn, prefixLcm_succ,
        Nat.gcd_comm (u n), hdistrib, Nat.gcd_comm (u (K + 1)) (u n),
        hstrong n (K + 1) hn (Nat.succ_pos K), Nat.gcd_comm (prefixLcm u K) (u n)]
      apply Nat.lcm_eq_right
      apply Nat.dvd_gcd
      · rw [← hstrong n (K + 1) hn (Nat.succ_pos K)]
        exact Nat.gcd_dvd_left _ _
      · apply Finset.dvd_lcm
        apply mem_Ioc.mpr
        refine ⟨Nat.gcd_pos_of_pos_left (K + 1) hn, ?_⟩
        have hle := Nat.gcd_le_right n (Nat.succ_pos K)
        have hne : Nat.gcd n (K + 1) ≠ K + 1 := by
          intro he
          exact hd (he ▸ Nat.gcd_dvd_left n (K + 1))
        simp only [Nat.succ_eq_add_one] at *
        omega

private theorem divisor_reconstruction (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < u n)
    (hstrong : ∀ a b : ℕ, 0 < a → 0 < b →
      Nat.gcd (u a) (u b) = u (Nat.gcd a b))
    (hdistrib : ∀ a b c : ℕ, Nat.gcd (Nat.lcm a b) c =
      Nat.lcm (Nat.gcd a c) (Nat.gcd b c))
    (n : ℕ) (hn : 0 < n) : u n = ∏ d ∈ n.divisors, lcmQuotient u d := by
  have hdvd : u n ∣ prefixLcm u n := Finset.dvd_lcm (mem_Ioc.mpr ⟨hn, le_rfl⟩)
  have hp := gcd_prefix_projection u hpos hstrong hdistrib n n hn
  rw [Nat.gcd_eq_left hdvd, ← Finset.prod_filter] at hp
  have hs : (Ioc 0 n).filter (fun d => d ∣ n) = n.divisors := by
    ext d
    simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
    constructor
    · intro h; exact ⟨h.2, hn.ne'⟩
    · intro h
      exact ⟨⟨Nat.pos_of_dvd_of_pos h.1 hn, Nat.le_of_dvd hn h.1⟩, h.1⟩
  rwa [hs] at hp

private theorem prefix_product (u : ℕ → ℕ) (N : ℕ) :
    prefixLcm u N = ∏ d ∈ Ioc 0 N, lcmQuotient u d := by
  induction N with
  | zero => simp [prefixLcm_zero]
  | succ N ih => rw [prefixLcm_step, prod_Ioc_succ_top (Nat.zero_le N), ih]

/-- Every positive natural strong divisibility sequence has this exact
prefix-lcm logarithm at every cutoff, including the empty cutoff. No
condition is imposed at index zero, and the first value need only be positive. -/
theorem log_prefix_lcm_eq_mertens_dilation
    (u : ℕ → ℕ)
    (hpos : ∀ n : ℕ, 0 < n → 0 < u n)
    (hstrong : ∀ a b : ℕ, 0 < a → 0 < b →
      Nat.gcd (u a) (u b) = u (Nat.gcd a b)) :
    ∀ N : ℕ,
      Real.log (((Finset.Ioc 0 N).lcm u : ℕ) : ℝ) =
        ∑ d ∈ Finset.Ioc 0 N, Real.log (u d : ℝ) *
          ∑ m ∈ Finset.Ioc 0 (N / d), (ArithmeticFunction.moebius m : ℝ) := by
  let hdistrib := D5.S3.Factorization.PrimePowers.FiniteCompatibleCrt.gcd_lcm_distrib
  let logU : ArithmeticFunction ℝ :=
    ⟨fun n => if n = 0 then 0 else Real.log (u n : ℝ), by simp⟩
  let mu : ArithmeticFunction ℝ := ArithmeticFunction.moebius
  have hlogDiv : ∀ n : ℕ, 0 < n →
      ∑ d ∈ n.divisors, Real.log (lcmQuotient u d : ℝ) = logU n := by
    intro n hn
    have he := divisor_reconstruction u hpos hstrong hdistrib n hn
    have heR := congrArg (fun x : ℕ => (x : ℝ)) he
    rw [Nat.cast_prod] at heR
    change _ = if n = 0 then 0 else Real.log (u n : ℝ)
    rw [if_neg hn.ne', heR, Real.log_prod]
    intro d hd
    exact_mod_cast (lcmQuotient_pos u hpos d (Nat.pos_of_mem_divisors hd)).ne'
  have hinv := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp hlogDiv
  have hinvApply : ∀ n : ℕ, 0 < n →
      (logU * mu) n = Real.log (lcmQuotient u n : ℝ) := by
    intro n hn
    rw [mul_comm, ArithmeticFunction.mul_apply]
    exact hinv n hn
  intro N
  calc
    Real.log (((Ioc 0 N).lcm u : ℕ) : ℝ)
        = ∑ d ∈ Ioc 0 N, Real.log (lcmQuotient u d : ℝ) := by
          change Real.log (prefixLcm u N : ℝ) = _
          rw [prefix_product, Nat.cast_prod, Real.log_prod]
          intro d hd
          exact_mod_cast (lcmQuotient_pos u hpos d (mem_Ioc.mp hd).1).ne'
    _ = ∑ d ∈ Ioc 0 N, (logU * mu) d := by
          apply sum_congr rfl
          intro d hd
          exact (hinvApply d (mem_Ioc.mp hd).1).symm
    _ = ∑ d ∈ Ioc 0 N, logU d * ∑ m ∈ Ioc 0 (N / d), mu m :=
          ArithmeticFunction.sum_Ioc_mul_eq_sum_sum logU mu N
    _ = _ := by
          apply sum_congr rfl
          intro d hd
          simp only [logU, mu, ArithmeticFunction.coe_mk, if_neg (mem_Ioc.mp hd).1.ne']
          rfl

end D5.S3.Arith.StrongDivisibilityLcmMertens
