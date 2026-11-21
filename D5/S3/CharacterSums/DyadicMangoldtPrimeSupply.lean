/- GID: D5/S3/CharacterSums/DyadicMangoldtPrimeSupply
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DyadicMangoldtPrimeSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: At the prescribed dyadic size the square-root bound for the actual truncated quadratic Mangoldt sum holds on a divergent logarithmic mass of auxiliary primes, and the exceptional mass is finite. -/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import D5.S3.CharacterSums.QuadraticPrimeCrossPeriod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Real Finset Filter
open ArithmeticFunction hiding log
open D5.S3.CharacterSums.QuadraticPrimeCrossPeriod

namespace D5.S3.CharacterSums.DyadicMangoldtPrimeSupply

private lemma clipped_weight {x : ℝ} {n : ℕ} (hx : 0 < x) (hn : 0 < n) :
    min 1 (x/n) = x * ∫ t in Set.Ioi x,
      (Set.Ioi (n:ℝ)).indicator (fun z : ℝ => z ^ (-2:ℝ)) t := by
  rw [setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    integral_Ioi_rpow_of_lt (by norm_num) (lt_max_of_lt_left hx)]
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  norm_num
  rw [Real.rpow_neg_one]
  rcases le_total x (n:ℝ) with h | h
  · rw [max_eq_right h, min_eq_right ((div_le_one hn').2 h)]; ring
  · rw [max_eq_left h, min_eq_left ((one_le_div hn').2 h)]
    field_simp

/-- Non-prime powers in the damped Mangoldt sum cost O(sqrt x), uniformly in the truncation. -/
private theorem clipped_prime_powers :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : ℝ, 0 < x → ∀ N : ℕ,
    ∑ n ∈ (Ioc 0 N).filter (fun n => ¬n.Prime), vonMangoldt n * min 1 (x/n) ≤ K * sqrt x := by
  obtain ⟨C,hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  use 2*max C 0
  refine ⟨by positivity,?_⟩
  intro x hx N
  let S := (Ioc 0 N).filter (fun n => ¬n.Prime)
  let kernel := fun t : ℝ => t ^ (-2:ℝ)
  have hi : IntegrableOn kernel (Set.Ioi x) := integrableOn_Ioi_rpow_of_lt (by norm_num) hx
  let f := fun (n : ℕ) (t : ℝ) => vonMangoldt n * (Set.Ioi (n:ℝ)).indicator kernel t
  have hf (n : ℕ) : IntegrableOn (f n) (Set.Ioi x) :=
    (hi.indicator measurableSet_Ioi).const_mul _
  have he (n : ℕ) (hn : n ∈ S) :
      vonMangoldt n * min 1 (x/n) = x * ∫ t in Set.Ioi x, f n t := by
    rw [clipped_weight hx (mem_Ioc.1 (mem_filter.1 hn).1).1]
    dsimp only [f,kernel]
    rw [integral_const_mul]; ring
  change ∑ n ∈ S, _ ≤ _
  rw [sum_congr rfl he, ← mul_sum, ← integral_finsetSum _ (fun n _ => hf n)]
  have maj : ∀ t ∈ Set.Ioi x, ∑ n ∈ S, f n t ≤ max C 0 * t^(-(3/2):ℝ) := by
    intro t ht
    have ht0 := hx.trans ht
    have hw : 0 ≤ kernel t := Real.rpow_nonneg ht0.le _
    have hid : ∑ n ∈ S, f n t =
        (∑ n ∈ S.filter (fun n : ℕ => (n:ℝ) < t), vonMangoldt n) * kernel t := by
      rw [sum_mul, sum_filter (p := fun n : ℕ => (n:ℝ) < t)]
      apply sum_congr rfl
      intro n _
      by_cases h : (n:ℝ) < t <;> simp [f, Set.indicator, Set.mem_Ioi,h]
    have hsub : S.filter (fun n : ℕ => (n:ℝ) < t) ⊆
        (Ioc 0 ⌊t⌋₊).filter (fun n => ¬n.Prime) := by
      intro n hn
      obtain ⟨hm,htn⟩ := mem_filter.1 hn
      obtain ⟨hi,hp⟩ := mem_filter.1 hm
      exact mem_filter.2 ⟨mem_Ioc.2 ⟨(mem_Ioc.1 hi).1,(Nat.le_floor htn.le)⟩,hp⟩
    have hb := sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => vonMangoldt_nonneg (n:=i))
    rw [← Chebyshev.psi_sub_theta_eq_sum_not_prime] at hb
    rw [hid]
    calc
      _ ≤ (max C 0 * sqrt t) * kernel t := mul_le_mul_of_nonneg_right
        ((hb.trans (hC t)).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sqrt_nonneg _))) hw
      _ = _ := by
        dsimp only [kernel]
        rw [mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add ht0]; norm_num
  have ih : IntegrableOn (fun t : ℝ => max C 0 * t^(-(3/2):ℝ)) (Set.Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx).const_mul _
  have upper := setIntegral_mono_on (integrable_finsetSum S (fun n _ => hf n)) ih measurableSet_Ioi maj
  apply (mul_le_mul_of_nonneg_left upper hx.le).trans
  rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx]
  rw [show -(3/2:ℝ)+1 = -(1/2) by norm_num, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow]
  have hs := Real.sq_sqrt hx.le
  have hsp := Real.sqrt_pos.2 hx
  field_simp
  nlinarith only [congrArg (fun z : ℝ => max C 0 * z) hs]

private theorem prime_second_moment (P : Finset ℕ) (a : ℕ → ℝ) (A L : ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2) (ha : ∀ p ∈ P, 0 ≤ a p) :
    (∑ i ∈ range L, if (A+i)%8=3 then
      (∑ p ∈ P, a p * (jacobiSym (p:ℤ) (A+i) : ℝ))^2 else 0) ≤
      L * (∑ p ∈ P, (a p)^2) + 8*(∑ p ∈ P, p*a p)^2 := by
  classical
  have point (i : ℕ) : (if (A+i)%8=3 then
      (∑ p ∈ P, a p * (jacobiSym (p:ℤ) (A+i) : ℝ))^2 else 0) =
      ∑ p ∈ P, ∑ r ∈ P, (a p*a r) * (weight p r (A+i):ℝ) := by
    by_cases h : (A+i)%8=3
    · simp only [h, ite_true, weight, Int.cast_mul, sq, sum_mul, mul_sum]
      apply sum_congr rfl; intro p _
      apply sum_congr rfl; intro r _; ring
    · simp [h,weight]
  have change_order :
      (∑ i ∈ range L, ∑ p ∈ P, ∑ r ∈ P, a p*a r*(weight p r (A+i):ℝ)) =
      ∑ p ∈ P, ∑ r ∈ P, a p*a r*(corr p r A L:ℝ) := by
    rw [sum_comm]
    apply sum_congr rfl; intro p _
    rw [sum_comm]
    apply sum_congr rfl; intro r _
    simp [corr, mul_sum]
  have bound (p : ℕ) (hp : p ∈ P) (r : ℕ) (hr : r ∈ P) :
      a p*a r*(corr p r A L:ℝ) ≤
        (if p=r then L*(a p)^2 else 0) + 8*((p:ℝ)*a p)*((r:ℝ)*a r) := by
    by_cases h : p = r
    · subst r; simp only [↓reduceIte]
      have hd := (quadratic_prime_cross_period p p A L).1.2
      have hdi : (corr p p A L:ℝ) ≤ (L:ℝ) := by exact_mod_cast hd
      nlinarith only [mul_le_mul_of_nonneg_left hdi (sq_nonneg (a p)), sq_nonneg ((p:ℝ)*a p)]
    · rw [ite_eq_right h,zero_add]
      have hc := ((quadratic_prime_cross_period p r A L).2
        (hP p hp).1 (hP r hr).1 (hP p hp).2 (hP r hr).2 h).2
      have hT : 0 < 8*(p*r) := by have := (hP p hp).1.pos; have := (hP r hr).1.pos; positivity
      have hi : corr p r A L ≤ (8*(p*r) : ℕ) := (le_abs_self _).trans
        (hc.trans (by exact_mod_cast (Nat.mod_lt L hT).le))
      have hreal : (corr p r A L:ℝ) ≤ 8*((p:ℝ)*r) := by exact_mod_cast hi
      nlinarith only [mul_le_mul_of_nonneg_left hreal (mul_nonneg (ha p hp) (ha r hr))]
  rw [sum_congr rfl (fun i _ => point i), change_order]
  refine (sum_le_sum fun p hp => sum_le_sum fun r hr => bound p hp r hr).trans_eq ?_
  simp only [sum_add_distrib]
  congr 1
  · rw [mul_sum]; apply sum_congr rfl; intro p hp; simp [hp]
  · simp_rw [← mul_sum]
    rw [← sum_mul, ← mul_sum, sq, mul_assoc]

private theorem coefficient_bounds (x : ℝ) (hx : 0 ≤ x) (N : ℕ) (hN : 1 ≤ N) (P : Finset ℕ)
    (hP : P ⊆ Icc 1 N) :
    let a := fun p : ℕ => log p * min 1 (x/p)
    (∑ p ∈ P, (a p)^2) ≤ (log N)^2*x*(1+log N) ∧
    (∑ p ∈ P, (p:ℝ)*a p) ≤ (N:ℝ)^2*log N := by
  dsimp only
  have hnon : 0 ≤ log (N:ℝ) := log_nonneg (by exact_mod_cast hN)
  have bound (p : ℕ) (hp : p ∈ P) :
      (log (p:ℝ)*min 1 (x/p))^2 ≤ (log N)^2*x*(p:ℝ)⁻¹ := by
    have h := mem_Icc.1 (hP hp)
    have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast h.1
    have hl := log_nonneg hp1
    have hp0 := zero_lt_one.trans_le hp1
    have hlog := log_le_log hp0 (by exact_mod_cast h.2 : (p:ℝ) ≤ N)
    have hm : 0 ≤ min 1 (x/p) := le_min zero_le_one (div_nonneg hx hp0.le)
    have hl2 := (sq_le_sq₀ hl hnon).2 hlog
    have hm2 : (min 1 (x/p))^2 ≤ x/p := by
      have hh := mul_le_mul_of_nonneg_left (min_le_left 1 (x/(p:ℝ))) hm
      nlinarith only [hh,min_le_right (1:ℝ) (x/p)]
    rw [mul_pow]
    calc
      _ ≤ (log N)^2*(x/p) := mul_le_mul hl2 hm2 (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  constructor
  · calc
      _ ≤ ∑ p ∈ P, (log N)^2*x*(p:ℝ)⁻¹ := sum_le_sum bound
      _ ≤ ∑ p ∈ Icc 1 N, (log N)^2*x*(p:ℝ)⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hP (fun i _ _ => by positivity)
      _ = (log N)^2*x*(harmonic N:ℝ) := by
        rw [← mul_sum, harmonic_eq_sum_Icc]; push_cast; rfl
      _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log _) (by positivity)
  · have each (p : ℕ) (hp : p ∈ P) :
        (p:ℝ)*(log (p:ℝ)*min 1 (x/p)) ≤ (N:ℝ)*log N := by
      have h := mem_Icc.1 (hP hp)
      have hp0 : 0 < (p:ℝ) := by exact_mod_cast h.1
      have hpN : (p:ℝ) ≤ N := by exact_mod_cast h.2
      have hl : 0 ≤ log (p:ℝ) := log_nonneg (by exact_mod_cast h.1)
      have ha := mul_le_mul_of_nonneg_left (min_le_left 1 (x/(p:ℝ))) hl
      exact (mul_le_mul_of_nonneg_left (by simpa using ha) hp0.le).trans
        (mul_le_mul hpN (log_le_log hp0 hpN) hl (Nat.cast_nonneg N))
    have hc : P.card ≤ N := by simpa using card_le_card hP
    calc
      _ ≤ ∑ p ∈ P, (N:ℝ)*log N := sum_le_sum each
      _ = (P.card:ℝ)*((N:ℝ)*log N) := by simp
      _ ≤ (N:ℝ)*((N:ℝ)*log N) := mul_le_mul_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = _ := by ring

/-- The unweighted twist from the reference, with a freely specified integer cutoff. -/
def twist (x : ℝ) (N q : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, ArithmeticFunction.vonMangoldt n * min 1 (x/n) * (jacobiSym (n:ℤ) q : ℝ)

private lemma small_terms {x : ℝ} (hx : 0 < x) (N q : ℕ) :
    let a := fun n : ℕ => Real.log n * min 1 (x/n)
    let P := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ≠ 2)
    |twist x N q - ∑ p ∈ P, a p * (jacobiSym (p:ℤ) q : ℝ)| ≤
      Real.log 2 + ∑ n ∈ (Finset.Ioc 0 N).filter (fun p => ¬p.Prime),
         ArithmeticFunction.vonMangoldt n * min 1 (x/n) := by
  classical
  let c := fun n : ℕ => ArithmeticFunction.vonMangoldt n * min 1 (x/n)
  let f := fun n : ℕ => c n * (jacobiSym (n:ℤ) q : ℝ)
  have hc (n : ℕ) : 0 ≤ c n := mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (le_min zero_le_one (div_nonneg hx.le (Nat.cast_nonneg n)))
  have hf (n : ℕ) : |f n| ≤ c n := by
    dsimp [f]
    rw [abs_mul, abs_of_nonneg (hc n)]
    refine mul_le_of_le_one_right (hc n) ?_
    rcases jacobiSym.trichotomy (n:ℤ) q with h|h|h <;> rw [h] <;> norm_num
  let S := Finset.Icc 1 N
  have eqp : ∑ p ∈ S.filter (fun n => n.Prime ∧ n ≠ 2), f p =
      ∑ p ∈ S.filter (fun n => n.Prime ∧ n ≠ 2), Real.log p * min 1 (x/p) * (jacobiSym (p:ℤ) q : ℝ) := by
    apply Finset.sum_congr rfl; intro p hp
    simp only [f,c,ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.1 hp).2.1]
  have sumsplit : (∑ n ∈ S, f n) - (∑ n ∈ S.filter (fun n => n.Prime ∧ n ≠ 2), f n) =
      (∑ n ∈ S.filter (fun n => n = 2), f n) + ∑ n ∈ S.filter (fun n => ¬n.Prime), f n := by
    simp only [Finset.sum_filter, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases h : n = 2
    · subst n; simp [Nat.prime_two]
    · by_cases hp : n.Prime <;> simp [h,hp]
  dsimp only
  change |(∑ n ∈ S, f n) - _| ≤ _
  rw [← eqp, sumsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [Finset.sum_filter]
    by_cases h : 2 ∈ S
    · simp [h]
      refine (hf 2).trans ?_
      dsimp [c]; rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact mul_le_of_le_one_right (Real.log_nonneg (by norm_num)) (min_le_left _ _)
    · simp [h, Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num)]
  · have hS : S = Finset.Ioc 0 N := by ext n; simp [S,Nat.lt_iff_add_one_le]
    rw [hS]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun n _ => hf n))

/-- An upper bound for the complete second moment over the auxiliary residue class. -/
private theorem actual_second_moment : ∃ H : ℝ, 0 ≤ H ∧ ∀ x : ℝ, 1 ≤ x → ∀ N A L : ℕ, 1 ≤ N →
    (∑ i ∈ Finset.range L, if (A+i)%8=3 then (twist x N (A+i))^2 else 0) ≤
    2*(L*((Real.log N)^2*x*(1+Real.log N)) + 8*((N:ℝ)^2*Real.log N)^2) + H*(L:ℝ)*x := by
  obtain ⟨K,hK,hpow⟩ := clipped_prime_powers
  let C := Real.log 2 + K
  have hC : 0 ≤ C := add_nonneg (Real.log_nonneg (by norm_num)) hK
  refine ⟨2*C^2, by positivity, ?_⟩
  intro x hx N A L hN
  let a := fun n : ℕ => Real.log n * min 1 (x/n)
  let P := (Finset.Icc 1 N).filter (fun p => p.Prime ∧ p ≠ 2)
  let v := fun q : ℕ => ∑ p ∈ P, a p * (jacobiSym (p:ℤ) q : ℝ)
  have hx0 := zero_lt_one.trans_le hx
  have hsx : 1 ≤ Real.sqrt x := (Real.one_le_sqrt).2 hx
  have e (q : ℕ) : |twist x N q - v q| ≤ C*Real.sqrt x := by
    refine (small_terms hx0 N q).trans ?_
    have h := hpow x hx0 N
    have hh := mul_le_mul_of_nonneg_left hsx (Real.log_nonneg (show (1:ℝ) ≤ 2 by norm_num))
    dsimp only [C]; nlinarith only [h,hh]
  have row (i : ℕ) : (if (A+i)%8=3 then (twist x N (A+i))^2 else 0) ≤
      2*(if (A+i)%8=3 then (v (A+i))^2 else 0) + 2*C^2*x := by
    by_cases h : (A+i)%8=3
    · simp only [h,ite_true]
      have he := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).2 (e (A+i))
      rw [sq_abs, mul_pow, Real.sq_sqrt hx0.le] at he
      nlinarith only [he, sq_nonneg (twist x N (A+i)-2*v (A+i))]
    · simp only [h,↓reduceIte]; positivity
  have hP (p : ℕ) (hp : p ∈ P) := (Finset.mem_filter.1 hp).2
  have ha (p : ℕ) (hp : p ∈ P) : 0 ≤ a p := by
    have hp1 := (hP p hp).1.one_le
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hp1))
      (le_min zero_le_one (div_nonneg hx0.le (Nat.cast_nonneg _)))
  have hm := prime_second_moment P a A L hP ha
  obtain ⟨hd,ho⟩ := coefficient_bounds x hx0.le N hN P (Finset.filter_subset _ _)
  have hw : 0 ≤ ∑ p ∈ P, (p:ℝ)*a p := Finset.sum_nonneg
    (fun p hp => mul_nonneg (Nat.cast_nonneg _) (ha p hp))
  have hsq := (sq_le_sq₀ hw (hw.trans ho)).2 ho
  have hbase := hm.trans (add_le_add (mul_le_mul_of_nonneg_left hd (Nat.cast_nonneg L))
    (mul_le_mul_of_nonneg_left hsq (by norm_num : (0:ℝ) ≤ 8)))
  change (∑ i ∈ Finset.range L, if (A+i)%8=3 then (v (A+i))^2 else 0) ≤ _ at hbase
  apply (Finset.sum_le_sum (fun i _ => row i)).trans
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  linarith only [hbase]

private theorem bad_weight_bound {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (F : ℕ → ℝ) {T B : ℝ} (hT : 0 < T)
    (hB : (∑ i ∈ Finset.range L, if (A+i)%8=3 then (F (A+i))^2 else 0) ≤ B) :
    let S := (Finset.range L).filter (fun i => (A+i)%8=3 ∧ (A+i).Prime ∧ T < |F (A+i)|)
    (∑ i ∈ S, Real.log (A+i:ℕ)/(A+i:ℕ)) ≤ (Real.log (A+L:ℕ) / A) * (B / T^2) := by
  dsimp only
  let S := (Finset.range L).filter (fun i => (A+i)%8=3 ∧ (A+i).Prime ∧ T < |F (A+i)|)
  have hT2 := sq_pos_of_pos hT
  let W := fun i : ℕ => if (A+i)%8=3 then (F (A+i))^2 else 0
  have hW (i : ℕ) : 0 ≤ W i := by dsimp [W]; split <;> positivity
  have count : (S.card:ℝ) ≤ B/T^2 := by
    apply (le_div_iff₀ hT2).2
    calc
      _ = ∑ _i ∈ S, T^2 := by simp
      _ ≤ ∑ i ∈ S, W i := Finset.sum_le_sum (fun i hi => by
        obtain ⟨_,h,hp,ht⟩ := Finset.mem_filter.1 hi
        simp only [W,h,ite_true]
        simpa using (sq_le_sq₀ hT.le (abs_nonneg _)).2 ht.le)
      _ ≤ ∑ i ∈ Finset.range L, W i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hW i)
      _ ≤ _ := hB
  have ha : 0 < (A:ℝ) := by exact_mod_cast hA
  have hln : 0 ≤ Real.log (A+L:ℕ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ A+L by omega))
  have each (i : ℕ) (hi : i ∈ S) :
      Real.log (A+i:ℕ)/(A+i:ℕ) ≤ Real.log (A+L:ℕ)/A := by
    have hi' := Finset.mem_range.1 (Finset.mem_filter.1 hi).1
    have hai : 0 < ((A+i:ℕ):ℝ) := by exact_mod_cast (show 0 < A+i by omega)
    exact div_le_div₀ hln (Real.log_le_log hai (by exact_mod_cast (show A+i ≤ A+L by omega))) ha
      (by exact_mod_cast Nat.le_add_right A i)
  calc
    _ ≤ ∑ _i ∈ S, Real.log (A+L:ℕ)/A := Finset.sum_le_sum each
    _ = (Real.log (A+L:ℕ)/A) * (S.card:ℝ) := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left count (div_nonneg hln ha.le)

/-- Scale at which the upper bound for the auxiliary prime is exactly 2^k for k > 0. -/
def height (ε : ℝ) (k : ℕ) : ℝ := (k*Real.log 2)^(5/ε)
/-- Truncation of the Mangoldt sum in the auxiliary-prime selection. -/
def cutoff (x : ℝ) : ℕ := ⌊x^(400:ℕ)⌋₊
/-- Logarithmic weight of primes failing the square-root bound in a dyadic block. -/
def badMass (ε : ℝ) (k : ℕ) : ℝ :=
  let A := 2^(k-1)
  let x := height ε k
  let N := cutoff x
  ∑ i ∈ (Finset.range A).filter (fun i => (A+i)%8=3 ∧ (A+i).Prime ∧
    x^(1/2+ε)/2 < |twist x N (A+i)|), Real.log (A+i:ℕ)/(A+i:ℕ)

private lemma analytic_scale {ε : ℝ} (hε : 0 < ε) (H : ℝ) :
    ∀ᶠ k : ℕ in atTop,
      let A := 2^(k-1)
      let x := height ε k
      let N := cutoff x
      1 ≤ k ∧ 1 ≤ x ∧ 1 ≤ N ∧
      2*((A:ℝ)*((Real.log N)^2*x*(1+Real.log N)) + 8*((N:ℝ)^2*Real.log N)^2) +
        H*(A:ℝ)*x ≤ A*x*x^ε := by
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hu : Tendsto (fun k : ℕ => (k:ℝ)*Real.log 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hc
  have he : 0 < 5/ε := by positivity
  have hheight : Tendsto (height ε) atTop atTop := (tendsto_rpow_atTop he).comp hu
  have hcube := (isLittleO_log_rpow_rpow_atTop 3 hε).bound
    (show (0:ℝ) < 1/1000000000 by norm_num)
  have hpower := (isLittleO_rpow_exp_atTop (5/ε*2400)).bound (show (0:ℝ) < 1/32 by norm_num)
  have hHlim := ((tendsto_rpow_atTop hε).comp hheight).eventually_ge_atTop (3*H+3)
  filter_upwards [eventually_ge_atTop (1:ℕ),hheight.eventually_ge_atTop 1,
    (Real.tendsto_log_atTop.comp hheight).eventually_ge_atTop 1,
    hu.eventually_ge_atTop 1,hheight.eventually hcube,hu.eventually hpower,hHlim] with k hk hx hlog hu1 h3 hfast hh
  let x := height ε k
  let N := cutoff x
  let A := 2^(k-1)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hN : 1 ≤ N := Nat.floor_pos.2 (one_le_pow₀ hx)
  change 1 ≤ Real.log x at hlog
  change ‖(Real.log x)^(3:ℝ)‖ ≤ _*‖x^ε‖ at h3
  have hNl : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hNu : (N:ℝ) ≤ x^(400:ℕ) := Nat.floor_le (by positivity)
  have hlogN := Real.log_le_log (show 0 < (N:ℝ) by exact_mod_cast hN) hNu
  rw [Real.log_pow] at hlogN
  norm_num at hlogN
  have hc3 : (Real.log x)^3 ≤ (1/1000000000)*x^ε := by
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 3),
      abs_of_nonneg (Real.rpow_nonneg hx0.le ε)] using h3
  have hbig : (Real.log N)^2*(1+Real.log N) ≤ x^ε/6 := by
    have hlog1 : 1 ≤ Real.log x := hlog
    have h1 : 1+Real.log N ≤ 401*Real.log x := by linarith
    have h2 := (sq_le_sq₀ hNl (by positivity)).2 hlogN
    calc
      _ ≤ (400*Real.log x)^2*(401*Real.log x) := mul_le_mul h2 h1 (by linarith) (sq_nonneg _)
      _ = 64160000*(Real.log x)^3 := by ring
      _ ≤ _ := by linarith only [hc3,Real.rpow_nonneg hx0.le ε]
  have hxfast : x^(2400:ℕ) ≤ (1/32)*Real.exp ((k:ℝ)*Real.log 2) := by
    have hxpow : x^(2400:ℕ) = (k*Real.log 2 : ℝ)^(5/ε*2400) := by
      dsimp only [x,height]; rw [← Real.rpow_natCast,← Real.rpow_mul (by linarith)]
      norm_num
    rw [hxpow]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ (k:ℝ)*Real.log 2) _),
      abs_of_pos (Real.exp_pos _)] using hfast
  have hA : (2:ℝ)*(A:ℝ) = Real.exp ((k:ℝ)*Real.log 2) := by
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    dsimp only [A]; push_cast
    rw [show k = (k-1)+1 from by omega] at ⊢
    simp [pow_succ,mul_comm]
  have hA0 : 0 ≤ (A:ℝ) := Nat.cast_nonneg _
  have hbdy : ((N:ℝ)^2 * Real.log N)^2 ≤ x^(2400:ℕ) := by
    have hl : Real.log N ≤ x^(400:ℕ) := (Real.log_le_self (Nat.cast_nonneg _)).trans hNu
    calc
      _ ≤ ((x^(400:ℕ))^2*x^(400:ℕ))^2 := by gcongr
      _ = _ := by ring
  refine ⟨hk,hx,hN,?_⟩
  change 2*((2:ℝ)^(k-1)*((Real.log N)^2*x*(1+Real.log N))+8*((N:ℝ)^2*Real.log N)^2)+H*(2:ℝ)^(k-1)*x ≤ (2:ℝ)^(k-1)*x*x^ε
  change 3*H+3 ≤ x^ε at hh
  have hD := mul_le_mul_of_nonneg_left hbig (mul_nonneg hA0 hx0.le)
  have hE := mul_le_mul_of_nonneg_left hh (mul_nonneg hA0 hx0.le)
  have hAx := mul_nonneg hA0 (sub_nonneg.mpr (show 1 ≤ x from hx))
  have hP := mul_nonneg (mul_nonneg hA0 hx0.le) (Real.rpow_nonneg hx0.le ε)
  have hAz := mul_nonneg hA0 hx0.le
  dsimp only [A] at hA hD hE hAx hAz hP
  push_cast at hA hD hE hAx hAz hP
  nlinarith only [hD,hE,hbdy,hxfast,hA,hAx,hAz,hP]

private theorem summable_bad_prime_blocks (ε : ℝ) (hε : 0 < ε) : Summable (badMass ε) := by
  classical
  obtain ⟨H,_,hm⟩ := actual_second_moment
  have hc : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs := (Real.summable_one_div_nat_pow.2 (by decide : 1 < 4)).mul_left (4/(Real.log 2)^4)
  apply Summable.of_norm_bounded_eventually_nat hs
  filter_upwards [analytic_scale hε H] with k hk
  obtain ⟨hk1,hx,hN,hscale⟩ := hk
  let A : ℕ := 2^(k-1)
  let x := height ε k
  let N := cutoff x
  have ha : 0 < A := by dsimp [A]; positivity
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hk0 : 0 < (k:ℝ) := by exact_mod_cast hk1
  have ht : 0 < x^(1/2+ε)/2 := by positivity
  have hsum := hm x hx N A A hN
  have hsc : 2*((A:ℝ)*((Real.log N)^2*x*(1+Real.log N))+8*((N:ℝ)^2*Real.log N)^2)+
      H*(A:ℝ)*x ≤ A*x*x^ε := by simpa only [A,N,x,Nat.cast_pow,Nat.cast_ofNat] using hscale
  have hle := bad_weight_bound ha ha (twist x N) ht (hsum.trans hsc)
  have hnon : 0 ≤ badMass ε k := by
    apply Finset.sum_nonneg
    intro i hi
    apply div_nonneg _ (Nat.cast_nonneg _)
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ A+i by omega)
  rw [Real.norm_eq_abs, abs_of_nonneg hnon]
  have hA : A+A=2^k := by
    dsimp [A]
    calc
      _ = 2^((k-1)+1) := by rw [pow_succ]; omega
      _ = _ := by congr 1; omega
  have hlog : Real.log ((A+A:ℕ):ℝ) = k*Real.log 2 := by rw [hA]; push_cast; rw [Real.log_pow]
  have hpow : x^ε = ((k:ℝ)*Real.log 2)^5 := by
    dsimp [x,height]
    rw [← Real.rpow_mul (mul_pos hk0 hc).le,div_mul_cancel₀ _ hε.ne']
    norm_num
  have ht2 : (x^(1/2+ε)/2)^2 = x*(x^ε)^2/4 := by
    rw [div_pow, ← Real.rpow_mul_natCast hx0.le,show (1/2+ε)*(2:ℕ) = 1+ε*2 by push_cast;ring,
        Real.rpow_add hx0,Real.rpow_one,Real.rpow_mul hx0.le]
    norm_num
  change badMass ε k ≤ _ at hle
  apply hle.trans
  rw [ht2,hlog,hpow]
  have ha0 : (A:ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  exact le_of_eq (by field_simp [ha0,hx0.ne',hk0.ne',hc.ne'])

private def classWeight (q : ℕ) : ℝ :=
  if q%8=3 ∧ q.Prime then Real.log q/q else 0

/-- Logarithmic weight of primes satisfying the square-root bound in a dyadic block. -/
def goodMass (ε : ℝ) (k : ℕ) : ℝ :=
  let A := 2^(k-1)
  let x := height ε k
  let N := cutoff x
  ∑ i ∈ (Finset.range A).filter (fun i => (A+i)%8=3 ∧ (A+i).Prime ∧
    |twist x N (A+i)| ≤ x^(1/2+ε)/2), Real.log (A+i:ℕ)/(A+i:ℕ)

private theorem classWeight_nonneg (q : ℕ) : 0 ≤ classWeight q := by
  dsimp only [classWeight]
  split
  · rename_i h
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.2.one_le)) (Nat.cast_nonneg _)
  · rfl

private theorem classWeight_diverges : ¬ Summable classWeight := by
  intro h
  have hu : IsUnit (3 : ZMod 8) := (ZMod.isUnit_iff_coprime 3 8).2 (by decide)
  apply ArithmeticFunction.vonMangoldt.not_summable_residueClass_prime_div hu
  refine h.congr ?_
  intro n
  have heq : (n : ZMod 8) = 3 ↔ n%8=3 := by
    simpa using ZMod.natCast_eq_natCast_iff' n 3 8
  by_cases hp : n.Prime
  · by_cases hm : n%8=3 <;> simp [classWeight,hp,hm,ArithmeticFunction.vonMangoldt.residueClass,
      Set.indicator,heq,ArithmeticFunction.vonMangoldt_apply_prime hp]
  · simp [classWeight,hp]

private lemma split_block (ε : ℝ) (k : ℕ) :
    goodMass ε (k+1) + badMass ε (k+1) =
       ∑ i ∈ Finset.range (2^k), classWeight (2^k+i) := by
  dsimp only [goodMass,badMass]
  simp only [Nat.add_sub_cancel, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold classWeight
  split_ifs <;> grind

/-- Divergence of the accepted primes in the prescribed dyadic bands for every positive loss. -/
private theorem divergent_good_prime_blocks (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, goodMass ε (k+1)) atTop atTop := by
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg (f := fun k => goodMass ε (k+1)) ?_).1
  · intro hg
    have hb := (summable_nat_add_iff (f := badMass ε) 1).2 (summable_bad_prime_blocks ε hε)
    have hsum := (hg.add hb).congr (fun k => split_block ε k)
    have hlim := (not_summable_iff_tendsto_nat_atTop_of_nonneg classWeight_nonneg).1 classWeight_diverges
    have hsub := hlim.comp (tendsto_pow_atTop_atTop_of_one_lt (by decide : 1 < (2:ℕ)))
    have hblocks (k : ℕ) :
        ∑ j ∈ Finset.range k, ∑ i ∈ Finset.range (2^j), classWeight (2^j+i) =
        ∑ q ∈ Finset.range (2^k), classWeight q := by
      induction k with
      | zero => simp [classWeight]
      | succ k ih =>
        rw [Finset.sum_range_succ,ih,show 2^(k+1) = 2^k+2^k by rw [pow_succ];omega,Finset.sum_range_add]
    have hlim' : Tendsto (fun k : ℕ => ∑ j ∈ Finset.range k,
        ∑ i ∈ Finset.range (2^j), classWeight (2^j+i)) atTop atTop := by
      simpa only [hblocks,Function.comp_def] using hsub
    apply not_tendsto_atTop_of_tendsto_nhds hsum.hasSum.tendsto_sum_nat hlim'
  · intro k
    apply Finset.sum_nonneg
    intro i hi
    have hp := (Finset.mem_filter.1 hi).2.2.1
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) (Nat.cast_nonneg _)

/-- Across the dyadic prime bands, the exceptional weight has finite sum and the
accepted weight grows without bound, for the same truncated Mangoldt test. -/
theorem dyadic_quadratic_mangoldt_supply (ε : ℝ) (hε : 0 < ε) :
    Summable (badMass ε) ∧
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.range K, goodMass ε (k+1)) atTop atTop :=
  ⟨summable_bad_prime_blocks ε hε, divergent_good_prime_blocks ε hε⟩

end D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
