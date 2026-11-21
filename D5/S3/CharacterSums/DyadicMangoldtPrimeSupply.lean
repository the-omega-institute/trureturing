/- GID: D5/S3/CharacterSums/DyadicMangoldtPrimeSupply
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DyadicMangoldtPrimeSupply
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The quadratic Mangoldt test has summable exceptional dyadic mass and a positive logarithmic mass of acceptable primes at every sufficiently large real scale, even after sparse exclusions. -/

import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import D5.S3.CharacterSums.PrimeProgressionWindowMass
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


open D5.S3.CharacterSums.PrimeProgressionWindowMass

private theorem window_moment_scale {ε : ℝ} (hε : 0 < ε) (H : ℝ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 1 ≤ cutoff x ∧ ∀ A : ℕ,
      Real.exp (x^(ε/5)/2) ≤ 2*(A:ℝ) →
      2*((A:ℝ)*((Real.log (cutoff x))^2*x*(1+Real.log (cutoff x))) +
        8*((cutoff x:ℝ)^2*Real.log (cutoff x))^2) + H*(A:ℝ)*x ≤ A*x*x^ε := by
  have hT := tendsto_rpow_atTop (show 0 < ε/5 by linarith)
  have hc := (isLittleO_log_rpow_rpow_atTop 3 hε).bound
    (show (0:ℝ) < 1/1000000000 by norm_num)
  have hb := (isLittleO_rpow_exp_pos_mul_atTop (2400*(5/ε)) (show (0:ℝ) < 1/2 by norm_num)).bound
    (show (0:ℝ) < 1/32 by norm_num)
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,hc,
    hT.eventually hb,(tendsto_rpow_atTop hε).eventually_ge_atTop (3*H+3)] with x hx hlog h3 hfast hh
  let N := cutoff x
  have hx0 : 0 < x := by linarith
  have hN : 1 ≤ N := Nat.floor_pos.2 (one_le_pow₀ hx)
  refine ⟨hx,hN,?_⟩
  intro A hA
  have hNl : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hNu : (N:ℝ) ≤ x^(400:ℕ) := Nat.floor_le (by positivity)
  have hlogN := Real.log_le_log (show 0 < (N:ℝ) by exact_mod_cast hN) hNu
  rw [Real.log_pow] at hlogN
  norm_num at hlogN
  change ‖(Real.log x)^(3:ℝ)‖ ≤ _*‖x^ε‖ at h3
  have hc3 : (Real.log x)^3 ≤ (1/1000000000)*x^ε := by
    simpa only [Real.norm_eq_abs,Real.rpow_ofNat,abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ Real.log x) 3),
      abs_of_nonneg (Real.rpow_nonneg hx0.le ε)] using h3
  have hbig : (Real.log N)^2*(1+Real.log N) ≤ x^ε/6 := by
    have h1 : 1+Real.log N ≤ 401*Real.log x := by linarith
    have h2 := (sq_le_sq₀ hNl (by positivity)).2 hlogN
    calc
      _ ≤ (400*Real.log x)^2*(401*Real.log x) := mul_le_mul h2 h1 (by linarith) (sq_nonneg _)
      _ = 64160000*(Real.log x)^3 := by ring
      _ ≤ _ := by linarith only [hc3,Real.rpow_nonneg hx0.le ε]
  have hpow : (x^(ε/5))^(2400*(5/ε)) = x^(2400:ℕ) := by
    rw [← Real.rpow_mul hx0.le,show ε/5*(2400*(5/ε))=2400 by field_simp]
    norm_num
  change ‖(x^(ε/5))^(2400*(5/ε))‖ ≤ _*‖Real.exp (1/2*x^(ε/5))‖ at hfast
  rw [hpow,Real.norm_eq_abs,abs_of_nonneg (by positivity),Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] at hfast
  have hbdy : ((N:ℝ)^2*Real.log N)^2 ≤ x^(2400:ℕ) := by
    have hl : Real.log N ≤ x^(400:ℕ) := (Real.log_le_self (Nat.cast_nonneg _)).trans hNu
    calc
      _ ≤ ((x^(400:ℕ))^2*x^(400:ℕ))^2 := by gcongr
      _ = _ := by ring
  change 3*H+3 ≤ x^ε at hh
  have hD := mul_le_mul_of_nonneg_left hbig (mul_nonneg (Nat.cast_nonneg A) hx0.le)
  have hE := mul_le_mul_of_nonneg_left hh (mul_nonneg (Nat.cast_nonneg A) hx0.le)
  have hAx := mul_nonneg (Nat.cast_nonneg (α:=ℝ) A) (sub_nonneg.mpr hx)
  rw [show (1:ℝ)/2*x^(ε/5)=x^(ε/5)/2 by ring] at hfast
  change 2*((A:ℝ)*((Real.log N)^2*x*(1+Real.log N))+8*((N:ℝ)^2*Real.log N)^2)+H*(A:ℝ)*x ≤ _
  nlinarith only [hD,hE,hbdy,hfast,hA,hAx,mul_nonneg (mul_nonneg (Nat.cast_nonneg (α:=ℝ) A) hx0.le) (Real.rpow_nonneg hx0.le ε)]

private lemma dyadic_prefix (w : ℕ → ℝ) (K : ℕ) :
    ∑ n ∈ range (2^K), w n =
      w 0 + ∑ j ∈ range K, ∑ i ∈ range (2^j), w (2^j+i) := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [show 2^(k+1) = 2^k+2^k by rw [pow_succ]; omega, sum_range_add, ih, sum_range_succ]
    ring

/-- Exceptional logarithmic prime weight in the actual selector's window at the same real x. -/
private def selectorBadMass (ε x : ℝ) : ℝ :=
  let T := x^(ε/5)
  let band := primeBand (3 : ZMod 8) T
  ∑ q ∈ band.filter (fun q => x^(1/2+ε)/2 < |twist x (cutoff x) q|), Real.log q/q

private theorem window_bad_estimate (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, selectorBadMass ε x ≤ 36*(x^(ε/5))^2/x^ε := by
  classical
  obtain ⟨H,_,hm⟩ := actual_second_moment
  have htlim := tendsto_rpow_atTop (show 0 < ε/5 by linarith)
  filter_upwards [window_moment_scale hε H, htlim.eventually_ge_atTop 2] with x hx ht
  obtain ⟨hx,hN,hscale⟩ := hx
  let T := x^(ε/5)
  let K := ⌈T/Real.log 2⌉₊+1
  let M := ⌊Real.exp T⌋₊+1
  let w := fun q : ℕ => if Real.exp (T/2) < (q:ℝ) ∧ q%8=3 ∧ q.Prime ∧
    x^(1/2+ε)/2 < |twist x (cutoff x) q| then Real.log q/q else 0
  have hx0 : 0 < x := by linarith
  have hT : 2 ≤ T := ht
  have hpT : 0 < T := by linarith
  have h2 : (1:ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hl2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hK0 := Nat.le_ceil (T/Real.log 2)
  have hK1 := Nat.ceil_lt_add_one (a:=T/Real.log 2) (by positivity)
  have hKK : (K:ℝ) ≤ 3*T := by
    dsimp [K]; push_cast
    have hq : T/Real.log 2 ≤ 2*T := (div_le_iff₀ (by linarith)).2 (by nlinarith [mul_nonneg hpT.le (sub_nonneg.mpr h2.le)])
    linarith
  have hbound : T < (K:ℝ)*Real.log 2 := by
    have hh := (div_le_iff₀ (by linarith : 0 < Real.log 2)).1 hK0
    dsimp [K]; push_cast; nlinarith
  have hM : M ≤ 2^K := by
    have he := Real.exp_lt_exp.mpr hbound
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)] at he
    dsimp [M]; apply Nat.succ_le_of_lt
    apply (Nat.floor_lt (Real.exp_pos _).le).2
    exact_mod_cast he
  have hnon (q : ℕ) : 0 ≤ w q := by
    dsimp [w]; split
    · rename_i h; exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.2.2.1.one_le)) (Nat.cast_nonneg _)
    · rfl
  have hrepresent : selectorBadMass ε x = ∑ q ∈ range M, w q := by
    have hclass (q : ℕ) : (q : ZMod 8) = 3 ↔ q%8=3 := by
      simpa using ZMod.natCast_eq_natCast_iff' q 3 8
    unfold selectorBadMass; simp only [primeBand,hclass]
    rw [Finset.sum_filter,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q _; dsimp only [w,T]; split_ifs <;> grind
  have hw0 : w 0=0 := by simp [w]
  have hblock (j : ℕ) (hj : j ∈ range K) :
      ∑ i ∈ range (2^j), w (2^j+i) ≤ 12*T/x^ε := by
    let A : ℕ := 2^j
    have ha : 0 < A := by dsimp [A]; positivity
    have haR : (0:ℝ) < A := by exact_mod_cast ha
    have ht2 : (x^(1/2+ε)/2)^2 = x*(x^ε)^2/4 := by
      rw [div_pow, ← Real.rpow_mul_natCast hx0.le,show (1/2+ε)*(2:ℕ) = 1+ε*2 by push_cast; ring,
        Real.rpow_add hx0,Real.rpow_one,Real.rpow_mul hx0.le]; norm_num
    by_cases hA : Real.exp (T/2) ≤ 2*(A:ℝ)
    · have moment := (hm x hx (cutoff x) A A hN).trans (hscale A hA)
      have bound := bad_weight_bound ha ha (twist x (cutoff x))
        (show 0 < x^(1/2+ε)/2 by positivity) moment
      have logA : Real.log ((A+A:ℕ):ℝ) ≤ 3*T := by
        have hz : A+A=2^(j+1) := by dsimp [A]; rw [pow_succ]; omega
        rw [hz]; push_cast; rw [Real.log_pow]
        have hj' : j+1 ≤ K := by simpa using Finset.mem_range.1 hj
        have hjR : (j:ℝ)+1 ≤ K := by exact_mod_cast hj'
        push_cast
        nlinarith [mul_nonneg (show 0 ≤ (j:ℝ)+1 by positivity) (sub_nonneg.mpr hl2.le)]
      have sub : (∑ i ∈ range A, w (A+i)) ≤
          ∑ i ∈ (range A).filter (fun i => (A+i)%8=3 ∧ (A+i).Prime ∧
            x^(1/2+ε)/2 < |twist x (cutoff x) (A+i)|), Real.log (A+i:ℕ)/(A+i:ℕ) := by
        rw [Finset.sum_filter]
        apply Finset.sum_le_sum
        intro i hi; dsimp [w]; split_ifs <;> first | rfl | (exfalso; tauto) | positivity
      apply sub.trans (bound.trans ?_)
      rw [ht2]
      have he : 0 < x^ε := Real.rpow_pos_of_pos hx0 _
      calc
        _ = 4*Real.log ((A+A:ℕ):ℝ)/x^ε := by field_simp
        _ ≤ _ := (div_le_div_iff_of_pos_right he).2 (by linarith only [logA])
    · have hw (i : ℕ) (hi : i ∈ range A) : w (A+i)=0 := by
        have hl : A+i<A+A := Nat.add_lt_add_left (Finset.mem_range.1 hi) _
        have hl' : (A:ℝ)+i < 2*(A:ℝ) := by exact_mod_cast (show A+i<2*A by omega)
        dsimp only [w]; rw [ite_eq_right]
        rintro ⟨h,_⟩; push_cast at h; linarith
      change (∑ i ∈ range A, w (A+i)) ≤ _
      rw [Finset.sum_eq_zero hw]; positivity
  rw [hrepresent]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hM) (fun q _ _ => hnon q)).trans
  rw [dyadic_prefix,hw0,zero_add]
  apply (Finset.sum_le_sum hblock).trans
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have he : 0 < x^ε := Real.rpow_pos_of_pos hx0 _
  dsimp only [T] at *
  calc
    _ ≤ (3*x^(ε/5))*(12*x^(ε/5)/x^ε) := by gcongr
    _ = _ := by ring

/-- At the prescribed real height the exceptional band weight is negligible on the log scale. -/
private theorem selector_bad_mass_small (ε c : ℝ) (hε : 0 < ε) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, selectorBadMass ε x ≤ c*x^(ε/5) := by
  have hlim := tendsto_rpow_atTop (show 0 < 4*ε/5 by linarith)
  filter_upwards [window_bad_estimate ε hε, hlim.eventually_ge_atTop (36/c), eventually_ge_atTop (1:ℝ)]
    with x h hx h1
  have hx0 : 0 < x := by linarith
  have hxε : 0 < x^ε := Real.rpow_pos_of_pos hx0 _
  have ht : 0 < x^(ε/5) := Real.rpow_pos_of_pos hx0 _
  have hh : 36 ≤ c*x^(4*ε/5) := by
    simpa [mul_comm] using (div_le_iff₀ hc).1 hx
  have hs : x^(ε/5)*x^(4*ε/5) = x^ε := by
    rw [← Real.rpow_add hx0, show ε/5+4*ε/5=ε by ring]
  apply h.trans ((div_le_iff₀ hxε).2 ?_)
  have hmul := mul_le_mul_of_nonneg_left hh (sq_nonneg (x^(ε/5)))
  calc
    _ ≤ (x^(ε/5))^2*(c*x^(4*ε/5)) := by linarith only [hmul]
    _ = (c*x^(ε/5))*(x^(ε/5)*x^(4*ε/5)) := by ring
    _ = _ := by rw [hs]

/-- The logarithmic prime weight left after the character-sum test and a further finite exclusion. -/
def survivingMass (ε x : ℝ) (E : Finset ℕ) : ℝ :=
  let T := x^(ε/5)
  ∑ q ∈ (primeBand (3 : ZMod 8) T).filter
    (fun q => |twist x (cutoff x) q| ≤ x^(1/2+ε)/2 ∧ q ∉ E), log q / q

private theorem deletion_cost {T : ℝ} (hT : 0 < T) (E : Finset ℕ)
    (hE : (E.card:ℝ) ≤ exp (T/3)) :
    (∑ q ∈ (primeBand (3:ZMod 8) T).filter (· ∈ E), log q / q) ≤ T * exp (-T/6) := by
  let S := (primeBand (3:ZMod 8) T).filter (· ∈ E)
  have hsub : S ⊆ E := fun q h => (mem_filter.1 h).2
  have hcard : (S.card:ℝ) ≤ exp (T/3) := (Nat.cast_le.mpr (card_le_card hsub)).trans hE
  have point (q : ℕ) (hq : q ∈ S) : log q/q ≤ T / exp (T/2) := by
    obtain ⟨hband,_⟩ := mem_filter.1 hq
    obtain ⟨hhi,hlo,_,hp⟩ := mem_filter.1 hband
    have hhi' : (q:ℝ) ≤ exp T := (Nat.le_floor_iff (exp_pos T).le).mp (Nat.lt_succ_iff.mp (mem_range.mp hhi))
    have hln := log_le_log (by exact_mod_cast hp.pos : (0:ℝ) < q) hhi'
    rw [log_exp] at hln
    exact div_le_div₀ hT.le hln (exp_pos _) hlo.le
  calc
    _ ≤ ∑ _q ∈ S, T / exp (T/2) := sum_le_sum point
    _ = (S.card:ℝ) * (T / exp (T/2)) := by simp
    _ ≤ exp (T/3) * (T / exp (T/2)) := mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = T * exp (-T/6) := by
      rw [show -T/6 = T/3 + -(T/2) by ring,exp_add,exp_neg]; ring

/-- Every sufficiently large real scale admits a positive logarithmic weight of
auxiliary primes passing the actual quadratic Mangoldt test, even after any
further exclusion of at most exp(x^(ε/5)/3) integers. -/
theorem real_scale_quadratic_mangoldt_supply (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ E : Finset ℕ, (E.card:ℝ) ≤ exp (x^(ε/5)/3) →
      x^(ε/5)/173065984000 ≤ survivingMass ε x E := by
  let D := (86532992000:ℝ)
  have hD : 0 < D := by norm_num [D]
  have htot := prime_progression_window_mass (3:ZMod 8)
    ((ZMod.isUnit_iff_coprime 3 8).2 (by decide))
  have hm : Nat.totient 8 = 4 := by decide
  rw [hm] at htot
  have hpow := tendsto_rpow_atTop (show 0 < ε/5 by positivity)
  filter_upwards [hpow.eventually htot,hpow.eventually_gt_atTop 0,
    hpow.eventually_ge_atTop (6 * log (4*D)),selector_bad_mass_small ε (1/(4*D)) hε (by positivity)] with x ht hx hlarge hb
  intro E hE
  let T := x^(ε/5)
  let S := primeBand (3:ZMod 8) T
  have ht' : T / D ≤ ∑ q ∈ S, log q / q := by simpa only [S,T,D,show (21633248000:ℝ) * (4:ℕ) = 86532992000 by norm_num] using ht
  have hd := deletion_cost hx E hE
  have he : exp (-T/6) ≤ 1/(4*D) := by
    rw [one_div,← exp_log (show 0 < 4*D by positivity),← exp_neg]
    apply exp_le_exp.mpr
    change 6 * log (4*D) ≤ T at hlarge
    rw [neg_div]
    apply neg_le_neg
    exact (le_div_iff₀ (by norm_num : (0:ℝ) < 6)).2 (by simpa only [mul_comm] using hlarge)
  have splitWeight : (∑ q ∈ S, log q / q) ≤ survivingMass ε x E +
      (∑ q ∈ S.filter (fun q => x^(1/2+ε)/2 < |twist x (cutoff x) q|), log q / q) +
      ∑ q ∈ S.filter (· ∈ E), log q / q := by
    change _ ≤ (∑ q ∈ S.filter _, _) + _ + _
    simp only [sum_filter,← sum_add_distrib]
    apply sum_le_sum; intro q hq
    have hp := (mem_filter.1 hq).2.2.2
    have hw : 0 ≤ log (q:ℝ)/q := div_nonneg (log_nonneg (by exact_mod_cast hp.one_le)) q.cast_nonneg
    split_ifs <;> grind
  have hh := mul_le_mul_of_nonneg_left he hx.le
  change (∑ q ∈ S.filter (fun q => x^(1/2+ε)/2 < |twist x (cutoff x) q|), log q/q) ≤ (1/(4*D))*T at hb
  change _ ≤ T * _ at hd
  change T/173065984000 ≤ _
  dsimp [D] at ht' hb hh
  linarith only [ht',hd,hh,hb,splitWeight,hx]

end D5.S3.CharacterSums.DyadicMangoldtPrimeSupply
