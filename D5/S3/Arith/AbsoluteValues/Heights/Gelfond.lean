/- GID: D5/S3/Arith/AbsoluteValues/Heights/Gelfond
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/Gelfond
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A power-of-two estimate controls the sup norm of a product of complex polynomials. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Order.Interval.Finset.Nat

public section

namespace Nat

private lemma centralBinom_sq_mul_le (n : ℕ) : n.centralBinom ^ 2 * (3 * n + 1) ≤ 16 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hkey : (n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2
        = 4 * (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by
      have h := Nat.succ_mul_centralBinom_succ n
      calc (n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2
          = ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 := by ring
        _ = (2 * (2 * n + 1) * n.centralBinom) ^ 2 := by rw [h]
        _ = 4 * (2 * n + 1) ^ 2 * n.centralBinom ^ 2 := by ring
    have h4 : 4 * (2 * n + 1) ^ 2 * (3 * n + 4) ≤ 16 * ((n + 1) ^ 2 * (3 * n + 1)) := by nlinarith
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < (n + 1) ^ 2 * (3 * n + 1) by positivity)
    calc (n + 1) ^ 2 * (3 * n + 1) * (Nat.centralBinom (n + 1) ^ 2 * (3 * (n + 1) + 1))
        = ((n + 1) ^ 2 * Nat.centralBinom (n + 1) ^ 2) * ((3 * n + 1) * (3 * n + 4)) := by ring
      _ = 4 * (2 * n + 1) ^ 2 * (3 * n + 4) * (n.centralBinom ^ 2 * (3 * n + 1)) := by
          rw [hkey]; ring
      _ ≤ 4 * (2 * n + 1) ^ 2 * (3 * n + 4) * 16 ^ n := Nat.mul_le_mul_left _ ih
      _ ≤ 16 * ((n + 1) ^ 2 * (3 * n + 1)) * 16 ^ n := Nat.mul_le_mul_right _ h4
      _ = (n + 1) ^ 2 * (3 * n + 1) * 16 ^ (n + 1) := by ring


/-- The square of the largest binomial coefficient of order `n`, times `n + 1`, is at most `4 ^ n`.
Equivalently `n.choose (n / 2) ≤ 2 ^ n / √(n + 1)`: the trivial bound `n.choose k ≤ 2 ^ n` loses
exactly this square root. -/
theorem choose_middle_sq_mul_le (n : ℕ) : n.choose (n / 2) ^ 2 * (n + 1) ≤ 4 ^ n := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · subst hm
    rw [show (m + m) / 2 = m by omega, show m + m = 2 * m by ring, ← Nat.centralBinom]
    calc Nat.centralBinom m ^ 2 * (2 * m + 1)
        ≤ Nat.centralBinom m ^ 2 * (3 * m + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ m := centralBinom_sq_mul_le m
      _ = 4 ^ (2 * m) := by rw [pow_mul]; norm_num
  · subst hm
    rw [show (2 * m + 1) / 2 = m by omega]
    refine Nat.le_of_mul_le_mul_left ?_ (show 0 < 4 by norm_num)
    calc 4 * ((2 * m + 1).choose m ^ 2 * (2 * m + 1 + 1))
        = Nat.centralBinom (m + 1) ^ 2 * (2 * m + 2) := by
          rw [← (open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Nat in (fun  (m : ℕ) => (show 2 * (2 * m + 1).choose m = Nat.centralBinom (m + 1) from by
              have hsymm : (2 * m + 1).choose (m + 1) = (2 * m + 1).choose m := by
                rw [← Nat.choose_symm (by omega)]
                congr 1
                omega
              rw [Nat.centralBinom, show 2 * (m + 1) = 2 * m + 2 by ring,
                Nat.choose_succ_succ (2 * m + 1) m, hsymm]
              ring)))) m]; ring
      _ ≤ Nat.centralBinom (m + 1) ^ 2 * (3 * (m + 1) + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ 16 ^ (m + 1) := centralBinom_sq_mul_le (m + 1)
      _ = 4 * 4 ^ (2 * m + 1) := by
          have h16 : (16 : ℕ) ^ (m + 1) = 4 ^ (2 * (m + 1)) := by rw [pow_mul]; norm_num
          rw [h16, show 2 * (m + 1) = 2 * m + 1 + 1 by ring, pow_succ]
          ring

end Nat

namespace Finsupp

open Finset

variable {K : Type*} [Field K]

private lemma sum_antidiagonal_le {α : Type*} [AddCommMonoid α] [IsCancelAdd α]
    [HasAntidiagonal α] (v : AbsoluteValue K ℝ) (x y : α →₀ K) (m : α) :
    v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
      ≤ x.support.card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) := by
  classical
  calc v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
      ≤ ∑ a ∈ antidiagonal m, v (x a.1 * y a.2) := v.sum_le _ _
    _ = ∑ a ∈ (antidiagonal m).filter (fun a ↦ a.1 ∈ x.support), v (x a.1 * y a.2) :=
        (Finset.sum_filter_of_ne fun a _ ha ↦ by
          refine Finsupp.mem_support_iff.mpr fun hc ↦ ha ?_
          rw [hc, zero_mul, map_zero]).symm
    _ ≤ ∑ _a ∈ (antidiagonal m).filter (fun a ↦ a.1 ∈ x.support),
          (⨆ i : α, v (x i)) * ⨆ i : α, v (y i) := by
        refine Finset.sum_le_sum fun a _ ↦ ?_
        rw [map_mul]
        exact mul_le_mul (le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) a.1)
          (le_ciSup ((by have hFiniteRange := (y).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) a.2) (v.nonneg _)
          (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    _ ≤ x.support.card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        gcongr
        · exact mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
            (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        · exact_mod_cast Finset.card_le_card_of_injOn Prod.fst
            (fun a ha ↦ (Finset.mem_filter.mp ha).2)
            (fun a ha b hb hab ↦ Prod.ext hab (by
              have ha' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp ha).1
              have hb' := Finset.mem_antidiagonal.mp (Finset.mem_filter.mp hb).1
              rw [← hab] at hb'
              exact add_left_cancel (ha'.trans hb'.symm)))


end Finsupp

namespace Polynomial

open Height AdmissibleAbsValues Finset

section LocalFactor

variable {K : Type*} [Field K]

/-- The sharpest elementary bound on the local factor of a product: the constant is the number of
terms of the convolution that can be nonzero. -/
theorem iSup_coeff_mul_le_card_support (v : AbsoluteValue K ℝ) (p q : K[X]) :
    (⨆ n : ℕ, v ((p * q).coeff n))
      ≤ (min #p.support #q.support : ℕ)
        * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) := by
  have hnn : (0 : ℝ) ≤ (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun n ↦ ?_) (by positivity)
  rw [Nat.cast_min, min_mul_of_nonneg _ _ hnn]
  refine le_min ?_ ?_
  · rw [coeff_mul]
    simpa only [Polynomial.toFinsupp_apply, Polynomial.support_toFinsupp] using
      (Finsupp.sum_antidiagonal_le v p.toFinsupp.coeff q.toFinsupp.coeff n)
  · rw [mul_comm p q, coeff_mul, mul_comm (⨆ n : ℕ, v (p.coeff n))]
    simpa only [Polynomial.toFinsupp_apply, Polynomial.support_toFinsupp] using
      (Finsupp.sum_antidiagonal_le v q.toFinsupp.coeff p.toFinsupp.coeff n)

end LocalFactor

section Complex


/-- **Gelfond's inequality at a complex place**, with the classical constant. The square root of
the native Mahler comparison is absorbed by `Nat.choose_middle_sq_mul_le`, after
splitting it as `√(d₁ + d₂ + 1) ≤ √(d₁ + 1) * √(d₂ + 1)`. -/
theorem supNorm_mul_supNorm_le_two_pow (p q : ℂ[X]) :
    p.supNorm * q.supNorm ≤ 2 ^ (p.natDegree + q.natDegree) * (p * q).supNorm := by
  have hChoose (n : ℕ) :
      (n.choose (n / 2) : ℝ) * Real.sqrt (n + 1) ≤ 2 ^ n := by
    have hnn : (0 : ℝ) ≤ (n.choose (n / 2) : ℝ) * Real.sqrt (n + 1) := by positivity
    have hsq : ((n.choose (n / 2) : ℝ) * Real.sqrt (n + 1)) ^ 2 ≤ ((2 : ℝ) ^ n) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
        show ((2 : ℝ) ^ 2) = 4 by norm_num]
      exact_mod_cast Nat.choose_middle_sq_mul_le n
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq hnn, Real.sqrt_sq (by positivity)] at h
  refine ((open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Polynomial in (fun  (p q : ℂ[X]) => (show p.supNorm * q.supNorm
          ≤ (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2)
              * Real.sqrt ((p * q).natDegree + 1)) * (p * q).supNorm from by
      calc p.supNorm * q.supNorm
          ≤ (p.natDegree.choose (p.natDegree / 2) * p.mahlerMeasure)
              * (q.natDegree.choose (q.natDegree / 2) * q.mahlerMeasure) :=
            mul_le_mul p.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure
              q.supNorm_le_choose_natDegree_div_two_mul_mahlerMeasure q.supNorm_nonneg
              (mul_nonneg (by positivity) p.mahlerMeasure_nonneg)
        _ = (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2))
              * (p * q).mahlerMeasure := by rw [mahlerMeasure_mul]; ring
        _ ≤ (p.natDegree.choose (p.natDegree / 2) * q.natDegree.choose (q.natDegree / 2))
              * (Real.sqrt ((p * q).natDegree + 1) * (p * q).supNorm) := by
            gcongr
            exact mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm _
        _ = _ := by ring)))) p q).trans (mul_le_mul_of_nonneg_right ?_ (supNorm_nonneg _))
  have hs : Real.sqrt ((p * q).natDegree + 1)
      ≤ Real.sqrt (p.natDegree + 1) * Real.sqrt (q.natDegree + 1) := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hd : ((p * q).natDegree : ℝ) ≤ p.natDegree + q.natDegree := by
      exact_mod_cast natDegree_mul_le (p := p) (q := q)
    nlinarith [Nat.cast_nonneg (α := ℝ) p.natDegree, Nat.cast_nonneg (α := ℝ) q.natDegree]
  calc (p.natDegree.choose (p.natDegree / 2) : ℝ) * q.natDegree.choose (q.natDegree / 2)
        * Real.sqrt ((p * q).natDegree + 1)
      ≤ (p.natDegree.choose (p.natDegree / 2) : ℝ) * q.natDegree.choose (q.natDegree / 2)
        * (Real.sqrt (p.natDegree + 1) * Real.sqrt (q.natDegree + 1)) := by gcongr
    _ = ((p.natDegree.choose (p.natDegree / 2) : ℝ) * Real.sqrt (p.natDegree + 1))
        * ((q.natDegree.choose (q.natDegree / 2) : ℝ) * Real.sqrt (q.natDegree + 1)) := by ring
    _ ≤ 2 ^ p.natDegree * 2 ^ q.natDegree :=
        mul_le_mul (hChoose _) (hChoose _) (by positivity) (by positivity)
    _ = 2 ^ (p.natDegree + q.natDegree) := (pow_add 2 _ _).symm

end Complex

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

/-- **Gelfond's inequality, upper half** (Bombieri–Gubler, Lemma 1.6.11; Hindry–Silverman,
Proposition B.7.3). In Mathlib's relative height the constant of the absolute statement,
`2 ^ (deg p + deg q)`, is raised to the power `totalWeight K`. No nonvanishing hypothesis is
needed: at `p = 0` the junk value sits on the side being bounded. -/
theorem mulHeight_mul_le (p q : K[X]) :
    (p * q).mulHeight
      ≤ 2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p.mulHeight * q.mulHeight) := by
  rw [pow_mul]
  have hsupp (x : ℕ →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoe (x : ℕ →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : ℕ →₀ K).support : Type _) := by
        simp only [Finsupp.support_zero]; infer_instance
      rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
      exact (Height.mulHeight_eq_one_of_subsingleton _).symm
    have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
      exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
    rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
    congr 1
    · congr 2
      ext1 v
      exact hsupp x v
    · exact finprod_congr fun v ↦ hsupp x v.val
  have hprod {F G : AbsoluteValue K ℝ → ℝ} {C : ℝ}
      (hF : ∀ v, 0 ≤ F v) (hG : ∀ v, 0 ≤ G v)
      (harch : ∀ v ∈ archAbsVal (K := K), G v ≤ C * F v)
      (hnon : ∀ v ∈ nonarchAbsVal (K := K), G v = F v) :
      (archAbsVal.map G).prod * ∏ᶠ v : nonarchAbsVal (K := K), G v.val
        ≤ C ^ totalWeight K * ((archAbsVal.map F).prod * ∏ᶠ v : nonarchAbsVal (K := K), F v.val) := by
    have hfin : ∏ᶠ v : nonarchAbsVal (K := K), G v.val = ∏ᶠ v : nonarchAbsVal (K := K), F v.val :=
      finprod_congr fun v ↦ hnon v.val v.prop
    have harch' : (archAbsVal.map G).prod ≤ C ^ totalWeight K * (archAbsVal.map F).prod := by
      calc (archAbsVal.map G).prod
          ≤ (archAbsVal.map fun v ↦ C * F v).prod :=
            Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hG v) harch
        _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod * (archAbsVal.map F).prod :=
            Multiset.prod_map_mul
        _ = C ^ totalWeight K * (archAbsVal.map F).prod := by
            rw [Multiset.map_const', Multiset.prod_replicate]
            rfl
    rw [hfin, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right harch' (finprod_nonneg fun v ↦ hF v.val)
  have htransportUpper {x y z : ℕ →₀ K} {C : ℝ}
      (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (harch : ∀ v ∈ archAbsVal (K := K),
        (⨆ i : ℕ, v (z i)) ≤ C * ((⨆ i : ℕ, v (x i)) * ⨆ i : ℕ, v (y i)))
      (hnon : ∀ v ∈ nonarchAbsVal (K := K),
        (⨆ i : ℕ, v (z i)) = (⨆ i : ℕ, v (x i)) * ⨆ i : ℕ, v (y i)) :
      z.mulHeight ≤ C ^ totalWeight K * (x.mulHeight * y.mulHeight) := by
    have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
    rw [← hcoe z, Height.mulHeight_eq hzc, Finsupp.mulHeight, Finsupp.mulHeight,
      ← Height.mulHeight_fun_mul_eq ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hx) ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hy),
      Height.mulHeight_eq ((fun {x : _ →₀ K} {y : _ →₀ K} (hx : x ≠ 0) (hy : y ≠ 0) ↦
        (show (fun a : x.support × y.support ↦ x a.1.val * y a.2.val) ≠ 0 from by
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
          obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hy
          exact Function.ne_iff.mpr ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩,
            mul_ne_zero (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)⟩)) hx hy)]
    simp only [Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg _
      (fun i : x.support ↦ x i.val) (fun i : y.support ↦ y i.val),
      ← hsupp x, ← hsupp y]
    exact hprod
      (fun v ↦ mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _) harch hnon
  have hpolyUpper {p q : K[X]} {C : ℝ} (hC : 1 ≤ C)
      (harch : ∀ v ∈ archAbsVal (K := K),
        (⨆ n : ℕ, v ((p * q).coeff n)) ≤ C * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n))) :
      (p * q).mulHeight ≤ C ^ totalWeight K * (p.mulHeight * q.mulHeight) := by
    have hCw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
    rcases eq_or_ne p 0 with rfl | hp
    · rw [zero_mul, (show (0 : K[X]).mulHeight = 1 from by
        rw [Polynomial.mulHeight, Polynomial.toFinsupp_zero, AddMonoidAlgebra.coeff_zero,
          Finsupp.mulHeight]
        exact Height.mulHeight_zero), one_mul]
      exact one_le_mul_of_one_le_of_one_le hCw ((fun p : Polynomial K ↦ Height.one_le_mulHeight (fun i : (p.toFinsupp.coeff).support ↦ (p.toFinsupp.coeff) i.val)) q)
    rcases eq_or_ne q 0 with rfl | hq
    · rw [mul_zero, (show (0 : K[X]).mulHeight = 1 from by
        rw [Polynomial.mulHeight, Polynomial.toFinsupp_zero, AddMonoidAlgebra.coeff_zero,
          Finsupp.mulHeight]
        exact Height.mulHeight_zero), mul_one]
      exact one_le_mul_of_one_le_of_one_le hCw ((fun p : Polynomial K ↦ Height.one_le_mulHeight (fun i : (p.toFinsupp.coeff).support ↦ (p.toFinsupp.coeff) i.val)) p)
    exact htransportUpper (x := p.toFinsupp.coeff) (y := q.toFinsupp.coeff)
      (z := (p * q).toFinsupp.coeff)
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp))
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hq))
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr (mul_ne_zero hp hq))) harch
      fun v hv ↦ (show (⨆ n : ℕ, v ((p * q).coeff n)) =
          (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) from by
        have hNorm (r : K[X]) : (⨆ n : ℕ, v (r.coeff n)) = r.gaussNorm v 1 := by
          rw [← Polynomial.gaussNorm_coe_powerSeries v r zero_le_one, PowerSeries.gaussNorm_eq]
          simp
        simp only [hNorm]
        exact Polynomial.gaussNorm_mul (AdmissibleAbsValues.isNonarchimedean v hv) one_pos p q)
  have hCoeffBound (v : AbsoluteValue K ℝ) :
      (⨆ n : ℕ, v ((p * q).coeff n))
        ≤ 2 ^ (p.natDegree + q.natDegree)
          * ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) := by
    have hnn : (0 : ℝ) ≤
        (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) :=
      mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _)
    have hp := p.card_supp_le_succ_natDegree
    have hq := q.card_supp_le_succ_natDegree
    have hmin : min #p.support #q.support ≤
        min p.natDegree q.natDegree + 1 := by omega
    have hpow : min p.natDegree q.natDegree + 1 ≤
        2 ^ (p.natDegree + q.natDegree) :=
      Nat.succ_le_of_lt
        (lt_of_le_of_lt ((Nat.min_le_left _ _).trans (Nat.le_add_right _ _))
          Nat.lt_two_pow_self)
    have hnum : ((min #p.support #q.support : ℕ) : ℝ) ≤
        2 ^ (p.natDegree + q.natDegree) := by
      exact_mod_cast hmin.trans hpow
    exact (iSup_coeff_mul_le_card_support v p q).trans
      (mul_le_mul_of_nonneg_right hnum hnn)
  exact hpolyUpper (one_le_pow₀ one_le_two) fun v _ ↦ hCoeffBound v

end Heights

section NumberField

variable {K : Type*} [Field K] [NumberField K]


/-- **Gelfond's inequality, lower half** (Bombieri–Gubler, Lemma 1.6.11; Hindry–Silverman,
Proposition B.7.3). The nonvanishing hypotheses are not removable: the junk value
`mulHeight 0 = 1` breaks the statement at `p = 0`, where the left side is `mulHeight q`, which is
unbounded, and the right side is a constant.

Unlike the upper half this is stated for a number field, not for an arbitrary field with
`AdmissibleAbsValues`: that class puts no condition on `archAbsVal` beyond its members being
absolute values, so in general there is no complex embedding to run the Mahler measure through. -/
theorem mulHeight_mul_mulHeight_le {p q : K[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    p.mulHeight * q.mulHeight
      ≤ 2 ^ ((p.natDegree + q.natDegree) * totalWeight K) * (p * q).mulHeight := by
  rw [pow_mul]
  have hsupp (x : ℕ →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoe (x : ℕ →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : ℕ →₀ K).support : Type _) := by
        simp only [Finsupp.support_zero]; infer_instance
      rw [Finsupp.coe_zero, Height.mulHeight_zero, Finsupp.mulHeight]
      exact (Height.mulHeight_eq_one_of_subsingleton _).symm
    have hx' : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hxs : (fun i : x.support ↦ x i.val) ≠ 0 := by
      obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
      exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
    rw [Height.mulHeight_eq hx', Finsupp.mulHeight, Height.mulHeight_eq hxs]
    congr 1
    · congr 2
      ext1 v
      exact hsupp x v
    · exact finprod_congr fun v ↦ hsupp x v.val
  have hprod {F G : AbsoluteValue K ℝ → ℝ} {C : ℝ}
      (hF : ∀ v, 0 ≤ F v) (hG : ∀ v, 0 ≤ G v)
      (harch : ∀ v ∈ archAbsVal (K := K), G v ≤ C * F v)
      (hnon : ∀ v ∈ nonarchAbsVal (K := K), G v = F v) :
      (archAbsVal.map G).prod * ∏ᶠ v : nonarchAbsVal (K := K), G v.val
        ≤ C ^ totalWeight K * ((archAbsVal.map F).prod * ∏ᶠ v : nonarchAbsVal (K := K), F v.val) := by
    have hfin : ∏ᶠ v : nonarchAbsVal (K := K), G v.val = ∏ᶠ v : nonarchAbsVal (K := K), F v.val :=
      finprod_congr fun v ↦ hnon v.val v.prop
    have harch' : (archAbsVal.map G).prod ≤ C ^ totalWeight K * (archAbsVal.map F).prod := by
      calc (archAbsVal.map G).prod
          ≤ (archAbsVal.map fun v ↦ C * F v).prod :=
            Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hG v) harch
        _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod * (archAbsVal.map F).prod :=
            Multiset.prod_map_mul
        _ = C ^ totalWeight K * (archAbsVal.map F).prod := by
            rw [Multiset.map_const', Multiset.prod_replicate]
            rfl
    rw [hfin, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right harch' (finprod_nonneg fun v ↦ hF v.val)
  have htransportLower {x y z : ℕ →₀ K}
      {C : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (harch : ∀ v ∈ archAbsVal (K := K),
        ((⨆ i : ℕ, v (x i)) * ⨆ i : ℕ, v (y i)) ≤ C * ⨆ i : ℕ, v (z i))
      (hnon : ∀ v ∈ nonarchAbsVal (K := K),
        (⨆ i : ℕ, v (z i)) = (⨆ i : ℕ, v (x i)) * ⨆ i : ℕ, v (y i)) :
      x.mulHeight * y.mulHeight ≤ C ^ totalWeight K * z.mulHeight := by
    have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
    rw [← hcoe z, Height.mulHeight_eq hzc, Finsupp.mulHeight, Finsupp.mulHeight,
      ← Height.mulHeight_fun_mul_eq ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hx) ((fun {x : _ →₀ K} (hx : x ≠ 0) ↦ (show (fun i : x.support ↦ x i.val) ≠ 0 from by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩)) hy),
      Height.mulHeight_eq ((fun {x : _ →₀ K} {y : _ →₀ K} (hx : x ≠ 0) (hy : y ≠ 0) ↦
        (show (fun a : x.support × y.support ↦ x a.1.val * y a.2.val) ≠ 0 from by
          obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hx
          obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hy
          exact Function.ne_iff.mpr ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩,
            mul_ne_zero (Finsupp.mem_support_iff.mp hi) (Finsupp.mem_support_iff.mp hj)⟩)) hx hy)]
    simp only [Real.iSup_fun_mul_eq_iSup_mul_iSup_of_nonneg _
      (fun i : x.support ↦ x i.val) (fun i : y.support ↦ y i.val),
      ← hsupp x, ← hsupp y]
    exact hprod (fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (fun v ↦ mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _)) harch fun v hv ↦ (hnon v hv).symm
  have hpolyLower {p q : K[X]} {C : ℝ} (hp : p ≠ 0)
      (hq : q ≠ 0)
      (harch : ∀ v ∈ archAbsVal (K := K),
        ((⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n)) ≤ C * ⨆ n : ℕ, v ((p * q).coeff n)) :
      p.mulHeight * q.mulHeight ≤ C ^ totalWeight K * (p * q).mulHeight :=
    htransportLower (x := p.toFinsupp.coeff) (y := q.toFinsupp.coeff)
      (z := (p * q).toFinsupp.coeff)
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp))
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hq))
      (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr (mul_ne_zero hp hq))) harch
      fun v hv ↦ (show (⨆ n : ℕ, v ((p * q).coeff n)) =
          (⨆ n : ℕ, v (p.coeff n)) * ⨆ n : ℕ, v (q.coeff n) from by
        have hNorm (r : K[X]) : (⨆ n : ℕ, v (r.coeff n)) = r.gaussNorm v 1 := by
          rw [← Polynomial.gaussNorm_coe_powerSeries v r zero_le_one, PowerSeries.gaussNorm_eq]
          simp
        simp only [hNorm]
        exact Polynomial.gaussNorm_mul (AdmissibleAbsValues.isNonarchimedean v hv) one_pos p q)
  refine hpolyLower hp hq fun v hv ↦ ?_
  obtain ⟨φ, rfl⟩ := NumberField.mem_multisetInfinitePlace.mp hv
  have hdp : (p.map φ).natDegree = p.natDegree := natDegree_map_eq_of_injective φ.injective p
  have hdq : (q.map φ).natDegree = q.natDegree := natDegree_map_eq_of_injective φ.injective q
  rw [(open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Polynomial in (fun {K : Type _} [instK : Field K] (φ : K →+* ℂ) (p : K[X]) => (show (⨆ n : ℕ, NumberField.place φ (p.coeff n)) = (p.map φ).supNorm from by
      rw [supNorm_eq_iSup]
      exact iSup_congr fun n ↦ by rw [NumberField.place_apply, coeff_map])))), (open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Polynomial in (fun {K : Type _} [instK : Field K] (φ : K →+* ℂ) (p : K[X]) => (show (⨆ n : ℕ, NumberField.place φ (p.coeff n)) = (p.map φ).supNorm from by
      rw [supNorm_eq_iSup]
      exact iSup_congr fun n ↦ by rw [NumberField.place_apply, coeff_map])))), (open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Polynomial in (fun {K : Type _} [instK : Field K] (φ : K →+* ℂ) (p : K[X]) => (show (⨆ n : ℕ, NumberField.place φ (p.coeff n)) = (p.map φ).supNorm from by
      rw [supNorm_eq_iSup]
      exact iSup_congr fun n ↦ by rw [NumberField.place_apply, coeff_map])))),
    Polynomial.map_mul]
  have h := supNorm_mul_supNorm_le_two_pow (p.map φ) (q.map φ)
  rwa [hdp, hdq] at h

end NumberField

end Polynomial

namespace MvPolynomial

open Height AdmissibleAbsValues Finset

section LocalFactor

variable {K : Type*} [Field K] {σ : Type*}

/-- The multivariate form of `Polynomial.iSup_coeff_mul_le_card_support`. -/
theorem iSup_coeff_mul_le_card_support (v : AbsoluteValue K ℝ) (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ (min #p.support #q.support : ℕ)
        * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)) := by
  classical
  have hnn : (0 : ℝ) ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rw [Nat.cast_min, min_mul_of_nonneg _ _ hnn]
  refine le_min ?_ ?_
  · rw [coeff_mul]
    exact Finsupp.sum_antidiagonal_le v (AddMonoidAlgebra.coeff p)
      (AddMonoidAlgebra.coeff q) m
  · rw [mul_comm p q, coeff_mul, mul_comm (⨆ m : σ →₀ ℕ, v (p.coeff m))]
    exact Finsupp.sum_antidiagonal_le v (AddMonoidAlgebra.coeff q)
      (AddMonoidAlgebra.coeff p) m

/-- A multivariate coefficient bound with total degree in the exponent and arbitrary index type. -/
theorem iSup_coeff_mul_le_two_pow (v : AbsoluteValue K ℝ) (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ 2 ^ (p.totalDegree + q.totalDegree)
        * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)) := by
  classical
  have hnn : (0 : ℝ) ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _) (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rcases eq_or_ne ((p * q).coeff m) 0 with h | h
  · rw [h, map_zero]
    positivity
  have hdeg : (∑ i ∈ m.support, m i) ≤ p.totalDegree + q.totalDegree :=
    (MvPolynomial.le_totalDegree (Finsupp.mem_support_iff.mpr h)).trans
      (MvPolynomial.totalDegree_mul p q)
  rw [coeff_mul]
  refine ((open scoped Classical NumberField in (open Height AdmissibleAbsValues Finset Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] {α : Type _} [AddCommMonoid α] [HasAntidiagonal α]
        (v : AbsoluteValue K ℝ) (x y : α →₀ K) (m : α) => (show v (∑ a ∈ antidiagonal m, x a.1 * y a.2)
          ≤ (antidiagonal m).card * ((⨆ i : α, v (x i)) * ⨆ i : α, v (y i)) from by
      refine (v.sum_le _ _).trans ?_
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun a _ ↦ ?_
      rw [map_mul]
      exact mul_le_mul (le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) a.1)
        (le_ciSup ((by have hFiniteRange := (y).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) a.2) (v.nonneg _)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))))) v (AddMonoidAlgebra.coeff p)
    (AddMonoidAlgebra.coeff q) m).trans ?_
  have hcard : #(antidiagonal m) ≤ 2 ^ (p.totalDegree + q.totalDegree) := by
    refine le_trans (Finset.card_le_card_of_injOn (t := Finset.Iic m) Prod.fst
      (fun a ha ↦ Finset.mem_Iic.mpr ?_) (fun a ha b hb hab ↦ Prod.ext hab ?_)) ?_
    · rw [← Finset.mem_antidiagonal.mp ha]
      exact le_self_add
    · have ha' := Finset.mem_antidiagonal.mp ha
      have hb' := Finset.mem_antidiagonal.mp hb
      rw [← hab] at hb'
      exact add_left_cancel (ha'.trans hb'.symm)
    · rw [Finsupp.card_Iic]
      calc ∏ i ∈ m.support, #(Finset.Iic (m i))
          = ∏ i ∈ m.support, (m i + 1) := by simp
        _ ≤ ∏ i ∈ m.support, 2 ^ (m i) := by
            gcongr with i hi
            exact Nat.lt_two_pow_self
        _ = 2 ^ (∑ i ∈ m.support, m i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ 2 ^ (p.totalDegree + q.totalDegree) := Nat.pow_le_pow_right (by norm_num) hdeg
  change ((antidiagonal m).card : ℝ) *
      ((⨆ i : σ →₀ ℕ, v (p.coeff i)) * ⨆ i : σ →₀ ℕ, v (q.coeff i)) ≤
    2 ^ (p.totalDegree + q.totalDegree) *
      ((⨆ i : σ →₀ ℕ, v (p.coeff i)) * ⨆ i : σ →₀ ℕ, v (q.coeff i))
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn

end LocalFactor

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-- **Gelfond's inequality, upper half, in several variables**, with the total degree in the
exponent. The lower half has no multivariate counterpart here: Mathlib's Mahler measure is
univariate. -/
theorem mulHeight_mul_le (p q : MvPolynomial σ K) :
    (p * q).mulHeight
      ≤ 2 ^ ((p.totalDegree + q.totalDegree) * totalWeight K) * (p.mulHeight * q.mulHeight) := by
  rw [pow_mul]
  exact mulHeight_mul_le_of_forall_iSup_le (one_le_pow₀ one_le_two)
    fun v _ ↦ iSup_coeff_mul_le_two_pow v p q

end Heights

end MvPolynomial

section Examples

open Height Polynomial

end Examples
