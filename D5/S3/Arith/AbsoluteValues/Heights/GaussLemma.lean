/- GID: D5/S3/Arith/AbsoluteValues/Heights/GaussLemma
   generality: G
   mirror-B: D5/B/S3/Arith/AbsoluteValues/Heights/GaussLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: At a nonarchimedean place, the coefficient sup norm of a polynomial product is multiplicative. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.PseudoBasisMetrics
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Data.Finsupp.MonomialOrder
public import Mathlib.NumberTheory.Height.MvPolynomial
public import Mathlib.RingTheory.Polynomial.GaussNorm

public section

namespace Polynomial

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K]

@[expose] noncomputable def mulHeight (p : K[X]) : ℝ := Finsupp.mulHeight p.toFinsupp.coeff

@[expose] noncomputable def logHeight (p : K[X]) : ℝ := Real.log p.mulHeight

end Polynomial

namespace MvPolynomial

open Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

@[expose] noncomputable def mulHeight (p : MvPolynomial σ K) : ℝ :=
  Finsupp.mulHeight (AddMonoidAlgebra.coeff p)

@[expose] noncomputable def logHeight (p : MvPolynomial σ K) : ℝ := Real.log p.mulHeight

end MvPolynomial

namespace MvPolynomial

open Height AdmissibleAbsValues

section LocalFactor

variable {K : Type*} [Field K] {σ : Type*}

private lemma iSup_coeff_mul_le {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) := by
  classical
  have hbp := (by have hFiniteRange := ((AddMonoidAlgebra.coeff p)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)
  have hbq := (by have hFiniteRange := ((AddMonoidAlgebra.coeff q)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)
  have hnp : (0 : ℝ) ≤ ⨆ m : σ →₀ ℕ, v (p.coeff m) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hnq : (0 : ℝ) ≤ ⨆ m : σ →₀ ℕ, v (q.coeff m) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  refine Real.iSup_le (fun m ↦ ?_) (by positivity)
  rw [MvPolynomial.coeff_mul]
  refine hv.apply_sum_le.trans (Real.iSup_le ?_ (by positivity))
  rintro ⟨⟨a, b⟩, hab⟩
  rw [map_mul]
  exact mul_le_mul (le_ciSup hbp a) (le_ciSup hbq b) (v.nonneg _) hnp

private lemma le_iSup_coeff_mul [LinearOrder σ] {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {p q : MvPolynomial σ K} (hp : p ≠ 0) (hq : q ≠ 0) :
    (⨆ m : σ →₀ ℕ, v (p.coeff m)) * (⨆ m : σ →₀ ℕ, v (q.coeff m))
      ≤ ⨆ m : σ →₀ ℕ, v ((p * q).coeff m) := by
  classical
  have hsupp (x : (σ →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : σ →₀ ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hmin (f : (σ →₀ ℕ) → Lex (σ →₀ ℕ))
      {x : (σ →₀ ℕ) →₀ K} (hx : x ≠ 0)
      (v : AbsoluteValue K ℝ) :
      ∃ i, v (x i) = (⨆ m : σ →₀ ℕ, v (x m)) ∧
        ∀ a, f a < f i → v (x a) < ⨆ m : σ →₀ ℕ, v (x m) := by
    classical
    obtain ⟨i₁, hi₁⟩ := Finsupp.support_nonempty_iff.mpr hx
    have hpos : 0 < ⨆ m : σ →₀ ℕ, v (x m) :=
      lt_of_lt_of_le (v.pos (Finsupp.mem_support_iff.mp hi₁))
        (le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i₁)
    have hne : Nonempty x.support := ⟨⟨i₁, hi₁⟩⟩
    obtain ⟨i₀, hi₀⟩ : ∃ i : x.support, v (x i.val) = ⨆ i : x.support, v (x i.val) :=
      exists_eq_ciSup_of_finite
    have hSne : (x.support.filter fun m ↦ v (x m) = ⨆ m : σ →₀ ℕ, v (x m)).Nonempty :=
      ⟨i₀.val, by simp [i₀.prop, hi₀, hsupp x]⟩
    obtain ⟨i, hiS, hmin⟩ := Finset.exists_min_image _ f hSne
    refine ⟨i, (Finset.mem_filter.mp hiS).2, fun a ha ↦ ?_⟩
    rcases eq_or_lt_of_le (le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) a) with h | h
    · refine absurd (hmin a (Finset.mem_filter.mpr ⟨?_, h⟩)) ha.not_ge
      refine Finsupp.mem_support_iff.mpr fun hc ↦ ?_
      change v (x a) = ⨆ m : σ →₀ ℕ, v (x m) at h
      rw [hc, map_zero] at h
      exact hpos.ne h
    · exact h

  have hpos {v : AbsoluteValue K ℝ} {p : MvPolynomial σ K} (hp : p ≠ 0) :
      0 < ⨆ m : σ →₀ ℕ, v (p.coeff m) := by
    obtain ⟨m, hm⟩ := Finsupp.support_nonempty_iff.mpr (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp))
    exact lt_of_lt_of_le (v.pos (Finsupp.mem_support_iff.mp hm))
      (le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff p)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) m)

  have hbp := (by have hFiniteRange := ((AddMonoidAlgebra.coeff p)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)
  have hbq := (by have hFiniteRange := ((AddMonoidAlgebra.coeff q)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)
  have hbpq := (by have hFiniteRange := ((AddMonoidAlgebra.coeff (p * q))).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)
  obtain ⟨i, hi, hilt⟩ :=
    hmin (toLex : (σ →₀ ℕ) → Lex (σ →₀ ℕ)) (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp)) v
  obtain ⟨j, hj, hjlt⟩ :=
    hmin (toLex : (σ →₀ ℕ) → Lex (σ →₀ ℕ)) (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hq)) v
  change v (MvPolynomial.coeff i p) =
    (⨆ m : σ →₀ ℕ, v (MvPolynomial.coeff m p)) at hi
  change v (MvPolynomial.coeff j q) =
    (⨆ m : σ →₀ ℕ, v (MvPolynomial.coeff m q)) at hj
  change ∀ a : σ →₀ ℕ, toLex a < toLex i →
    v (MvPolynomial.coeff a p) < (⨆ m : σ →₀ ℕ, v (MvPolynomial.coeff m p)) at hilt
  change ∀ b : σ →₀ ℕ, toLex b < toLex j →
    v (MvPolynomial.coeff b q) < (⨆ m : σ →₀ ℕ, v (MvPolynomial.coeff m q)) at hjlt
  have key : v ((p * q).coeff (i + j)) = v (p.coeff i * q.coeff j) := by
    rw [MvPolynomial.coeff_mul]
    refine hv.apply_sum_eq_of_lt (fun a ↦ (v.map_neg a).symm)
      (s := Finset.antidiagonal (i + j))
      (l := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) ↦ p.coeff x.1 * q.coeff x.2)
      (k := (i, j)) (Finset.mem_antidiagonal.mpr rfl) ?_
    rintro ⟨a, b⟩ hab hne
    have hsum : a + b = i + j := Finset.mem_antidiagonal.mp hab
    have hane : a ≠ i := by
      rintro rfl
      exact hne (by simp [add_left_cancel hsum])
    change v (MvPolynomial.coeff a p * MvPolynomial.coeff b q) <
      v (MvPolynomial.coeff i p * MvPolynomial.coeff j q)
    rw [map_mul, map_mul, hi, hj]
    rcases lt_or_gt_of_ne (fun h ↦ hane (toLex.injective h)) with h | h
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_ciSup hbq b) (v.nonneg _))
        (mul_lt_mul_of_pos_right (hilt a h) (hpos hq))
    · have hb : toLex b < toLex j := by
        have heq : toLex a + toLex b = toLex i + toLex j := by
          rw [← toLex_add, ← toLex_add, hsum]
        by_contra hcon
        exact absurd heq (ne_of_gt (add_lt_add_of_lt_of_le h (not_lt.mp hcon)))
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (le_ciSup hbp a) (v.nonneg _))
        (mul_lt_mul_of_pos_left (hjlt b hb) (hpos hp))
  calc (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m)
      = v ((p * q).coeff (i + j)) := by rw [key, map_mul, ← hi, ← hj]
    _ ≤ ⨆ m : σ →₀ ℕ, v ((p * q).coeff m) := le_ciSup hbpq _

/-- **Gauss's lemma for heights, multivariate.** At a nonarchimedean absolute value the local
factor of the height is exactly multiplicative. The dominant exponent is the one *least* in a
monomial order among those realising the supremum, which is why a linear order on `σ →₀ ℕ`
compatible with addition — and no more — is what the proof needs. -/
theorem iSup_coeff_mul {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    (p q : MvPolynomial σ K) :
    (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      = (⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m) := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  classical
  let _ : LinearOrder σ := linearOrderOfSTO WellOrderingRel
  exact le_antisymm (iSup_coeff_mul_le hv p q) (le_iSup_coeff_mul hv hp hq)

end LocalFactor

section Heights

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {σ : Type*}

/-- **The height of a product, upper half, multivariate.** -/
theorem mulHeight_mul_le_of_forall_iSup_le {p q : MvPolynomial σ K} {C : ℝ} (hC : 1 ≤ C)
    (harch : ∀ v ∈ archAbsVal (K := K), (⨆ m : σ →₀ ℕ, v ((p * q).coeff m))
      ≤ C * ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))) :
    (p * q).mulHeight ≤ C ^ totalWeight K * (p.mulHeight * q.mulHeight) := by
  have hCw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_mul, (show (0 : MvPolynomial (σ) K).mulHeight = 1 from by
      rw [MvPolynomial.mulHeight, AddMonoidAlgebra.coeff_zero, Finsupp.mulHeight]
      exact Height.mulHeight_zero), one_mul]
    exact one_le_mul_of_one_le_of_one_le hCw ((fun p : MvPolynomial _ K ↦ Height.one_le_mulHeight (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val)) q)
  rcases eq_or_ne q 0 with rfl | hq
  · rw [mul_zero, (show (0 : MvPolynomial (σ) K).mulHeight = 1 from by
      rw [MvPolynomial.mulHeight, AddMonoidAlgebra.coeff_zero, Finsupp.mulHeight]
      exact Height.mulHeight_zero), mul_one]
    exact one_le_mul_of_one_le_of_one_le hCw ((fun p : MvPolynomial _ K ↦ Height.one_le_mulHeight (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val)) p)
  have hsupp (x : (σ →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : σ →₀ ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoe (x : (σ →₀ ℕ) →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : (σ →₀ ℕ) →₀ K).support : Type _) := by
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
  have htransportUpper {x y z : (σ →₀ ℕ) →₀ K} {C : ℝ}
      (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (harch : ∀ v ∈ archAbsVal (K := K),
        (⨆ i : σ →₀ ℕ, v (z i)) ≤
          C * ((⨆ i : σ →₀ ℕ, v (x i)) * ⨆ i : σ →₀ ℕ, v (y i)))
      (hnon : ∀ v ∈ nonarchAbsVal (K := K),
        (⨆ i : σ →₀ ℕ, v (z i)) =
          (⨆ i : σ →₀ ℕ, v (x i)) * ⨆ i : σ →₀ ℕ, v (y i)) :
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
  exact htransportUpper (x := AddMonoidAlgebra.coeff p)
    (y := AddMonoidAlgebra.coeff q) (z := AddMonoidAlgebra.coeff (p * q))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hq))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr (mul_ne_zero hp hq))) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

/-- **The height of a product, lower half, multivariate.** -/
theorem mulHeight_mul_mulHeight_le_of_forall_le_iSup {p q : MvPolynomial σ K} {C : ℝ}
    (hp : p ≠ 0) (hq : q ≠ 0)
    (harch : ∀ v ∈ archAbsVal (K := K),
      ((⨆ m : σ →₀ ℕ, v (p.coeff m)) * ⨆ m : σ →₀ ℕ, v (q.coeff m))
        ≤ C * ⨆ m : σ →₀ ℕ, v ((p * q).coeff m)) :
    p.mulHeight * q.mulHeight ≤ C ^ totalWeight K * (p * q).mulHeight := by
  have hsupp (x : (σ →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
      (⨆ i : σ →₀ ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
    refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
      (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
        (Real.iSup_nonneg fun _ ↦ v.nonneg _))
    rcases eq_or_ne (x i) 0 with h | h
    · simp only [h, map_zero]
      exact Real.iSup_nonneg fun _ ↦ v.nonneg _
    · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
  have hcoe (x : (σ →₀ ℕ) →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
    rcases eq_or_ne x 0 with rfl | hx
    · have : IsEmpty ((0 : (σ →₀ ℕ) →₀ K).support : Type _) := by
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
  have htransportLower {x y z : (σ →₀ ℕ) →₀ K}
      {C : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
      (harch : ∀ v ∈ archAbsVal (K := K),
        ((⨆ i : σ →₀ ℕ, v (x i)) * ⨆ i : σ →₀ ℕ, v (y i)) ≤
          C * ⨆ i : σ →₀ ℕ, v (z i))
      (hnon : ∀ v ∈ nonarchAbsVal (K := K),
        (⨆ i : σ →₀ ℕ, v (z i)) =
          (⨆ i : σ →₀ ℕ, v (x i)) * ⨆ i : σ →₀ ℕ, v (y i)) :
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
  exact htransportLower (x := AddMonoidAlgebra.coeff p)
    (y := AddMonoidAlgebra.coeff q) (z := AddMonoidAlgebra.coeff (p * q))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hp))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr hq))
    (Finsupp.support_nonempty_iff.mp (support_nonempty.mpr (mul_ne_zero hp hq))) harch
    fun v hv ↦ iSup_coeff_mul (AdmissibleAbsValues.isNonarchimedean v hv) p q

end Heights

end MvPolynomial

section Examples

open Height Polynomial

end Examples
