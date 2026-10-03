/- GID: D5/S3/Arith/DiophantineApproximation/PolynomialDeterminantHeight
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/PolynomialDeterminantHeight
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The determinant height of a polynomial matrix has an explicit product bound. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.AbsoluteValues.Heights.Gelfond
public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
import all Mathlib.NumberTheory.Height.Basic

@[expose] public section

open Finset Height AdmissibleAbsValues

namespace MvPolynomial

section Local

variable {K : Type*} [Field K] {σ ι : Type*} {v : AbsoluteValue K ℝ}

/-- **The local factor of a finite product**, with one support count per factor. -/
theorem iSup_coeff_prod_le (s : Finset ι) (f : ι → MvPolynomial σ K) {B C : ℝ} (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hsupp : ∀ a ∈ s, (#(f a).support : ℝ) ≤ B)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∏ a ∈ s, f a).coeff ν)) ≤ (B * C) ^ #s := by
  classical
  have hOne : (⨆ ν : σ →₀ ℕ, v ((1 : MvPolynomial σ K).coeff ν)) = 1 := by
    classical
    have h0 : v ((1 : MvPolynomial σ K).coeff 0) = 1 := by
      rw [MvPolynomial.coeff_one, if_pos rfl, map_one]
    have hBdd : BddAbove (Set.range
        (fun ν : σ →₀ ℕ ↦ v ((1 : MvPolynomial σ K).coeff ν))) := by
      have hFiniteRange := (AddMonoidAlgebra.coeff (1 : MvPolynomial σ K)).finite_range.image v
      rw [← Set.range_comp] at hFiniteRange
      change (Set.range (fun ν : σ →₀ ℕ ↦ v ((1 : MvPolynomial σ K).coeff ν))).Finite
        at hFiniteRange
      exact hFiniteRange.bddAbove
    refine le_antisymm (Real.iSup_le (fun ν ↦ ?_) zero_le_one) (le_of_eq_of_le h0.symm
      (le_ciSup hBdd (0 : σ →₀ ℕ)))
    rcases eq_or_ne ν 0 with rfl | h
    · exact le_of_eq h0
    · rw [MvPolynomial.coeff_one, if_neg (Ne.symm h), map_zero]
      exact zero_le_one
  induction s using Finset.induction with
  | empty => simpa using le_of_eq hOne
  | insert a s ha ih =>
      have hBC : (0 : ℝ) ≤ B * C := mul_nonneg (le_trans zero_le_one hB) hC
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ']
      refine le_trans (iSup_coeff_mul_le_card_support v (f a) (∏ b ∈ s, f b)) ?_
      refine le_trans (mul_le_mul (le_trans (by exact_mod_cast Nat.cast_le.mpr (min_le_left _ _))
        (hsupp a (Finset.mem_insert_self a s)))
        (mul_le_mul (hf a (Finset.mem_insert_self a s))
          (ih (fun b hb ↦ hsupp b (Finset.mem_insert_of_mem hb))
            fun b hb ↦ hf b (Finset.mem_insert_of_mem hb))
          ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (_)))) hC)
        (mul_nonneg ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (_)))) ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (_)))))
        (le_trans zero_le_one hB)) (le_of_eq (by ring)) |>.trans (le_of_eq rfl)

/-- **The local factor of a finite product at a nonarchimedean absolute value**, by Gauss's
lemma, with no constant. -/
theorem iSup_coeff_prod_le_of_isNonarchimedean (hv : IsNonarchimedean v) (s : Finset ι)
    (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
    (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) :
    (⨆ ν, v ((∏ a ∈ s, f a).coeff ν)) ≤ C ^ #s := by
  classical
  have hOne : (⨆ ν : σ →₀ ℕ, v ((1 : MvPolynomial σ K).coeff ν)) = 1 := by
    classical
    have h0 : v ((1 : MvPolynomial σ K).coeff 0) = 1 := by
      rw [MvPolynomial.coeff_one, if_pos rfl, map_one]
    have hBdd : BddAbove (Set.range
        (fun ν : σ →₀ ℕ ↦ v ((1 : MvPolynomial σ K).coeff ν))) := by
      have hFiniteRange := (AddMonoidAlgebra.coeff (1 : MvPolynomial σ K)).finite_range.image v
      rw [← Set.range_comp] at hFiniteRange
      change (Set.range (fun ν : σ →₀ ℕ ↦ v ((1 : MvPolynomial σ K).coeff ν))).Finite
        at hFiniteRange
      exact hFiniteRange.bddAbove
    refine le_antisymm (Real.iSup_le (fun ν ↦ ?_) zero_le_one) (le_of_eq_of_le h0.symm
      (le_ciSup hBdd (0 : σ →₀ ℕ)))
    rcases eq_or_ne ν 0 with rfl | h
    · exact le_of_eq h0
    · rw [MvPolynomial.coeff_one, if_neg (Ne.symm h), map_zero]
      exact zero_le_one
  induction s using Finset.induction with
  | empty => simpa using le_of_eq hOne
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, pow_succ',
        iSup_coeff_mul hv]
      exact mul_le_mul (hf a (Finset.mem_insert_self a s))
        (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)) ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (_)))) hC

end Local

section Det

variable {K : Type*} [Field K] {σ : Type*} {v : AbsoluteValue K ℝ} {n : ℕ}

/-- **The local factor of a determinant.** -/
theorem iSup_coeff_det_le (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {B C : ℝ} (hB : 1 ≤ B)
    (hC : 0 ≤ C) (hsupp : ∀ i j, (#(A i j).support : ℝ) ≤ B)
    (hA : ∀ i j, (⨆ ν, v ((A i j).coeff ν)) ≤ C) :
    (⨆ ν, v (A.det.coeff ν)) ≤ (n.factorial : ℝ) * (B * C) ^ n := by
  let nativeSource65 := (open Finset Height AdmissibleAbsValues in (fun {K : Type _} [instSource1 : Field K] {σ : Type _} {ι : Type _} {v : AbsoluteValue K ℝ} (s : Finset ι) (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
      (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) => (show (⨆ ν, v ((∑ a ∈ s, f a).coeff ν)) ≤ #s * C from by
    classical
    refine Real.iSup_le (fun ν ↦ ?_) (by positivity)
    rw [MvPolynomial.coeff_sum]
    refine le_trans (v.sum_le _ _) ?_
    calc ∑ a ∈ s, v ((f a).coeff ν) ≤ ∑ _a ∈ s, C :=
          Finset.sum_le_sum fun a ha ↦ by
            have hBdd : BddAbove (Set.range (fun μ : σ →₀ ℕ ↦ v ((f a).coeff μ))) := by
              have hFiniteRange := (AddMonoidAlgebra.coeff (f a)).finite_range.image v
              rw [← Set.range_comp] at hFiniteRange
              change (Set.range (fun μ : σ →₀ ℕ ↦ v ((f a).coeff μ))).Finite at hFiniteRange
              exact hFiniteRange.bddAbove
            exact le_trans (le_ciSup hBdd ν) (hf a ha)
      _ = #s * C := by rw [Finset.sum_const, nsmul_eq_mul])))
  classical
  rw [Matrix.det_apply']
  refine le_trans (nativeSource65 (C := (B * C) ^ n) _ _ (by positivity) fun τ _ ↦ ?_)
    (le_of_eq ?_)
  · have hprod : (⨆ ν, v ((∏ i, A (τ i) i).coeff ν)) ≤ (B * C) ^ n := by
      simpa using iSup_coeff_prod_le Finset.univ (fun i ↦ A (τ i) i) hB hC
        (fun i _ ↦ hsupp _ _) fun i _ ↦ hA _ _
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simpa using hprod
  · rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]

/-- **The local factor of a determinant at a nonarchimedean absolute value.** -/
theorem iSup_coeff_det_le_of_isNonarchimedean (hv : IsNonarchimedean v)
    (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K)) {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ i j, (⨆ ν, v ((A i j).coeff ν)) ≤ C) :
    (⨆ ν, v (A.det.coeff ν)) ≤ C ^ n := by
  let nativeSource66 := (open Finset Height AdmissibleAbsValues in (fun {K : Type _} [instSource1 : Field K] {σ : Type _} {ι : Type _} {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v) (s : Finset ι)
      (f : ι → MvPolynomial σ K) {C : ℝ} (hC : 0 ≤ C)
      (hf : ∀ a ∈ s, (⨆ ν, v ((f a).coeff ν)) ≤ C) => (show (⨆ ν, v ((∑ a ∈ s, f a).coeff ν)) ≤ C from by
    classical
    refine Real.iSup_le (fun ν ↦ ?_) hC
    rcases s.eq_empty_or_nonempty with rfl | hs
    · simpa using hC
    rw [MvPolynomial.coeff_sum]
    obtain ⟨b, hb, hble⟩ := hv.finset_image_add_of_nonempty (g := fun a ↦ (f a).coeff ν) hs
    have hBdd : BddAbove (Set.range (fun μ : σ →₀ ℕ ↦ v ((f b).coeff μ))) := by
      have hFiniteRange := (AddMonoidAlgebra.coeff (f b)).finite_range.image v
      rw [← Set.range_comp] at hFiniteRange
      change (Set.range (fun μ : σ →₀ ℕ ↦ v ((f b).coeff μ))).Finite at hFiniteRange
      exact hFiniteRange.bddAbove
    exact le_trans hble (le_trans (le_ciSup hBdd ν) (hf b hb)))))
  classical
  rw [Matrix.det_apply']
  refine nativeSource66 hv _ _ (by positivity) fun τ _ ↦ ?_
  have hprod : (⨆ ν, v ((∏ i, A (τ i) i).coeff ν)) ≤ C ^ n := by
    simpa using iSup_coeff_prod_le_of_isNonarchimedean hv Finset.univ (fun i ↦ A (τ i) i) hC
      fun i _ ↦ hA _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> rw [h] <;> simpa using hprod

variable [AdmissibleAbsValues K]

/-- **The height of a determinant of polynomials.** The entries are compared with one polynomial
`P`, up to a constant at the archimedean absolute values and with no constant at the others,
which is exactly what a Hasse derivative satisfies. -/
theorem mulHeight_det_le (A : Matrix (Fin n) (Fin n) (MvPolynomial σ K))
    {P : MvPolynomial σ K} (hP : P ≠ 0) {B C : ℝ} (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hsupp : ∀ i j, (#(A i j).support : ℝ) ≤ B)
    (harch : ∀ v ∈ archAbsVal (K := K), ∀ i j,
      (⨆ ν, v ((A i j).coeff ν)) ≤ C * ⨆ ν, v (P.coeff ν))
    (hnon : ∀ v ∈ nonarchAbsVal (K := K), ∀ i j,
      (⨆ ν, v ((A i j).coeff ν)) ≤ ⨆ ν, v (P.coeff ν)) :
    A.det.mulHeight ≤ ((n.factorial : ℝ) * (B * C) ^ n) ^ totalWeight K * P.mulHeight ^ n := by
  have hTransport {x z : (σ →₀ ℕ) →₀ K} {C : ℝ} {p : ℕ}
      (hx : x ≠ 0) (hC : 1 ≤ C)
      (harch : ∀ v ∈ AdmissibleAbsValues.archAbsVal (K := K),
        (⨆ i, v (z i)) ≤ C * (⨆ i, v (x i)) ^ p)
      (hnon : ∀ v ∈ AdmissibleAbsValues.nonarchAbsVal (K := K),
        (⨆ i, v (z i)) ≤ (⨆ i, v (x i)) ^ p) :
      z.mulHeight ≤ C ^ totalWeight K * x.mulHeight ^ p := by
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
    have hSupport {a : (σ →₀ ℕ) →₀ K} (ha : a ≠ 0) :
        (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (a i)).HasFiniteMulSupport := by
      have has : (fun i : a.support ↦ a i.val) ≠ 0 := by
        obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr ha
        exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
      have hs := Height.hasFiniteMulSupport_iSup_nonarchAbsVal has
      convert hs using 1
      ext v
      exact hsupp a v.val
    have hCtw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
    have hxh : (1 : ℝ) ≤ x.mulHeight ^ p := one_le_pow₀ ((fun p : _ →₀ K ↦ Height.one_le_mulHeight (fun i : (p).support ↦ (p) i.val)) x)
    rcases eq_or_ne z 0 with rfl | hz
    · rw [(show (0 : (σ →₀ ℕ) →₀ K).mulHeight = 1 from by
      rw [Finsupp.mulHeight]
      exact Height.mulHeight_zero)]
      exact one_le_mul_of_one_le_of_one_le hCtw hxh
    have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
    have hxc : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
    have hFnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : (σ →₀ ℕ), v (x i) :=
      fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
    have hGnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : (σ →₀ ℕ), v (z i) :=
      fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
    rw [← hcoe z, ← hcoe x, Height.mulHeight_eq hzc,
      Height.mulHeight_eq hxc]
    have harchprod :
        (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (z i)).prod
          ≤ C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (x i)).prod ^ p := by
      calc (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (z i)).prod
          ≤ (archAbsVal.map fun v ↦ C * (⨆ i : (σ →₀ ℕ), v (x i)) ^ p).prod :=
            Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hGnn v) harch
        _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod
              * (archAbsVal.map fun v ↦ (⨆ i : (σ →₀ ℕ), v (x i)) ^ p).prod := Multiset.prod_map_mul
        _ = C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (x i)).prod ^ p := by
            rw [Multiset.map_const', Multiset.prod_replicate, ← Multiset.prod_map_pow]
            rfl
    have hnonprod :
        (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (σ →₀ ℕ), v.val (z i))
          ≤ (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (σ →₀ ℕ), v.val (x i)) ^ p := by
      have hFp : (fun v : nonarchAbsVal (K := K) ↦ (⨆ i : (σ →₀ ℕ), v.val (x i)) ^ p).HasFiniteMulSupport :=
        Set.Finite.subset (hSupport hx) fun v hv ↦ by
          simp only [Function.mem_mulSupport] at hv ⊢
          exact fun h ↦ hv (by rw [h, one_pow])
      rw [finprod_pow (hSupport hx)]
      exact finprod_le_finprod (hSupport hz) (fun v ↦ hGnn v.val)
        hFp fun v ↦ hnon v.val v.prop
    have hXnn : (0 : ℝ) ≤ (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (x i)).prod :=
      Multiset.prod_nonneg fun a ha ↦ by
        obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
        exact hFnn v
    calc (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (z i)).prod
            * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (σ →₀ ℕ), v.val (z i)
        ≤ (C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (x i)).prod ^ p)
            * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (σ →₀ ℕ), v.val (x i)) ^ p :=
          mul_le_mul harchprod hnonprod (finprod_nonneg fun v ↦ hGnn v.val)
            (mul_nonneg (by positivity) (pow_nonneg hXnn p))
      _ = C ^ totalWeight K * ((archAbsVal.map fun v ↦ ⨆ i : (σ →₀ ℕ), v (x i)).prod
            * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (σ →₀ ℕ), v.val (x i)) ^ p := by
          rw [mul_pow, mul_assoc]
  have hone : (1 : ℝ) ≤ (n.factorial : ℝ) * (B * C) ^ n := by
    have h1 : (1 : ℝ) ≤ (n.factorial : ℝ) := by exact_mod_cast n.factorial_pos
    have h2 : (1 : ℝ) ≤ (B * C) ^ n := one_le_pow₀ (one_le_mul_of_one_le_of_one_le hB hC)
    exact one_le_mul_of_one_le_of_one_le h1 h2
  refine hTransport (x := AddMonoidAlgebra.coeff P) (z := AddMonoidAlgebra.coeff A.det)
    (fun h ↦ hP (by ext ν; exact congrFun (congrArg DFunLike.coe h) ν))
    hone (fun v hv ↦ ?_) fun v hv ↦ ?_
  · refine le_trans (iSup_coeff_det_le A hB
      (mul_nonneg (le_trans zero_le_one hC) ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (P))))) hsupp (harch v hv))
      (le_of_eq ?_)
    change (n.factorial : ℝ) * (B * (C * (⨆ ν, v (P.coeff ν)))) ^ n
      = (n.factorial : ℝ) * (B * C) ^ n * (⨆ ν, v (P.coeff ν)) ^ n
    rw [mul_pow]
    ring
  · exact iSup_coeff_det_le_of_isNonarchimedean (AdmissibleAbsValues.isNonarchimedean v hv) A
      ((Real.iSup_nonneg fun ν ↦ (v).nonneg (MvPolynomial.coeff ν (P)))) (hnon v hv)

end Det

end MvPolynomial
