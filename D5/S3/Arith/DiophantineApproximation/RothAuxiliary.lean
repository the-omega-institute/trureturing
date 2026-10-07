/- GID: D5/S3/Arith/DiophantineApproximation/RothAuxiliary
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothAuxiliary
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An auxiliary polynomial realizes prescribed derivative vanishing with degree and height bounds. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.AuxiliaryPolynomial
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
import all Mathlib.NumberTheory.Height.Basic
public import D5.S3.Arith.DiophantineApproximation.MvPolynomialEvalBound
public import D5.S3.Arith.DiophantineApproximation.RothLemma

@[expose] public section

open Height MeasureTheory MvPolynomial Module AdmissibleAbsValues

namespace NumberField

variable {K F : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]

/-- **Steps I and II of Roth's proof** (Bombieri–Gubler 6.4.5–6.4.7): the auxiliary polynomial of
Layer 2.6, differentiated until it survives at `β` by Layer 2.7. The index is taken at the point
`tgt a` for every `a`, and `C₁ j` bounds the heights of the `j`-th coordinates of those points; in
Roth's theorem the points are diagonal and `C₁` is constant, and in Layer 3.8 they are not. -/
theorem exists_auxiliary_deriv {A : Type*} [Fintype A] {m : ℕ} (tgt : A → Fin (m + 1) → F)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2)
    (hfeas : (finrank K F : ℝ) * (Fintype.card A : ℝ)
      * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) < 1 / 2)
    {C₁ : Fin (m + 1) → ℝ} (hC₁0 : ∀ j, 0 ≤ C₁ j)
    (hC₁ : ∀ a j, absLogHeight₁ (tgt a j) + Real.log 2 + 1 ≤ C₁ j) :
    ∃ D₀ : ℕ, ∀ d : Fin (m + 1) → ℕ, (∀ j, D₀ ≤ d j) → ∀ β : Fin (m + 1) → K,
      (∀ j : Fin m, (d j.succ : ℝ) ≤ ε ^ (2 ^ m) * (d j.castSucc : ℝ)) →
      (∀ j, (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ)
            + 4 * ((m : ℝ) + 1) * (d 0 : ℝ) * (totalWeight K : ℝ)
          ≤ ε ^ (2 ^ m) * ((d j : ℝ) * logHeight₁ (β j))) →
      ∃ Q : MvPolynomial (Fin (m + 1)) K, eval β Q ≠ 0 ∧ (∀ j, Q.degreeOf j ≤ d j) ∧
        (∀ a, ENNReal.ofReal ((1 / 2 - 4 * ε) * ((m : ℝ) + 1))
          ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (Q.map (algebraMap K F))) ∧
        Real.log Q.mulHeight ≤ (totalWeight K : ℝ) * ∑ i, (C₁ i + Real.log 2) * (d i : ℝ) := by
  have nativeSource72 := (open Nat Finset in (fun {σ : Type _} [instSource1 : Fintype σ] {K : Type _} [instSource3 : Field K] {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) => (show P.totalDegree ≤ ∑ j, d j from by
    classical
    refine Finset.sup_le fun ν hν ↦ ?_
    rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    exact Finset.sum_le_sum fun j _ ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j))))
  have nativeSource91 := (open Function IntermediateField Module in (open scoped Classical in (fun {K : Type _} [instSource1 : Field K] [instSource2 : CharZero K] (x : K) => (show 0 ≤ NumberField.absLogHeight₁ x from by
    classical
    rw [NumberField.absLogHeight₁]
    apply Real.log_nonneg
    by_cases hx : IsIntegral ℚ x
    · haveI : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
      haveI : NumberField ℚ⟮x⟯ := {}
      rw [NumberField.absMulHeight₁, dif_pos hx]
      exact Real.one_le_rpow (Height.one_le_mulHeight₁ _) (by positivity)
    · rw [NumberField.absMulHeight₁, dif_neg hx]))))
  have prod_choose_le_two_pow (μ ν : Fin (m + 1) →₀ ℕ) :
    (μ.prod fun j k ↦ (ν j).choose k) ≤ 2 ^ (ν.sum fun _ k ↦ k) := by
    classical
    calc (μ.prod fun j k ↦ (ν j).choose k) ≤ ∏ j ∈ μ.support, 2 ^ ν j :=
          Finset.prod_le_prod₀ (fun _ _ ↦ Nat.zero_le _)
            (fun j _ ↦ Nat.choose_le_two_pow (ν j) (μ j))
      _ = 2 ^ ∑ j ∈ μ.support, ν j := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ ∑ j ∈ μ.support ∪ ν.support, ν j :=
          Nat.pow_le_pow_right (by norm_num)
            (Finset.sum_le_sum_of_subset Finset.subset_union_left)
      _ = 2 ^ (ν.sum fun _ k ↦ k) := by
          rw [Finsupp.sum]
          congr 1
          exact (Finset.sum_subset Finset.subset_union_right fun j _ hj ↦
            Finsupp.notMem_support_iff.mp hj).symm
  have iSup_coeff_hasseDeriv_le (v : AbsoluteValue K ℝ) (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
    (⨆ n : Fin (m + 1) →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : Fin (m + 1) →₀ ℕ, v (P.coeff n) := by
    have hasseDeriv_apply (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
      MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
        MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials (Fin (m + 1)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    have prod_choose_eq_zero {μ ν : Fin (m + 1) →₀ ℕ} (h : ¬ μ ≤ ν) :
      (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
    have MvPolynomial.hasseDeriv_coeff (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) (n : Fin (m + 1) →₀ ℕ) :
      (MvPolynomial.hasseDeriv μ P).coeff n
        = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
      classical
      rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n + μ)]
      · rw [if_pos (add_tsub_cancel_right n μ)]
        have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k :=
          Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
        rw [h]
      · intro m _ hne
        by_cases h : m - μ = n
        · rw [if_pos h]
          have hle : ¬ μ ≤ m := fun hle ↦ hne (by rw [← h, tsub_add_cancel_of_le hle])
          rw [prod_choose_eq_zero hle]
          simp
        · rw [if_neg h]
      · intro h
        rw [notMem_support_iff.mp h]
        simp
    have hnn : (0 : ℝ) ≤ ⨆ n : Fin (m + 1) →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
    refine Real.iSup_le (fun n ↦ ?_) (by positivity)
    rw [MvPolynomial.hasseDeriv_coeff, map_mul]
    rcases eq_or_ne (P.coeff (n + μ)) 0 with h | h
    · rw [h, map_zero, mul_zero]
      positivity
    · have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) ≤ 2 ^ P.totalDegree := by
        refine (v.apply_nat_le_self _).trans ?_
        have h1 : (μ.prod fun j k ↦ (n j + k).choose k) ≤ 2 ^ ((n + μ).sum fun _ k ↦ k) := by
          refine le_trans (le_of_eq ?_) (prod_choose_le_two_pow μ (n + μ))
          exact Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
        have h2 : ((n + μ).sum fun _ k ↦ k) ≤ P.totalDegree := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr h)
        calc ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : ℝ)
            ≤ ((2 ^ ((n + μ).sum fun _ k ↦ k) : ℕ) : ℝ) := by exact_mod_cast h1
          _ ≤ ((2 ^ P.totalDegree : ℕ) : ℝ) := by
              exact_mod_cast Nat.pow_le_pow_right (by norm_num) h2
          _ = 2 ^ P.totalDegree := by push_cast; ring
      exact mul_le_mul hc (le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) (n + μ))
        (v.nonneg _) (by positivity)
  have iSup_coeff_hasseDeriv_le_of_isNonarchimedean {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
    (⨆ n : Fin (m + 1) →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n)) ≤ ⨆ n : Fin (m + 1) →₀ ℕ, v (P.coeff n) := by
    have hasseDeriv_apply (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
      MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
        MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials (Fin (m + 1)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    have prod_choose_eq_zero {μ ν : Fin (m + 1) →₀ ℕ} (h : ¬ μ ≤ ν) :
      (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
    have MvPolynomial.hasseDeriv_coeff (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) (n : Fin (m + 1) →₀ ℕ) :
      (MvPolynomial.hasseDeriv μ P).coeff n
        = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
      classical
      rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n + μ)]
      · rw [if_pos (add_tsub_cancel_right n μ)]
        have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k :=
          Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
        rw [h]
      · intro m _ hne
        by_cases h : m - μ = n
        · rw [if_pos h]
          have hle : ¬ μ ≤ m := fun hle ↦ hne (by rw [← h, tsub_add_cancel_of_le hle])
          rw [prod_choose_eq_zero hle]
          simp
        · rw [if_neg h]
      · intro h
        rw [notMem_support_iff.mp h]
        simp
    have hnn : (0 : ℝ) ≤ ⨆ n : Fin (m + 1) →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
    refine Real.iSup_le (fun n ↦ ?_) hnn
    rw [MvPolynomial.hasseDeriv_coeff, map_mul]
    have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) ≤ 1 :=
      IsNonarchimedean.apply_natCast_le_one hv
    calc v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * v (P.coeff (n + μ))
        ≤ 1 * v (P.coeff (n + μ)) := by gcongr
      _ = v (P.coeff (n + μ)) := one_mul _
      _ ≤ ⨆ n : Fin (m + 1) →₀ ℕ, v (P.coeff n) :=
          le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) (n + μ)
  have hasseDeriv_apply (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials (Fin (m + 1)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ ν : Fin (m + 1) →₀ ℕ} (h : ¬ μ ≤ ν) :
    (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) (n : Fin (m + 1) →₀ ℕ) :
    (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
    classical
    rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single (n + μ)]
    · rw [if_pos (add_tsub_cancel_right n μ)]
      have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k :=
        Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
      rw [h]
    · intro m _ hne
      by_cases h : m - μ = n
      · rw [if_pos h]
        have hle : ¬ μ ≤ m := fun hle ↦ hne (by rw [← h, tsub_add_cancel_of_le hle])
        rw [prod_choose_eq_zero hle]
        simp
      · rw [if_neg h]
    · intro h
      rw [notMem_support_iff.mp h]
      simp
  have degreeOf_hasseDeriv_le (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) (j : Fin (m + 1)) :
    (MvPolynomial.hasseDeriv μ P).degreeOf j ≤ P.degreeOf j - μ j := by
    classical
    rw [MvPolynomial.degreeOf_le_iff]
    intro m hm
    have hne : P.coeff (m + μ) ≠ 0 := by
      intro h
      rw [MvPolynomial.mem_support_iff, hasseDeriv_coeff, h, mul_zero] at hm
      exact hm rfl
    have := (MvPolynomial.degreeOf_le_iff).mp (le_refl (P.degreeOf j)) (m + μ) (mem_support_iff.mpr hne)
    rw [Finsupp.add_apply] at this
    omega
  classical
  have hr0 : (0 : ℝ) ≤ (finrank K F : ℝ) := Nat.cast_nonneg _
  set e := (Fintype.equivFin A).symm with hedef
  set V : ℝ := cubeSimplexVolume (m + 1) ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ)) with hVdef
  have hV0 : (0 : ℝ) ≤ V := (fun m t ↦ (show 0 ≤ MeasureTheory.cubeSimplexVolume m t from ENNReal.toReal_nonneg)) _ _
  have hVexp : V ≤ Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) := by
    have h := cubeSimplexVolume_le_exp_neg (m + 1) hε0.le
    rw [hVdef]
    push_cast at h ⊢
    exact h
  have hsumV : (∑ _k : Fin (Fintype.card A), V) = (Fintype.card A : ℝ) * V := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  have hfeas2 : (finrank K F : ℝ) * (∑ _k : Fin (Fintype.card A), V) < 1 / 2 := by
    rw [hsumV]
    calc (finrank K F : ℝ) * ((Fintype.card A : ℝ) * V)
        ≤ (finrank K F : ℝ) * ((Fintype.card A : ℝ)
            * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2))) := by gcongr
      _ = (finrank K F : ℝ) * (Fintype.card A : ℝ)
            * Real.exp (-(6 * ((m : ℝ) + 1) * ε ^ 2)) := by ring
      _ < 1 / 2 := hfeas
  obtain ⟨D₀, hD₀⟩ := MvPolynomial.exists_ne_zero_le_index_logHeight_le (K := K) (F := F)
    (α := fun k : Fin (Fintype.card A) ↦ tgt (e k))
    (t := fun _ : Fin (Fintype.card A) ↦ (1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
    (fun _ ↦ by positivity) (by rw [← hVdef]; linarith) (δ := 1) one_pos
  refine ⟨max D₀ 1, fun d hd β hratio hheight ↦ ?_⟩
  have hd1 : ∀ j, 1 ≤ d j := fun j ↦ le_trans (le_max_right D₀ 1) (hd j)
  obtain ⟨P, hP0, hPdeg, hPindex, hPheight⟩ := hD₀ d fun j ↦ le_trans (le_max_left D₀ 1) (hd j)
  rw [← hVdef] at hPheight
  -- the height of the auxiliary polynomial
  have hCd0 : (0 : ℝ) ≤ ∑ i, C₁ i * (d i : ℝ) :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hC₁0 i) (Nat.cast_nonneg _)
  have hPh : Real.log P.mulHeight ≤ (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ) := by
    have hstep1 : (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
          V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
        ≤ ((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ) := by
      calc (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
            V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
          ≤ ∑ _k : Fin (Fintype.card A), ∑ j : Fin (m + 1), V * (C₁ j * (d j : ℝ)) := by
            refine Finset.sum_le_sum fun k _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hC₁ (e k) j) hV0) (Nat.cast_nonneg _)
        _ = ∑ _k : Fin (Fintype.card A), V * ∑ j : Fin (m + 1), C₁ j * (d j : ℝ) :=
            Finset.sum_congr rfl fun k _ ↦ (Finset.mul_sum _ _ _).symm
        _ = ((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
            ring
    have hcoef : (finrank K F : ℝ)
        / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
        ≤ 2 * (finrank K F : ℝ) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hstep2 : (finrank K F : ℝ)
        / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
        * (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
            V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
        ≤ ∑ i, C₁ i * (d i : ℝ) := by
      calc (finrank K F : ℝ) / (1 - (finrank K F : ℝ) * ∑ _k : Fin (Fintype.card A), V)
            * (∑ k : Fin (Fintype.card A), ∑ j : Fin (m + 1),
              V * (absLogHeight₁ (tgt (e k) j) + Real.log 2 + 1) * (d j : ℝ))
          ≤ (2 * (finrank K F : ℝ)) * (((Fintype.card A : ℝ) * V) * ∑ i, C₁ i * (d i : ℝ)) := by
            refine mul_le_mul hcoef hstep1 ?_ (by positivity)
            refine Finset.sum_nonneg fun k _ ↦ Finset.sum_nonneg fun j _ ↦ ?_
            have h3 : (0 : ℝ) ≤ absLogHeight₁ (tgt (e k) j) := nativeSource91 _
            have h4 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
            exact mul_nonneg (mul_nonneg hV0 (by linarith)) (Nat.cast_nonneg _)
        _ = (2 * ((finrank K F : ℝ) * ((Fintype.card A : ℝ) * V))) * ∑ i, C₁ i * (d i : ℝ) := by
            ring
        _ ≤ 1 * ∑ i, C₁ i * (d i : ℝ) := by
            refine mul_le_mul_of_nonneg_right ?_ hCd0
            rw [← hsumV]
            linarith
        _ = ∑ i, C₁ i * (d i : ℝ) := one_mul _
    have hfr : (0 : ℝ) < (finrank ℚ K : ℝ) := by
      exact_mod_cast Module.finrank_pos
    rw [div_le_iff₀ hfr] at hPheight
    calc Real.log P.mulHeight ≤ _ * (finrank ℚ K : ℝ) := hPheight
      _ ≤ (∑ i, C₁ i * (d i : ℝ)) * (finrank ℚ K : ℝ) :=
          mul_le_mul_of_nonneg_right hstep2 hfr.le
      _ = (totalWeight K : ℝ) * ∑ i, C₁ i * (d i : ℝ) := by
          rw [totalWeight_eq_finrank]
          ring
  -- Roth's lemma
  have hσ0 : (0 : ℝ) < ε ^ 2 ^ m := pow_pos hε0 _
  have hσ1 : ε ^ 2 ^ m ≤ 1 / 2 := by
    calc ε ^ 2 ^ m ≤ ε ^ 1 :=
          pow_le_pow_of_le_one hε0.le (by linarith) Nat.one_le_two_pow
      _ = ε := pow_one _
      _ ≤ 1 / 2 := hε1.le
  have hPidx := MvPolynomial.index_le_of_degree_ratio hd1 hσ0 hσ1 hratio hP0 hPdeg β
    (fun j ↦ by
      rw [MvPolynomial.logHeight]
      have := hheight j
      linarith)
  have hexpid : (ε ^ 2 ^ m : ℝ) ^ ((1 / 2 : ℝ) ^ m) = ε := by
    have h2 : (((2 ^ m : ℕ) : ℝ)) * ((1 / 2 : ℝ) ^ m) = 1 := by
      push_cast
      rw [← mul_pow]
      norm_num
    rw [← Real.rpow_natCast ε (2 ^ m), ← Real.rpow_mul hε0.le, h2, Real.rpow_one]
  rw [hexpid] at hPidx
  -- a derivative that survives at `β`
  have hexμ : ∃ μ : Fin (m + 1) →₀ ℕ, eval β (hasseDeriv μ P) ≠ 0 ∧
      (μ.sum fun j k ↦ (k : ℝ) / d j) < 3 * ((m : ℝ) + 1) * ε := by
    by_contra hcon
    push Not at hcon
    have hge := (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {c : ENNReal}
      (h : ∀ μ : _ →₀ ℕ, MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0 →
        c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) ↦
      (show c ≤ MvPolynomial.index d α P from le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ)) (fun j ↦ (d j : ℝ)) (α := β) (P := P)
      (c := ENNReal.ofReal (3 * ((m : ℝ) + 1) * ε))
      fun μ hμ ↦ ENNReal.ofReal_le_ofReal (hcon μ hμ)
    have h2 := le_trans hge hPidx
    rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
    nlinarith
  obtain ⟨μ, hμne, hμw⟩ := hexμ
  have hμw0 : (0 : ℝ) ≤ μ.sum fun j k ↦ (k : ℝ) / d j :=
    Finset.sum_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  refine ⟨hasseDeriv μ P, hμne, fun j ↦ ?_, fun a ↦ ?_, ?_⟩
  · exact le_trans (le_trans (degreeOf_hasseDeriv_le μ P j) (Nat.sub_le _ _)) (hPdeg j)
  · -- the index at the target drops by at most the weight of `μ`
    have hmap : (hasseDeriv μ P).map (algebraMap K F) = hasseDeriv μ (P.map (algebraMap K F)) :=
      map_hasseDeriv _ μ P
    have hPa : ENNReal.ofReal ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
        ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (P.map (algebraMap K F)) := by
      have h := hPindex (e.symm a)
      rwa [Equiv.apply_symm_apply] at h
    have hdrop := MvPolynomial.index_le_hasseDeriv_add (fun j ↦ (d j : ℝ))
      (fun j ↦ Nat.cast_nonneg _) (tgt a) (P.map (algebraMap K F)) μ
    rw [hmap]
    have hchain : ENNReal.ofReal ((1 / 2 - ε) * ((m + 1 : ℕ) : ℝ))
        ≤ index (fun j ↦ (d j : ℝ)) (tgt a) (hasseDeriv μ (P.map (algebraMap K F)))
          + ENNReal.ofReal (μ.sum fun j k ↦ (k : ℝ) / d j) := le_trans hPa hdrop
    rw [← tsub_le_iff_right, ← ENNReal.ofReal_sub _ hμw0] at hchain
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) hchain
    push_cast
    nlinarith
  · -- the height of the derivative
    have hCle : (1 : ℝ) ≤ 2 ^ ∑ i, d i := one_le_pow₀ (by norm_num)
    have hQle : (hasseDeriv μ P).mulHeight
        ≤ (2 ^ ∑ i, d i : ℝ) ^ totalWeight K * P.mulHeight ^ 1 := by
      have hTransport {x z : (Fin (m + 1) →₀ ℕ) →₀ K} {C : ℝ} {p : ℕ}
          (hx : x ≠ 0) (hC : 1 ≤ C)
          (harch : ∀ v ∈ AdmissibleAbsValues.archAbsVal (K := K),
            (⨆ i, v (z i)) ≤ C * (⨆ i, v (x i)) ^ p)
          (hnon : ∀ v ∈ AdmissibleAbsValues.nonarchAbsVal (K := K),
            (⨆ i, v (z i)) ≤ (⨆ i, v (x i)) ^ p) :
          z.mulHeight ≤ C ^ totalWeight K * x.mulHeight ^ p := by
        classical
        have hsupp (x : (Fin (m + 1) →₀ ℕ) →₀ K) (v : AbsoluteValue K ℝ) :
            (⨆ i : Fin (m + 1) →₀ ℕ, v (x i)) = ⨆ i : x.support, v (x i.val) := by
          refine le_antisymm (Real.iSup_le (fun i ↦ ?_) (Real.iSup_nonneg fun _ ↦ v.nonneg _))
            (Real.iSup_le (fun i ↦ le_ciSup ((by have hFiniteRange := (x).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) i.val)
              (Real.iSup_nonneg fun _ ↦ v.nonneg _))
          rcases eq_or_ne (x i) 0 with h | h
          · simp only [h, map_zero]
            exact Real.iSup_nonneg fun _ ↦ v.nonneg _
          · exact Finite.le_ciSup_of_le (⟨i, Finsupp.mem_support_iff.mpr h⟩ : x.support) le_rfl
        have hcoe (x : (Fin (m + 1) →₀ ℕ) →₀ K) : Height.mulHeight ⇑x = x.mulHeight := by
          rcases eq_or_ne x 0 with rfl | hx
          · have : IsEmpty ((0 : (Fin (m + 1) →₀ ℕ) →₀ K).support : Type _) := by
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
        have hSupport {a : (Fin (m + 1) →₀ ℕ) →₀ K} (ha : a ≠ 0) :
            (fun v : nonarchAbsVal (K := K) ↦ ⨆ i, v.val (a i)).HasFiniteMulSupport := by
          have has : (fun i : a.support ↦ a i.val) ≠ 0 := by
            obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr ha
            exact Function.ne_iff.mpr ⟨⟨i, hi⟩, Finsupp.mem_support_iff.mp hi⟩
          have hs := Height.hasFiniteMulSupport_iSup_nonarchAbsVal has
          convert hs using 1
          ext v
          exact hsupp a v.val
        have hCtw : (1 : ℝ) ≤ C ^ totalWeight K := one_le_pow₀ hC
        have hxh : (1 : ℝ) ≤ x.mulHeight ^ p := one_le_pow₀ ((fun p : _ →₀ K ↦ (show 1 ≤ p.mulHeight from Height.one_le_mulHeight (fun i : (p).support ↦ (p) i.val))) x)
        rcases eq_or_ne z 0 with rfl | hz
        · rw [(show (0 : (Fin (m + 1) →₀ ℕ) →₀ K).mulHeight = 1 from by
      rw [Finsupp.mulHeight]
      exact Height.mulHeight_zero)]
          exact one_le_mul_of_one_le_of_one_le hCtw hxh
        have hzc : ⇑z ≠ 0 := fun h ↦ hz (DFunLike.coe_injective h)
        have hxc : ⇑x ≠ 0 := fun h ↦ hx (DFunLike.coe_injective h)
        have hFnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i) :=
          fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
        have hGnn : ∀ v : AbsoluteValue K ℝ, 0 ≤ ⨆ i : (Fin (m + 1) →₀ ℕ), v (z i) :=
          fun v ↦ Real.iSup_nonneg fun _ ↦ v.nonneg _
        rw [← hcoe z, ← hcoe x, Height.mulHeight_eq hzc,
          Height.mulHeight_eq hxc]
        have harchprod :
            (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (z i)).prod
              ≤ C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)).prod ^ p := by
          calc (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (z i)).prod
              ≤ (archAbsVal.map fun v ↦ C * (⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)) ^ p).prod :=
                Multiset.prod_map_le_prod_map₀ _ _ (fun v _ ↦ hGnn v) harch
            _ = (archAbsVal.map fun _ : AbsoluteValue K ℝ ↦ C).prod
                  * (archAbsVal.map fun v ↦ (⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)) ^ p).prod := Multiset.prod_map_mul
            _ = C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)).prod ^ p := by
                rw [Multiset.map_const', Multiset.prod_replicate, ← Multiset.prod_map_pow]
                rfl
        have hnonprod :
            (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (Fin (m + 1) →₀ ℕ), v.val (z i))
              ≤ (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (Fin (m + 1) →₀ ℕ), v.val (x i)) ^ p := by
          have hFp : (fun v : nonarchAbsVal (K := K) ↦ (⨆ i : (Fin (m + 1) →₀ ℕ), v.val (x i)) ^ p).HasFiniteMulSupport :=
            Set.Finite.subset (hSupport hx) fun v hv ↦ by
              simp only [Function.mem_mulSupport] at hv ⊢
              exact fun h ↦ hv (by rw [h, one_pow])
          rw [finprod_pow (hSupport hx)]
          exact finprod_le_finprod₀ (hSupport hz) (fun v ↦ hGnn v.val)
            hFp fun v ↦ hnon v.val v.prop
        have hXnn : (0 : ℝ) ≤ (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)).prod :=
          Multiset.prod_nonneg fun a ha ↦ by
            obtain ⟨v, _, rfl⟩ := Multiset.mem_map.mp ha
            exact hFnn v
        calc (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (z i)).prod
                * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (Fin (m + 1) →₀ ℕ), v.val (z i)
            ≤ (C ^ totalWeight K * (archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)).prod ^ p)
                * (∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (Fin (m + 1) →₀ ℕ), v.val (x i)) ^ p :=
              mul_le_mul harchprod hnonprod (finprod_nonneg fun v ↦ hGnn v.val)
                (mul_nonneg (by positivity) (pow_nonneg hXnn p))
          _ = C ^ totalWeight K * ((archAbsVal.map fun v ↦ ⨆ i : (Fin (m + 1) →₀ ℕ), v (x i)).prod
                * ∏ᶠ v : nonarchAbsVal (K := K), ⨆ i : (Fin (m + 1) →₀ ℕ), v.val (x i)) ^ p := by
              rw [mul_pow, mul_assoc]
      refine hTransport (x := AddMonoidAlgebra.coeff P)
        (z := AddMonoidAlgebra.coeff (hasseDeriv μ P))
        (fun h ↦ hP0 (by ext ν; exact congrFun (congrArg DFunLike.coe h) ν))
        hCle (fun v _ ↦ ?_) fun v hv ↦ ?_
      · rw [pow_one]
        refine le_trans (iSup_coeff_hasseDeriv_le v μ P) ?_
        refine mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun _ ↦ v.nonneg _)
        exact pow_le_pow_right₀ one_le_two (nativeSource72 hPdeg)
      · rw [pow_one]
        exact iSup_coeff_hasseDeriv_le_of_isNonarchimedean
          (AdmissibleAbsValues.isNonarchimedean v hv) μ P
    rw [pow_one] at hQle
    have hlog := Real.log_le_log (show 0 < (hasseDeriv μ P).mulHeight from Height.mulHeight_pos
      (fun i : (AddMonoidAlgebra.coeff (hasseDeriv μ P)).support ↦
        (AddMonoidAlgebra.coeff (hasseDeriv μ P)) i.val)) hQle
    rw [Real.log_mul (by positivity) (show 0 < P.mulHeight from Height.mulHeight_pos
      (fun i : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff P) i.val)).ne', ← Real.rpow_natCast
      ((2 : ℝ) ^ ∑ i, d i) (totalWeight K), Real.log_rpow (by positivity), Real.log_pow] at hlog
    have hcast : ((∑ i, d i : ℕ) : ℝ) = ∑ i, (d i : ℝ) := by push_cast; ring
    rw [hcast] at hlog
    have hsplit : ∑ i, (C₁ i + Real.log 2) * (d i : ℝ)
        = ∑ i, C₁ i * (d i : ℝ) + Real.log 2 * ∑ i, (d i : ℝ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hsplit]
    rw [totalWeight_eq_finrank] at hPh hlog ⊢
    nlinarith [hlog, hPh]

end NumberField

end
