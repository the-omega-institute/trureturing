/- GID: D5/S3/Arith/DiophantineApproximation/RothLemma
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothLemma
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Degree ratios bound the polynomial index in Roth's lemma. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module
public import D5.S3.Arith.DiophantineApproximation.DisjointVariables
public import D5.S3.Arith.DiophantineApproximation.RothBaseCase
public import D5.S3.Arith.DiophantineApproximation.RothDecomposition
public import D5.S3.Arith.DiophantineApproximation.IndexRename
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Nat.Choose.Bounds
public import D5.S3.Arith.DiophantineApproximation.PolynomialDeterminantHeight
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
open Nat
open Finset Height AdmissibleAbsValues
open scoped ENNReal
namespace MvPolynomial
def rothConst (m : ℕ) : ℝ := 2 * (m + 1)
def RothProp (K : Type*) [Field K] [NumberField K] (m : ℕ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ ^ 2 ^ m ≤ 1 / 2 →
    ∀ d : Fin (m + 1) → ℕ, (∀ j, 1 ≤ d j) →
      (∀ j : Fin m, (d j.castSucc : ℝ) ≤ θ ^ 2 ^ m * d j.succ) →
      ∀ P : MvPolynomial (Fin (m + 1)) K, P ≠ 0 → (∀ j, P.degreeOf j ≤ d j) →
        ∀ ξ : Fin (m + 1) → K,
          (∀ j, P.logHeight + 4 * (m + 1) * d (Fin.last m) * totalWeight K
                  ≤ θ ^ 2 ^ m * (d j * logHeight₁ (ξ j))) →
          index (fun j ↦ (d j : ℝ)) ξ P ≤ ENNReal.ofReal (rothConst m * θ)
variable {K : Type*} [Field K] [NumberField K]
set_option maxHeartbeats 1600000 in
theorem rothProp_succ {m : ℕ} (ih : RothProp K m) : RothProp K (m + 1) := by
  have prod_choose_le_two_pow (μ ν : Fin (m + 2) →₀ ℕ) : (μ.prod fun j k ↦ (ν j).choose k) ≤ 2 ^ (ν.sum fun _ k ↦ k) := by
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
  have iSup_coeff_hasseDeriv_le (v : AbsoluteValue K ℝ) (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) : (⨆ n : Fin (m + 2) →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : Fin (m + 2) →₀ ℕ, v (P.coeff n) := by
    have hasseDeriv_apply (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) : MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
        MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials (Fin (m + 2)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    have prod_choose_eq_zero {μ ν : Fin (m + 2) →₀ ℕ} (h : ¬ μ ≤ ν) : (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
    have MvPolynomial.hasseDeriv_coeff (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) (n : Fin (m + 2) →₀ ℕ) : (MvPolynomial.hasseDeriv μ P).coeff n
        = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
      classical
      rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n + μ)]
      · rw [if_pos (add_tsub_cancel_right n μ)]
        have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k := Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
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
    have hnn : (0 : ℝ) ≤ ⨆ n : Fin (m + 2) →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
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
    (hv : IsNonarchimedean v) (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) :
    (⨆ n : Fin (m + 2) →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n)) ≤ ⨆ n : Fin (m + 2) →₀ ℕ, v (P.coeff n) := by
    have hasseDeriv_apply (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) : MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
        MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials (Fin (m + 2)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    have prod_choose_eq_zero {μ ν : Fin (m + 2) →₀ ℕ} (h : ¬ μ ≤ ν) : (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
    have MvPolynomial.hasseDeriv_coeff (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) (n : Fin (m + 2) →₀ ℕ) : (MvPolynomial.hasseDeriv μ P).coeff n
        = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
      classical
      rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
      simp only [MvPolynomial.coeff_monomial]
      rw [Finset.sum_eq_single (n + μ)]
      · rw [if_pos (add_tsub_cancel_right n μ)]
        have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k := Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
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
    have hnn : (0 : ℝ) ≤ ⨆ n : Fin (m + 2) →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
    refine Real.iSup_le (fun n ↦ ?_) hnn
    rw [MvPolynomial.hasseDeriv_coeff, map_mul]
    have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) ≤ 1 :=
      hv.apply_natCast_le_one (by simp) (map_one v)
    calc v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * v (P.coeff (n + μ))
        ≤ 1 * v (P.coeff (n + μ)) := by gcongr
      _ = v (P.coeff (n + μ)) := one_mul _
      _ ≤ ⨆ n : Fin (m + 2) →₀ ℕ, v (P.coeff n) :=
          le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) (n + μ)
  have hasseDeriv_apply (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) : MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials (Fin (m + 2)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ ν : Fin (m + 2) →₀ ℕ} (h : ¬ μ ≤ ν) : (μ.prod fun j k ↦ (ν j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) (n : Fin (m + 2) →₀ ℕ) : (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : K) * P.coeff (n + μ) := by
    classical
    rw [hasseDeriv_apply, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single (n + μ)]
    · rw [if_pos (add_tsub_cancel_right n μ)]
      have h : (μ.prod fun j k ↦ ((n + μ) j).choose k) = μ.prod fun j k ↦ (n j + k).choose k := Finsupp.prod_congr fun j _ ↦ by rw [Finsupp.add_apply]
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
  have degreeOf_hasseDeriv_le (μ : Fin (m + 2) →₀ ℕ) (P : MvPolynomial (Fin (m + 2)) K) (j : Fin (m + 2)) : (MvPolynomial.hasseDeriv μ P).degreeOf j ≤ P.degreeOf j - μ j := by
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
  have hInduction1 (m : ℕ) : rothConst m ≤ 2 * m + 2 := le_of_eq (by rw [rothConst]; ring)
  have hInduction2 (m : ℕ) : 0 ≤ rothConst m := by
    rw [rothConst]
    positivity
  have hInduction3 (m : ℕ) : rothConst (m + 1) = 2 * (m + 2) := by
    rw [rothConst]
    push_cast
    ring
  have hInduction5 {n : ℕ} (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (m + 2)) K)) (j : (Fin (m + 2))) {D : ℕ}
      (h : ∀ i l, (A i l).degreeOf j ≤ D) : (A.det).degreeOf j ≤ n * D := by
    classical
    rw [Matrix.det_apply']
    refine le_trans (degreeOf_sum_le j _ _) (Finset.sup_le fun τ _ ↦ ?_)
    refine le_trans (degreeOf_mul_le j _ _) ?_
    have hsign : ((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin (m + 2)) K).degreeOf j = 0 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs <;> rw [hs] <;> simp
    rw [hsign, zero_add]
    refine le_trans (degreeOf_prod_le j _ _) ?_
    calc ∑ i, (A (τ i) i).degreeOf j ≤ ∑ _i : Fin n, D := Finset.sum_le_sum fun i _ ↦ h _ _
      _ = n * D := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  have hInduction6 (P : MvPolynomial (Fin (m + 2)) K) : P.totalDegree ≤ ∑ j, P.degreeOf j := by
    rw [totalDegree]
    refine Finset.sup_le fun ν hν ↦ ?_
    have hsum : (ν.sum fun _ e ↦ e) = ∑ j, ν j := Finsupp.sum_of_support_subset ν (Finset.subset_univ _) (fun _ e ↦ e) fun _ _ ↦ rfl
    rw [hsum]
    exact Finset.sum_le_sum fun j _ ↦ degreeOf_le_iff.mp (le_refl (P.degreeOf j)) ν hν
  have hInduction7 {n : ℕ} {d : (Fin (m + 2)) → ℕ} {P : MvPolynomial (Fin (m + 2)) K} (hP : P ≠ 0)
      (hdeg : ∀ j, P.degreeOf j ≤ d j) (ρ : Fin n → Fin n → ((Fin (m + 2)) →₀ ℕ)) :
      (Matrix.of fun i j ↦ hasseDeriv (ρ i j) P).det.logHeight
        ≤ (totalWeight K : ℝ) * (Real.log n.factorial + 2 * (∑ j, (d j : ℝ)) * n * Real.log 2)
          + n * P.logHeight := by
    set D : ℕ := ∑ j, d j with hD
    have hdD : P.totalDegree ≤ D := le_trans (hInduction6 P)
      (Finset.sum_le_sum fun j _ ↦ hdeg j)
    have hentrydeg : ∀ i j (l : (Fin (m + 2))), ((Matrix.of fun i j ↦ hasseDeriv (ρ i j) P) i j).degreeOf l ≤ d l := fun i j l ↦ le_trans (le_trans (degreeOf_hasseDeriv_le _ _ _)
          (Nat.sub_le _ _)) (hdeg l)
    have hsupp : ∀ i j, (#((Matrix.of fun i j ↦ hasseDeriv (ρ i j) P) i j).support : ℝ) ≤ (2 : ℝ) ^ D := by
      intro i j
      let Q := ((Matrix.of fun i j ↦ hasseDeriv (ρ i j) P) i j)
      have hsub : Q.support ⊆ Finset.image (boxMonomial d) Finset.univ := fun ν hν ↦ by
        obtain ⟨I, rfl⟩ : ∃ I : ∀ l, Fin (d l + 1), boxMonomial d I = ν := by
          refine ⟨fun l ↦ ⟨ν l, Nat.lt_succ_of_le ?_⟩, ?_⟩
          · exact degreeOf_le_iff.mp (hentrydeg i j l) ν hν
          · ext l; rfl
        exact Finset.mem_image.mpr ⟨I, Finset.mem_univ I, rfl⟩
      have hcardprod : #Q.support ≤ ∏ l, (d l + 1) := by
        refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_image_le ?_)
        rw [Finset.card_univ, Fintype.card_pi]
        simp
      have hcardpow : #Q.support ≤ 2 ^ ∑ l, d l := by
        refine le_trans hcardprod ?_
        rw [← Finset.prod_pow_eq_pow_sum]
        exact Finset.prod_le_prod' fun l _ ↦ Nat.succ_le_of_lt (d l).lt_two_pow_self
      exact_mod_cast hcardpow
    have hB : (1 : ℝ) ≤ (2 : ℝ) ^ D := one_le_pow₀ one_le_two
    have hpowle : (2 : ℝ) ^ P.totalDegree ≤ (2 : ℝ) ^ D := pow_le_pow_right₀ one_le_two hdD
    have hbound := mulHeight_det_le (Matrix.of fun i j ↦ hasseDeriv (ρ i j) P) hP hB hB hsupp
      (fun v _ i j ↦ le_trans (iSup_coeff_hasseDeriv_le v (ρ i j) P)
        (mul_le_mul_of_nonneg_right hpowle ((Real.iSup_nonneg fun ν ↦ (v).nonneg (AddMonoidAlgebra.coeff (P) ν)))))
      (fun v hv i j ↦ iSup_coeff_hasseDeriv_le_of_isNonarchimedean
        (AdmissibleAbsValues.isNonarchimedean v hv) (ρ i j) P)
    have hC : ((n.factorial : ℝ) * ((2 : ℝ) ^ D * (2 : ℝ) ^ D) ^ n)
        = (n.factorial : ℝ) * (2 : ℝ) ^ (2 * D * n) := by
      rw [← pow_add, ← pow_mul]
      ring_nf
    rw [hC] at hbound
    have hlog := Real.log_le_log ((fun p : MvPolynomial _ K ↦ (show 0 < p.mulHeight from Height.mulHeight_pos (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val))) _) hbound
    rw [← MvPolynomial.logHeight,
      Real.log_mul (by positivity) (pow_ne_zero _ ((fun p : MvPolynomial _ K ↦ (show p.mulHeight ≠ 0 from Height.mulHeight_ne_zero (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val))) P)),
      Real.log_pow, Real.log_pow, Real.log_mul (by positivity) (by positivity), Real.log_pow,
      ← MvPolynomial.logHeight] at hlog
    refine le_trans hlog (le_of_eq ?_)
    have hDcast : (D : ℝ) = ∑ j, (d j : ℝ) := by rw [hD]; push_cast; ring
    push_cast
    rw [← hDcast]
  have hweightEq (d : Fin (m + 2) → ℝ) (hd : ∀ j, 0 ≤ d j)
      (α : Fin (m + 2) → K) (Q : MvPolynomial (Fin (m + 2)) K) :
      index d α Q = weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt α Q) := by
    have hw (μ : Fin (m + 2) →₀ ℕ) :
        Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) μ =
          ENNReal.ofReal (μ.sum fun j k ↦ k / d j) := by
      classical
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
        ENNReal.ofReal_sum_of_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (hd j)]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), div_eq_mul_inv]
    refine le_antisymm ?_ ?_
    · refine (Finset.le_inf fun μ hμ ↦ ?_)
      rw [hw]
      have hμcoeff := MvPolynomial.mem_support_iff.mp hμ
      exact iInf_le_of_le μ (iInf_le _ (by rwa [coeff_taylorAt] at hμcoeff))
    · refine le_iInf fun μ ↦ le_iInf fun hμ ↦ ?_
      rw [← hw]
      exact Finset.inf_le (MvPolynomial.mem_support_iff.mpr (by rwa [coeff_taylorAt]))
  have hInduction8 {n : ℕ} (d : (Fin (m + 2)) → ℝ) (hd : ∀ j, 0 ≤ d j) (α : (Fin (m + 2)) → K)
      (A : Matrix (Fin n) (Fin n) (MvPolynomial (Fin (m + 2)) K)) {c : Fin n → ℝ≥0∞}
      (h : ∀ i j, c j ≤ index d α (A i j)) :
      ∑ j, c j ≤ index d α A.det := by
    classical
    have hneg (Q : MvPolynomial (Fin (m + 2)) K) : index d α (-Q) = index d α Q := by
      have h : ∀ Q : MvPolynomial (Fin (m + 2)) K,
          index d α (-Q) ≤ index d α Q := fun Q ↦
        (fun {P : MvPolynomial (Fin (m + 2)) K} {c : ℝ≥0∞}
          (h : ∀ μ : Fin (m + 2) →₀ ℕ, eval α (hasseDeriv μ P) ≠ 0 →
            c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) ↦
          (show c ≤ index d α P from le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ))
          fun μ hμ ↦ (show index d α (-Q) ≤
            ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
            iInf_le_of_le μ (iInf_le _ (by
              rw [map_neg, map_neg]
              exact neg_ne_zero.mpr hμ)))
      refine le_antisymm (h Q) ?_
      have hb := h (-Q)
      rwa [neg_neg] at hb
    have hsum (s : Finset (Equiv.Perm (Fin n)))
        (f : Equiv.Perm (Fin n) → MvPolynomial (Fin (m + 2)) K) {b : ℝ≥0∞}
        (hf : ∀ a ∈ s, b ≤ index d α (f a)) :
        b ≤ index d α (∑ a ∈ s, f a) := by
      induction s using Finset.induction with
      | empty => simp [MvPolynomial.index, le_top]
      | insert a s ha ih =>
          rw [Finset.sum_insert ha]
          refine le_trans (le_min (hf a (Finset.mem_insert_self a s))
            (ih fun b hb ↦ hf b (Finset.mem_insert_of_mem hb)))
            (by rw [hweightEq d hd α, hweightEq d hd α, hweightEq d hd α, map_add]
                exact le_weightedOrder_add _ _ _)
    have hwone (w : Fin (m + 2) → ℝ≥0∞) :
        weightedOrder w (1 : MvPolynomial (Fin (m + 2)) K) = 0 := by
      have h1 : (1 : MvPolynomial (Fin (m + 2)) K) = monomial 0 1 := by
        rw [monomial_zero', C_1]
      rw [h1, (fun {w : _ → ENNReal} {μ} {a} (ha : a ≠ 0) ↦
          (show MvPolynomial.weightedOrder w (MvPolynomial.monomial μ a) = Finsupp.weight w μ from by
            classical
            rw [MvPolynomial.weightedOrder, MvPolynomial.support_monomial, if_neg ha,
              Finset.inf_singleton])) (one_ne_zero (α := K)), map_zero]
    have hprod (s : Finset (Fin n))
        (f : Fin n → MvPolynomial (Fin (m + 2)) K) :
        index d α (∏ a ∈ s, f a) = ∑ a ∈ s, index d α (f a) := by
      induction s using Finset.induction with
      | empty => simp [hweightEq d hd, map_one, hwone]
      | insert a s ha ih =>
          rw [Finset.prod_insert ha, Finset.sum_insert ha]
          rw [show index d α (f a * ∏ b ∈ s, f b) =
              index d α (f a) + index d α (∏ b ∈ s, f b) from by
            rw [hweightEq d hd, hweightEq d hd, hweightEq d hd, map_mul,
              weightedOrder_mul fun _ ↦ ENNReal.ofReal_ne_top], ih]
    rw [Matrix.det_apply']
    refine hsum _ _ fun τ _ ↦ ?_
    have hsign : index d α (((Equiv.Perm.sign τ : ℤ) : MvPolynomial (Fin (m + 2)) K) * ∏ i, A (τ i) i)
        = index d α (∏ i, A (τ i) i) := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with hs | hs
      · rw [hs]
        norm_num
      · rw [hs]
        push_cast
        rw [neg_one_mul, hneg]
    rw [hsign, hprod]
    exact Finset.sum_le_sum fun i _ ↦ h (τ i) i
  have hInduction9 : ∀ {n : ℕ} (D : Fin (n + 1) → ℝ), (∀ j, 0 ≤ D j) →
      (∀ j : Fin n, 2 * D j.castSucc ≤ D j.succ) → ∑ j, D j ≤ 2 * D (Fin.last n) := by
    intro n
    induction n with
    | zero =>
        intro D hnn _
        rw [Fin.sum_univ_one]
        have h0 : (0 : Fin 1) = Fin.last 0 := rfl
        rw [h0]
        linarith [hnn (Fin.last 0)]
    | succ n ih =>
        intro D hnn h
        rw [Fin.sum_univ_castSucc]
        have hIH := ih (fun j ↦ D j.castSucc) (fun j ↦ hnn _)
          (fun j ↦ by rw [← Fin.succ_castSucc]; exact h j.castSucc)
        have hlast := h (Fin.last n)
        rw [Fin.succ_last] at hlast
        linarith [hnn (Fin.last (n + 1))]
  have hInduction10 (n : ℕ) : ∑ i ∈ Finset.range n, (i : ℝ) = n * (n - 1) / 2 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1 : 1 ≤ n := hn
      have h := congrArg (fun k : ℕ ↦ (k : ℝ)) (Finset.sum_range_id_mul_two n)
      push_cast [Nat.cast_sub h1] at h
      linarith
  have hInduction11 {p e n : ℕ} (hn : n ≤ p) {x : ℝ} :
      (n : ℝ) * x - (n : ℝ) * ((n : ℝ) - 1) / 2 / e
        ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
    have hstep : ∑ i ∈ Finset.range n, (x - (i : ℕ) / (e : ℝ))
        ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
      refine le_trans (Finset.sum_le_sum fun i _ ↦ le_max_right 0 _) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun i hi ↦ Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hn))
        fun i _ _ ↦ le_max_left _ _
    refine le_trans (le_of_eq ?_) hstep
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hInduction10]
  have hInduction12 {p e : ℕ} (hp : 0 < p) (hple : p ≤ e + 1) (he : 1 ≤ e) {x : ℝ}
      (hx : 0 ≤ x) :
      (p : ℝ) * min (x / 2) (x ^ 2 / 4)
        ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
    have hep : (0 : ℝ) < e := by exact_mod_cast he
    have hpp : (0 : ℝ) < p := by exact_mod_cast hp
    have hple' : (p : ℝ) ≤ (e : ℝ) + 1 := by exact_mod_cast hple
    have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
    rcases le_or_gt ((p : ℝ) - 1) (x * e) with hcase | hcase
    · refine le_trans (mul_le_mul_of_nonneg_left (min_le_left _ _) hpp.le) ?_
      refine le_trans ?_ (hInduction11 (le_refl p) (e := e) (x := x))
      have hd1 : ((p : ℝ) - 1) / e ≤ x := (div_le_iff₀ hep).mpr hcase
      have hd2 : (p : ℝ) * ((p : ℝ) - 1) / 2 / e = (p : ℝ) * (((p : ℝ) - 1) / e) / 2 := by
        field_simp
      rw [hd2]
      have := mul_le_mul_of_nonneg_left hd1 hpp.le
      linarith
    · set N : ℕ := ⌊x * e⌋₊ with hN
      have hfl : (N : ℝ) ≤ x * e := Nat.floor_le (by positivity)
      have hfl' : x * e < (N : ℝ) + 1 := Nat.lt_floor_add_one _
      have hNp : N + 1 ≤ p := by
        have h1 : (N : ℝ) + 1 < (p : ℝ) := by linarith
        have h2 : N + 1 < p := by exact_mod_cast h1
        omega
      have hkey := hInduction11 (n := N + 1) (e := e) hNp (x := x)
      have hkey' : ((N : ℝ) + 1) * x - ((N : ℝ) + 1) * (N : ℝ) / 2 / e
          ≤ ∑ i ∈ Finset.range p, max 0 (x - (i : ℕ) / (e : ℝ)) := by
        refine le_trans (le_of_eq ?_) hkey
        push_cast
        ring
      refine le_trans (mul_le_mul_of_nonneg_left (min_le_right _ _) hpp.le) (le_trans ?_ hkey')
      have h2e : (p : ℝ) ≤ 2 * e := by linarith
      have hNe : (N : ℝ) / e ≤ x := (div_le_iff₀ hep).mpr hfl
      have hA : ((N : ℝ) + 1) * (N : ℝ) / 2 / e = ((N : ℝ) + 1) * ((N : ℝ) / e) / 2 := by
        field_simp
      have hstep1 : ((N : ℝ) + 1) * x / 2
          ≤ ((N : ℝ) + 1) * x - ((N : ℝ) + 1) * (N : ℝ) / 2 / e := by
        rw [hA]
        have := mul_le_mul_of_nonneg_left hNe (by positivity : (0 : ℝ) ≤ (N : ℝ) + 1)
        linarith
      have hstep2 : x * e * x / 2 ≤ ((N : ℝ) + 1) * x / 2 := by
        have := mul_le_mul_of_nonneg_right hfl'.le hx
        linarith
      have hstep3 : (p : ℝ) * (x ^ 2 / 4) ≤ x * e * x / 2 := by
        nlinarith [mul_le_mul_of_nonneg_right h2e (sq_nonneg x)]
      linarith
  have hInduction13 {mm θ t x s c : ℝ} (hmm : 0 ≤ mm) (hθ0 : 0 < θ) (hθ : θ < 1 / 2)
      (hs : s ≤ θ ^ 2) (hx : x = t - s) (hc : c ≤ 2 * mm + 2)
      (ht : 2 * (mm + 2) * θ < t) (hmin : min (x / 2) (x ^ 2 / 4) ≤ c * θ ^ 2 + s) : False := by
    have hθ2 : θ ^ 2 < θ / 2 := by nlinarith
    have hxlb : (2 * mm + 3.5) * θ < x := by nlinarith
    have hub : c * θ ^ 2 + s ≤ (2 * mm + 3) * θ ^ 2 := by nlinarith
    have hx0 : 0 < x := by nlinarith
    rcases min_cases (x / 2) (x ^ 2 / 4) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hmin
      have hgap : (0 : ℝ) < (2 * mm + 3) * (θ / 2 - θ ^ 2) :=
        mul_pos (by linarith) (by linarith)
      nlinarith [hgap]
    · rw [h] at hmin
      have hpos : (0 : ℝ) < (2 * mm + 3.5) * θ := mul_pos (by linarith) hθ0
      have hsq : ((2 * mm + 3.5) * θ) ^ 2 < x ^ 2 := by
        rw [sq, sq]
        exact mul_self_lt_mul_self hpos.le hxlb
      have hfin : (2 * mm + 3) * θ ^ 2 * 4 ≤ ((2 * mm + 3.5) * θ) ^ 2 := by
        nlinarith [sq_nonneg θ, mul_nonneg (mul_nonneg hmm hmm) (sq_nonneg θ),
          mul_nonneg hmm (sq_nonneg θ)]
      linarith
  have hInduction14 {p : ℕ} {d : Fin (m + 2) → ℕ} {P : MvPolynomial (Fin (m + 2)) K}
      (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j)
      (hdd : ∀ j : Fin (m + 1), 2 * (d j.castSucc : ℝ) ≤ d j.succ)
      (hple : p ≤ d 0 + 1) (ρ : Fin p → Fin p → (Fin (m + 2) →₀ ℕ)) :
      (Matrix.of fun i j ↦ hasseDeriv (ρ i j) P).det.logHeight
        ≤ p * (P.logHeight + 4 * (d (Fin.last (m + 1)) : ℝ) * totalWeight K) := by
    have hmono : Monotone fun j ↦ (d j : ℝ) := Fin.monotone_iff_le_succ.mpr fun j ↦ by
      have h := hdd j
      have h0 : (0 : ℝ) ≤ (d j.castSucc : ℝ) := Nat.cast_nonneg _
      linarith
    set M : ℝ := (d (Fin.last (m + 1)) : ℝ) with hM
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    have hd0M : (d 0 : ℝ) ≤ M := hmono (Fin.zero_le _)
    have hDsum : ∑ j, (d j : ℝ) ≤ 2 * M :=
      hInduction9 _ (fun j ↦ Nat.cast_nonneg _) hdd
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
    have hplereal : (p : ℝ) ≤ M + 1 := by
      have hpd : (p : ℝ) ≤ (d 0 : ℝ) + 1 := by exact_mod_cast hple
      linarith
    have hlogp : Real.log p ≤ M := by
      rcases Nat.eq_zero_or_pos p with rfl | hpp
      · simpa using hM0
      · refine le_trans (Real.log_le_log (by exact_mod_cast hpp) hplereal) ?_
        have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < M + 1 by linarith)
        linarith
    have hfact : Real.log (p.factorial : ℝ) ≤ (p : ℝ) * M := by
      have h1 : ((p.factorial : ℕ) : ℝ) ≤ ((p ^ p : ℕ) : ℝ) := by
        exact_mod_cast Nat.factorial_le_pow p
      refine le_trans (Real.log_le_log (by exact_mod_cast p.factorial_pos) h1) ?_
      rw [Nat.cast_pow, Real.log_pow]
      exact mul_le_mul_of_nonneg_left hlogp hp0
    have hlog2' : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hA : 2 * (∑ j, (d j : ℝ)) * p * Real.log 2 ≤ 4 * M * p * Real.log 2 := by
      nlinarith [hDsum, mul_nonneg hp0 hlog2']
    have hB : 4 * M * p * Real.log 2 ≤ 4 * M * p * 0.6931471808 := by
      nlinarith [Real.log_two_lt_d9, mul_nonneg hM0 hp0]
    have hkey : Real.log (p.factorial : ℝ) + 2 * (∑ j, (d j : ℝ)) * p * Real.log 2
        ≤ 4 * (p : ℝ) * M := by
      nlinarith [hfact, hA, hB, mul_nonneg hp0 hM0]
    have htw : (0 : ℝ) ≤ (totalWeight K : ℝ) := Nat.cast_nonneg _
    refine le_trans (hInduction7 hP hdeg ρ) ?_
    nlinarith [hkey, htw]
  have hInduction15 {σ : Type} (μ : σ →₀ ℕ) {D : σ → ℝ} {e : ℝ}
      (he : 0 < e) (hD : ∀ l, e ≤ D l) :
      (μ.sum fun l k ↦ (k : ℝ) / D l) ≤ ((μ.degree : ℕ) : ℝ) / e := by
    have hDpos : ∀ l, 0 < D l := fun l ↦ lt_of_lt_of_le he (hD l)
    rw [Finsupp.degree_apply, Nat.cast_sum, Finset.sum_div, Finsupp.sum]
    refine Finset.sum_le_sum fun l _ ↦ ?_
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) he (hD l)
  intro θ hθ0 hθ1 d hd1 hratio P hP hdeg ξ hheight
  set s : ℝ := θ ^ 2 ^ (m + 1) with hsdef
  obtain ⟨dr, hdrf⟩ : ∃ dr : Fin (m + 2) → ℝ, dr = fun j ↦ (d j : ℝ) := ⟨_, rfl⟩
  have hdr : ∀ j, dr j = (d j : ℝ) := fun j ↦ by rw [hdrf]
  rw [← hdrf]
  have hdrpos : ∀ j, 0 < dr j := fun j ↦ by
    rw [hdr]
    exact_mod_cast hd1 j
  have hdrnn : ∀ j, 0 ≤ dr j := fun j ↦ (hdrpos j).le
  have hθlt1 : θ < 1 := by
    by_contra hc
    push Not at hc
    exact absurd hθ1 (by nlinarith [one_le_pow₀ hc (n := 2 ^ (m + 1))])
  have hs0 : 0 < s := by
    rw [hsdef]
    positivity
  have hsθ2 : s ≤ θ ^ 2 := by
    rw [hsdef]
    exact pow_le_pow_of_le_one hθ0.le hθlt1.le
      (by simpa using Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show 1 ≤ m + 1 by omega))
  have hshalf : s ≤ 1 / 2 := hθ1
  have hdd : ∀ j : Fin (m + 1), 2 * dr j.castSucc ≤ dr j.succ := by
    intro j
    have h := hratio j
    have h2 : s * dr j.succ ≤ (1 / 2) * dr j.succ :=
      mul_le_mul_of_nonneg_right hshalf (hdrnn _)
    rw [hdr, hdr]
    rw [hdr] at h2
    linarith
  have hTcard : index dr ξ P ≤ ((m + 2 : ℕ) : ℝ≥0∞) := by
    have h := index_le_card hdrpos hP (fun j ↦ by rw [hdr]; exact_mod_cast hdeg j) ξ
    simpa using h
  rcases le_or_gt (1 / 2 : ℝ) θ with hbig | hsmall
  · refine le_trans hTcard ?_
    rw [← ENNReal.ofReal_natCast, hInduction3]
    refine ENNReal.ofReal_le_ofReal ?_
    push_cast
    nlinarith
  by_contra hcon
  push Not at hcon
  have hTne : index dr ξ P ≠ ⊤ := ne_top_of_le_ne_top (by simp) hTcard
  set t : ℝ := (index dr ξ P).toReal with htdef
  have hTeq : index dr ξ P = ENNReal.ofReal t := (ENNReal.ofReal_toReal hTne).symm
  have ht0 : 0 ≤ t := ENNReal.toReal_nonneg
  have htlb : rothConst (m + 1) * θ < t := by
    by_contra hle
    push Not at hle
    have hbad : index dr ξ P ≤ ENNReal.ofReal (rothConst (m + 1) * θ) := by
      rw [hTeq]
      exact ENNReal.ofReal_le_ofReal hle
    exact absurd hbad (not_le.mpr hcon)
  obtain ⟨p, f, g, hp0, hple, hfind, hgind, hdecomp⟩ := exists_tensor_decomposition hP
  obtain ⟨μ, hμord, hWf0⟩ := exists_genWronskian_ne_zero hfind
  obtain ⟨ν, hνord, hWg0⟩ := exists_genWronskian_ne_zero hgind
  set Wf := genWronskian μ f with hWfd
  set Wg := genWronskian ν g with hWgd
  set U := (hasseDerivMatrix μ ν P).det with hUd
  have hple' : p ≤ d 0 + 1 := le_trans hple (Nat.add_le_add_right (hdeg 0) 1)
  have hUeq : U = rename Fin.succ Wf * rename (lastVar (m + 1)) Wg :=
    det_hasseDerivMatrix f g hdecomp μ ν
  have hrenWf0 : rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf ≠ 0 :=
    fun h ↦ hWf0 (rename_injective _ (Fin.succ_injective _) (by rw [h, map_zero]))
  have hrenWg0 : rename (lastVar (m + 1)) Wg ≠ 0 :=
    fun h ↦ hWg0 (rename_injective _ (Function.injective_of_subsingleton (lastVar _)) (by rw [h, map_zero]))
  have hU0 : U ≠ 0 := by
    rw [hUeq]
    exact mul_ne_zero hrenWf0 hrenWg0
  have hdisj : Disjoint (Set.range (Fin.succ : Fin (m + 1) → Fin (m + 2)))
      (Set.range (lastVar (m + 1))) := by
    rw [(show Set.range (lastVar (m + 1)) = {(0 : Fin (m + 2))} from by
      simp [lastVar]), Set.disjoint_singleton_right]
    exact (fun ⟨i, hi⟩ ↦ Fin.succ_ne_zero i hi)
  have hEdeg : ∀ (i j : Fin p) (l : Fin (m + 2)),
      (hasseDerivMatrix μ ν P i j).degreeOf l ≤ d l := fun i j l ↦
    le_trans (le_trans (degreeOf_hasseDeriv_le _ _ _) (Nat.sub_le _ _)) (hdeg l)
  have hUdeg : ∀ l, U.degreeOf l ≤ p * d l := fun l ↦
    hInduction5 _ l fun i j ↦ hEdeg i j l
  have hWfdeg : ∀ j : Fin (m + 1), Wf.degreeOf j ≤ p * d j.succ := by
    intro j
    have h1 : U.degreeOf j.succ = (rename Fin.succ Wf).degreeOf j.succ
        + (rename (lastVar (m + 1)) Wg).degreeOf j.succ := by
      rw [hUeq, degreeOf_mul_eq hrenWf0 hrenWg0]
    have hjlast : j.succ ∉ Set.range (lastVar (m + 1)) := by
      rintro ⟨i, hi⟩
      change (0 : Fin (m + 2)) = j.succ at hi
      exact Fin.succ_ne_zero j hi.symm
    have hdegree : (rename (lastVar (m + 1)) Wg).degreeOf j.succ = 0 := by
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro ν hν
      by_contra hc
      have hs : ¬ ((ν.support : Set (Fin (m + 2))) ⊆
          Set.range (lastVar (m + 1))) := fun hsub ↦
        hjlast (hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by omega))))
      have hz : (rename (lastVar (m + 1)) Wg).coeff ν = 0 := by
        refine coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd (fun t ht ↦ ?_) hs
        rw [← hu] at ht
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp ht))
        exact ⟨a, rfl⟩
      exact absurd hz (mem_support_iff.mp hν)
    rw [hdegree,
      degreeOf_rename_of_injective (Fin.succ_injective _), add_zero] at h1
    rw [← h1]
    exact hUdeg j.succ
  have hWgdeg : Wg.degreeOf default ≤ p * d 0 := by
    have hdf : (default : Fin 1) = 0 := Subsingleton.elim _ _
    have h2 : (rename (lastVar (m + 1)) Wg).degreeOf 0 = Wg.degreeOf 0 :=
      degreeOf_rename_of_injective (Function.injective_of_subsingleton (lastVar (m + 1))) (0 : Fin 1)
    have h1 : U.degreeOf 0 = (rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf).degreeOf 0
        + (rename (lastVar (m + 1)) Wg).degreeOf 0 := by
      rw [hUeq, degreeOf_mul_eq hrenWf0 hrenWg0]
    have hdegree : (rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf).degreeOf 0 = 0 := by
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro ν hν
      by_contra hc
      have hs : ¬ ((ν.support : Set (Fin (m + 2))) ⊆
          Set.range (Fin.succ : Fin (m + 1) → Fin (m + 2))) := fun hsub ↦
        (fun ⟨i, hi⟩ ↦ Fin.succ_ne_zero i hi)
          (hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by omega))))
      have hz : (rename (Fin.succ : Fin (m + 1) → Fin (m + 2)) Wf).coeff ν = 0 := by
        refine coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd (fun t ht ↦ ?_) hs
        rw [← hu] at ht
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp ht))
        exact ⟨a, rfl⟩
      exact absurd hz (mem_support_iff.mp hν)
    rw [hdegree, zero_add, h2] at h1
    rw [hdf, ← h1]
    exact hUdeg 0
  have hdd' : ∀ j : Fin (m + 1), 2 * (d j.castSucc : ℝ) ≤ (d j.succ : ℝ) := fun j ↦ by
    rw [← hdr, ← hdr]
    exact hdd j
  have hUheight : U.logHeight
      ≤ p * (P.logHeight + 4 * (d (Fin.last (m + 1)) : ℝ) * totalWeight K) :=
    hInduction14 hP hdeg hdd' hple'
      (fun i j ↦ (μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1)))
  have hsplit : Wf.logHeight + Wg.logHeight = U.logHeight := by
    have hWfMul : Wf.mulHeight ≠ 0 :=
      Height.mulHeight_ne_zero fun i : (AddMonoidAlgebra.coeff Wf).support ↦
        (AddMonoidAlgebra.coeff Wf) i.val
    have hWgMul : Wg.mulHeight ≠ 0 :=
      Height.mulHeight_ne_zero fun i : (AddMonoidAlgebra.coeff Wg).support ↦
        (AddMonoidAlgebra.coeff Wg) i.val
    calc
      Wf.logHeight + Wg.logHeight = Real.log (Wf.mulHeight * Wg.mulHeight) := by
        rw [MvPolynomial.logHeight, MvPolynomial.logHeight,
          Real.log_mul hWfMul hWgMul]
      _ = U.logHeight := by
        rw [hUeq, MvPolynomial.logHeight,
          MvPolynomial.mulHeight_rename_mul_rename_of_disjoint (Fin.succ_injective _)
            (Function.injective_of_subsingleton (lastVar _)) hdisj hWf0 hWg0]
  have hWfh : Wf.logHeight ≤ U.logHeight := by
    have h := (fun p : MvPolynomial _ K ↦ (show 0 ≤ p.logHeight from Real.log_nonneg (Height.one_le_mulHeight (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val)))) Wg
    linarith [hsplit]
  have hWgh : Wg.logHeight ≤ U.logHeight := by
    have h := (fun p : MvPolynomial _ K ↦ (show 0 ≤ p.logHeight from Real.log_nonneg (Height.one_le_mulHeight (fun i : (AddMonoidAlgebra.coeff p).support ↦ (AddMonoidAlgebra.coeff p) i.val)))) Wf
    linarith [hsplit]
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp0
  have htw : (0 : ℝ) ≤ (totalWeight K : ℝ) := Nat.cast_nonneg _
  have hpow : (θ ^ 2) ^ 2 ^ m = s := by
    rw [hsdef, ← pow_mul, pow_succ]
    ring_nf
  have hmono : Monotone dr := Fin.monotone_iff_le_succ.mpr fun j ↦ by
    have h := hdd j
    have h0 := hdrnn j.castSucc
    linarith
  have hIHf : index (fun j : Fin (m + 1) ↦ ((p * d j.succ : ℕ) : ℝ)) (fun j ↦ ξ j.succ) Wf
      ≤ ENNReal.ofReal (rothConst m * θ ^ 2) := by
    refine ih (θ ^ 2) (by positivity) (by rw [hpow]; exact hθ1) (fun j ↦ p * d j.succ)
      (fun j ↦ Nat.mul_pos hp0 (hd1 j.succ)) (fun j ↦ ?_) Wf hWf0 hWfdeg
      (fun j ↦ ξ j.succ) (fun j ↦ ?_)
    · rw [hpow]
      have h := hratio j.succ
      rw [← Fin.succ_castSucc] at h
      push_cast
      nlinarith [h, hpr]
    · rw [hpow, Fin.succ_last]
      have hh := mul_le_mul_of_nonneg_left (hheight j.succ) hpr.le
      push_cast at hh ⊢
      nlinarith [hWfh, hUheight, hh]
  have hIHg : index (fun _ : Fin 1 ↦ ((p * d 0 : ℕ) : ℝ)) (fun _ ↦ ξ 0) Wg
      ≤ ENNReal.ofReal s := by
    refine index_le_base hWg0 (Nat.mul_pos hp0 (hd1 0)) hWgdeg (fun _ ↦ ξ 0) hs0 ?_
    have hh := mul_le_mul_of_nonneg_left (hheight 0) hpr.le
    have hd0M : (d 0 : ℝ) ≤ (d (Fin.last (m + 1)) : ℝ) := by
      rw [← hdr, ← hdr]
      exact hmono (Fin.zero_le _)
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    push_cast at hh ⊢
    have hWgU : Wg.logHeight ≤ (p : ℝ) * P.logHeight
        + 4 * (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ) := by
      nlinarith [hWgh, hUheight]
    have hA : 4 * ((p : ℝ) * (d 0 : ℝ)) * (totalWeight K : ℝ)
        ≤ 4 * ((p : ℝ) * (d (Fin.last (m + 1)) : ℝ)) * (totalWeight K : ℝ) := by
      have h1 : (0 : ℝ) ≤ 4 * (p : ℝ) * (totalWeight K : ℝ) := by positivity
      nlinarith [hd0M, h1]
    have hB : (8 : ℝ) * (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ)
        ≤ 4 * ((m : ℝ) + 1 + 1) * ((p : ℝ) * (d (Fin.last (m + 1)) : ℝ))
          * (totalWeight K : ℝ) := by
      have h2 : (0 : ℝ) ≤ (p : ℝ) * (d (Fin.last (m + 1)) : ℝ) * (totalWeight K : ℝ) := by
        positivity
      nlinarith [hmm, h2]
    linarith [hWgU, hA, hB, hh]
  have hcastf : (fun j : Fin (m + 1) ↦ ((p * d j.succ : ℕ) : ℝ))
      = fun j : Fin (m + 1) ↦ (p : ℝ) * dr j.succ := by
    funext j
    rw [hdr]
    push_cast
    ring
  have hcastg : (fun _ : Fin 1 ↦ ((p * d 0 : ℕ) : ℝ)) = fun _ : Fin 1 ↦ (p : ℝ) * dr 0 := by
    funext j
    rw [hdr]
    push_cast
    ring
  rw [hcastf] at hIHf
  rw [hcastg] at hIHg
  have hscale : index (fun l ↦ (p : ℝ) * dr l) ξ U =
      ENNReal.ofReal (p : ℝ)⁻¹ * index dr ξ U := by
    have hcd : ∀ l, 0 ≤ (p : ℝ) * dr l := fun l ↦ mul_nonneg hpr.le (hdrnn l)
    have hw : (fun l ↦ ENNReal.ofReal ((p : ℝ) * dr l)⁻¹)
        = fun l ↦ ENNReal.ofReal (p : ℝ)⁻¹ * ENNReal.ofReal (dr l)⁻¹ := by
      funext l
      rw [mul_inv, ENNReal.ofReal_mul (by positivity)]
    rw [hweightEq _ hcd, hweightEq dr hdrnn, hw,
      weightedOrder_const_mul (ENNReal.ofReal_pos.mpr (inv_pos.mpr hpr)).ne' _ _]
  have hIndexRename {σ τ : Type} {e : σ → τ} (he : Function.Injective e)
      (d : τ → ℝ) (α : τ → K) (Q : MvPolynomial σ K) :
      index d α (rename e Q) = index (fun j ↦ d (e j)) (fun j ↦ α (e j)) Q := by
    classical
    have hdegree {j : τ} (hj : j ∉ Set.range e) (P : MvPolynomial σ K) :
        (rename e P).degreeOf j = 0 := by
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro ν hν
      by_contra hc
      have hs : ¬ ((ν.support : Set τ) ⊆ Set.range e) := fun hsub ↦
        hj (hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by omega))))
      have hz : (rename e P).coeff ν = 0 := by
        refine coeff_rename_eq_zero _ _ _ fun u hu ↦ absurd (fun t ht ↦ ?_) hs
        rw [← hu] at ht
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support (Finset.mem_coe.mp ht))
        exact ⟨a, rfl⟩
      exact absurd hz (mem_support_iff.mp hν)
    refine le_antisymm (le_iInf fun μ ↦ le_iInf fun hμ ↦ ?_)
      ((fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {c : ℝ≥0∞}
        (h : ∀ μ : _ →₀ ℕ, eval α (hasseDeriv μ P) ≠ 0 →
          c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) ↦
        (show c ≤ index d α P from le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ)) d
        fun ρ hρ ↦ ?_)
    · refine le_of_le_of_eq
        ((fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {μ : _ →₀ ℕ}
          (h : eval α (hasseDeriv μ P) ≠ 0) ↦
          (show index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
            iInf_le_of_le μ (iInf_le _ h))) d (μ := μ.mapDomain e) ?_)
        (by rw [Finsupp.sum_mapDomain_index_inj he])
      rwa [hasseDeriv_rename he, eval_rename]
    · by_cases hs : (ρ.support : Set τ) ⊆ Set.range e
      · obtain ⟨μ, rfl⟩ : ∃ μ : σ →₀ ℕ, μ.mapDomain e = ρ :=
          ⟨Finsupp.comapDomain e ρ he.injOn,
            Finsupp.mapDomain_comapDomain e he ρ hs⟩
        rw [Finsupp.sum_mapDomain_index_inj he]
        refine (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {μ : _ →₀ ℕ}
          (h : eval α (hasseDeriv μ P) ≠ 0) ↦
          (show index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
            iInf_le_of_le μ (iInf_le _ h))) (fun j ↦ d (e j)) ?_
        rwa [hasseDeriv_rename he, eval_rename] at hρ
      · have hex : ∃ j, ρ j ≠ 0 ∧ j ∉ Set.range e := by
          by_contra h
          refine hs fun j hj ↦ ?_
          by_contra hjr
          exact h ⟨j, Finsupp.mem_support_iff.mp (Finset.mem_coe.mp hj), hjr⟩
        obtain ⟨j, hj, hjr⟩ := hex
        have hz : hasseDeriv ρ (rename e Q) = 0 :=
          hasseDeriv_eq_zero_of_lt (j := j)
            (by simpa [hdegree hjr Q] using Nat.pos_of_ne_zero hj)
        exact absurd (by rw [hz, map_zero]) hρ
  have hUup : index (fun l ↦ (p : ℝ) * dr l) ξ U
      ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := by
    rw [hUeq, show index (fun l ↦ (p : ℝ) * dr l) ξ
        (rename Fin.succ Wf * rename (lastVar (m + 1)) Wg) =
          index (fun l ↦ (p : ℝ) * dr l) ξ (rename Fin.succ Wf) +
            index (fun l ↦ (p : ℝ) * dr l) ξ (rename (lastVar (m + 1)) Wg) from by
      rw [hweightEq _ (fun l ↦ mul_nonneg hpr.le (hdrnn l)),
        hweightEq _ (fun l ↦ mul_nonneg hpr.le (hdrnn l)),
        hweightEq _ (fun l ↦ mul_nonneg hpr.le (hdrnn l)), map_mul,
        weightedOrder_mul fun _ ↦ ENNReal.ofReal_ne_top],
      hIndexRename (Fin.succ_injective _),
      hIndexRename (Function.injective_of_subsingleton (lastVar _)),
      ENNReal.ofReal_add (mul_nonneg (hInduction2 m) (sq_nonneg θ)) hs0.le]
    exact add_le_add hIHf hIHg
  have hdr0succ : dr 0 ≤ s * dr (Fin.succ 0) := by
    have h := hratio 0
    rw [Fin.castSucc_zero] at h
    rw [hdr, hdr]
    exact h
  have hμbound : ∀ i : Fin p, ((μ i).sum fun l k ↦ (k : ℝ) / dr l.succ) ≤ s := by
    intro i
    have hminw : ∀ l : Fin (m + 1), dr (Fin.succ 0) ≤ dr l.succ := fun l ↦
      hmono (Fin.succ_le_succ_iff.mpr (Fin.zero_le l))
    refine le_trans (hInduction15 (μ i) (hdrpos _) hminw) ?_
    rw [div_le_iff₀ (hdrpos _)]
    have h1 : (((μ i).degree : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hμord i
    have hi : ((i : ℕ) : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast i.isLt
    have h2 : (p : ℝ) ≤ dr 0 + 1 := by
      rw [hdr]
      exact_mod_cast hple'
    linarith [hdr0succ]
  have hνbound : ∀ j : Fin p, ((ν j).sum fun _ k ↦ (k : ℝ) / dr 0) ≤ ((j : ℕ) : ℝ) / dr 0 := by
    intro j
    refine le_trans (hInduction15 (ν j) (hdrpos 0) fun _ ↦ le_refl _) ?_
    have h1 : (((ν j).degree : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hνord j
    gcongr
    exact hdrnn 0
  have hweight : ∀ i j : Fin p,
      (((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1))).sum
          fun l k ↦ (k : ℝ) / dr l)
        ≤ s + ((j : ℕ) : ℝ) / dr 0 := by
    intro i j
    rw [Finsupp.sum_add_index' (fun l ↦ by simp) (fun l k₁ k₂ ↦ by push_cast; ring),
      Finsupp.sum_mapDomain_index_inj
        (h := fun (l : Fin (m + 2)) (k : ℕ) ↦ (k : ℝ) / dr l) (Fin.succ_injective _),
      Finsupp.sum_mapDomain_index_inj
        (h := fun (l : Fin (m + 2)) (k : ℕ) ↦ (k : ℝ) / dr l) (Function.injective_of_subsingleton (lastVar _))]
    exact add_le_add (hμbound i) (hνbound j)
  have hentry : ∀ i j : Fin p,
      index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0)
        ≤ index dr ξ (hasseDerivMatrix μ ν P i j) := by
    intro i j
    rw [tsub_le_iff_right]
    change index dr ξ P ≤
      index dr ξ (hasseDeriv ((μ i).mapDomain Fin.succ +
        (ν j).mapDomain (lastVar (m + 1))) P) +
        ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0)
    exact le_trans (index_le_hasseDeriv_add dr hdrnn ξ P
        ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar (m + 1))))
      (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hweight i j)))
  have hlow : ∑ j : Fin p, (index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0))
      ≤ index dr ξ U := by
    rw [hUd]
    exact hInduction8 dr hdrnn ξ _ hentry
  have hSum : ∑ j : Fin p, (index dr ξ P - ENNReal.ofReal (s + ((j : ℕ) : ℝ) / dr 0))
      = ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0)) := by
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ ↦ le_max_left _ _]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hnn : (0 : ℝ) ≤ s + ((j : ℕ) : ℝ) / dr 0 :=
      add_nonneg hs0.le (div_nonneg (Nat.cast_nonneg _) (hdrnn 0))
    have hcg : t - (s + ((j : ℕ) : ℝ) / dr 0) = t - s - ((j : ℕ) : ℝ) / dr 0 := by ring
    rw [hTeq, ← ENNReal.ofReal_sub _ hnn, hcg]
    rcases le_or_gt 0 (t - s - ((j : ℕ) : ℝ) / dr 0) with hge | hlt
    · rw [max_eq_right hge]
    · rw [max_eq_left hlt.le, ENNReal.ofReal_of_nonpos hlt.le, ENNReal.ofReal_zero]
  have hcomb : (p : ℝ)⁻¹ * (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
      ≤ rothConst m * θ ^ 2 + s := by
    have h1 : ENNReal.ofReal ((p : ℝ)⁻¹)
        * ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
        ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := by
      calc ENNReal.ofReal ((p : ℝ)⁻¹)
            * ENNReal.ofReal (∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0))
          ≤ ENNReal.ofReal ((p : ℝ)⁻¹) * index dr ξ U := by
            gcongr
            exact hSum ▸ hlow
        _ = index (fun l ↦ (p : ℝ) * dr l) ξ U :=
            hscale.symm
        _ ≤ ENNReal.ofReal (rothConst m * θ ^ 2 + s) := hUup
    rw [← ENNReal.ofReal_mul (by positivity)] at h1
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp h1
    exact add_nonneg (mul_nonneg (hInduction2 m) (sq_nonneg θ)) hs0.le
  have hrc : rothConst (m + 1) * θ = 2 * ((m : ℝ) + 2) * θ := by
    rw [hInduction3]
  rw [hrc] at htlb
  have hts : (0 : ℝ) ≤ t - s := by
    have h2 : θ ^ 2 < θ := by nlinarith
    have hmm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    nlinarith [htlb, hsθ2, hθ0]
  have hS : (p : ℝ) * min ((t - s) / 2) ((t - s) ^ 2 / 4)
      ≤ ∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0) := by
    have heq : ∑ j : Fin p, max 0 (t - s - ((j : ℕ) : ℝ) / dr 0)
        = ∑ j ∈ Finset.range p, max 0 (t - s - (j : ℝ) / ((d 0 : ℕ) : ℝ)) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j ↦ max 0 (t - s - (j : ℝ) / ((d 0 : ℕ) : ℝ))) p]
      exact Finset.sum_congr rfl fun j _ ↦ by rw [hdr]
    rw [heq]
    exact hInduction12 hp0 hple' (hd1 0) hts
  have hmin : min ((t - s) / 2) ((t - s) ^ 2 / 4) ≤ rothConst m * θ ^ 2 + s := by
    refine le_of_mul_le_mul_left ?_ hpr
    refine le_trans hS ?_
    have h := mul_le_mul_of_nonneg_left hcomb hpr.le
    rw [← mul_assoc, mul_inv_cancel₀ hpr.ne', one_mul] at h
    exact h
  exact hInduction13 (Nat.cast_nonneg m) hθ0 hsmall hsθ2 rfl (hInduction1 m) htlb hmin
set_option maxHeartbeats 2000000 in
theorem index_le_of_degree_ratio {m : ℕ} {d : Fin (m + 1) → ℕ} (hd1 : ∀ j, 1 ≤ d j)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1 / 2)
    (hratio : ∀ j : Fin m, (d j.succ : ℝ) ≤ σ * d j.castSucc)
    {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0) (hdeg : ∀ j, P.degreeOf j ≤ d j)
    (ξ : Fin (m + 1) → K)
    (hheight : ∀ j, P.logHeight + 4 * (m + 1) * d 0 * totalWeight K
        ≤ σ * (d j * logHeight₁ (ξ j))) :
    index (fun j ↦ (d j : ℝ)) ξ P
      ≤ ENNReal.ofReal (2 * ((m : ℝ) + 1) * σ ^ ((1 / 2 : ℝ) ^ m)) := by
  have hInduction4 : RothProp K 0 := by
    let _ : Unique (Fin (0 + 1)) := ⟨⟨0⟩, fun j ↦ Fin.ext (by omega)⟩
    intro θ hθ0 hθ1 d hd1 _ P hP hdeg ξ hheight
    simp only [pow_zero, pow_one] at hθ1 hheight
    have hlast : (Fin.last 0 : Fin (0 + 1)) = default := Fin.ext (by omega)
    have hfun : (fun j : Fin (0 + 1) ↦ (d j : ℝ))
        = fun _ : Fin (0 + 1) ↦ ((d default : ℕ) : ℝ) :=
      funext fun j ↦ by rw [show j = default from Fin.ext (by omega)]
    rw [hfun]
    refine le_trans (index_le_base hP (hd1 default) (hdeg default) ξ hθ0 ?_) ?_
    · have h := hheight default
      rw [hlast] at h; push_cast at h ⊢
      linarith
    · refine ENNReal.ofReal_le_ofReal ?_
      rw [rothConst]
      push_cast
      linarith
  have hInduction16 (m : ℕ) : rothConst m ≤ 2 * ((m : ℝ) + 1) := le_of_eq (by rw [rothConst])
  have hInduction17 (m : ℕ) : RothProp K m := by induction m with
    | zero => exact hInduction4 | succ m ih => exact rothProp_succ ih
  set θ : ℝ := σ ^ ((1 / 2 : ℝ) ^ m) with hθdef
  have hθ0 : 0 < θ := Real.rpow_pos_of_pos hσ0 _
  have hθpow : θ ^ 2 ^ m = σ := by
    rw [hθdef, ← Real.rpow_natCast (σ ^ ((1 / 2 : ℝ) ^ m)) (2 ^ m), ← Real.rpow_mul hσ0.le]
    rw [show ((1 / 2 : ℝ) ^ m) * ((2 ^ m : ℕ) : ℝ) = 1 by
      push_cast
      rw [div_pow, one_pow, div_mul_cancel₀]; positivity]
    exact Real.rpow_one σ
  have hkey := hInduction17 m θ hθ0 (by rw [hθpow]; exact hσ1)
    (fun j ↦ d j.rev) (fun j ↦ hd1 _) (fun j ↦ ?_) (rename Fin.rev P)
    (fun h ↦ hP (rename_injective _ Fin.rev_injective (by rw [h, map_zero]))) (fun j ↦ ?_)
    (fun j ↦ ξ j.rev) (fun j ↦ ?_)
  · have hforward (w : Fin (m + 1) → ℝ) (a : Fin (m + 1) → K) (Q : MvPolynomial (Fin (m + 1)) K) :
        index (fun j ↦ w j.rev) (fun j ↦ a j.rev) (rename Fin.rev Q) ≤ index w a Q := by
      refine le_iInf fun μ ↦ le_iInf fun hμ ↦ ?_
      have hne : eval (fun j ↦ a j.rev) (hasseDeriv (μ.mapDomain Fin.rev) (rename Fin.rev Q)) ≠ 0 := by
        rwa [hasseDeriv_rename Fin.rev_injective, eval_rename,
          show (fun j ↦ a j.rev) ∘ Fin.rev = a from by funext j; simp]
      refine le_of_le_of_eq (iInf_le_of_le (μ.mapDomain Fin.rev) (iInf_le _ hne)) ?_
      congr 1; rw [Finsupp.sum_mapDomain_index_inj Fin.rev_injective]; simp
    have hrev : index (fun j ↦ (d j.rev : ℝ)) (fun j ↦ ξ j.rev) (rename Fin.rev P) = index (fun j ↦ (d j : ℝ)) ξ P := by
      apply le_antisymm
      · exact hforward (fun j : Fin (m + 1) ↦ (d j : ℝ)) ξ P
      · have hback := hforward (fun j : Fin (m + 1) ↦ (d j.rev : ℝ)) (fun j ↦ ξ j.rev) (rename Fin.rev P)
        have hid : (Fin.rev ∘ Fin.rev : Fin (m + 1) → Fin (m + 1)) = id := by funext j; simp
        simpa only [rename_rename, hid, Fin.rev_rev, rename_id_apply] using hback
    rw [hrev] at hkey
    refine le_trans hkey (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hInduction16 m) hθ0.le
  · rw [hθpow]
    have h := hratio j.rev; rwa [← Fin.rev_castSucc, ← Fin.rev_succ] at h
  · have h := hdeg j.rev
    have h2 : (rename Fin.rev P).degreeOf j = P.degreeOf j.rev := by
      have := degreeOf_rename_of_injective (p := P) Fin.rev_injective j.rev
      rwa [Fin.rev_rev] at this
    rw [h2]
    exact h
  · have hren : (rename Fin.rev P).mulHeight = P.mulHeight := by
      let e : Fin (m + 1) → Fin (m + 1) := Fin.rev
      have he : Function.Injective e := Fin.rev_injective
      change (rename e P).mulHeight = P.mulHeight
      have hinj : Function.Injective fun m : (AddMonoidAlgebra.coeff P).support ↦ Finsupp.mapDomain e m.val := fun m n h ↦ Subtype.ext (Finsupp.mapDomain_injective he h)
      have hcov : ∀ d ∈ (AddMonoidAlgebra.coeff (rename e P)).support, d ∈ Set.range fun m : (AddMonoidAlgebra.coeff P).support ↦ Finsupp.mapDomain e m.val := by
        intro d hd
        obtain ⟨u, hu, hu0⟩ := coeff_rename_ne_zero e P d (Finsupp.mem_support_iff.mp hd)
        exact ⟨⟨u, Finsupp.mem_support_iff.mpr hu0⟩, hu⟩
      have hfun : (fun m : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff (rename e P)) (Finsupp.mapDomain e m.val)) = fun m : (AddMonoidAlgebra.coeff P).support ↦ (AddMonoidAlgebra.coeff P) m.val := funext fun m ↦ coeff_rename_mapDomain e he P m.val
      change Finsupp.mulHeight (AddMonoidAlgebra.coeff (rename e P)) = Finsupp.mulHeight (AddMonoidAlgebra.coeff P)
      rw [(open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α) (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
          have hbij : Function.Bijective (fun i : Function.support (fun i ↦ x (f i)) ↦
                (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
            refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
            obtain ⟨i, rfl⟩ := hx a ha
            exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
          rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight, ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
          rfl)))) _ _ hinj hcov, hfun,
        (open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {s : Finset α} (x : α →₀ K) (hx : x.support ⊆ s) => (show x.mulHeight = Height.mulHeight fun i : s ↦ x i.val from ((open scoped Classical NumberField in (open Height Module Matrix Set Finsupp in (fun {K : Type _} [instK : Field K] [instH : Height.AdmissibleAbsValues K] {α : Type _} {ι : Type _} [Finite ι] (x : α →₀ K) (f : ι → α) (hf : Function.Injective f) (hx : ∀ a ∈ x.support, a ∈ Set.range f) => (show x.mulHeight = Height.mulHeight fun i ↦ x (f i) from by
              have hbij : Function.Bijective (fun i : Function.support (fun i ↦ x (f i)) ↦
                    (⟨f i.val, Finsupp.mem_support_iff.mpr i.prop⟩ : x.support)) := by
                refine ⟨fun i j h ↦ Subtype.ext (hf (congrArg Subtype.val h)), fun ⟨a, ha⟩ ↦ ?_⟩
                obtain ⟨i, rfl⟩ := hx a ha
                exact ⟨⟨i, Finsupp.mem_support_iff.mp ha⟩, rfl⟩
              rw [Height.mulHeight_eq_mulHeight_restrict_support fun i ↦ x (f i), Finsupp.mulHeight, ← Height.mulHeight_comp_equiv (Equiv.ofBijective _ hbij)]
              rfl)))) x) Subtype.val Subtype.val_injective fun _ ha ↦ ⟨⟨_, hx ha⟩, rfl⟩)))) (AddMonoidAlgebra.coeff P) (Finset.Subset.refl _)]
    rw [hθpow, Fin.rev_last, show (rename Fin.rev P).logHeight = P.logHeight from congrArg Real.log hren]
    exact hheight j.rev
end MvPolynomial
