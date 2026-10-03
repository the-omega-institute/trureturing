/- GID: D5/S3/Arith/DiophantineApproximation/MvPolynomialEvalBound
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/MvPolynomialEvalBound
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A polynomial evaluation admits a controlled local bound after subtraction. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.BoxMonomial
public import D5.S3.Arith.AbsoluteValues.Heights.GaussLemma
public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Finsupp.Antidiagonal

@[expose] public section

open Nat

open Finset

namespace MvPolynomial

variable {σ : Type*} [Fintype σ] {K : Type*} [Field K]

omit [Fintype σ] in
/-- **A Hasse derivative commutes with a change of coefficient ring.** -/
theorem map_hasseDeriv {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    map f (hasseDeriv μ P) = hasseDeriv μ (map f P) := by
  have hasseDeriv_apply :
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ R),
        MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
          MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m)) ∧
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ S),
        MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
          MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m)) := by
    constructor
    all_goals
      intro μ P
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials σ _).repr P = AddMonoidAlgebra.coeff P from rfl,
        MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff :
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (n : σ →₀ ℕ),
        (MvPolynomial.hasseDeriv μ P).coeff n
          = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ)) ∧
      (∀ (μ : σ →₀ ℕ) (P : MvPolynomial σ S) (n : σ →₀ ℕ),
        (MvPolynomial.hasseDeriv μ P).coeff n
          = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : S) * P.coeff (n + μ)) := by
    constructor
    all_goals
      intro μ P n
      classical
      first
      | rw [hasseDeriv_apply.1, MvPolynomial.coeff_sum]
      | rw [hasseDeriv_apply.2, MvPolynomial.coeff_sum]
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
  ext n
  rw [coeff_map, hasseDeriv_coeff.1, hasseDeriv_coeff.2, coeff_map, map_mul, map_natCast]

/-- **The trivial bound on a value, at an arbitrary absolute value.** -/
theorem apply_eval_le (v : AbsoluteValue K ℝ) {d : σ → ℕ} {P : MvPolynomial σ K}
    (hP : ∀ j, P.degreeOf j ≤ d j) (x : σ → K) :
    v (eval x P) ≤ (∏ j, ((d j : ℝ) + 1)) * (⨆ ν, v (P.coeff ν))
      * ∏ j, max (v (x j)) 1 ^ d j := by
  have apply_term_le {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
      v (P.coeff ν * ∏ j, x j ^ ν j)
        ≤ (⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j := by
    have hle : ∀ j, ν j ≤ d j := fun j ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)
    have hcoeff : v (P.coeff ν) ≤ ⨆ μ, v (P.coeff μ) :=
      le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) ν
    have hprod : (∏ j, v (x j) ^ ν j) ≤ ∏ j, max (v (x j)) 1 ^ d j := by
      refine Finset.prod_le_prod (fun j _ ↦ pow_nonneg (v.nonneg _) _) fun j _ ↦ ?_
      calc v (x j) ^ ν j ≤ max (v (x j)) 1 ^ ν j :=
            pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _
        _ ≤ max (v (x j)) 1 ^ d j := pow_le_pow_right₀ (le_max_right _ _) (hle j)
    rw [map_mul, map_prod]
    simp only [map_pow]
    exact mul_le_mul hcoeff hprod (Finset.prod_nonneg fun j _ ↦ by positivity)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  let nativeSource62 := (open Nat Finset in (fun {σ : Type _} [instSource1 : Fintype σ] {K : Type _} [instSource3 : Field K] {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) => (show #P.support ≤ ∏ j, (d j + 1) from by
    classical
    classical
    have hsub : P.support ⊆ Finset.image (MvPolynomial.boxMonomial d) Finset.univ := fun ν hν ↦ by
      obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = ν := by
        refine ⟨fun j ↦ ⟨ν j, Nat.lt_succ_of_le ?_⟩, ?_⟩
        · exact (degreeOf_le_iff.mp (hP j) ν hν)
        · ext j; rfl
      exact Finset.mem_image_of_mem _ (Finset.mem_univ I)
    calc #P.support ≤ #(Finset.image (MvPolynomial.boxMonomial d) (Finset.univ : Finset (∀ j, Fin (d j + 1)))) :=
          Finset.card_le_card hsub
      _ ≤ #(Finset.univ : Finset (∀ j, Fin (d j + 1))) := Finset.card_image_le
      _ = ∏ j, (d j + 1) := by simp [Fintype.card_pi])))
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Finset.prod_nonneg fun j _ ↦ by positivity)
  rw [eval_eq', mul_assoc]
  calc v (∑ ν ∈ P.support, P.coeff ν * ∏ j, x j ^ ν j)
      ≤ ∑ ν ∈ P.support, v (P.coeff ν * ∏ j, x j ^ ν j) := v.sum_le _ _
    _ ≤ ∑ _ν ∈ P.support, (⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j :=
        Finset.sum_le_sum fun ν hν ↦ apply_term_le hν
    _ = (#P.support : ℝ) * ((⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j, ((d j : ℝ) + 1)) * ((⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j) := by
        refine mul_le_mul_of_nonneg_right ?_ hnn
        calc (#P.support : ℝ) ≤ ((∏ j, (d j + 1) : ℕ) : ℝ) := by
              exact_mod_cast nativeSource62 hP
          _ = ∏ j, ((d j : ℝ) + 1) := by push_cast; ring

/-- **The trivial bound on a value, at a nonarchimedean absolute value**, with no constant. -/
theorem apply_eval_le_of_isNonarchimedean {v : AbsoluteValue K ℝ} (hv : IsNonarchimedean v)
    {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) (x : σ → K) :
    v (eval x P) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j := by
  have apply_term_le {ν : σ →₀ ℕ} (hν : ν ∈ P.support) :
      v (P.coeff ν * ∏ j, x j ^ ν j)
        ≤ (⨆ μ, v (P.coeff μ)) * ∏ j, max (v (x j)) 1 ^ d j := by
    have hle : ∀ j, ν j ≤ d j := fun j ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j)
    have hcoeff : v (P.coeff ν) ≤ ⨆ μ, v (P.coeff μ) :=
      le_ciSup ((by have hFiniteRange := ((AddMonoidAlgebra.coeff P)).finite_range.image (v); rw [← Set.range_comp] at hFiniteRange; exact hFiniteRange.bddAbove)) ν
    have hprod : (∏ j, v (x j) ^ ν j) ≤ ∏ j, max (v (x j)) 1 ^ d j := by
      refine Finset.prod_le_prod (fun j _ ↦ pow_nonneg (v.nonneg _) _) fun j _ ↦ ?_
      calc v (x j) ^ ν j ≤ max (v (x j)) 1 ^ ν j :=
            pow_le_pow_left₀ (v.nonneg _) (le_max_left _ _) _
        _ ≤ max (v (x j)) 1 ^ d j := pow_le_pow_right₀ (le_max_right _ _) (hle j)
    rw [map_mul, map_prod]
    simp only [map_pow]
    exact mul_le_mul hcoeff hprod (Finset.prod_nonneg fun j _ ↦ by positivity)
      (Real.iSup_nonneg fun _ ↦ v.nonneg _)
  have hnn : (0 : ℝ) ≤ (⨆ ν, v (P.coeff ν)) * ∏ j, max (v (x j)) 1 ^ d j :=
    mul_nonneg (Real.iSup_nonneg fun _ ↦ v.nonneg _)
      (Finset.prod_nonneg fun j _ ↦ by positivity)
  rcases eq_or_ne P 0 with rfl | hP0
  · rw [map_zero, AbsoluteValue.map_zero]
    exact hnn
  rw [eval_eq']
  obtain ⟨ν, hν, hle⟩ :=
    hv.finset_image_add_of_nonempty (fun ν ↦ P.coeff ν * ∏ j, x j ^ ν j)
      (support_nonempty.mpr hP0)
  exact le_trans hle (apply_term_le hν)

section Taylor

variable {F : Type*} [Field F]

/-- **The Taylor expansion of `Q` at `a`, with one surviving term chosen.** -/
theorem exists_apply_eval_le_taylor (W : AbsoluteValue F ℝ) {d : σ → ℕ}
    {Q : MvPolynomial σ F} (hQ : ∀ j, Q.degreeOf j ≤ d j) (a b : σ → F)
    (hb : eval b Q ≠ 0) :
    ∃ ν : σ →₀ ℕ, (∀ j, ν j ≤ d j) ∧ eval a (hasseDeriv ν Q) ≠ 0 ∧
      W (eval b Q) ≤ (∏ j, ((d j : ℝ) + 1))
        * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ F) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ F).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have hasseDeriv_monomial (μ m : σ →₀ ℕ) (a : F) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.monomial m a) = MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * a) := by
    classical
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [hasseDeriv_apply]
      simp [MvPolynomial.support_monomial, ha, MvPolynomial.coeff_monomial]
  have add_sub_single_left {n μ : σ →₀ ℕ} {j : σ} (h : n j ≠ 0) :
    n + μ - (Finsupp.single j 1 : σ →₀ ℕ) = n - (Finsupp.single j 1 : σ →₀ ℕ) + μ := by
    ext i
    rcases eq_or_ne i j with rfl | hij
    · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · have h1 : (Finsupp.single j 1 : σ →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
      omega
  have add_sub_single_right {n μ : σ →₀ ℕ} {j : σ} (h : μ j ≠ 0) :
    n + μ - (Finsupp.single j 1 : σ →₀ ℕ) = n + (μ - (Finsupp.single j 1 : σ →₀ ℕ)) := by
    ext i
    rcases eq_or_ne i j with rfl | hij
    · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · have h1 : (Finsupp.single j 1 : σ →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
      omega
  have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ F) (n : σ →₀ ℕ) :
    (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : F) * P.coeff (n + μ) := by
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
  have choose_pascal_aux  {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a + b).choose b = (a - 1 + b).choose b + (a + (b - 1)).choose (b - 1) := by
    obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    rw [show a + 1 + (b + 1) = a + b + 1 + 1 by ring, Nat.choose_succ_succ,
      show a + (b + 1) = a + b + 1 by ring, show a + 1 + b = a + b + 1 by ring]
    exact add_comm _ _
  have prod_choose_pascal {μ n : σ →₀ ℕ} {j : σ} (hn : n j ≠ 0) (hμ : μ j ≠ 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
        + ((μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k) := by
    classical
    have hjs : j ∈ μ.support := Finsupp.mem_support_iff.mpr hμ
    have hA : (μ.prod fun i k ↦ (n i + k).choose k)
        = (n j + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) :=
      (Finset.mul_prod_erase _ _ hjs).symm
    have hB : (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
        = (n j - 1 + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) := by
      have h0 : (μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k)
          = ((n - (Finsupp.single j 1 : σ →₀ ℕ)) j + μ j).choose (μ j)
            * ∏ i ∈ μ.support.erase j,
                ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + μ i).choose (μ i) :=
        (Finset.mul_prod_erase _ _ hjs).symm
      rw [h0, Finsupp.tsub_apply, Finsupp.single_eq_same]
      congr 1
      exact Finset.prod_congr rfl fun i hi ↦ by
        rw [(fun (n : σ →₀ ℕ) {j i : σ} (h : i ≠ j) ↦
        (show (n - (Finsupp.single j 1 : σ →₀ ℕ)) i = n i from by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, Nat.sub_zero])) n (Finset.ne_of_mem_erase hi)]
    have hsub : (μ - (Finsupp.single j 1 : σ →₀ ℕ)).support ⊆ μ.support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [Finsupp.tsub_apply] at hi
      omega
    have hC : ((μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k)
        = (n j + (μ j - 1)).choose (μ j - 1)
          * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) := by
      rw [Finsupp.prod_of_support_subset _ hsub _ (by simp),
        ← Finset.mul_prod_erase _ _ hjs, Finsupp.tsub_apply, Finsupp.single_eq_same]
      congr 1
      exact Finset.prod_congr rfl fun i hi ↦ by
        rw [(fun (n : σ →₀ ℕ) {j i : σ} (h : i ≠ j) ↦
        (show (n - (Finsupp.single j 1 : σ →₀ ℕ)) i = n i from by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, Nat.sub_zero])) μ (Finset.ne_of_mem_erase hi)]
    rw [hA, hB, hC, ← add_mul, choose_pascal_aux hn hμ]
  have prod_choose_sub_single_left {μ n : σ →₀ ℕ} {j : σ} (hm : μ j = 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = μ.prod fun i k ↦ ((n - (Finsupp.single j 1 : σ →₀ ℕ)) i + k).choose k := by
    apply Finsupp.prod_congr
    intro i hi
    have hij : i ≠ j := by
        rintro rfl
        exact (Finsupp.mem_support_iff.mp hi) hm
    rw [(fun (n : σ →₀ ℕ) {j i : σ} (h : i ≠ j) ↦
      (show (n - (Finsupp.single j 1 : σ →₀ ℕ)) i = n i from by
      rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, Nat.sub_zero])) n hij]
  have prod_choose_sub_single_right {μ n : σ →₀ ℕ} {j : σ} (hn : n j = 0) (hμ : μ j ≠ 0) :
    (μ.prod fun i k ↦ (n i + k).choose k)
      = (μ - (Finsupp.single j 1 : σ →₀ ℕ)).prod fun i k ↦ (n i + k).choose k := by
    classical
    have hjs : j ∈ μ.support := Finsupp.mem_support_iff.mpr hμ
    have hsub : (μ - (Finsupp.single j 1 : σ →₀ ℕ)).support ⊆ μ.support := by
      intro i hi
      rw [Finsupp.mem_support_iff] at hi ⊢
      rw [Finsupp.tsub_apply] at hi
      omega
    rw [Finsupp.prod_of_support_subset _ hsub _ (by simp),
      show (μ.prod fun i k ↦ (n i + k).choose k)
        = (n j + μ j).choose (μ j) * ∏ i ∈ μ.support.erase j, (n i + μ i).choose (μ i) from
        (Finset.mul_prod_erase _ _ hjs).symm,
      ← Finset.mul_prod_erase _ _ hjs, Finsupp.tsub_apply, Finsupp.single_eq_same, hn]
    congr 1
    · rw [Nat.zero_add, Nat.zero_add, Nat.choose_self, Nat.choose_self]
    · exact Finset.prod_congr rfl fun i hi ↦ by
        rw [(fun (n : σ →₀ ℕ) {j i : σ} (h : i ≠ j) ↦
        (show (n - (Finsupp.single j 1 : σ →₀ ℕ)) i = n i from by
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne h, Nat.sub_zero])) μ (Finset.ne_of_mem_erase hi)]
  have hasseDeriv_mul_X (μ : σ →₀ ℕ) (P : MvPolynomial σ F) (j : σ) :
    MvPolynomial.hasseDeriv μ (P * MvPolynomial.X j)
      = MvPolynomial.hasseDeriv μ P * MvPolynomial.X j
        + if μ j = 0 then 0 else MvPolynomial.hasseDeriv (μ - (Finsupp.single j 1 : σ →₀ ℕ)) P := by
    classical
    by_cases hm : μ j = 0
    · rw [if_pos hm, add_zero]
      apply MvPolynomial.ext; intro n
      rw [hasseDeriv_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X']
      by_cases hn : n j = 0
      · have h1 : j ∉ (n + μ).support := by
          simp [Finsupp.mem_support_iff, Finsupp.add_apply, hn, hm]
        rw [if_neg h1, if_neg (by simpa using hn), mul_zero]
      · have h1 : j ∈ (n + μ).support := by
          rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega
        rw [if_pos h1, if_pos (by simpa using hn), hasseDeriv_coeff,
          add_sub_single_left hn, prod_choose_sub_single_left (n := n) hm]
    · rw [if_neg hm]
      apply MvPolynomial.ext; intro n
      have h1 : j ∈ (n + μ).support := by
        rw [Finsupp.mem_support_iff, Finsupp.add_apply]; omega
      rw [MvPolynomial.coeff_add, hasseDeriv_coeff, MvPolynomial.coeff_mul_X', MvPolynomial.coeff_mul_X', if_pos h1]
      by_cases hn : n j = 0
      · rw [if_neg (by simpa using hn), zero_add, hasseDeriv_coeff,
          add_sub_single_right hm, prod_choose_sub_single_right hn hm]
      · rw [if_pos (by simpa using hn), hasseDeriv_coeff, hasseDeriv_coeff,
          prod_choose_pascal hn hm, Nat.cast_add, add_mul]
        congr 1
        · rw [add_sub_single_left hn]
        · rw [add_sub_single_right hm]
  have coeff_taylor (P : MvPolynomial σ F) (μ : σ →₀ ℕ) :
    (MvPolynomial.aeval (fun j ↦ MvPolynomial.C (MvPolynomial.X j) + MvPolynomial.X j) P : MvPolynomial σ (MvPolynomial σ F)).coeff μ
      = MvPolynomial.hasseDeriv μ P := by
    classical
    induction P using MvPolynomial.induction_on generalizing μ with
    | C a =>
        rw [MvPolynomial.aeval_C, show algebraMap F (MvPolynomial σ (MvPolynomial σ F)) a = MvPolynomial.C (MvPolynomial.C a) from rfl,
          MvPolynomial.coeff_C, ← MvPolynomial.monomial_zero', hasseDeriv_monomial]
        by_cases h : μ = 0
        · subst h; simp [hasseDeriv_monomial]
        · rw [if_neg (fun hz ↦ h hz.symm),
            prod_choose_eq_zero (m := 0) (by simpa using h),
            Nat.cast_zero, zero_mul, MvPolynomial.monomial_zero]
    | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, hp, hq, map_add]
    | mul_X p j hp =>
        rw [map_mul, MvPolynomial.aeval_X, mul_add, MvPolynomial.coeff_add, mul_comm (MvPolynomial.aeval _ p) (MvPolynomial.C (MvPolynomial.X j)),
          MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X', hp, hasseDeriv_mul_X, mul_comm (MvPolynomial.X j) (MvPolynomial.hasseDeriv μ p)]
        congr 1
        by_cases h : μ j = 0
        · rw [if_neg (by simpa using h), if_pos h]
        · rw [if_pos (Finsupp.mem_support_iff.mpr h), if_neg h, hp]
  have eval_add_eq_sum_hasseDeriv (P : MvPolynomial σ F) (x y : σ → F)
    {s : Finset (σ →₀ ℕ)} (hs : ∀ μ, MvPolynomial.hasseDeriv μ P ≠ 0 → μ ∈ s) :
    MvPolynomial.eval (x + y) P = ∑ μ ∈ s, MvPolynomial.eval x (MvPolynomial.hasseDeriv μ P) * μ.prod fun j k ↦ y j ^ k := by
    classical
    have hev : ∀ Q : MvPolynomial σ F,
        MvPolynomial.eval₂ (MvPolynomial.eval x) y (MvPolynomial.aeval (fun j ↦ MvPolynomial.C (MvPolynomial.X j) + MvPolynomial.X j) Q : MvPolynomial σ (MvPolynomial σ F))
          = MvPolynomial.eval (x + y) Q := by
      intro Q
      induction Q using MvPolynomial.induction_on with
      | C a => simp
      | add p q hp hq => rw [map_add, MvPolynomial.eval₂_add, hp, hq, map_add]
      | mul_X p j hp =>
          rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.eval₂_mul, hp, map_mul, MvPolynomial.eval_X]
          simp [Pi.add_apply]
    have hsub : (MvPolynomial.aeval (fun j ↦ MvPolynomial.C (MvPolynomial.X j) + MvPolynomial.X j) P :
        MvPolynomial σ (MvPolynomial σ F)).support ⊆ s := fun μ hμ ↦
      hs μ (by rw [← coeff_taylor]; exact mem_support_iff.mp hμ)
    rw [← hev P, MvPolynomial.eval₂_eq]
    refine Eq.trans (Finset.sum_subset hsub fun μ _ hμ ↦ ?_) (Finset.sum_congr rfl fun μ _ ↦ ?_)
    · rw [notMem_support_iff.mp hμ, map_zero, zero_mul]
    · rw [coeff_taylor]
      rfl
  classical
  set s : Finset (σ →₀ ℕ) := Finset.image (boxMonomial d) Finset.univ with hsdef
  have hmem : ∀ μ : σ →₀ ℕ, hasseDeriv μ Q ≠ 0 → μ ∈ s := by
    intro μ hμ
    have hle : ∀ j, μ j ≤ d j := fun j ↦ by
      by_contra hlt
      exact hμ (hasseDeriv_eq_zero_of_lt (lt_of_le_of_lt (hQ j) (not_le.mp hlt)))
    obtain ⟨I, rfl⟩ : ∃ I : ∀ j, Fin (d j + 1), boxMonomial d I = μ := by
      refine ⟨fun j ↦ ⟨μ j, Nat.lt_succ_of_le (hle j)⟩, ?_⟩
      ext j
      rfl
    exact Finset.mem_image_of_mem _ (Finset.mem_univ I)
  have hbox : ∀ μ ∈ s, ∀ j, μ j ≤ d j := by
    intro μ hμ j
    obtain ⟨I, _, rfl⟩ := Finset.mem_image.mp hμ
    exact (fun d (I : ∀ j, Fin (d j + 1)) j ↦
      (show MvPolynomial.boxMonomial d I j ≤ d j from by
        simpa [MvPolynomial.boxMonomial] using Nat.lt_succ_iff.mp (I j).isLt)) d I j
  have hexp : eval b Q = ∑ μ ∈ s, eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j := by
    have hab : a + (b - a) = b := by
      funext j
      simp only [hasseDeriv_monomial, Pi.add_apply, Pi.sub_apply]
      ring
    have := eval_add_eq_sum_hasseDeriv Q a (b - a) hmem
    rw [hab] at this
    rw [this]
    refine Finset.sum_congr rfl fun μ _ ↦ ?_
    congr 1
    exact Finsupp.prod_of_support_subset μ (Finset.subset_univ _) _ fun j _ ↦ pow_zero _
  set s' : Finset (σ →₀ ℕ) := s.filter fun μ ↦ eval a (hasseDeriv μ Q) ≠ 0 with hs'def
  have hexp' : eval b Q = ∑ μ ∈ s', eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j := by
    rw [hexp]
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun μ hμ hμ' ↦ ?_).symm
    simp only [hasseDeriv_monomial, Finset.mem_filter, not_and, not_not] at hμ'
    rw [hμ' hμ, zero_mul]
  have hne : s'.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro h
    rw [h, Finset.sum_empty] at hexp'
    exact hb hexp'
  obtain ⟨ν, hν, hmax⟩ := s'.exists_max_image
    (fun μ ↦ W (eval a (hasseDeriv μ Q)) * ∏ j, W (b j - a j) ^ μ j) hne
  have hνs : ν ∈ s := Finset.mem_of_mem_filter _ hν
  have hνne : eval a (hasseDeriv ν Q) ≠ 0 := (Finset.mem_filter.mp hν).2
  refine ⟨ν, hbox ν hνs, hνne, ?_⟩
  have hnn : (0 : ℝ) ≤ W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j :=
    mul_nonneg (W.nonneg _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (W.nonneg _) _)
  calc W (eval b Q)
      = W (∑ μ ∈ s', eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j) := by rw [← hexp']
    _ ≤ ∑ μ ∈ s', W (eval a (hasseDeriv μ Q) * ∏ j, (b j - a j) ^ μ j) := W.sum_le _ _
    _ ≤ ∑ _μ ∈ s', W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j := by
        refine Finset.sum_le_sum fun μ hμ ↦ ?_
        rw [map_mul, map_prod]
        simp only [hasseDeriv_monomial, map_pow]
        exact hmax μ hμ
    _ = (#s' : ℝ) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (∏ j, ((d j : ℝ) + 1)) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j) := by
        refine mul_le_mul_of_nonneg_right ?_ hnn
        have h1 : #s' ≤ ∏ j, (d j + 1) := by
          calc #s' ≤ #s := Finset.card_filter_le _ _
            _ ≤ #(Finset.univ : Finset (∀ j, Fin (d j + 1))) := Finset.card_image_le
            _ = ∏ j, (d j + 1) := by simp [hasseDeriv_monomial, Fintype.card_pi]
        calc (#s' : ℝ) ≤ ((∏ j, (d j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
          _ = ∏ j, ((d j : ℝ) + 1) := by push_cast; ring

/-- **The value of a Hasse derivative**, in terms of the local factor of `Q`. -/
theorem apply_eval_hasseDeriv_le (W : AbsoluteValue F ℝ) {d : σ → ℕ} {Q : MvPolynomial σ F}
    (hQ : ∀ j, Q.degreeOf j ≤ d j) (a : σ → F) (ν : σ →₀ ℕ) :
    W (eval a (hasseDeriv ν Q))
      ≤ (∏ j, ((d j : ℝ) + 1)) * (2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ))
        * ∏ j, max (W (a j)) 1 ^ d j := by
  let nativeSource72 := (open Nat Finset in (fun {σ : Type _} [instSource1 : Fintype σ] {K : Type _} [instSource3 : Field K] {d : σ → ℕ} {P : MvPolynomial σ K} (hP : ∀ j, P.degreeOf j ≤ d j) => (show P.totalDegree ≤ ∑ j, d j from by
    classical
    refine Finset.sup_le fun ν hν ↦ ?_
    rw [Finsupp.sum_fintype _ _ fun _ ↦ rfl]
    exact Finset.sum_le_sum fun j _ ↦ le_trans (degreeOf_le_iff.mp le_rfl ν hν) (hP j))))
  have prod_choose_le_two_pow (μ m : σ →₀ ℕ) :
    (μ.prod fun j k ↦ (m j).choose k) ≤ 2 ^ (m.sum fun _ k ↦ k) := by
    classical
    calc (μ.prod fun j k ↦ (m j).choose k) ≤ ∏ j ∈ μ.support, 2 ^ m j :=
          Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
            (fun j _ ↦ Nat.choose_le_two_pow (m j) (μ j))
      _ = 2 ^ ∑ j ∈ μ.support, m j := Finset.prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ ∑ j ∈ μ.support ∪ m.support, m j :=
          Nat.pow_le_pow_right (by norm_num)
            (Finset.sum_le_sum_of_subset Finset.subset_union_left)
      _ = 2 ^ (m.sum fun _ k ↦ k) := by
          rw [Finsupp.sum]
          congr 1
          exact (Finset.sum_subset Finset.subset_union_right fun j _ hj ↦
            Finsupp.notMem_support_iff.mp hj).symm
  have iSup_coeff_hasseDeriv_le (v : AbsoluteValue F ℝ) (μ : σ →₀ ℕ) (P : MvPolynomial σ F) :
    (⨆ n : σ →₀ ℕ, v ((MvPolynomial.hasseDeriv μ P).coeff n))
      ≤ 2 ^ P.totalDegree * ⨆ n : σ →₀ ℕ, v (P.coeff n) := by
    have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ F) :
      MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
        MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
      rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
      rw [show (MvPolynomial.basisMonomials σ F).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
      exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
    have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
      (μ.prod fun j k ↦ (m j).choose k) = 0 := by
      rw [Finsupp.le_def] at h
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
        (Nat.choose_eq_zero_of_lt hj)
    have MvPolynomial.hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ F) (n : σ →₀ ℕ) :
      (MvPolynomial.hasseDeriv μ P).coeff n
        = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : F) * P.coeff (n + μ) := by
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
    have hnn : (0 : ℝ) ≤ ⨆ n : σ →₀ ℕ, v (P.coeff n) := Real.iSup_nonneg fun _ ↦ v.nonneg _
    refine Real.iSup_le (fun n ↦ ?_) (by positivity)
    rw [MvPolynomial.hasseDeriv_coeff, map_mul]
    rcases eq_or_ne (P.coeff (n + μ)) 0 with h | h
    · rw [h, map_zero, mul_zero]
      positivity
    · have hc : v ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : F) ≤ 2 ^ P.totalDegree := by
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
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ F) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ F).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ F) (n : σ →₀ ℕ) :
    (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : F) * P.coeff (n + μ) := by
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
  have degreeOf_hasseDeriv_le (μ : σ →₀ ℕ) (P : MvPolynomial σ F) (j : σ) :
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
  have hdeg : ∀ j, (hasseDeriv ν Q).degreeOf j ≤ d j := fun j ↦
    le_trans (le_trans (degreeOf_hasseDeriv_le ν Q j) (Nat.sub_le _ _)) (hQ j)
  refine le_trans (apply_eval_le W hdeg a) ?_
  have hstep : (⨆ μ, W ((hasseDeriv ν Q).coeff μ)) ≤ 2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ) := by
    refine le_trans (iSup_coeff_hasseDeriv_le W ν Q) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.iSup_nonneg fun _ ↦ W.nonneg _)
    exact pow_le_pow_right₀ one_le_two (nativeSource72 hQ)
  have hM : (0 : ℝ) ≤ ∏ j, ((d j : ℝ) + 1) := Finset.prod_nonneg fun j _ ↦ by positivity
  have hP : (0 : ℝ) ≤ ∏ j, max (W (a j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hstep hM) hP

/-- **Splitting the distances into a truncated part and a bounded part.** -/
theorem prod_apply_sub_le (W : AbsoluteValue F ℝ) {d : σ → ℕ} {ν : σ →₀ ℕ}
    (hν : ∀ j, ν j ≤ d j) (a b : σ → F) :
    (∏ j, W (b j - a j) ^ ν j)
      ≤ 2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j) * (∏ j, max (W (b j)) 1 ^ d j)
        * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
  have key : ∀ j, W (b j - a j) ^ ν j
      ≤ 2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
        * min 1 (W (b j - a j)) ^ ν j := by
    intro j
    have ha1 : (1 : ℝ) ≤ max (W (a j)) 1 := le_max_right _ _
    have hb1 : (1 : ℝ) ≤ max (W (b j)) 1 := le_max_right _ _
    have hsplit : W (b j - a j) = min 1 (W (b j - a j)) * max (W (b j - a j)) 1 := by
      rw [max_comm, min_mul_max, one_mul]
    have htri : W (b j - a j) ≤ W (b j) + W (a j) := by
      simpa using W.sub_le (b j) 0 (a j)
    have h2 : max (W (b j - a j)) 1 ≤ 2 * max (W (a j)) 1 * max (W (b j)) 1 := by
      refine max_le (le_trans htri ?_) ?_
      · calc W (b j) + W (a j) ≤ max (W (b j)) 1 + max (W (a j)) 1 := by
              gcongr <;> exact le_max_left _ _
          _ ≤ 2 * max (W (a j)) 1 * max (W (b j)) 1 := by nlinarith
      · nlinarith
    have hmin0 : (0 : ℝ) ≤ min 1 (W (b j - a j)) := le_min zero_le_one (W.nonneg _)
    have hpow : W (b j - a j) ^ ν j
        = min 1 (W (b j - a j)) ^ ν j * max (W (b j - a j)) 1 ^ ν j := by
      rw [← mul_pow, ← hsplit]
    calc W (b j - a j) ^ ν j
        = min 1 (W (b j - a j)) ^ ν j * max (W (b j - a j)) 1 ^ ν j := hpow
      _ ≤ min 1 (W (b j - a j)) ^ ν j * (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ d j := by
          refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hmin0 _)
          calc max (W (b j - a j)) 1 ^ ν j
              ≤ (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ ν j :=
                pow_le_pow_left₀ (le_trans zero_le_one (le_max_right _ _)) h2 _
            _ ≤ (2 * max (W (a j)) 1 * max (W (b j)) 1) ^ d j :=
                pow_le_pow_right₀ (by nlinarith) (hν j)
      _ = 2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
            * min 1 (W (b j - a j)) ^ ν j := by
          rw [mul_pow, mul_pow]
          ring
  calc (∏ j, W (b j - a j) ^ ν j)
      ≤ ∏ j, (2 ^ d j * max (W (a j)) 1 ^ d j * max (W (b j)) 1 ^ d j
          * min 1 (W (b j - a j)) ^ ν j) :=
        Finset.prod_le_prod (fun j _ ↦ pow_nonneg (W.nonneg _) _) fun j _ ↦ key j
    _ = 2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j) * (∏ j, max (W (b j)) 1 ^ d j)
          * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
          Finset.prod_pow_eq_pow_sum]

/-- **The local bound at a place carrying a target.** -/
theorem exists_apply_eval_le_of_sub (W : AbsoluteValue F ℝ) {d : σ → ℕ} {Q : MvPolynomial σ F}
    (hQ : ∀ j, Q.degreeOf j ≤ d j) (a b : σ → F) (hb : eval b Q ≠ 0) :
    ∃ ν : σ →₀ ℕ, (∀ j, ν j ≤ d j) ∧ eval a (hasseDeriv ν Q) ≠ 0 ∧
      W (eval b Q) ≤ (∏ j, ((d j : ℝ) + 1)) ^ 2 * 4 ^ (∑ j, d j) * (⨆ μ, W (Q.coeff μ))
        * (∏ j, max (W (a j)) 1 ^ d j) ^ 2 * (∏ j, max (W (b j)) 1 ^ d j)
        * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
  obtain ⟨ν, hν, hνne, hbound⟩ := exists_apply_eval_le_taylor W hQ a b hb
  refine ⟨ν, hν, hνne, le_trans hbound ?_⟩
  have hM : (0 : ℝ) ≤ ∏ j, ((d j : ℝ) + 1) := Finset.prod_nonneg fun j _ ↦ by positivity
  have hPa : (0 : ℝ) ≤ ∏ j, max (W (a j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have hPb : (0 : ℝ) ≤ ∏ j, max (W (b j)) 1 ^ d j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_trans zero_le_one (le_max_right _ _)) _
  have hPm : (0 : ℝ) ≤ ∏ j, min 1 (W (b j - a j)) ^ ν j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (le_min zero_le_one (W.nonneg _)) _
  have hQn : (0 : ℝ) ≤ ⨆ μ, W (Q.coeff μ) := Real.iSup_nonneg fun _ ↦ W.nonneg _
  have h1 := apply_eval_hasseDeriv_le W hQ a ν
  have h2 := prod_apply_sub_le W hν a b
  have hfour : (4 : ℝ) ^ (∑ j, d j) = 2 ^ (∑ j, d j) * 2 ^ (∑ j, d j) := by
    rw [← mul_pow]; norm_num
  calc (∏ j, ((d j : ℝ) + 1)) * (W (eval a (hasseDeriv ν Q)) * ∏ j, W (b j - a j) ^ ν j)
      ≤ (∏ j, ((d j : ℝ) + 1))
          * (((∏ j, ((d j : ℝ) + 1)) * (2 ^ (∑ j, d j) * ⨆ μ, W (Q.coeff μ))
              * ∏ j, max (W (a j)) 1 ^ d j)
            * (2 ^ (∑ j, d j) * (∏ j, max (W (a j)) 1 ^ d j)
              * (∏ j, max (W (b j)) 1 ^ d j) * ∏ j, min 1 (W (b j - a j)) ^ ν j)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 ?_ ?_) hM
        · exact Finset.prod_nonneg fun j _ ↦ pow_nonneg (W.nonneg _) _
        · positivity
    _ = (∏ j, ((d j : ℝ) + 1)) ^ 2 * 4 ^ (∑ j, d j) * (⨆ μ, W (Q.coeff μ))
          * (∏ j, max (W (a j)) 1 ^ d j) ^ 2 * (∏ j, max (W (b j)) 1 ^ d j)
          * ∏ j, min 1 (W (b j - a j)) ^ ν j := by
        rw [hfour]; ring

end Taylor

end MvPolynomial

end
