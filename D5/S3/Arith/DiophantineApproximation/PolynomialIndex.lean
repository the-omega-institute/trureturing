/- GID: D5/S3/Arith/DiophantineApproximation/PolynomialIndex
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/PolynomialIndex
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Hasse derivative lowers a polynomial's weighted index by at most its derivative weight. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.MvHasseDeriv
public import Mathlib.Data.Finsupp.Antidiagonal
public import D5.S3.Arith.DiophantineApproximation.WeightedOrder
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.ENNReal.Real
import Mathlib.Data.ZMod.Basic

-- Used only by the acceptance criteria.

@[expose] public section

open Nat

noncomputable section

open scoped ENNReal

namespace MvPolynomial

variable {σ R : Type*} [CommRing R]

/-- **Translation**: `taylorAt α P` is `P (X + α)`, the several-variable `Polynomial.taylor`. -/
def taylorAt (α : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun j ↦ X j + C (α j)

/-- **The coefficients of the translate are the Hasse derivatives at the point.** This one
identity is the whole of Layer 2.3. -/
theorem coeff_taylorAt (α : σ → R) (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (taylorAt α P).coeff μ = eval α (hasseDeriv μ P) := by
  let nativeSource67 := (open Nat in (open scoped ENNReal in (fun {σ : Type _} {R : Type _} [instSource1 : CommRing R] (α : σ → R) (P : MvPolynomial σ R) => (show MvPolynomial.map (MvPolynomial.eval α) (MvPolynomial.aeval (fun j ↦ C (X j) + X j) P : MvPolynomial σ (MvPolynomial σ R))
        = MvPolynomial.taylorAt α P from by
    classical
    induction P using MvPolynomial.induction_on with
    | C a =>
        rw [MvPolynomial.aeval_C, show Algebra.algebraMap R (MvPolynomial σ (MvPolynomial σ R)) a = C (C a) from rfl,
          MvPolynomial.map_C, MvPolynomial.eval_C, (fun α a ↦ (show MvPolynomial.taylorAt α (C a) = C a from MvPolynomial.aeval_C _ _))]
    | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
    | mul_X p j hp =>
        simp only [map_mul, MvPolynomial.aeval_X, (fun α j ↦ (show MvPolynomial.taylorAt α (X j) = X j + C (α j) from MvPolynomial.aeval_X _ _)), map_add, MvPolynomial.map_C, MvPolynomial.eval_X, MvPolynomial.map_X, hp]
        ring))))
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ R).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have hasseDeriv_monomial (μ m : σ →₀ ℕ) (a : R) :
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
  have hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ) := by
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
  have hasseDeriv_mul_X (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (j : σ) :
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
  have coeff_taylor (P : MvPolynomial σ R) (μ : σ →₀ ℕ) :
    (MvPolynomial.aeval (fun j ↦ MvPolynomial.C (MvPolynomial.X j) + MvPolynomial.X j) P : MvPolynomial σ (MvPolynomial σ R)).coeff μ
      = MvPolynomial.hasseDeriv μ P := by
    classical
    induction P using MvPolynomial.induction_on generalizing μ with
    | C a =>
        rw [MvPolynomial.aeval_C, show algebraMap R (MvPolynomial σ (MvPolynomial σ R)) a = MvPolynomial.C (MvPolynomial.C a) from rfl,
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
  rw [← nativeSource67, coeff_map, coeff_taylor]

variable (d : σ → ℝ)

/-- **Layer 2.3. The index of `P` at `α` with respect to the weights `d`** (Bombieri–Gubler,
Definition 6.3.2): the least weighted order `∑ j, μ j / d j` of a Hasse derivative that does not
vanish at `α`. It is `⊤` exactly at `P = 0`, which is its value as a valuation and not a junk
value. -/
def index (d : σ → ℝ) (α : σ → R) (P : MvPolynomial σ R) : ℝ≥0∞ :=
  ⨅ (μ : σ →₀ ℕ) (_ : eval α (hasseDeriv μ P) ≠ 0), ENNReal.ofReal (μ.sum fun j k ↦ k / d j)

end MvPolynomial

namespace Finsupp

end Finsupp

namespace MvPolynomial

variable {σ R : Type*} [CommRing R] (d : σ → ℝ)

/-- **Differentiating costs at most the weight of the order.** This is the estimate Roth's lemma
uses, in the form that avoids truncated subtraction in `ℝ≥0∞`. -/
theorem index_le_hasseDeriv_add (hd : ∀ j, 0 ≤ d j) (α : σ → R) (P : MvPolynomial σ R)
    (μ : σ →₀ ℕ) :
    index d α P
      ≤ index d α (hasseDeriv μ P) + ENNReal.ofReal (μ.sum fun j k ↦ k / d j) := by
  let nativeSource2 := (open Nat in (open scoped ENNReal in (fun {σ : Type _} (d : σ → ℝ) (hd : ∀ j, 0 ≤ d j) (μ : σ →₀ ℕ) => (show Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) μ
        = ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from by
    classical
    rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum,
      ENNReal.ofReal_sum_of_nonneg fun j _ ↦ div_nonneg (Nat.cast_nonneg _) (hd j)]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
      div_eq_mul_inv]))))
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ R).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have prod_choose_eq_zero {μ m : σ →₀ ℕ} (h : ¬ μ ≤ m) :
    (μ.prod fun j k ↦ (m j).choose k) = 0 := by
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (i := j) (Finsupp.mem_support_iff.mpr (by omega))
      (Nat.choose_eq_zero_of_lt hj)
  have hasseDeriv_coeff (μ : σ →₀ ℕ) (P : MvPolynomial σ R) (n : σ →₀ ℕ) :
    (MvPolynomial.hasseDeriv μ P).coeff n
      = ((μ.prod fun j k ↦ (n j + k).choose k : ℕ) : R) * P.coeff (n + μ) := by
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
  have choose_add_mul_choose  (a b c : ℕ) :
    (a + b).choose b * (a + b + c).choose c
      = (b + c).choose b * (a + (b + c)).choose (b + c) := by
    have e1 : (a + b).choose b * a ! * b ! = (a + b)! :=
      Nat.add_choose_mul_factorial_mul_factorial a b
    have e2 : (a + b + c).choose c * (a + b)! * c ! = (a + b + c)! :=
      Nat.add_choose_mul_factorial_mul_factorial (a + b) c
    have e3 : (b + c).choose c * b ! * c ! = (b + c)! :=
      Nat.add_choose_mul_factorial_mul_factorial b c
    have e4 : (a + (b + c)).choose (b + c) * a ! * (b + c)! = (a + (b + c))! :=
      Nat.add_choose_mul_factorial_mul_factorial a (b + c)
    refine Nat.eq_of_mul_eq_mul_right (m := a ! * b ! * c !)
      (Nat.mul_pos (Nat.mul_pos a.factorial_pos b.factorial_pos) c.factorial_pos) ?_
    calc (a + b).choose b * (a + b + c).choose c * (a ! * b ! * c !)
        = ((a + b).choose b * a ! * b !) * ((a + b + c).choose c * c !) := by ring
      _ = (a + b + c).choose c * (a + b)! * c ! := by rw [e1]; ring
      _ = (a + b + c)! := e2
      _ = (a + (b + c))! := by rw [add_assoc]
      _ = (a + (b + c)).choose (b + c) * a ! * (b + c)! := e4.symm
      _ = (a + (b + c)).choose (b + c) * a ! * ((b + c).choose c * b ! * c !) := by rw [e3]
      _ = (b + c).choose c * (a + (b + c)).choose (b + c) * (a ! * b ! * c !) := by ring
      _ = (b + c).choose b * (a + (b + c)).choose (b + c) * (a ! * b ! * c !) := by
          rw [Nat.choose_symm_add]
  have prod_choose_comp (μ ν n : σ →₀ ℕ) :
    (μ.prod fun j k ↦ (n j + k).choose k) * (ν.prod fun j k ↦ ((n + μ) j + k).choose k)
      = (μ.prod fun j k ↦ (k + ν j).choose k) * ((μ + ν).prod fun j k ↦ (n j + k).choose k) := by
    classical
    set s : Finset σ := μ.support ∪ ν.support with hs
    have h1 : (μ.prod fun j k ↦ (n j + k).choose k) = ∏ j ∈ s, (n j + μ j).choose (μ j) :=
      Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (by simp)
    have h2 : (ν.prod fun j k ↦ ((n + μ) j + k).choose k)
        = ∏ j ∈ s, (n j + μ j + ν j).choose (ν j) :=
      Finsupp.prod_of_support_subset _ Finset.subset_union_right _ (by simp)
    have h3 : (μ.prod fun j k ↦ (k + ν j).choose k) = ∏ j ∈ s, (μ j + ν j).choose (μ j) :=
      Finsupp.prod_of_support_subset _ Finset.subset_union_left _ (by simp)
    have h4 : ((μ + ν).prod fun j k ↦ (n j + k).choose k)
        = ∏ j ∈ s, (n j + (μ j + ν j)).choose (μ j + ν j) :=
      Finsupp.prod_of_support_subset _
        (Finsupp.support_add.trans (Finset.union_subset_union subset_rfl subset_rfl)) _ (by simp)
    rw [h1, h2, h3, h4, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ ↦ choose_add_mul_choose (n j) (μ j) (ν j)
  have hasseDeriv_comp (μ ν : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.hasseDeriv ν P)
      = (μ.prod fun j k ↦ (k + ν j).choose k) • MvPolynomial.hasseDeriv (μ + ν) P := by
    apply MvPolynomial.ext; intro n
    rw [MvPolynomial.coeff_smul, hasseDeriv_coeff, hasseDeriv_coeff, hasseDeriv_coeff, nsmul_eq_mul,
      ← add_assoc, ← mul_assoc, ← mul_assoc, ← Nat.cast_mul, ← Nat.cast_mul,
      prod_choose_comp μ ν n]
  have hIndexWeight : ∀ Q : MvPolynomial σ R,
      index d α Q = weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt α Q) := by
    intro Q
    refine le_antisymm ((fun {w : _ → ENNReal} {P : MvPolynomial _ _} {c : ENNReal}
        (h : ∀ ν, P.coeff ν ≠ 0 → c ≤ Finsupp.weight w ν) ↦
        (show c ≤ MvPolynomial.weightedOrder w P from
          Finset.le_inf fun _ hν ↦ h _ (MvPolynomial.mem_support_iff.mp hν))) fun ν hν ↦ ?_)
      ((fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {c : ℝ≥0∞}
        (h : ∀ ν : _ →₀ ℕ, MvPolynomial.eval α (MvPolynomial.hasseDeriv ν P) ≠ 0 →
          c ≤ ENNReal.ofReal (ν.sum fun j k ↦ k / d j)) ↦
        (show c ≤ MvPolynomial.index d α P from le_iInf fun ν ↦ le_iInf fun hν ↦ h ν hν))
        d fun ν hν ↦ ?_)
    · rw [nativeSource2 d hd]
      exact (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {ν : _ →₀ ℕ}
        (h : MvPolynomial.eval α (MvPolynomial.hasseDeriv ν P) ≠ 0) ↦
        (show MvPolynomial.index d α P ≤ ENNReal.ofReal (ν.sum fun j k ↦ k / d j) from
          iInf_le_of_le ν (iInf_le _ h))) d (by rwa [coeff_taylorAt] at hν)
    · rw [← nativeSource2 d hd]
      exact (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {ν} (h : P.coeff ν ≠ 0) ↦
        (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w ν from
          Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) (by rwa [coeff_taylorAt])
  rw [hIndexWeight P, hIndexWeight (hasseDeriv μ P), ← nativeSource2 d hd]
  refine (fun {Q : MvPolynomial σ R} {c A : ℝ≥0∞}
      (h : ∀ ν, Q.coeff ν ≠ 0 →
        A ≤ Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) ν + c) ↦
      (show A ≤ weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) Q + c from by
        rcases eq_or_ne Q 0 with rfl | hQ
        · rw [show MvPolynomial.weightedOrder _ (0 : MvPolynomial _ _) = ⊤ from by
            rw [MvPolynomial.weightedOrder, MvPolynomial.support_zero, Finset.inf_empty],
            top_add]
          exact le_top
        · obtain ⟨ν, hν, hval⟩ : ∃ ν, Q.coeff ν ≠ 0 ∧
              weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) Q =
                Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) ν := by
            obtain ⟨ν, hν, hmin⟩ := Finset.exists_mem_eq_inf Q.support
              (support_nonempty.mpr hQ) (Finsupp.weight fun j ↦ ENNReal.ofReal (d j)⁻¹)
            exact ⟨ν, mem_support_iff.mp hν, hmin⟩
          rw [hval]
          exact h ν hν)) fun ν hν ↦ ?_
  rw [coeff_taylorAt, hasseDeriv_comp, map_nsmul] at hν
  have hne : eval α (hasseDeriv (ν + μ) P) ≠ 0 := fun h ↦ hν (by rw [h, smul_zero])
  calc weightedOrder (fun j ↦ ENNReal.ofReal (d j)⁻¹) (taylorAt α P)
      ≤ Finsupp.weight (fun j ↦ ENNReal.ofReal (d j)⁻¹) (ν + μ) :=
        (fun {w : _ → ENNReal} {P : MvPolynomial _ _} {μ} (h : P.coeff μ ≠ 0) ↦
      (show MvPolynomial.weightedOrder w P ≤ Finsupp.weight w μ from
        Finset.inf_le (MvPolynomial.mem_support_iff.mpr h))) (by rw [coeff_taylorAt]; exact hne)
    _ = _ := map_add _ _ _

/-- **In one variable with weight `1` the index is the multiplicity of the root.** The
nonvanishing hypothesis is forced by `Polynomial.rootMultiplicity a 0 = 0`, where the index is
`⊤`. -/
theorem index_of_unique [Unique σ] (a : R) {P : MvPolynomial σ R} (hP : P ≠ 0) :
    index (fun _ ↦ 1) (fun _ ↦ a) P
      = ((uniqueAlgEquiv R σ P).rootMultiplicity a : ℝ≥0∞) := by
  let nativeSource63 := (open Nat in (open scoped ENNReal in (fun {σ : Type _} {R : Type _} [instSource1 : CommRing R] [Unique σ] (a : R) (P : MvPolynomial σ R) => (show MvPolynomial.eval (fun _ ↦ a) P = Polynomial.eval a (MvPolynomial.uniqueAlgEquiv R σ P) from by
    classical
    induction P using MvPolynomial.induction_on with
    | C r => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p j hp => simp [hp]))))
  have hasseDeriv_apply (μ : σ →₀ ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials σ R).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have hasseDeriv_monomial (μ m : σ →₀ ℕ) (a : R) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.monomial m a) = MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * a) := by
    classical
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [hasseDeriv_apply]
      simp [MvPolynomial.support_monomial, ha, MvPolynomial.coeff_monomial]
  have uniqueAlgEquiv_hasseDeriv (k : ℕ) (P : MvPolynomial σ R) :
    MvPolynomial.uniqueAlgEquiv R σ (MvPolynomial.hasseDeriv (Finsupp.single default k) P) =
      Polynomial.hasseDeriv k (MvPolynomial.uniqueAlgEquiv R σ P) := by
    induction P using MvPolynomial.induction_on' with
    | monomial m a =>
        rw [hasseDeriv_monomial, MvPolynomial.uniqueAlgEquiv_monomial, MvPolynomial.uniqueAlgEquiv_monomial,
          Polynomial.hasseDeriv_monomial, Finsupp.prod_single_index (by simp),
          Finsupp.tsub_apply, Finsupp.single_eq_same]
    | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]
  set p : Polynomial R := uniqueAlgEquiv R σ P with hpdef
  have hp0 : p ≠ 0 := fun h ↦ hP ((uniqueAlgEquiv R σ).injective (by rw [← hpdef, h, map_zero]))
  have htp : Polynomial.taylor a p ≠ 0 := fun h ↦ hp0 (Polynomial.taylor_injective a
    (by rw [h, map_zero]))
  set m : ℕ := (Polynomial.taylor a p).natTrailingDegree with hmdef
  have hroot : p.rootMultiplicity a = m := by
    rw [hmdef, Polynomial.taylor_apply, Polynomial.rootMultiplicity_eq_natTrailingDegree]
  have hkey : ∀ k : ℕ, eval (fun _ ↦ a) (hasseDeriv (Finsupp.single default k) P)
      = (Polynomial.taylor a p).coeff k := by
    intro k
    rw [nativeSource63, uniqueAlgEquiv_hasseDeriv, Polynomial.taylor_coeff, ← hpdef]
  have hweight : ∀ k : ℕ,
      ((Finsupp.single (default : σ) k).sum fun _ e ↦ (e : ℝ) / 1) = (k : ℝ) := by
    intro k
    rw [Finsupp.sum_single_index (by norm_num), div_one]
  rw [hroot]
  refine le_antisymm ?_ ((fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {c : ℝ≥0∞}
      (h : ∀ μ : _ →₀ ℕ, MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0 →
        c ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j)) ↦
      (show c ≤ MvPolynomial.index d α P from le_iInf fun μ ↦ le_iInf fun hμ ↦ h μ hμ)) _ fun μ hμ ↦ ?_)
  · have hne : eval (fun _ ↦ a) (hasseDeriv (Finsupp.single (default : σ) m) P) ≠ 0 := by
      rw [hkey m, hmdef]
      exact Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr htp
    have := (fun (d : _ → ℝ) {α : _ → _} {P : MvPolynomial _ _} {μ : _ →₀ ℕ}
      (h : MvPolynomial.eval α (MvPolynomial.hasseDeriv μ P) ≠ 0) ↦
      (show MvPolynomial.index d α P ≤ ENNReal.ofReal (μ.sum fun j k ↦ k / d j) from
        iInf_le_of_le μ (iInf_le _ h))) (fun _ ↦ (1 : ℝ)) hne
    rwa [hweight m, ENNReal.ofReal_natCast] at this
  · obtain ⟨k, rfl⟩ : ∃ k, μ = Finsupp.single (default : σ) k :=
      ⟨μ default, Finsupp.unique_single μ⟩
    rw [hweight k, ENNReal.ofReal_natCast, Nat.cast_le]
    rw [hkey k] at hμ
    exact Polynomial.natTrailingDegree_le_of_ne_zero hμ

end MvPolynomial

end

end
