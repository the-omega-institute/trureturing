/- GID: D5/S3/Arith/DiophantineApproximation/RothDecomposition
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/RothDecomposition
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A Hasse derivative matrix determinant factors through the Roth decomposition. -/
/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
Adapted for trureturing: module namespace, pinned-library compatibility, and direct library reuse.
-/
module

public import D5.S3.Arith.DiophantineApproximation.GeneralizedWronskian
public import D5.S3.Arith.DiophantineApproximation.IndexRename
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

@[expose] public section

open Nat

noncomputable section

open Finset Finsupp Function

namespace Module

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]

/-- **A finite family is expressed by a linearly independent one of no greater size, and the
coefficients that do it are jointly nondegenerate.** The last clause is what makes the second
family of Roth's decomposition linearly independent: a linear relation among the coefficient
*columns* is a linear functional killing every member of the family, hence the span, hence every
basis vector. -/
theorem exists_basis_repr {n : ℕ} (c : Fin n → M) :
    ∃ (p : ℕ) (f : Fin p → M) (a : Fin n → Fin p → K),
      p ≤ n ∧ LinearIndependent K f ∧ (∀ k, c k = ∑ l, a k l • f l) ∧
      ∀ lam : Fin p → K, (∀ k, ∑ l, lam l * a k l = 0) → lam = 0 := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  have : FiniteDimensional K W := FiniteDimensional.span_of_finite K (Set.finite_range c)
  set p := Module.finrank K W with hp
  set b : Module.Basis (Fin p) K W := Module.finBasis K W with hb
  set c' : Fin n → W := fun k ↦ ⟨c k, Submodule.subset_span ⟨k, rfl⟩⟩ with hc'
  have hspan : Submodule.span K (Set.range c') = ⊤ := by
    refine Submodule.map_injective_of_injective W.injective_subtype ?_
    rw [Submodule.map_span, Submodule.map_subtype_top]
    congr 1
    rw [← Set.range_comp]
    rfl
  refine ⟨p, fun l ↦ (b l : M), fun k l ↦ b.repr (c' k) l,
    le_of_le_of_eq (finrank_range_le_card c) (Fintype.card_fin n),
    b.linearIndependent.map' W.subtype (Submodule.ker_subtype W), fun k ↦ ?_, fun lam hlam ↦ ?_⟩
  · have := congrArg (W.subtype) (b.sum_repr (c' k))
    rw [map_sum] at this
    simpa using this.symm
  · set ψ : W →ₗ[K] K := (Finsupp.linearCombination K lam).comp b.repr.toLinearMap with hψ
    have hker : ∀ k, c' k ∈ LinearMap.ker ψ := by
      intro k
      simp only [LinearMap.mem_ker, hψ, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Finsupp.linearCombination_apply]
      rw [Finsupp.sum_fintype _ _ (fun i ↦ zero_smul K (lam i))]
      simp only [smul_eq_mul]
      simpa [mul_comm] using hlam k
    have htop : LinearMap.ker ψ = ⊤ :=
      top_le_iff.mp (hspan ▸ Submodule.span_le.mpr (Set.range_subset_iff.mpr hker))
    funext l
    have hbl : ψ (b l) = lam l := by
      simp [hψ, Module.Basis.repr_self, Finsupp.linearCombination_single]
    rw [← hbl]
    exact LinearMap.mem_ker.mp (htop ▸ Submodule.mem_top)

end Module

namespace MvPolynomial

variable {K : Type*} [Field K] {m : ℕ}

/-- The embedding of the separated variable: `Fin 1` onto the index `0`. -/
def lastVar (m : ℕ) : Fin 1 → Fin (m + 1) := fun _ ↦ 0

section Decomposition

/-- **The tensor decomposition of a polynomial along the variable `X 0`.** -/
theorem exists_tensor_decomposition {P : MvPolynomial (Fin (m + 1)) K} (hP : P ≠ 0) :
    ∃ (p : ℕ) (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K),
      0 < p ∧ p ≤ P.degreeOf 0 + 1 ∧ LinearIndependent K f ∧ LinearIndependent K g ∧
      P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l) := by
  have hrename (q : MvPolynomial (Fin m) K) :
      finSuccEquiv K m (rename Fin.succ q) = Polynomial.C q := by
    induction q using MvPolynomial.induction_on with
    | C r => rw [rename_C, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    | add a b ha hb => rw [map_add, map_add, ha, hb, map_add]
    | mul_X a j ha => rw [map_mul, rename_X, map_mul, ha, finSuccEquiv_X_succ, ← map_mul]
  have hsum (P : MvPolynomial (Fin (m + 1)) K) (N : ℕ)
      (hN : (finSuccEquiv K m P).natDegree < N + 1) :
      P = ∑ k ∈ Finset.range (N + 1),
        rename Fin.succ ((finSuccEquiv K m P).coeff k)
          * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ k := by
    refine (finSuccEquiv K m).injective ?_
    rw [map_sum]
    simp only [map_mul, map_pow, hrename, finSuccEquiv_X_zero]
    simp only [Polynomial.C_mul_X_pow_eq_monomial]
    exact Polynomial.as_sum_range' _ _ hN
  classical
  obtain ⟨p, f, a, hple, hf, hrepr, hnd⟩ := Module.exists_basis_repr (K := K)
    (fun k : Fin (P.degreeOf 0 + 1) ↦ (finSuccEquiv K m P).coeff (k : ℕ))
  set g : Fin p → MvPolynomial (Fin 1) K :=
    fun l ↦ ∑ k : Fin (P.degreeOf 0 + 1), monomial (Finsupp.single 0 (k : ℕ)) (a k l) with hg
  have hgrename : ∀ l, rename (lastVar m) (g l)
      = ∑ k : Fin (P.degreeOf 0 + 1),
        C (a k l) * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ (k : ℕ) := by
    intro l
    rw [hg, map_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by
      rw [rename_monomial, Finsupp.mapDomain_single, MvPolynomial.lastVar, monomial_eq,
        Finsupp.prod_single_index (by rw [pow_zero])]
  have hdecomp : P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l) := by
    rw [hsum P (P.degreeOf 0) (by rw [natDegree_finSuccEquiv]; omega),
      ← Fin.sum_univ_eq_sum_range (fun k ↦ rename Fin.succ ((finSuccEquiv K m P).coeff k)
        * (X 0 : MvPolynomial (Fin (m + 1)) K) ^ k)]
    simp only [hgrename, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hrepr k, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [map_smul, MvPolynomial.smul_eq_C_mul]
    ring
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h
      exact absurd (by simpa using hdecomp) hP
    · exact h
  refine ⟨p, f, g, hp0, hple, hf, ?_, hdecomp⟩
  refine Fintype.linearIndependent_iff.mpr fun lam hlam ↦ ?_
  have hcoeff : ∀ k : Fin (P.degreeOf 0 + 1), ∑ l, lam l * a k l = 0 := by
    intro k
    have := congrArg (fun Q : MvPolynomial (Fin 1) K ↦ Q.coeff (Finsupp.single 0 (k : ℕ))) hlam
    simp only [coeff_sum, coeff_smul, smul_eq_mul] at this
    have h2 : ∑ l, lam l * (g l).coeff (Finsupp.single 0 (k : ℕ)) = 0 := by simpa using this
    rw [← h2]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [hg, coeff_sum, Finset.sum_eq_single k]
      · rw [coeff_monomial, if_pos rfl]
      · intro j _ hj
        refine (coeff_monomial _ _ _).trans (if_neg fun h ↦ hj ?_)
        exact Fin.val_injective (Finsupp.single_injective 0 h)
      · intro h
        exact absurd (Finset.mem_univ k) h
  exact congrFun (hnd lam hcoeff)

end Decomposition

section Determinant

/-- Every term of the Leibniz expansion other than the split one vanishes: its order reaches
into the wrong variable set. -/
theorem hasseDeriv_rename_mul_eq_zero_of_ne {ρ : Fin m →₀ ℕ} {τ : Fin 1 →₀ ℕ}
    (u : MvPolynomial (Fin m) K) (w : MvPolynomial (Fin 1) K) {x y : Fin (m + 1) →₀ ℕ}
    (hxy : x + y = ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m))
    (hne : (x, y) ≠ (ρ.mapDomain Fin.succ, τ.mapDomain (lastVar m))) :
    hasseDeriv x (rename Fin.succ u) * hasseDeriv y (rename (lastVar m) w) = 0 := by
  by_cases hx0 : x 0 = 0
  swap
  · have hdegree : (rename Fin.succ u).degreeOf 0 = 0 := by
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro n hn
      by_contra hc
      have hs : ¬ ((n.support : Set (Fin (m + 1))) ⊆ Set.range Fin.succ) :=
        fun hsub ↦ (fun ⟨i, hi⟩ ↦ Fin.succ_ne_zero i hi)
          (hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr (by omega))))
      have hz : (rename Fin.succ u).coeff n = 0 := by
        refine coeff_rename_eq_zero _ _ _ fun v hv ↦ absurd (fun t ht ↦ ?_) hs
        rw [← hv] at ht
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (mapDomain_support (Finset.mem_coe.mp ht))
        exact ⟨a, rfl⟩
      exact absurd hz (mem_support_iff.mp hn)
    rw [hasseDeriv_eq_zero_of_lt (j := 0) (by simpa [hdegree] using Nat.pos_of_ne_zero hx0), zero_mul]
  by_cases hy : ∃ j, j ≠ 0 ∧ y j ≠ 0
  · obtain ⟨j, hj, hyj⟩ := hy
    have hdegree : (rename (lastVar m) w).degreeOf j = 0 := by
      rw [← Nat.le_zero, degreeOf_le_iff]
      intro n hn
      by_contra hc
      have hs : ¬ ((n.support : Set (Fin (m + 1))) ⊆ Set.range (lastVar m)) := by
        intro hsub
        have hnj : n j ≠ 0 := by omega
        obtain ⟨i, hi⟩ := hsub (Finset.mem_coe.mpr (Finsupp.mem_support_iff.mpr hnj))
        exact hj (by simpa [lastVar] using hi.symm)
      have hz : (rename (lastVar m) w).coeff n = 0 := by
        refine coeff_rename_eq_zero _ _ _ fun v hv ↦ absurd (fun t ht ↦ ?_) hs
        rw [← hv] at ht
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp (mapDomain_support (Finset.mem_coe.mp ht))
        exact ⟨a, rfl⟩
      exact absurd hz (mem_support_iff.mp hn)
    rw [hasseDeriv_eq_zero_of_lt (P := rename (lastVar m) w) (μ := y)
      (j := j) (by simpa [hdegree] using Nat.pos_of_ne_zero hyj), mul_zero]
  · refine absurd ?_ hne
    push Not at hy
    have hyt : y = τ.mapDomain (lastVar m) := by
      refine Finsupp.ext fun j ↦ ?_
      rcases eq_or_ne j 0 with rfl | hj
      · have h0 : x 0 + y 0 = (ρ.mapDomain Fin.succ) 0 + (τ.mapDomain (lastVar m)) 0 := by
          rw [← Finsupp.add_apply, ← Finsupp.add_apply, hxy]
        rw [hx0, (Finsupp.mapDomain_of_notMem_range ρ (0 : Fin (m + 1))
          (fun ⟨i, hi⟩ ↦ Fin.succ_ne_zero i hi))] at h0
        omega
      · rw [hy j hj, Finsupp.mapDomain_of_notMem_range τ j
          (fun ⟨i, hi⟩ ↦ hj (by simpa [lastVar] using hi.symm))]
    exact Prod.ext (add_right_cancel (hxy.trans (by rw [hyt]))) hyt

/-- **A Hasse derivative of an order split between two disjoint variable sets acts factor by
factor.** -/
theorem hasseDeriv_add_rename_mul (ρ : Fin m →₀ ℕ) (τ : Fin 1 →₀ ℕ)
    (u : MvPolynomial (Fin m) K) (w : MvPolynomial (Fin 1) K) :
    hasseDeriv (ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m))
        (rename Fin.succ u * rename (lastVar m) w)
      = rename Fin.succ (hasseDeriv ρ u) * rename (lastVar m) (hasseDeriv τ w) := by
  let σ := Fin (m + 1)
  have hasseDeriv_apply (μ : Fin (m + 1) →₀ ℕ) (P : MvPolynomial (Fin (m + 1)) K) :
    MvPolynomial.hasseDeriv μ P = ∑ m ∈ P.support,
      MvPolynomial.monomial (m - μ) ((μ.prod fun j k ↦ (m j).choose k : ℕ) * P.coeff m) := by
    rw [MvPolynomial.hasseDeriv, Module.Basis.constr_apply]
    rw [show (MvPolynomial.basisMonomials (Fin (m + 1)) K).repr P = AddMonoidAlgebra.coeff P from rfl, MvPolynomial.sum_def]
    exact Finset.sum_congr rfl fun m _ ↦ by rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_comm]
  have hasseDeriv_monomial (μ ν : Fin (m + 1) →₀ ℕ) (a : K) :
    MvPolynomial.hasseDeriv μ (MvPolynomial.monomial ν a) = MvPolynomial.monomial (ν - μ) ((μ.prod fun j k ↦ (ν j).choose k : ℕ) * a) := by
    classical
    rcases eq_or_ne a 0 with rfl | ha
    · simp
    · rw [hasseDeriv_apply]
      simp [MvPolynomial.support_monomial, ha, MvPolynomial.coeff_monomial]
  have add_sub_single_left {n μ : Fin (m + 1) →₀ ℕ} {j : Fin (m + 1)} (h : n j ≠ 0) :
    n + μ - (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ) = n - (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ) + μ := by
    ext i
    rcases eq_or_ne i j with rfl | hij
    · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · have h1 : (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
      omega
  have add_sub_single_right {n μ : Fin (m + 1) →₀ ℕ} {j : Fin (m + 1)} (h : μ j ≠ 0) :
    n + μ - (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ) = n + (μ - (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ)) := by
    ext i
    rcases eq_or_ne i j with rfl | hij
    · simp only [Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    · have h1 : (Finsupp.single j 1 : Fin (m + 1) →₀ ℕ) i = 0 := Finsupp.single_eq_of_ne hij
      simp only [Finsupp.tsub_apply, Finsupp.add_apply, h1]
      omega
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
  have hasseDeriv_mul_X (μ : σ →₀ ℕ) (P : MvPolynomial σ K) (j : σ) :
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
  have coeff_taylor (P : MvPolynomial σ K) (μ : σ →₀ ℕ) :
    (MvPolynomial.aeval (fun j ↦ MvPolynomial.C (MvPolynomial.X j) + MvPolynomial.X j) P : MvPolynomial σ (MvPolynomial σ K)).coeff μ
      = MvPolynomial.hasseDeriv μ P := by
    classical
    induction P using MvPolynomial.induction_on generalizing μ with
    | C a =>
        rw [MvPolynomial.aeval_C, show algebraMap K (MvPolynomial σ (MvPolynomial σ K)) a = MvPolynomial.C (MvPolynomial.C a) from rfl,
          MvPolynomial.coeff_C, ← MvPolynomial.monomial_zero', hasseDeriv_monomial]
        by_cases h : μ = 0
        · subst h; simp [hasseDeriv_monomial]
        · rw [if_neg (fun hz ↦ h hz.symm),
            prod_choose_eq_zero (ν := 0) (by simpa using h),
            Nat.cast_zero, zero_mul, MvPolynomial.monomial_zero]
    | add p q hp hq => rw [map_add, MvPolynomial.coeff_add, hp, hq, map_add]
    | mul_X p j hp =>
        rw [map_mul, MvPolynomial.aeval_X, mul_add, MvPolynomial.coeff_add, mul_comm (MvPolynomial.aeval _ p) (MvPolynomial.C (MvPolynomial.X j)),
          MvPolynomial.coeff_C_mul, MvPolynomial.coeff_mul_X', hp, hasseDeriv_mul_X, mul_comm (MvPolynomial.X j) (MvPolynomial.hasseDeriv μ p)]
        congr 1
        by_cases h : μ j = 0
        · rw [if_neg (by simpa using h), if_pos h]
        · rw [if_pos (Finsupp.mem_support_iff.mpr h), if_neg h, hp]
  have hasseDeriv_mul (μ : σ →₀ ℕ) (P Q : MvPolynomial σ K) :
    MvPolynomial.hasseDeriv μ (P * Q)
      = ∑ x ∈ Finset.antidiagonal μ, MvPolynomial.hasseDeriv x.1 P * MvPolynomial.hasseDeriv x.2 Q := by
    classical
    rw [← coeff_taylor, map_mul, MvPolynomial.coeff_mul]
    exact Finset.sum_congr rfl fun x _ ↦ by rw [coeff_taylor, coeff_taylor]
  rw [hasseDeriv_mul]
  have hmem : (ρ.mapDomain Fin.succ, τ.mapDomain (lastVar m))
      ∈ Finset.antidiagonal (ρ.mapDomain Fin.succ + τ.mapDomain (lastVar m)) :=
    Finset.mem_antidiagonal.mpr rfl
  refine (Finset.sum_eq_single_of_mem _ hmem ?_).trans ?_
  · rintro ⟨x, y⟩ hxy hne
    exact hasseDeriv_rename_mul_eq_zero_of_ne u w (Finset.mem_antidiagonal.mp hxy) hne
  · rw [hasseDeriv_rename (Fin.succ_injective m), hasseDeriv_rename (Function.injective_of_subsingleton (lastVar m))]

/-- The matrix of Hasse derivatives of `P` at the orders `μ i` in the first `m` variables and
`ν j` in the last. -/
@[expose] def hasseDerivMatrix {p : ℕ} (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ))
    (P : MvPolynomial (Fin (m + 1)) K) :
    Matrix (Fin p) (Fin p) (MvPolynomial (Fin (m + 1)) K) :=
  .of fun i j ↦ hasseDeriv ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar m)) P

/-- **The determinant of the matrix of Hasse derivatives is the product of the two generalized
Wronskians.** This is Cauchy's formula for the determinant of a product: the matrix is the
product of the Wronskian matrix of the `f` family and the transpose of the one of the `g`
family. -/
theorem det_hasseDerivMatrix {p : ℕ} {P : MvPolynomial (Fin (m + 1)) K}
    (f : Fin p → MvPolynomial (Fin m) K) (g : Fin p → MvPolynomial (Fin 1) K)
    (hP : P = ∑ l, rename Fin.succ (f l) * rename (lastVar m) (g l))
    (μ : Fin p → (Fin m →₀ ℕ)) (ν : Fin p → (Fin 1 →₀ ℕ)) :
    (hasseDerivMatrix μ ν P).det
      = rename Fin.succ (genWronskian μ f) * rename (lastVar m) (genWronskian ν g) := by
  have hmat : hasseDerivMatrix μ ν P
      = (genWronskianMatrix μ f).map (rename Fin.succ)
        * Matrix.transpose ((genWronskianMatrix ν g).map (rename (lastVar m))) := by
    ext i j
    have hij : hasseDerivMatrix μ ν P i j
        = ∑ l, rename Fin.succ (hasseDeriv (μ i) (f l))
            * rename (lastVar m) (hasseDeriv (ν j) (g l)) := by
      change hasseDeriv ((μ i).mapDomain Fin.succ + (ν j).mapDomain (lastVar m)) P = _
      rw [hP, map_sum]
      exact Finset.sum_congr rfl fun l _ ↦ hasseDeriv_add_rename_mul _ _ _ _
    rw [hij, Matrix.mul_apply]
    rfl
  rw [hmat, Matrix.det_mul, Matrix.det_transpose, genWronskian, genWronskian,
    AlgHom.map_det, AlgHom.map_det]
  rfl

end Determinant

end MvPolynomial
