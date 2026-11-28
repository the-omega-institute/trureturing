/- GID: D5/S3/Geometry/HermitianSpinorContraction
   generality: G
   mirror-B: none(waiver:covered-by-petrov-bel-robinson-superenergy4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Hermitian contractions of finite tensors, their permutation action, and rank-one expansion. -/

import OmegaBuild.Commands
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Multilinear.Basic

/-!
Omega original.

Hermitian contractions of finite tensors, their permutation action, and rank-one expansion.
-/

compile_only_with_mathlib

open scoped BigOperators ComplexConjugate

namespace Omega.HermitianSpinorContraction

open Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

/-- The Hermitian quadratic pairing of a tensor against one matrix in each slot. -/
noncomputable def contract (T : (ι → κ) → ℂ) (M : ι → Matrix κ κ ℂ) : ℂ :=
  ∑ a, ∑ b, T a * conj (T b) * ∏ i, M i (a i) (b i)

theorem contract_real (T : (ι → κ) → ℂ) (M : ι → Matrix κ κ ℂ)
    (hM : ∀ i, (M i).IsHermitian) : (contract T M).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  unfold contract
  simp only [map_sum, map_mul, map_prod, Complex.conj_conj]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h : ∀ i, conj (M i (b i) (a i)) = M i (a i) (b i) :=
    fun i => (hM i).apply (a i) (b i)
  simp only [h, mul_comm (conj (T b)) (T a)]

theorem contract_perm (T : (ι → κ) → ℂ) (M : ι → Matrix κ κ ℂ)
    (σ : Equiv.Perm ι) (hT : ∀ a, T (a ∘ σ) = T a) :
    contract T (M ∘ σ) = contract T M := by
  classical
  let e : (ι → κ) ≃ (ι → κ) := Equiv.arrowCongr σ (Equiv.refl κ)
  unfold contract
  refine Fintype.sum_equiv e _ _ fun a => ?_
  refine Fintype.sum_equiv e _ _ fun b => ?_
  change T a * conj (T b) * (∏ i, M (σ i) (a i) (b i)) =
    T (a ∘ σ.symm) * conj (T (b ∘ σ.symm)) * (∏ i, M i (a (σ.symm i)) (b (σ.symm i)))
  have hTs (a : ι → κ) : T (a ∘ σ.symm) = T a := by
    simpa [Function.comp_def] using (hT (a ∘ σ.symm)).symm
  rw [hTs, hTs]
  congr 1
  simpa using Equiv.prod_comp σ (fun i => M i (a (σ.symm i)) (b (σ.symm i)))


omit [Fintype κ] in
private theorem product_update (M : ι → Matrix κ κ ℂ) (i : ι)
    (A : Matrix κ κ ℂ) (a b : ι → κ) :
    (∏ j, Function.update M i A j (a j) (b j)) =
      A (a i) (b i) * ∏ j ∈ Finset.univ \ {i}, M j (a j) (b j) := by
  rw [← Finset.prod_update_of_mem (s := Finset.univ) (f := fun j => M j (a j) (b j))
    (Finset.mem_univ i) (A (a i) (b i))]
  apply Finset.prod_congr rfl
  intro j _
  by_cases h : j = i
  · subst j
    simp
  · simp [Function.update_of_ne h]

/-- A contraction is separately complex-linear in each matrix slot. -/
noncomputable def contractMultilinear (T : (ι → κ) → ℂ) :
    MultilinearMap ℂ (fun _ : ι => Matrix κ κ ℂ) ℂ :=
  MultilinearMap.mk' (contract T)
    (by
      intro M i A B
      simp only [contract, product_update, Matrix.add_apply, add_mul, mul_add,
        Finset.sum_add_distrib])
    (by
      intro M i c A
      simp only [contract, product_update, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring)

theorem contract_smul_tensor (T : (ι → κ) → ℂ) (M : ι → Matrix κ κ ℂ)
    (s : ℂ) (hs : ‖s‖ = 1) : contract (fun a => s * T a) M = contract T M := by
  unfold contract
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have h : s * conj s = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hs]
    norm_num
  rw [map_mul]
  calc
    s * T a * (conj s * conj (T b)) * (∏ i, M i (a i) (b i)) =
        (s * conj s) * (T a * conj (T b) * (∏ i, M i (a i) (b i))) := by ring
    _ = _ := by rw [h, one_mul]

/-- The outer product of a vector with its Hermitian adjoint. -/
def rankOne (x : κ → ℂ) : Matrix κ κ ℂ := Matrix.vecMulVec x (star x)

omit [Fintype κ] in
@[simp] theorem rankOne_apply (x : κ → ℂ) (i j : κ) : rankOne x i j = x i * conj (x j) :=
  rfl

theorem contract_rankOne (T : (ι → κ) → ℂ) (x : ι → κ → ℂ) :
    contract T (fun i => rankOne (x i)) =
      ↑(‖∑ a, T a * ∏ i, x i (a i)‖ ^ 2) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  simp only [contract, rankOne_apply, Finset.prod_mul_distrib, map_sum, map_mul, map_prod,
    Finset.sum_mul, Finset.mul_sum]
  nth_rw 2 [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem contract_sum_rankOne {η : ι → Type*} [∀ i, Fintype (η i)]
    (T : (ι → κ) → ℂ) (x : (i : ι) → η i → κ → ℂ) :
    contract T (fun i => ∑ j, rankOne (x i j)) =
      ∑ p : (i : ι) → η i, ↑(‖∑ a, T a * ∏ i, x i (p i) (a i)‖ ^ 2) := by
  classical
  rw [show (∑ p : (i : ι) → η i, (↑(‖∑ a, T a * ∏ i, x i (p i) (a i)‖ ^ 2) : ℂ)) =
      ∑ p : (i : ι) → η i, contract T (fun i => rankOne (x i (p i))) by
    simp only [contract_rankOne]]
  unfold contract
  have h (a b : ι → κ) :
      (∏ i, (∑ j, rankOne (x i j)) (a i) (b i)) =
        ∑ p : (i : ι) → η i, ∏ i, rankOne (x i (p i)) (a i) (b i) := by
    simpa only [Matrix.sum_apply, Fintype.piFinset_univ] using
      (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (η i)))
        (fun i j => rankOne (x i j) (a i) (b i)))
  simp only [h, Finset.mul_sum]
  calc
    _ = ∑ a : ι → κ, ∑ p : (i : ι) → η i, ∑ b : ι → κ,
          T a * conj (T b) * ∏ i, rankOne (x i (p i)) (a i) (b i) := by
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

theorem contract_identity [DecidableEq κ] (T : (ι → κ) → ℂ) :
    contract T (fun _ => 1) = ∑ a, (↑(‖T a‖ ^ 2) : ℂ) := by
  classical
  unfold contract
  apply Finset.sum_congr rfl
  intro a _
  have hp (b : ι → κ) : (∏ i, (1 : Matrix κ κ ℂ) (a i) (b i)) = if a = b then 1 else 0 := by
    split_ifs with h
    · subst b
      simp
    · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
        by_contra! hef
        exact h (funext hef)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (Matrix.one_apply_ne hi)
  simp [hp, mul_ite, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem contract_identityExcept [DecidableEq κ] (T : (ι → κ) → ℂ) (i : ι)
    (A : Matrix κ κ ℂ) :
    contract T (Function.update (fun _ => 1) i A) =
      ∑ a, ∑ y : κ, T a * conj (T (Function.update a i y)) * A (a i) y := by
  classical
  unfold contract
  apply Finset.sum_congr rfl
  intro a _
  simp only [product_update]
  have hp (b : ι → κ) :
      (∏ j ∈ Finset.univ \ {i}, (1 : Matrix κ κ ℂ) (a j) (b j)) =
        if b = Function.update a i (b i) then 1 else 0 := by
    split_ifs with h
    · apply Finset.prod_eq_one
      intro j hj
      have hji : j ≠ i := by simpa using hj
      rw [show b j = a j by simpa [Function.update_of_ne hji] using congrFun h j]
      simp
    · have hn : ∃ j, j ≠ i ∧ b j ≠ a j := by
        by_contra! h'
        apply h
        funext j
        by_cases hji : j = i
        · subst j
          simp
        · simpa [Function.update_of_ne hji] using h' j hji
      obtain ⟨j, hji, hab⟩ := hn
      exact Finset.prod_eq_zero (by simpa using hji) (Matrix.one_apply_ne hab.symm)
  simp only [hp, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl (fun b (_ : b ∈ Finset.univ) => show
      (if b = Function.update a i (b i) then T a * conj (T b) * A (a i) (b i) else 0) =
      ∑ y : κ, if b = Function.update a i y then T a * conj (T b) * A (a i) y else 0 by
    rw [Finset.sum_eq_single (b i)]
    · intro y _ hy
      apply ite_eq_right
      intro h
      exact hy (by simpa using (congrFun h i).symm)
    · simp)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_eq_single (Function.update a i y)]
  · simp
  · intro b _ h
    exact ite_eq_right h
  · simp

end Omega.HermitianSpinorContraction
