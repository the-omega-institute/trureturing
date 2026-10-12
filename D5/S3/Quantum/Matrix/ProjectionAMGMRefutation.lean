/- GID: D5/S3/Quantum/Matrix/ProjectionAMGMRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/ProjectionAMGMRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.claim; result=D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.result; claim=D5/S3/Quantum/Matrix/ProjectionAMGMRefutation.claim
   digest: A 3 by 3 rank-one projection witness refutes the Sun--Luo--Ye matrix AM-GM claim. -/

/- Source: Sun--Luo--Ye, Math. Oper. Res. 45(1) (2020), Section 3.3, Conjecture 1.
   admission_basis: open-problem-resolution (#15647; Refuted)
   The public result is the designated refutation result (`basis=refutes`) and is exempt from four-slot escape registration (CLAUDE.md §3.9).
   proof_shape: result: bind-only; its private consumed helpers are listed below.
   escape_witness: none (the designated refutation result is exempt from four-slot registration).
   Direct frozen dependencies: none; all imported mathematical declarations are pinned Mathlib.
   The projection condition is inlined literally in claim; its private instance proof uses
   the pinned Mathlib IsStarProjection owner through the real-matrix correspondence.
   Private theorem proof_shape and consumers:
     instance_is_projection: bind-only; consumer: result
     sixPerms_univ: bind-only; consumer=sym_form
     v_dot_v: bind-only; consumer=word_product
     v_dot_z: bind-only; consumer=word_form
     word_product: bind-only; consumer=word_form
     word_form: bind-only; consumer=sym_form
     mean_mul_z: bind-only; consumer=mean_form
     mean_form: bind-only; consumer=quadratic_form_value
     sym_form: bind-only; consumer=quadratic_form_value
     quadratic_form_value: bind-only; consumer=instance_not_posSemidef
     instance_not_posSemidef: bind-only; consumer=result
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Star.StarProjection

open Matrix
open scoped BigOperators

namespace D5.S3.Quantum.Matrix.ProjectionAMGMRefutation

noncomputable section

def meanProj {n N : ℕ} (P : Fin n → Matrix (Fin N) (Fin N) ℝ) :=
  ((n : ℝ)⁻¹) • ∑ i, P i

def symProd {n N : ℕ} (P : Fin n → Matrix (Fin N) (Fin N) ℝ) :=
  ((n.factorial : ℝ)⁻¹) • ∑ σ : Equiv.Perm (Fin n),
    (List.ofFn (fun k => P (σ k))).reverse.prod

def claim : Prop :=
  ∀ (n N : ℕ) (P : Fin n → Matrix (Fin N) (Fin N) ℝ),
    1 ≤ n → (∀ i, (P i)ᵀ = P i ∧ P i * P i = P i) →
      (meanProj P ^ n - symProd P).PosSemidef

private def z : Fin 3 → ℝ := fun _ => 1

private def v (i : Fin 3) : Fin 3 → ℝ := fun j => 2 * (if j.val = i.val then 1 else 0) - z j

private def P (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℝ :=
  (1 / 3 : ℝ) • Matrix.vecMulVec (v i) (v i)

private theorem instance_is_projection (i : Fin 3) :
    (P i)ᵀ = P i ∧ P i * P i = P i := by
  have h : IsStarProjection (P i) := by
    rw [isStarProjection_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    fin_cases i <;> constructor
    all_goals
      ext a b
      fin_cases a <;> fin_cases b <;>
        norm_num [P, v, z, Matrix.transpose_apply, Matrix.mul_apply,
          Matrix.vecMulVec, Matrix.smul_apply, Fin.sum_univ_succ]
  rw [isStarProjection_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.symm

private def sixPerms : Finset (Equiv.Perm (Fin 3)) :=
  {1, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.swap 1 2 * Equiv.swap 0 1}

private theorem sixPerms_univ : sixPerms = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Fintype.card_perm, Fintype.card_fin]
  decide +kernel

private theorem v_dot_v (a b : Fin 3) (h : a ≠ b) : v a ⬝ᵥ v b = -1 := by
  fin_cases a <;> fin_cases b <;>
    first | exact (h rfl).elim | norm_num [v, z, dotProduct, Fin.sum_univ_succ]

private theorem v_dot_z (a : Fin 3) : v a ⬝ᵥ z = -1 := by
  fin_cases a <;> norm_num [v, z, dotProduct, Fin.sum_univ_succ]

private theorem word_product (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) :
    P a * P b * P c = (1 / 27 : ℝ) • Matrix.vecMulVec (v a) (v c) := by
  simp only [P, Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_smul, smul_smul]
  rw [v_dot_v a b hab, v_dot_v b c hbc]
  norm_num

private theorem word_form (a b c : Fin 3) (hab : a ≠ b) (hbc : b ≠ c) :
    z ⬝ᵥ ((P a * P b * P c) *ᵥ z) = 1 / 27 := by
  rw [word_product a b c hab hbc, Matrix.smul_mulVec, dotProduct_smul,
    dotProduct_mulVec, Matrix.vecMul_vecMulVec, smul_dotProduct,
    dotProduct_comm z (v a), v_dot_z a, v_dot_z c]
  norm_num

private theorem mean_mul_z : meanProj P *ᵥ z = (1 / 9 : ℝ) • z := by
  ext i
  fin_cases i <;>
    norm_num [meanProj, P, v, z, Matrix.mulVec, dotProduct, Matrix.vecMulVec,
      Matrix.smul_apply, Matrix.sum_apply, Fin.sum_univ_succ]

private theorem mean_form : z ⬝ᵥ ((meanProj P ^ 3) *ᵥ z) = 1 / 243 := by
  simp only [pow_succ, pow_zero, ← Matrix.mulVec_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_smul, mean_mul_z, smul_smul, dotProduct_smul]
  norm_num [dotProduct, z, Fin.sum_univ_succ]

private theorem sym_form : z ⬝ᵥ (symProd P *ᵥ z) = 1 / 27 := by
  have hword (σ : Equiv.Perm (Fin 3)) :
      z ⬝ᵥ ((List.ofFn (fun k => P (σ k))).reverse.prod *ᵥ z) = 1 / 27 := by
    simp only [List.ofFn_succ, List.ofFn_zero, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.prod_cons, List.prod_nil, mul_one]
    rw [← Matrix.mul_assoc]
    apply word_form
    · exact σ.injective.ne (by decide)
    · exact σ.injective.ne (by decide)
  unfold symProd
  rw [← sixPerms_univ, Matrix.smul_mulVec, dotProduct_smul,
    Matrix.sum_mulVec, dotProduct_sum]
  simp only [hword, Finset.sum_const, nsmul_eq_mul]
  have hcard : sixPerms.card = 6 := by decide +kernel
  rw [hcard]
  norm_num [Nat.factorial]

private theorem quadratic_form_value :
    z ⬝ᵥ ((meanProj P ^ 3 - symProd P) *ᵥ z) = -8 / 243 := by
  rw [Matrix.sub_mulVec, dotProduct_sub, mean_form, sym_form]
  norm_num

private theorem instance_not_posSemidef : ¬ (meanProj P ^ 3 - symProd P).PosSemidef := by
  intro h
  have hq := h.dotProduct_mulVec_nonneg z
  have hz : star z = z := by ext i; simp [z]
  rw [hz, quadratic_form_value] at hq
  norm_num at hq

theorem result : ¬ claim := by
  intro h
  exact instance_not_posSemidef (h 3 3 P (by norm_num) instance_is_projection)


end
end D5.S3.Quantum.Matrix.ProjectionAMGMRefutation
