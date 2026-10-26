/- GID: D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.claim; result=D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.result; claim=D5/S3/Quantum/Matrix/MalkounSubgroupLowerBoundRefutation.claim
   digest: Two cyclic permutation subgroups and a complex Gram matrix refute the unrestricted MO456248 lower bound. -/

/- Source: Malkoun, MO456248, revision 8.
   admission_basis: open-problem-resolution
   Preregistration: https://github.com/the-omega-institute/trureturing/issues/19798
   Direct frozen D5 dependencies: none; mathematical suppliers are pinned Mathlib.
   proof_shape: bind-only for each theorem below, including result.
   Consumers: diagonal_product_eq_real -> H_diagonal; g_order, k_order, sum_powers
   -> H_crossSum; H_posSemidef -> H_diagonal and result; H_diagonal, H_crossSum
   -> result. Arrows in this list run from prerequisite to consumer.
   The designated result is exempt from four-slot registration. The public
   real-diagonal bridge has its source-owned Reg mirror.
   Concrete permutations, groups and matrices are internal witness data.
-/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Basic.Complex.BigOperators
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # The arbitrary-subgroup lower bound fails for a complex Gram matrix -/

open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation

noncomputable section

/-- The full, unnormalized sum over the two actual permutation subgroups. -/
def crossSum {n : ℕ} (G K : Subgroup (Equiv.Perm (Fin n)))
    (H : Matrix (Fin n) (Fin n) ℂ) : ℂ := by
  classical
  exact ∑ σ : G, ∑ τ : K, ∏ i, H (σ.val i) (τ.val i)

/-- The main arbitrary-subgroup assertion of MO456248, revision 8. -/
def claim : Prop :=
  ∀ (n : ℕ) (G K : Subgroup (Equiv.Perm (Fin n))),
    ∃ c : ℝ, 0 < c ∧ ∀ H : Matrix (Fin n) (Fin n) ℂ,
      H.IsHermitian → H.PosSemidef →
        c * (∏ i, (H i i).re) ≤ (crossSum G K H).re

/-- For a Hermitian matrix, the product of the complex diagonal entries is the
real embedding of the product of their real parts. -/
theorem diagonal_product_eq_real {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.IsHermitian) :
    (∏ i, H i i) = ((∏ i, (H i i).re : ℝ) : ℂ) := by
  have hd (i : Fin n) : H i i = ((H i i).re : ℂ) := by
    apply Complex.ext
    · simp
    · have h := congrArg Complex.im (hH.apply i i)
      simp at h
      simp only [Complex.ofReal_im]
      linarith
  rw [Complex.ofReal_prod]
  exact Finset.prod_congr rfl fun i _ => hd i

private def g : Equiv.Perm (Fin 7) where
  toFun := ![1, 4, 6, 2, 5, 3, 0]
  invFun := ![6, 0, 3, 5, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def k : Equiv.Perm (Fin 7) where
  toFun := ![1, 6, 0, 2, 5, 3, 4]
  invFun := ![2, 0, 3, 5, 6, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

private def G : Subgroup (Equiv.Perm (Fin 7)) := Subgroup.zpowers g
private def K : Subgroup (Equiv.Perm (Fin 7)) := Subgroup.zpowers k

private theorem g_order : orderOf g = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private theorem k_order : orderOf k = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide +kernel) (by decide +kernel)

private def V : Matrix (Fin 2) (Fin 7) ℂ :=
  !![1, 3, 1, 3, 1, 1, 3; 2, 2, -2, 2, 0, -3, -2]

private def H : Matrix (Fin 7) (Fin 7) ℂ := V.conjTranspose * V

private theorem H_posSemidef : H.PosSemidef :=
  Matrix.posSemidef_conjTranspose_mul_self V

private theorem H_diagonal : (∏ i, (H i i).re) = 549250 := by
  apply Complex.ofReal_injective
  rw [← diagonal_product_eq_real H H_posSemidef.1]
  norm_num [H, V, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Fin.prod_univ_succ, map_ofNat]

private theorem sum_powers (p : Equiv.Perm (Fin 7)) (hp : orderOf p = 7)
    (f : Equiv.Perm (Fin 7) → ℂ) :
    (∑ σ : Subgroup.zpowers p, f σ.val) = ∑ i : Fin 7, f (p ^ i.val) := by
  classical
  have h := (finEquivZPowers (isOfFinOrder_of_finite p)).sum_comp
    (fun σ : Subgroup.zpowers p => f σ.val)
  simp only [finEquivZPowers_apply] at h
  rw [hp] at h
  exact h.symm

private theorem H_crossSum : crossSum G K H = -23944 := by
  classical
  change (∑ σ : Subgroup.zpowers g, ∑ τ : Subgroup.zpowers k,
    ∏ i, H (σ.val i) (τ.val i)) = -23944
  trans ∑ a : Fin 7, ∑ b : Fin 7, ∏ i, H ((g ^ a.val) i) ((k ^ b.val) i)
  · trans ∑ a : Fin 7, ∑ τ : Subgroup.zpowers k, ∏ i, H ((g ^ a.val) i) (τ.val i)
    · exact sum_powers g g_order (fun σ => ∑ τ : Subgroup.zpowers k,
        ∏ i, H (σ i) (τ.val i))
    · apply Finset.sum_congr rfl
      intro a _
      exact sum_powers k k_order (fun τ => ∏ i, H ((g ^ a.val) i) (τ i))
  · norm_num [H, V, g, k, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.prod_univ_succ, pow_succ, Equiv.Perm.mul_apply,
      map_ofNat]

/-- No positive constant can satisfy the complete main assertion. -/
theorem result : ¬ claim := by
  intro h
  obtain ⟨c, hc, hbound⟩ := h 7 G K
  have hb := hbound H H_posSemidef.1 H_posSemidef
  rw [H_diagonal, H_crossSum] at hb
  norm_num at hb
  linarith

end

end D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
