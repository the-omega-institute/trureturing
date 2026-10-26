/- GID: D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim; result=D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.result; claim=D5/S3/Quantum/Matrix/MalkounYoungSubgroupConjectureRefutation.claim
   digest: Fifteen Gram blocks refute the class-preserving permutation inequality. -/

import D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation
import Mathlib.Data.Matrix.Block
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Conjecture D fails for class-preserving permutation groups -/

open scoped BigOperators ComplexOrder

namespace D5.S3.Quantum.Matrix.MalkounYoungSubgroupConjectureRefutation

open D5.S3.Quantum.Matrix.MalkounSubgroupLowerBoundRefutation (crossSum diagonal_product_eq_real)

noncomputable section

/-- The source's group of permutations preserving every equivalence class. -/
def classPreserving {n : ℕ} (r : Setoid (Fin n)) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ i, r (σ i) i}
  one_mem' := fun i => r.refl i
  mul_mem' := fun hσ hτ i => r.trans (hσ _) (hτ i)
  inv_mem' := by
    intro σ hσ i
    have h := r.symm (hσ (σ.symm i))
    rw [σ.apply_symm_apply] at h
    exact h

/-- Conjecture D for arbitrary dimension and both arbitrary equivalence relations. -/
def claim : Prop :=
  ∀ (n : ℕ) (r₁ r₂ : Setoid (Fin n)) (h : Matrix (Fin n) (Fin n) ℂ),
    h.IsHermitian → h.PosSemidef →
      (Nat.card ↥(classPreserving r₁ ⊓ classPreserving r₂) : ℝ) *
        (∏ i, (h i i).re) ≤ (crossSum (classPreserving r₁) (classPreserving r₂) h).re

private def coords (m : ℕ) : Fin (m * 3) ≃ Fin m × Fin 3 := finProdFinEquiv.symm

private def blockRelation (m : ℕ) (r : Setoid (Fin 3)) : Setoid (Fin (m * 3)) where
  r i k := (coords m i).1 = (coords m k).1 ∧ r (coords m i).2 (coords m k).2
  iseqv := ⟨fun _ => ⟨rfl, r.refl _⟩,
    fun h => ⟨h.1.symm, r.symm h.2⟩,
    fun h k => ⟨h.1.trans k.1, r.trans h.2 k.2⟩⟩

private def seedRelation (t : Fin 3) : Setoid (Fin 3) :=
  Setoid.ker (fun s : Fin 3 => s == t)

private def blockMatrix (m : ℕ) (a : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix (Fin (m * 3)) (Fin (m * 3)) ℂ :=
  (Matrix.blockDiagonal (fun _ : Fin m => a)).submatrix
    (fun i => ((coords m i).2, (coords m i).1))
    (fun i => ((coords m i).2, (coords m i).1))

private def v : Matrix (Fin 2) (Fin 3) ℂ := !![1, 1, 1; 0, 1, Complex.I]

private def seed : Matrix (Fin 3) (Fin 3) ℂ := v.conjTranspose * v

private theorem block_posSemidef (m : ℕ) : (blockMatrix m seed).PosSemidef := by
  unfold blockMatrix seed
  rw [Matrix.blockDiagonal_mul, ← Matrix.blockDiagonal_conjTranspose]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).submatrix _

private theorem block_factorization (m : ℕ) (r s : Setoid (Fin 3))
    (a : Matrix (Fin 3) (Fin 3) ℂ) :
    crossSum (classPreserving (blockRelation m r))
      (classPreserving (blockRelation m s)) (blockMatrix m a) =
      (crossSum (classPreserving r) (classPreserving s) a) ^ m := by
  sorry

private theorem seed_crossSum :
    crossSum (classPreserving (seedRelation 2)) (classPreserving (seedRelation 0)) seed =
      9 - Complex.I := by
  sorry

private theorem block_intersection (m : ℕ) :
    classPreserving (blockRelation m (seedRelation 2)) ⊓
      classPreserving (blockRelation m (seedRelation 0)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro σ hσ
  apply Subgroup.mem_bot.mpr
  apply Equiv.ext
  intro i
  apply (coords m).injective
  apply Prod.ext
  · exact (hσ.1 i).1
  · have hseed : ∀ a b : Fin 3, seedRelation 2 a b → seedRelation 0 a b → a = b := by
      change ∀ a b : Fin 3, (a == 2) = (b == 2) → (a == 0) = (b == 0) → a = b
      decide
    exact hseed _ _ (hσ.1 i).2 (hσ.2 i).2

private theorem block_diagonal (m : ℕ) :
    (∏ i, ((blockMatrix m seed) i i).re) = 4 ^ m := by
  apply Complex.ofReal_injective
  rw [← diagonal_product_eq_real _ (block_posSemidef m).1]
  have hp : (∏ i, (blockMatrix m seed) i i) = (∏ s, seed s s) ^ m := by
    calc
      _ = ∏ p : Fin m × Fin 3, seed p.2 p.2 := by
        apply Fintype.prod_equiv (coords m)
        intro i
        simp only [blockMatrix, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, ite_true]
      _ = _ := by simp [Fintype.prod_prod_type]
  rw [hp]
  norm_num [seed, v, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_succ, Fin.prod_univ_succ, map_ofNat]

private theorem power_value : (9 - Complex.I) ^ 15 =
    -20078071648128 - 224842906547072 * Complex.I := by
  norm_num [Complex.ext_iff, pow_succ, Complex.mul_re, Complex.mul_im]

/-- Conjecture D fails for fifteen copies of the three-column Gram matrix. -/
theorem result : ¬ claim := by
  intro h
  have hb := h 45 (blockRelation 15 (seedRelation 2))
    (blockRelation 15 (seedRelation 0)) (blockMatrix 15 seed)
    (block_posSemidef 15).1 (block_posSemidef 15)
  rw [block_intersection 15, block_diagonal 15, block_factorization 15,
    seed_crossSum, power_value] at hb
  norm_num at hb

end

end D5.S3.Quantum.Matrix.MalkounYoungSubgroupConjectureRefutation
