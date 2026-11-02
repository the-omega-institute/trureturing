/- GID: D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cyclic shifts give the second family in every dimension. -/

import D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! Cyclic shifts give difference labels, while sum-indexed shield vectors supply the
partial-transpose certificate. -/

set_option autoImplicit false
open scoped BigOperators
open Matrix

namespace D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions

noncomputable section

def multiplicity {d : ℕ} (a : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : ℕ :=
  Fintype.card {p : Fin d × Fin d // a p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m}

def tVec {d : ℕ} (a : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : Fin d × Fin d → ℂ := fun p =>
  if a p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m then
    (a p.1 p.2 : ℂ) / Real.sqrt d
  else 0

def IsSecondFamilyData (d : ℕ) (q : Fin d → Matrix (Fin d) (Fin d) ℝ)
    (qbar : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (a : Fin d → Fin d → ℝ) (s : Fin d → Fin d × Fin d → ℂ) : Prop :=
  (∀ j, (q j)ᵀ * q j = 1) ∧
  (∀ m n, ∑ k, qbar m k * qbar n k = if m = n then 1 else 0) ∧
  (∀ i j k, q k i j = a i j * qbar (μ i j) k) ∧
  (∀ i j, a i j ≠ 0 → a i j ^ 2 = (d : ℝ) / multiplicity a μ (μ i j)) ∧
  (∀ m n, ∑ x, star (s m x) * s n x = if m = n then 1 else 0) ∧
  D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
      (∑ m, Matrix.vecMulVec (s m) (star (s m))) =
    ∑ m, Matrix.vecMulVec (tVec a μ m) (star (tVec a μ m))

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ q qbar μ a s, IsSecondFamilyData d q qbar μ a s

private def cyclicQ (d : ℕ) (k : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  Equiv.Perm.permMatrix ℝ (finCycle k)

private def cyclicMu (d : ℕ) : Fin d → Fin d → Fin d := fun i j => j - i

private def cyclicS (d : ℕ) : Fin d → Fin d → ℝ := fun _ _ => 1

private def cyclicQbar (d : ℕ) : Fin d → Fin d → ℝ :=
  fun m k => if k = m then 1 else 0

private def cyclicShield (d : ℕ) : Fin d → Fin d × Fin d → ℂ :=
  fun m p => if p.1 + p.2 = m then (Real.sqrt d : ℂ)⁻¹ else 0

private theorem cyclic_shift_factor (d : ℕ) (i j k : Fin d) :
    i + k = j ↔ k = cyclicMu d i j := by
  have := i.neZero
  simp only [cyclicMu, eq_sub_iff_add_eq, add_comm]

private theorem cyclic_q_orthogonal (d : ℕ) (k : Fin d) :
    (cyclicQ d k)ᵀ * cyclicQ d k = 1 := by
  change (Equiv.Perm.permMatrix ℝ (finCycle k))ᵀ *
    Equiv.Perm.permMatrix ℝ (finCycle k) = 1
  rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
  simp

private theorem cyclic_q_factorization (d : ℕ) :
    ∀ i j k, cyclicQ d k i j = cyclicS d i j * cyclicQbar d (cyclicMu d i j) k := by
  intro i j k
  delta cyclicQ cyclicS cyclicQbar
  simp [Equiv.Perm.permMatrix, cyclic_shift_factor d i j k]

private def cyclicFiberEquiv (d : ℕ) (m : Fin d) :
    {p : Fin d × Fin d // cyclicS d p.1 p.2 ≠ 0 ∧ cyclicMu d p.1 p.2 = m} ≃ Fin d :=
  { toFun := fun p => p.1.1
    invFun := fun i => ⟨(i, finCycle m i), by
      refine ⟨by change (1 : ℝ) ≠ 0; simp, ?_⟩
      have hm := (cyclic_shift_factor d i (finCycle m i) m).mp ?_
      · exact hm.symm
      · rfl⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext
      · rfl
      · have hm : m = cyclicMu d p.1.1 p.1.2 := p.2.2.symm
        have hs := (cyclic_shift_factor d p.1.1 p.1.2 m).mpr hm
        exact hs
    right_inv := by intro i; rfl }

private theorem cyclic_multiplicity (d : ℕ) (h : 2 ≤ d) (i j : Fin d) :
    (cyclicS d i j) ^ 2 = (d : ℝ) / multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j) := by
  have hc : multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j) = d := by
    delta multiplicity
    simpa only [Fintype.card_fin] using Fintype.card_congr
      (cyclicFiberEquiv d (cyclicMu d i j))
  have hd : (d : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by omega) h))
  change (1 : ℝ) ^ 2 =
    (d : ℝ) / multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j)
  simp [hc, hd]

private theorem cyclic_qbar_orthonormal (d : ℕ) :
    ∀ m n, ∑ k, cyclicQbar d m k * cyclicQbar d n k = if m = n then 1 else 0 := by
  classical
  intro m n
  delta cyclicQbar
  by_cases hmn : m = n
  · subst n
    simp
  · have hnm : n ≠ m := Ne.symm hmn
    simp [hmn, hnm]

private theorem cyclic_shield_orthonormal (d : ℕ) (h : 2 ≤ d) :
    ∀ m n, ∑ x, star (cyclicShield d m x) * cyclicShield d n x = if m = n then 1 else 0 := by
  classical
  have hp : 0 < d := by omega
  let : NeZero d := ⟨Nat.ne_of_gt hp⟩
  intro m n
  have hi (i : Fin d) :
      (∑ j : Fin d, star (cyclicShield d m (i, j)) * cyclicShield d n (i, j)) =
        if m = n then ((Real.sqrt d : ℂ)⁻¹) ^ 2 else 0 := by
    change (∑ j : Fin d,
      star (if i + j = m then (Real.sqrt d : ℂ)⁻¹ else 0) *
        (if i + j = n then (Real.sqrt d : ℂ)⁻¹ else 0)) = _
    have he := Equiv.sum_comp (Equiv.addLeft i) (fun j : Fin d =>
      star (if j = m then (Real.sqrt d : ℂ)⁻¹ else 0) *
        (if j = n then (Real.sqrt d : ℂ)⁻¹ else 0))
    simp only [Equiv.coe_addLeft] at he
    refine he.trans ?_
    by_cases hmn : m = n
    · subst n
      simp [← pow_two]
    · simp [hmn, Ne.symm hmn]
  rw [Fintype.sum_prod_type]
  simp_rw [hi]
  have hs : (Real.sqrt d : ℂ) ^ 2 = (d : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg d)
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hp
  by_cases hmn : m = n <;> simp [hmn, inv_pow, hs, hd]

private theorem cyclic_partial_transpose (d : ℕ) :
    D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
        (∑ m, Matrix.vecMulVec (cyclicShield d m) (star (cyclicShield d m))) =
      ∑ m, Matrix.vecMulVec (tVec (cyclicS d) (cyclicMu d) m)
        (star (tVec (cyclicS d) (cyclicMu d) m)) := by
  classical
  apply Matrix.ext
  intro p q
  have := p.1.neZero
  have heq : q.1 + p.2 = p.1 + q.2 ↔ q.2 - q.1 = p.2 - p.1 := by
    rw [sub_eq_sub_iff_add_eq_add]
    constructor <;> intro hh <;> simpa only [add_comm] using hh.symm
  delta D5.S3.Quantum.Entanglement.AbsolutePPT.Bipartite.partialTranspose
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply]
  delta cyclicShield tVec cyclicS
  simp [cyclicMu, ite_mul, heq]

private theorem cyclic_data (d : ℕ) (h : 2 ≤ d) :
    IsSecondFamilyData d (cyclicQ d) (cyclicQbar d) (cyclicMu d) (cyclicS d)
      (cyclicShield d) := by
  refine ⟨?_, cyclic_qbar_orthonormal d, cyclic_q_factorization d, ?_,
    cyclic_shield_orthonormal d h, cyclic_partial_transpose d⟩
  · intro j
    exact cyclic_q_orthogonal d j
  · intro i j _
    exact cyclic_multiplicity d h i j

theorem result : claim := by
  intro d hd
  exact ⟨cyclicQ d, cyclicQbar d, cyclicMu d, cyclicS d, cyclicShield d,
    cyclic_data d hd⟩

end
end D5.S3.Quantum.Entanglement.BoundEntanglement.SecondFamilyAllDimensions
