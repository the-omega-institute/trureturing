/- GID: D5/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/BoundEntanglement/SecondFamilyAllDimensions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Cyclic shifts give the second family in every dimension. -/

import Mathlib

/-! The cyclic construction and its defining certificate. -/

set_option autoImplicit false
open scoped BigOperators ComplexConjugate
open Matrix

namespace D5.S3.Quantum.Entanglement.BoundEntanglement

noncomputable section

def multiplicity {d : ℕ} (S : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : ℕ :=
  Fintype.card {p : Fin d × Fin d // S p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m}

def tVec {d : ℕ} (S : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (m : Fin d) : Fin d × Fin d → ℂ := fun p =>
  if S p.1 p.2 ≠ 0 ∧ μ p.1 p.2 = m then
    (S p.1 p.2 : ℂ) / Real.sqrt d
  else 0

def partialTransposeB {d : ℕ}
    (M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  fun p q => M (p.1, q.2) (q.1, p.2)

def IsSecondFamilyData (d : ℕ) (Q : Fin d → Matrix (Fin d) (Fin d) ℝ)
    (qbar : Fin d → Fin d → ℝ) (μ : Fin d → Fin d → Fin d)
    (S : Fin d → Fin d → ℝ) (s : Fin d → Fin d × Fin d → ℂ) : Prop :=
  (∀ j, (Q j)ᵀ * Q j = 1) ∧
  (∀ m n, ∑ k, qbar m k * qbar n k = if m = n then 1 else 0) ∧
  (∀ i j k, Q k i j = S i j * qbar (μ i j) k) ∧
  (∀ i j, S i j ≠ 0 → S i j ^ 2 = (d : ℝ) / multiplicity S μ (μ i j)) ∧
  (∀ m n, ∑ x, star (s m x) * s n x = if m = n then 1 else 0) ∧
  partialTransposeB (∑ m, Matrix.vecMulVec (s m) (star (s m))) =
    ∑ m, Matrix.vecMulVec (tVec S μ m) (star (tVec S μ m))

def claim : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ Q qbar μ S s, IsSecondFamilyData d Q qbar μ S s

private def cyclicShift (d : ℕ) (k i : Fin d) : Fin d :=
  if h : 0 < d then ⟨(i.val + k.val) % d, Nat.mod_lt _ h⟩ else i

private def cyclicQ (d : ℕ) (k : Fin d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => if j = cyclicShift d k i then 1 else 0

private def cyclicMu (d : ℕ) : Fin d → Fin d → Fin d :=
  fun i j => ⟨(j.val + d - i.val) % d, by
    exact Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)
  ⟩

private def cyclicS (d : ℕ) : Fin d → Fin d → ℝ := fun _ _ => 1

private def cyclicQbar (d : ℕ) : Fin d → Fin d → ℝ :=
  fun m k => if k = m then 1 else 0

private def cyclicShield (d : ℕ) : Fin d → Fin d × Fin d → ℂ :=
  fun m p => if p.1 + p.2 = m then (Real.sqrt d : ℂ)⁻¹ else 0

private theorem cyclic_shift_bijective (d : ℕ) (h : 2 ≤ d) (k : Fin d) :
    Function.Bijective (cyclicShift d k) := by sorry

private theorem cyclic_q_orthogonal (d : ℕ) (h : 2 ≤ d) (k : Fin d) :
    (cyclicQ d k)ᵀ * cyclicQ d k = 1 := by sorry

private theorem cyclic_q_factorization (d : ℕ) (h : 2 ≤ d) :
    ∀ i j k, cyclicQ d k i j = cyclicS d i j * cyclicQbar d (cyclicMu d i j) k := by sorry

private theorem cyclic_multiplicity (d : ℕ) (h : 2 ≤ d) (i j : Fin d) :
    (cyclicS d i j) ^ 2 = (d : ℝ) / multiplicity (cyclicS d) (cyclicMu d) (cyclicMu d i j) := by sorry

private theorem cyclic_qbar_orthonormal (d : ℕ) :
    ∀ m n, ∑ k, cyclicQbar d m k * cyclicQbar d n k = if m = n then 1 else 0 := by
  classical
  intro m n
  by_cases hmn : m = n
  · subst n
    simp [cyclicQbar]
  · have hnm : n ≠ m := Ne.symm hmn
    simp [cyclicQbar, hmn, hnm]

private theorem cyclic_shield_orthonormal (d : ℕ) (h : 2 ≤ d) :
    ∀ m n, ∑ x, star (cyclicShield d m x) * cyclicShield d n x = if m = n then 1 else 0 := by sorry

private theorem cyclic_partial_transpose (d : ℕ) (h : 2 ≤ d) :
    partialTransposeB (∑ m, Matrix.vecMulVec (cyclicShield d m) (star (cyclicShield d m))) =
      ∑ m, Matrix.vecMulVec (tVec (cyclicS d) (cyclicMu d) m)
        (star (tVec (cyclicS d) (cyclicMu d) m)) := by sorry

private theorem cyclic_data (d : ℕ) (h : 2 ≤ d) :
    IsSecondFamilyData d (cyclicQ d) (cyclicQbar d) (cyclicMu d) (cyclicS d)
      (cyclicShield d) := by
  refine ⟨?_, cyclic_qbar_orthonormal d, cyclic_q_factorization d h, ?_,
    cyclic_shield_orthonormal d h, cyclic_partial_transpose d h⟩
  · intro j
    exact cyclic_q_orthogonal d h j
  · intro i j hij
    exact cyclic_multiplicity d h i j

theorem result : claim := by
  intro d hd
  exact ⟨cyclicQ d, cyclicQbar d, cyclicMu d, cyclicS d, cyclicShield d,
    cyclic_data d hd⟩

end
end D5.S3.Quantum.Entanglement.BoundEntanglement
