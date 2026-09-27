/- GID: D5/S3/VertexAlgebra/HeisenbergModeLocality
   generality: G
   mirror-B: D5/B/S3/VertexAlgebra/HeisenbergModeLocality
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Heisenberg modes on Mathlib vertex operators have sharp second-order locality. -/

/-
proof_shape: heisenberg_mode_locality: content
escape_witness: form (2), the public conclusion identifies the first coefficient shift on
  the entire integer plane, proves its second shift vanishes, and recovers the central
  endomorphism at a specified coefficient. This derives locality from the mode relation.
admission_basis: escape-witness
Direct frozen dependencies: none; the vertex-operator carrier is pinned Mathlib.
-/

import Mathlib.Algebra.Vertex.VertexOperator
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.VertexAlgebra.HeisenbergModeLocality

open scoped VertexOperator

/-!
Chu and Lin, *Moduli spaces of conformal structures on Heisenberg vertex algebras*,
arXiv:1812.11378v1, section 3.1, give the Heisenberg mode bracket and the expansion
`Y(h,z) = sum_n h(n) z^(-n-1)`. Kac, *Vertex Algebras for Beginners* (1998),
DOI 10.1090/ulect/010, is foundational background. This module derives the finite-difference
locality implication for Mathlib's `VertexOperator` and its actual normalized `ncoeff` modes.
-/

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- Multiplication by `z-w` on two-variable coefficients in normalized mode indexing. -/
def coefficientShift {E : Type*} [AddCommGroup E] (F : ℤ → ℤ → E) : ℤ → ℤ → E :=
  fun m n => F (m + 1) n - F m (n + 1)

/-- The two-variable commutator coefficients of a Mathlib vertex operator. -/
noncomputable def modeCommutator (A : VertexOperator ℚ V) :
    ℤ → ℤ → Module.End ℚ V :=
  fun m n => (A[[m]]).comp (A[[n]]) - (A[[n]]).comp (A[[m]])

/-- The Heisenberg relation gives second-order locality, and its central endomorphism is
exactly the obstruction to first-order locality. The same normalized modes are supplied by
`VertexOperator.ncoeff`; no locality hypothesis is assumed. -/
theorem heisenberg_mode_locality (A : VertexOperator ℚ V) (K : Module.End ℚ V)
    (hCCR : ∀ m n : ℤ, modeCommutator A m n =
      if m + n = 0 then (m : ℚ) • K else 0) :
    (∀ m n : ℤ, coefficientShift (coefficientShift (modeCommutator A)) m n = 0) ∧
    coefficientShift (modeCommutator A) 0 (-1) = K ∧
    ((∀ m n : ℤ, coefficientShift (modeCommutator A) m n = 0) ↔ K = 0) := by
  have hfirst (m n : ℤ) : coefficientShift (modeCommutator A) m n =
      if m + n + 1 = 0 then K else 0 := by
    simp only [coefficientShift]
    rw [hCCR (m + 1) n, hCCR m (n + 1)]
    by_cases hsum : m + n + 1 = 0
    · have hleft : m + 1 + n = 0 := by omega
      have hright : m + (n + 1) = 0 := by omega
      simp only [if_pos hleft, if_pos hright, if_pos hsum,
        Int.cast_add, Int.cast_one, add_smul, one_smul]
      abel
    · have hleft : m + 1 + n ≠ 0 := by omega
      have hright : m + (n + 1) ≠ 0 := by omega
      simp only [if_neg hleft, if_neg hright, if_neg hsum, sub_self]
  have hsecond (m n : ℤ) :
      coefficientShift (coefficientShift (modeCommutator A)) m n = 0 := by
    change coefficientShift (modeCommutator A) (m + 1) n -
      coefficientShift (modeCommutator A) m (n + 1) = 0
    rw [hfirst (m + 1) n, hfirst m (n + 1)]
    have hindex : m + 1 + n + 1 = m + (n + 1) + 1 := by omega
    rw [hindex, sub_self]
  have hpoint : coefficientShift (modeCommutator A) 0 (-1) = K := by
    simpa using hfirst 0 (-1)
  refine ⟨hsecond, hpoint, ?_⟩
  constructor
  · intro hall
    simpa only [hpoint] using hall 0 (-1)
  · intro hzero m n
    simp [hfirst, hzero]

end D5.S3.VertexAlgebra.HeisenbergModeLocality
