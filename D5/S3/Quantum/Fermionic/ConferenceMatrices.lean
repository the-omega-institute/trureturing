/- GID: D5/S3/Quantum/Fermionic/ConferenceMatrices
   generality: G
   mirror-B: D5/B/S3/Quantum/Fermionic/ConferenceMatrices
   mirror-E: none(waiver:general-recursive-matrix-family)
   anchors: [mathlib/module/Mathlib.Data.Matrix.Block]
   utility: none
   digest: Recursive skew conference matrices have order a power of two and flat square. -/

/-
conference_properties:
  proof_shape: content
  escape_witness: conference_properties (form 2): induction constructs a sign matrix of
    each power-of-two order, preserving skewness and its scalar square.
admission_basis: escape-witness
Same-delivery inlined content: local declarations.
Direct frozen public dependencies after inlining same-delivery content:
  none; remaining prerequisites are pinned Mathlib declarations.
computational_content.kind: none; the statement is uniform in an unbounded recursive order,
  not a bounded enumeration, checker, numerical reduction or certified finite instance.
Information-escape registration is paused under CLAUDE.md §3.9.
-/

import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NoncommRing

open Matrix
open scoped Matrix

namespace D5.S3.Quantum.Fermionic.ConferenceMatrices

/-- The initial two labels are doubled at each recursive step. -/
def Index : ℕ → Type
  | 0 => Fin 2
  | r + 1 => Index r ⊕ Index r

/-- The recursive label type has the ordinary finite sum enumeration. -/
instance indexFintype : (r : ℕ) → Fintype (Index r)
  | 0 => inferInstanceAs (Fintype (Fin 2))
  | r + 1 =>
    letI := indexFintype r
    inferInstanceAs (Fintype (Index r ⊕ Index r))

/-- Equality of recursive labels uses equality in their finite sum type. -/
instance indexDecidableEq : (r : ℕ) → DecidableEq (Index r)
  | 0 => inferInstanceAs (DecidableEq (Fin 2))
  | r + 1 =>
    letI := indexDecidableEq r
    inferInstanceAs (DecidableEq (Index r ⊕ Index r))

/-- The skew conference family, starting at order two. -/
def conference : (r : ℕ) → Matrix (Index r) (Index r) ℤ
  | 0 => !![0, 1; -1, 0]
  | r + 1 => Matrix.fromBlocks (conference r) (conference r + 1)
      (conference r - 1) (-conference r)

/-- Skewness, signs, order and the exact scalar square hold at every recursive order. -/
theorem conference_properties (r : ℕ) :
    Fintype.card (Index r) = 2 ^ (r + 1) ∧
    (conference r).transpose = -conference r ∧
    (∀ i, conference r i i = 0) ∧
    (∀ i j, i ≠ j → conference r i j = 1 ∨ conference r i j = -1) ∧
    conference r * conference r = (-((Fintype.card (Index r) : ℤ) - 1)) • 1 := by
  induction r with
  | zero =>
    refine ⟨by change Fintype.card (Fin 2) = 2 ^ (0 + 1); norm_num, ?_, ?_, ?_, ?_⟩
    · ext i j
      change conference 0 j i = -(conference 0 i j)
      fin_cases i <;> fin_cases j <;> rfl
    · intro i
      fin_cases i <;> rfl
    · intro i j hij
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · left; rfl
      · right; rfl
      · exact False.elim (hij rfl)
    · ext i j
      change (∑ k : Fin 2, conference 0 i k * conference 0 k j) =
        (-((Fintype.card (Fin 2) : ℤ) - 1)) * (1 : Matrix (Fin 2) (Fin 2) ℤ) i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Fin.sum_univ_two, conference, Matrix.one_apply, Matrix.of_apply]
  | succ r ih =>
    let C := conference r
    let d : ℤ := (Fintype.card (Index r) : ℤ) - 1
    have hc (i j : Index r) : C j i = -C i j :=
      congrFun (congrFun ih.2.1 i) j
    have hsquare : C * C = (-d) • 1 := ih.2.2.2.2
    have h11 : C*C + (C+1)*(C-1) = (-(2*d+1)) • (1 : Matrix (Index r) (Index r) ℤ) := by
      calc
        _ = C*C + C*C - 1 := by noncomm_ring
        _ = _ := by
          rw [hsquare]
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
          ring
    have h12 : C*(C+1) + (C+1)*(-C) = 0 := by noncomm_ring
    have h21 : (C-1)*C + (-C)*(C-1) = 0 := by noncomm_ring
    have h22 : (C-1)*(C+1) + (-C)*(-C) =
        (-(2*d+1)) • (1 : Matrix (Index r) (Index r) ℤ) := by
      calc
        _ = C*C + C*C - 1 := by noncomm_ring
        _ = _ := by
          rw [hsquare]
          ext i j
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
          ring
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change Fintype.card (Index r ⊕ Index r) = 2 ^ ((r + 1) + 1)
      rw [Fintype.card_sum, ih.1, pow_succ]
      ring
    · ext i j
      change conference (r + 1) j i = -(conference (r + 1) i j)
      cases i <;> cases j <;>
        simp only [conference, Matrix.fromBlocks, Matrix.add_apply, Matrix.sub_apply,
          Matrix.neg_apply, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
      all_goals rw [show ∀ i j, conference r j i = -conference r i j from hc]
      all_goals simp only [Matrix.one_apply, eq_comm]
      all_goals split_ifs <;> ring
    · intro i
      cases i <;> simp [conference, Matrix.fromBlocks, ih.2.2.1]
    · intro i j hij
      cases i with
      | inl i =>
        cases j with
        | inl j => exact ih.2.2.2.1 i j (fun h => hij (congrArg Sum.inl h))
        | inr j =>
          by_cases h : i = j
          · subst j
            simp [conference, Matrix.fromBlocks, Matrix.add_apply, ih.2.2.1]
          · simpa [conference, Matrix.fromBlocks, Matrix.add_apply, Matrix.one_apply, h]
              using ih.2.2.2.1 i j h
      | inr i =>
        cases j with
        | inl j =>
          by_cases h : i = j
          · subst j
            simp [conference, Matrix.fromBlocks, Matrix.sub_apply, ih.2.2.1]
          · simpa [conference, Matrix.fromBlocks, Matrix.sub_apply, Matrix.one_apply, h]
              using ih.2.2.2.1 i j h
        | inr j =>
          rcases ih.2.2.2.1 i j (fun h => hij (congrArg Sum.inr h)) with h | h
          · right
            simp [conference, Matrix.fromBlocks, h]
          · left
            simp [conference, Matrix.fromBlocks, h]
    · change Matrix.fromBlocks C (C+1) (C-1) (-C) *
          Matrix.fromBlocks C (C+1) (C-1) (-C) =
          (-((Fintype.card (Index r ⊕ Index r) : ℤ) - 1)) • 1
      rw [Matrix.fromBlocks_multiply, h11, h12, h21, h22]
      have hdeg : -((Fintype.card (Index r ⊕ Index r) : ℤ) - 1) = -(2*d+1) := by
        rw [Fintype.card_sum, Nat.cast_add]
        dsimp [d]
        ring
      rw [hdeg]
      have hz : (0 : Matrix (Index r) (Index r) ℤ) = (-(2*d+1)) • 0 := by simp
      rw [hz, ← Matrix.fromBlocks_smul, Matrix.fromBlocks_one]

end D5.S3.Quantum.Fermionic.ConferenceMatrices
