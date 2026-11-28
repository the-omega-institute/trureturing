/- GID: D5/S3/LinearAlgebra/Matrix/AdjointIrreducibility
   generality: G
   mirror-B: none(waiver:covered-by-su5-so10-grand-unification4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Invariant subspaces of traceless square and rectangular matrices under the matrix actions of the corresponding traceless algebras. -/

import OmegaBuild.Commands
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.NoncommRing

/-! Omega original.

Invariant subspaces of traceless square and rectangular matrices under
the matrix actions of the corresponding traceless algebras. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix

namespace OmegaMath.MatrixAdjoint

variable {K n m : Type*} [Field K] [CharZero K] [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m]

private abbrev unit (i : n) (j : m) : Matrix n m K := single i j 1

private abbrev bracket (A B : Matrix n n K) : Matrix n n K := A * B - B * A

omit [CharZero K] in
private theorem offdiag_trace (i j : n) (h : i ≠ j) : (unit (K := K) i j).trace = 0 := by
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro k _
  change Matrix.single i j (1 : K) k k = 0
  rw [Matrix.single_apply]
  split_ifs with h'
  · exact (h (h'.1.trans h'.2.symm)).elim
  · rfl

omit [CharZero K] [Fintype n] [Fintype m] in
private theorem unit_smul (a : K) (i : n) (j : m) :
    a • (unit (K := K) i j) = single i j a := by
  ext k l
  simp only [Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs <;> simp

omit [CharZero K] in
private theorem double_bracket (A : Matrix n n K) (i j : n) (h : i ≠ j) :
    bracket (unit i j) (bracket (unit i j) A) = (-2 * A j i) • unit i j := by
  let E : Matrix n n K := unit i j
  have hsq : E * E = 0 := Matrix.single_mul_single_of_ne 1 i j i h.symm 1
  have he : E * A * E = A j i • E := by
    simp [E, Matrix.single_mul_mul_single]
  change E * (E * A - A * E) - (E * A - A * E) * E = _
  calc
    _ = (E * E) * A - E * A * E - E * A * E + A * (E * E) := by noncomm_ring
    _ = _ := by
      rw [hsq, he, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_sub, ← neg_smul,
        ← sub_smul]
      congr 1
      ring

private theorem offdiag_from_nondiag (S : Submodule K (Matrix n n K))
    (stable : ∀ A B : Matrix n n K, A.trace = 0 → B ∈ S → bracket A B ∈ S)
    (A : Matrix n n K) (hA : A ∈ S) (i j : n) (hij : i ≠ j) (hji : A j i ≠ 0) :
    unit i j ∈ S := by
  have h := stable (unit i j) _ (offdiag_trace i j hij)
    (stable (unit i j) A (offdiag_trace i j hij) hA)
  rw [double_bracket A i j hij] at h
  have ha : (-2 * A j i) ≠ 0 := mul_ne_zero (by norm_num) hji
  have ht := S.smul_mem (-2 * A j i)⁻¹ h
  rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at ht

private theorem offdiag_flip (S : Submodule K (Matrix n n K))
    (stable : ∀ A B : Matrix n n K, A.trace = 0 → B ∈ S → bracket A B ∈ S)
    (i j : n) (hij : i ≠ j) (h : unit i j ∈ S) : unit j i ∈ S :=
  offdiag_from_nondiag S stable _ h j i hij.symm (by simp)

omit [CharZero K] in
private theorem bracket_diag (d : n → K) (i j : n) :
    bracket (unit i j) (Matrix.diagonal d) = (d j - d i) • unit i j := by
  ext k l
  simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  split_ifs with h
  · rcases h with ⟨rfl, rfl⟩
    simp
  · simp

omit [DecidableEq n] in
private theorem distinct_diag_of_trace_zero (A : Matrix n n K) (ht : A.trace = 0)
    (hd : ∀ i j : n, i ≠ j → A i j = 0) (hA : A ≠ 0) :
    ∃ i j : n, A i i ≠ A j j := by
  classical
  by_contra! h
  apply hA
  ext i j
  by_cases hij : i = j
  · subst j
    have hc : (∑ j : n, A j j) = (Fintype.card n : K) * A i i := by
      simp [h _ i]
    have hn : Fintype.card n ≠ 0 := Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨i⟩)
    have hK : (Fintype.card n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
    change (∑ j : n, A j j) = 0 at ht
    rw [hc] at ht
    exact (mul_eq_zero.mp ht).resolve_left hK
  · exact hd i j hij

omit [CharZero K] in
private theorem tracefree_eq_sum_units (A : Matrix n n K) (ht : A.trace = 0) (k : n) :
    A = (∑ i, ∑ j, if i = j then 0 else A i j • unit i j) +
      ∑ i, A i i • (unit i i - unit k k) := by
  have hdiag : (∑ i, A i i • (unit i i - unit k k)) =
      ∑ i, single i i (A i i) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul]
    change ∑ i, A i i = 0 at ht
    rw [ht, zero_smul, sub_zero]
    simp only [unit_smul]
  rw [hdiag]
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hsum : (∑ j : n, if j = i then single i i (A i i) else 0) = single i i (A i i) := by simp
  rw [← hsum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i = j
  · subst j
    simp
  · simp [h, Ne.symm h]

omit [DecidableEq n] in
/-- The adjoint action on the trace-zero space has only the zero and full
invariant subspaces. -/
theorem tracefree_adjoint_irreducible (S : Submodule K (Matrix n n K))
    (tracefree : ∀ A ∈ S, A.trace = 0)
    (stable : ∀ A B : Matrix n n K, A.trace = 0 → B ∈ S → bracket A B ∈ S) :
    S = ⊥ ∨ ∀ A : Matrix n n K, A.trace = 0 → A ∈ S := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  obtain ⟨A, hA, hne⟩ := (Submodule.ne_bot_iff S).mp hS
  have hex : ∃ i j : n, i ≠ j ∧ unit i j ∈ S := by
    by_cases hd : ∃ i j : n, i ≠ j ∧ A i j ≠ 0
    · obtain ⟨i, j, hij, ha⟩ := hd
      exact ⟨j, i, hij.symm, offdiag_from_nondiag S stable A hA j i hij.symm ha⟩
    push Not at hd
    obtain ⟨i, j, hdij⟩ := distinct_diag_of_trace_zero A (tracefree A hA) hd hne
    have hij : i ≠ j := fun heq => hdij (heq ▸ rfl)
    have hdiag : A = diagonal fun i => A i i := by
      ext p q
      by_cases hpq : p = q
      · subst q
        simp
      · simp [hpq, hd p q hpq]
    have h := stable (unit i j) A (offdiag_trace i j hij) hA
    rw [show bracket (unit i j) A = (A j j - A i i) • unit i j by
      conv_lhs => rw [hdiag]
      exact bracket_diag (fun k => A k k) i j] at h
    have hn := sub_ne_zero.mpr hdij.symm
    have hmem := S.smul_mem (A j j - A i i)⁻¹ h
    rw [smul_smul, inv_mul_cancel₀ hn, one_smul] at hmem
    exact ⟨i, j, hij, hmem⟩
  obtain ⟨i, j, hij, hu⟩ := hex
  have col (p : n) (hp : p ≠ j) : unit p j ∈ S := by
    by_cases hpi : p = i
    · simpa [hpi] using hu
    have h := stable (unit p i) (unit i j) (offdiag_trace p i hpi) hu
    change Matrix.single p i 1 * Matrix.single i j 1 -
      Matrix.single i j 1 * Matrix.single p i 1 ∈ S at h
    rwa [Matrix.single_mul_single_same, one_mul, Matrix.single_mul_single_of_ne 1 i j p
      (Ne.symm hp) 1, sub_zero] at h
  have allUnits (p q : n) (hpq : p ≠ q) : unit p q ∈ S := by
    by_cases hp : p = j
    · subst p
      exact offdiag_flip S stable q j hpq.symm (col q hpq.symm)
    by_cases hq : q = j
    · simpa [hq] using col p hp
    have h := stable (unit j q) (unit p j) (offdiag_trace j q (Ne.symm hq)) (col p hp)
    change Matrix.single j q 1 * Matrix.single p j 1 -
      Matrix.single p j 1 * Matrix.single j q 1 ∈ S at h
    rw [Matrix.single_mul_single_of_ne 1 j q p (Ne.symm hpq) 1,
      Matrix.single_mul_single_same, one_mul, zero_sub] at h
    simpa only [neg_neg] using S.neg_mem h
  refine Or.inr fun B hB => ?_
  rw [tracefree_eq_sum_units B hB j]
  apply S.add_mem
  · apply Submodule.sum_mem
    intro p _
    apply Submodule.sum_mem
    intro q _
    split_ifs with h
    · exact S.zero_mem
    · exact S.smul_mem _ (allUnits p q h)
  · apply Submodule.sum_mem
    intro p _
    apply S.smul_mem
    by_cases hp : p = j
    · simp [hp]
    · have h := stable (unit p j) (unit j p) (offdiag_trace p j hp)
        (allUnits j p (Ne.symm hp))
      simpa [bracket, unit] using h

omit [DecidableEq n] [DecidableEq m] in
/-- Left and right traceless matrix actions have only the zero and full joint
invariant subspaces of a rectangular block. -/
theorem rectangular_irreducible (S : Submodule K (Matrix n m K))
    (left : ∀ (A : Matrix n n K) (X : Matrix n m K), A.trace = 0 → X ∈ S → A * X ∈ S)
    (right : ∀ (B : Matrix m m K) (X : Matrix n m K), B.trace = 0 → X ∈ S → X * B ∈ S) :
    S = ⊥ ∨ S = ⊤ := by
  classical
  by_cases hS : S = ⊥
  · exact Or.inl hS
  obtain ⟨A, hA, hne⟩ := (Submodule.ne_bot_iff S).mp hS
  have hex : ∃ i j, A i j ≠ 0 := by
    by_contra! he
    exact hne (Matrix.ext he)
  obtain ⟨i, j, hij⟩ := hex
  have l (p q : n) (X : Matrix n m K) (hX : X ∈ S) : unit p q * X ∈ S := by
    by_cases hp : p = q
    · subst q
      let c := (Fintype.card n : K)⁻¹
      have hc : (Fintype.card n : K) ≠ 0 := Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨p⟩))
      have hz : (unit p p - c • (1 : Matrix n n K)).trace = 0 := by
        simp [c, smul_eq_mul, inv_mul_cancel₀ hc]
      have hs := S.add_mem (left _ X hz hX) (S.smul_mem c hX)
      simpa [Matrix.sub_mul, Matrix.smul_mul] using hs
    · exact left _ X (offdiag_trace p q hp) hX
  have r (p q : m) (X : Matrix n m K) (hX : X ∈ S) : X * unit p q ∈ S := by
    by_cases hp : p = q
    · subst q
      let c := (Fintype.card m : K)⁻¹
      have hc : (Fintype.card m : K) ≠ 0 := Nat.cast_ne_zero.mpr
        (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨p⟩))
      have hz : (unit p p - c • (1 : Matrix m m K)).trace = 0 := by
        simp [c, smul_eq_mul, inv_mul_cancel₀ hc]
      have hs := S.add_mem (right _ X hz hX) (S.smul_mem c hX)
      simpa [Matrix.mul_sub, Matrix.mul_smul] using hs
    · exact right _ X (offdiag_trace p q hp) hX
  have hunit (p : n) (q : m) : unit p q ∈ S := by
    have h := r j q _ (l p i A hA)
    rw [show unit p i * A * unit j q = A i j • unit p q by
      simp [Matrix.single_mul_mul_single]] at h
    simpa [smul_smul, inv_mul_cancel₀ hij] using S.smul_mem (A i j)⁻¹ h
  refine Or.inr (Submodule.eq_top_iff'.mpr fun B => ?_)
  rw [Matrix.matrix_eq_sum_single B]
  apply Submodule.sum_mem
  intro p _
  apply Submodule.sum_mem
  intro q _
  rw [← unit_smul]
  exact S.smul_mem _ (hunit p q)

end OmegaMath.MatrixAdjoint
