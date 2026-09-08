/- GID: D5/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension
   generality: G
   mirror-B: D5/B/S3/Quantum/FockSpace/ForbiddenNeighbourTraceExtension
   mirror-E: none(waiver:arbitrary-degree-symbolic-identity)
   anchors: []
   utility: none
   digest: Nonnegative bidiagonal weights have fixed trace and zero-tail extension rigidity. -/

import D5.S3.Quantum.FockSpace.ForbiddenNeighbourDeterminant
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.FockSpace.ForbiddenNeighbourTraceExtension

open Polynomial
open ForbiddenNeighbourDeterminant

/-- Both Gram orders have trace equal to the sum of the actual nonnegative weights. -/
theorem lower_bidiagonal_trace_weights (d : ℕ) (hd : 1 ≤ d)
    (w : Fin (2 * d - 1) → ℝ) (hw : ∀ i, 0 ≤ w i) :
    Matrix.trace (lowerBidiagonal w * (lowerBidiagonal w).transpose) = ∑ i, w i ∧
    Matrix.trace ((lowerBidiagonal w).transpose * lowerBidiagonal w) = ∑ i, w i := by
  classical
  let a : ℕ → ℝ := fun k => if h : k < 2 * d - 1 then w ⟨k, h⟩ else 0
  have hsquare (i j : Fin d) : lowerBidiagonal w i j * lowerBidiagonal w i j =
      (if i = j then a (2 * j.val) else 0) +
      (if i.val = j.val + 1 then a (2 * j.val + 1) else 0) := by
    by_cases hij : i = j
    · subst i
      have hb : 2 * j.val < 2 * d - 1 := by omega
      simp [lowerBidiagonal, a, hb, ← pow_two, Real.sq_sqrt (hw _)]
    · by_cases hs : j.val + 1 = i.val
      · have hb : 2 * j.val + 1 < 2 * d - 1 := by omega
        simp only [lowerBidiagonal, if_neg hij, dif_pos hs, if_pos hs.symm,
          zero_add, a, dif_pos hb]
        simpa only [pow_two] using Real.sq_sqrt (hw ⟨2 * j.val + 1, hb⟩)
      · simp [lowerBidiagonal, hij, hs, Ne.symm hs]
  have hcolumn (j : Fin d) :
      (∑ i, lowerBidiagonal w i j * lowerBidiagonal w i j) =
        a (2 * j.val) + a (2 * j.val + 1) := by
    simp_rw [hsquare]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    by_cases hj : j.val + 1 < d
    · have heq (i : Fin d) : i.val = j.val + 1 ↔ i = ⟨j.val + 1, hj⟩ :=
        ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
      simp_rw [heq]
      simp
    · have hz (i : Fin d) : i.val ≠ j.val + 1 := by omega
      have hb : ¬2 * j.val + 1 < 2 * d - 1 := by omega
      simp [hz, a, hb]
  have hsplit (k : ℕ) : (∑ i ∈ Finset.range (2 * k), a i) =
      ∑ j ∈ Finset.range k, (a (2 * j) + a (2 * j + 1)) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, show 2 * k + 2 = (2 * k + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      ring
  have hsum : (∑ j : Fin d, (a (2 * j.val) + a (2 * j.val + 1))) = ∑ i, w i := by
    rw [← Finset.sum_range (n := d) (fun j => a (2 * j) + a (2 * j + 1)), ← hsplit d]
    have hlen : 2 * d = (2 * d - 1) + 1 := by omega
    conv_lhs => rw [hlen, Finset.sum_range_succ]
    simp only [a, lt_self_iff_false, dite_false, add_zero]
    rw [Finset.sum_range]
    apply Finset.sum_congr rfl
    intro i _
    simp [i.isLt]
  have htrace : Matrix.trace (lowerBidiagonal w * (lowerBidiagonal w).transpose) = ∑ i, w i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp_rw [hcolumn]
    exact hsum
  refine ⟨htrace, ?_⟩
  rw [Matrix.trace_mul_comm]
  exact htrace

/-- An unchanged nonnegative prefix with fixed total forces both appended weights to zero. -/
theorem unchanged_weights_zero_append (d : ℕ) (hd : 1 ≤ d)
    (w : Fin (2 * d - 1) → ℝ) (u : Fin (2 * (d + 1) - 1) → ℝ)
    (hu : ∀ i, 0 ≤ u i)
    (hprefix : ∀ i : Fin (2 * d - 1), u ⟨i.val, by omega⟩ = w i)
    (htotal : (∑ i, u i) = ∑ i, w i) :
    u ⟨2 * d - 1, by omega⟩ = 0 ∧ u ⟨2 * d, by omega⟩ = 0 ∧
    (lowerBidiagonal u).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (lowerBidiagonal w) 0 0 (0 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    forbiddenPartition u = forbiddenPartition w := by
  classical
  let k : ℕ := 2 * d - 2
  have hlen : k + 3 = 2 * (d + 1) - 1 := by dsimp [k]; omega
  have hshort : k + 1 = 2 * d - 1 := by dsimp [k]; omega
  let v : Fin (k + 3) → ℝ := fun i => u (Fin.cast hlen i)
  have hv (i : Fin (k + 1)) : v i.castSucc.castSucc = w (Fin.cast hshort i) :=
    hprefix (Fin.cast hshort i)
  have hlast : v (Fin.last (k + 2)) = u ⟨2 * d, by omega⟩ := by
    apply congrArg u
    apply Fin.ext
    dsimp [k]
    omega
  have hprev : v (Fin.last (k + 1)).castSucc = u ⟨2 * d - 1, by omega⟩ := by
    apply congrArg u
    apply Fin.ext
    dsimp [k]
    omega
  have hold : (∑ i : Fin (k + 1), v i.castSucc.castSucc) = ∑ i, w i := by
    simp only [hv]
    exact (finCongr hshort).sum_comp w
  have hmass := htotal
  rw [← (finCongr hlen).sum_comp u] at hmass
  change (∑ i : Fin (k + 3), v i) = ∑ i, w i at hmass
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, hold, hlast, hprev] at hmass
  have hu1 : u ⟨2 * d - 1, by omega⟩ = 0 := by
    have ha := hu ⟨2 * d - 1, by omega⟩
    have hb := hu ⟨2 * d, by omega⟩
    linarith
  have hu2 : u ⟨2 * d, by omega⟩ = 0 := by
    have ha := hu ⟨2 * d - 1, by omega⟩
    have hb := hu ⟨2 * d, by omega⟩
    linarith
  have hleft (i j : Fin d) : lowerBidiagonal u i.castSucc j.castSucc = lowerBidiagonal w i j := by
    by_cases hij : i = j
    · subst j
      simp only [lowerBidiagonal, if_true, Fin.val_castSucc]
      exact congrArg Real.sqrt (hprefix ⟨2 * i.val, by omega⟩)
    · by_cases hs : j.val + 1 = i.val
      · simp only [lowerBidiagonal, Fin.castSucc_inj, if_neg hij, Fin.val_castSucc, dif_pos hs]
        exact congrArg Real.sqrt (hprefix ⟨2 * j.val + 1, by omega⟩)
      · simp only [lowerBidiagonal, Fin.castSucc_inj, if_neg hij, Fin.val_castSucc, dif_neg hs]
  have hrow (i : Fin (d + 1)) : lowerBidiagonal u (Fin.last d) i = 0 := by
    unfold lowerBidiagonal
    split_ifs with hi hs
    · simp only [Fin.val_last, hu2, Real.sqrt_zero]
    · have heq : 2 * i.val + 1 = 2 * d - 1 := by
        change i.val + 1 = d at hs
        omega
      simp only [heq, hu1, Real.sqrt_zero]
    · rfl
  have hcol (i : Fin (d + 1)) : lowerBidiagonal u i (Fin.last d) = 0 := by
    unfold lowerBidiagonal
    split_ifs with hi hs
    · subst i
      simp only [Fin.val_last, hu2, Real.sqrt_zero]
    · have := i.isLt
      change d + 1 = i.val at hs
      omega
    · rfl
  have hblock : (lowerBidiagonal u).submatrix finSumFinEquiv finSumFinEquiv =
      Matrix.fromBlocks (lowerBidiagonal w) 0 0 (0 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b
    · exact hleft a b
    · have hb : b = 0 := Subsingleton.elim _ _
      subst b
      exact hcol a.castSucc
    · have ha : a = 0 := Subsingleton.elim _ _
      subst a
      exact hrow b.castSucc
    · have ha : a = 0 := Subsingleton.elim _ _
      have hb : b = 0 := Subsingleton.elim _ _
      subst a
      subst b
      exact hrow (Fin.last d)
  refine ⟨hu1, hu2, hblock, ?_⟩
  have hw (i : Fin (2 * d - 1)) : 0 ≤ w i := by rw [← hprefix i]; exact hu _
  have hrec := (forbidden_neighbour_determinant hd w hw).2.2.2.2.2.2.2.1
  have hcast {n m : ℕ} (h : n = m) (a : Fin n → ℝ) :
      forbiddenPartition (fun i : Fin m => a (Fin.cast h.symm i)) = forbiddenPartition a := by
    subst m
    rfl
  have hp1 : forbiddenPartition v = forbiddenPartition (fun i : Fin (k + 2) => v i.castSucc) := by
    rw [hrec (k + 1) v, hlast, hu2, C_0, mul_zero, zero_mul, add_zero]
  have hp2 : forbiddenPartition (fun i : Fin (k + 2) => v i.castSucc) =
      forbiddenPartition (fun i : Fin (k + 1) => v i.castSucc.castSucc) := by
    rw [hrec k (fun i : Fin (k + 2) => v i.castSucc), hprev, hu1,
      C_0, mul_zero, zero_mul, add_zero]
  have hpu : forbiddenPartition v = forbiddenPartition u := hcast hlen.symm u
  have hpw : forbiddenPartition (fun i : Fin (k + 1) => v i.castSucc.castSucc) =
      forbiddenPartition w := by
    simp only [hv]
    exact hcast hshort.symm w
  exact hpu.symm.trans (hp1.trans (hp2.trans hpw))

end D5.S3.Quantum.FockSpace.ForbiddenNeighbourTraceExtension
