/- GID: D5/S3/Quantum/Thermal/WeylPartialTraceLeakage
   generality: G
   mirror-B: D5/B/S3/Quantum/Thermal/WeylPartialTraceLeakage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Derive the actual bipartite Weyl twirl from reconstruction and prove operator-norm and normalized Hilbert-Schmidt leakage certificates. -/

import D5.S3.Quantum.Algebra.WeylReconstruction
import D5.S3.Quantum.Thermal.UnitaryAverageLeakage
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

/-!
The tested matrices are the repository's actual finite Weyl words tensored
with the identity. Their completeness and the partial-trace twirl are proved,
so the zero-average premise of the general averaging estimate is discharged
from the physical condition Tr_A V = 0. All unadorned matrix norms in this
module are Euclidean operator norms, explicitly selected by the scope below.
The Hilbert-Schmidt square is separately defined by its normalized trace.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Quantum.Thermal.WeylPartialTraceLeakage

open D5.S3.Quantum.Algebra.WeylReconstruction
open D5.S3.Quantum.Algebra.WeylDisplacement
open D5.S3.Quantum.Algebra.WeylDisplacementAdjoint
open D5.S3.Quantum.Thermal.UnitaryAverageLeakage
open Kronecker
open scoped BigOperators Matrix.Norms.L2Operator

variable {M : ℕ} [NeZero M]
variable {b : Type*} [Fintype b] [DecidableEq b]

private theorem dimension_ne_zero : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M

/-- The Weyl words are actual unitary matrices. -/
theorem word_star_mul (p : ZMod M × ZMod M) :
    star (word M p) * word M p = 1 := by
  unfold word displacement
  rw [star_mul, star_clockMatrix_pow, star_shiftMatrix_pow]
  calc
    (D5.S3.Observer.WindowRegister.clockMatrix M ^ (-p.2).val *
      D5.S3.Observer.WindowRegister.shiftMatrix M ^ (-p.1).val) *
      (D5.S3.Observer.WindowRegister.shiftMatrix M ^ p.1.val *
      D5.S3.Observer.WindowRegister.clockMatrix M ^ p.2.val) =
      D5.S3.Observer.WindowRegister.clockMatrix M ^ (-p.2).val *
        ((D5.S3.Observer.WindowRegister.shiftMatrix M ^ (-p.1).val *
          D5.S3.Observer.WindowRegister.shiftMatrix M ^ p.1.val) *
          D5.S3.Observer.WindowRegister.clockMatrix M ^ p.2.val) := by
            simp only [mul_assoc]
    _ = 1 := by rw [shiftMatrix_pow_neg_mul, one_mul, clockMatrix_pow_neg_mul]

theorem word_mul_star (p : ZMod M × ZMod M) :
    word M p * star (word M p) = 1 := mul_eq_one_comm.mp (word_star_mul p)

private theorem trace_star_single (A : Matrix (ZMod M) (ZMod M) ℂ)
    (i j : ZMod M) :
    Matrix.trace (star A * Matrix.single i j 1) = star (A i j) := by
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul]
  simp [Matrix.star_eq_conjTranspose]

/-- The entrywise completeness identity is derived from the existing exact
reconstruction theorem. It is not an assumed unitary-design certificate. -/
theorem weyl_completeness (i j k l : ZMod M) :
    (∑ p : ZMod M × ZMod M, word M p i k * star (word M p j l)) =
      if i = j ∧ k = l then (M : ℂ) else 0 := by
  classical
  have he := congrArg (fun A : Matrix (ZMod M) (ZMod M) ℂ => A i k)
    (weyl_reconstruction (Matrix.single j l 1))
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    trace_star_single] at he
  have hs : (M : ℂ) * (Matrix.single j l 1) i k =
      ∑ p : ZMod M × ZMod M, word M p i k * star (word M p j l) := by
    rw [he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    field_simp [dimension_ne_zero] <;> ring
  rw [← hs]
  by_cases hi : i = j <;> by_cases hk : k = l <;>
    simp [Matrix.single_apply, hi, hk, eq_comm]

/-- The physical local unitary acts on the first tensor factor only. -/
def localWord (p : ZMod M × ZMod M) : Matrix (ZMod M × b) (ZMod M × b) ℂ :=
  word M p ⊗ₖ (1 : Matrix b b ℂ)

theorem localWord_star_mul (p : ZMod M × ZMod M) :
    star (localWord (b := b) p) * localWord p = 1 := by
  unfold localWord
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul]
  simp only [← Matrix.star_eq_conjTranspose, word_star_mul,
    one_mul, Matrix.one_kronecker_one]

theorem localWord_mul_star (p : ZMod M × ZMod M) :
    localWord (b := b) p * star (localWord p) = 1 :=
  mul_eq_one_comm.mp (localWord_star_mul p)

def localUnitary (p : ZMod M × ZMod M) :
    unitary (Matrix (ZMod M × b) (ZMod M × b) ℂ) :=
  ⟨localWord p, Unitary.mem_iff.mpr ⟨localWord_star_mul p, localWord_mul_star p⟩⟩

/-- Unnormalized partial trace over the first factor. -/
def partialTraceA (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) : Matrix b b ℂ :=
  fun u v => ∑ i : ZMod M, X (i, u) (i, v)

def twirlSum (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) :
    Matrix (ZMod M × b) (ZMod M × b) ℂ :=
  ∑ p : ZMod M × ZMod M, localWord p * X * star (localWord p)

private theorem local_left_apply (p : ZMod M × ZMod M)
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (i j : ZMod M) (u v : b) :
    (localWord p * X) (i, u) (j, v) =
      ∑ k : ZMod M, word M p i k * X (k, u) (j, v) := by
  classical
  simp [localWord, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply]

private theorem local_right_apply (p : ZMod M × ZMod M)
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (i j : ZMod M) (u v : b) :
    (X * star (localWord p)) (i, u) (j, v) =
      ∑ k : ZMod M, X (i, u) (k, v) * star (word M p j k) := by
  classical
  simp [localWord, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_apply, Matrix.one_apply]

private theorem local_conjugation_apply (p : ZMod M × ZMod M)
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (i j : ZMod M) (u v : b) :
    (localWord p * X * star (localWord p)) (i, u) (j, v) =
      ∑ k : ZMod M, ∑ l : ZMod M,
        word M p i k * X (k, u) (l, v) * star (word M p j l) := by
  rw [local_right_apply]
  simp_rw [local_left_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-- The complete bipartite Weyl average is the actual partial trace.
There is no supplied twirl or completeness hypothesis. -/
theorem twirlSum_partialTrace (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) :
    twirlSum X = (M : ℂ) • ((1 : Matrix (ZMod M) (ZMod M) ℂ) ⊗ₖ partialTraceA X) := by
  classical
  ext ⟨i, u⟩ ⟨j, v⟩
  change (∑ p, localWord p * X * star (localWord p)) (i, u) (j, v) = _
  simp only [Matrix.sum_apply, local_conjugation_apply]
  have hreorder :
      (∑ p : ZMod M × ZMod M, ∑ k : ZMod M, ∑ l : ZMod M,
        word M p i k * X (k, u) (l, v) * star (word M p j l)) =
      ∑ k : ZMod M, ∑ l : ZMod M,
        (∑ p : ZMod M × ZMod M, word M p i k * star (word M p j l)) * X (k, u) (l, v) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hreorder]
  simp_rw [weyl_completeness]
  by_cases hi : i = j
  · subst j
    simp [partialTraceA, Matrix.smul_apply, Matrix.kronecker_apply,
      Matrix.one_apply, ← Finset.mul_sum]
  · simp [hi, Matrix.smul_apply, Matrix.kronecker_apply, Matrix.one_apply]

/-- Zero physical hidden marginal discharges the averaging premise. -/
theorem average_eq_zero_of_partialTrace_zero
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (hX : partialTraceA X = 0) :
    average (localUnitary (M := M) (b := b)) X = 0 := by
  have hs : twirlSum X = 0 := by
    rw [twirlSum_partialTrace, hX, Matrix.kronecker_zero, smul_zero]
  change (Fintype.card (ZMod M × ZMod M) : ℝ)⁻¹ • twirlSum X = 0
  rw [hs, smul_zero]

/-- The operator-norm certificate for the actual local Weyl tests. -/
theorem physical_leakage_bounds
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (hX : partialTraceA X = 0) :
    ‖X‖ ≤ leakage (localUnitary (M := M) (b := b)) X ∧
      leakage (localUnitary (M := M) (b := b)) X ≤ 2 * ‖X‖ :=
  centered_leakage_bounds _ _ (average_eq_zero_of_partialTrace_zero X hX)

theorem physical_zero_leakage_iff
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (hX : partialTraceA X = 0) :
    leakage (localUnitary (M := M) (b := b)) X = 0 ↔ X = 0 := by
  constructor
  · intro h
    apply norm_eq_zero.mp
    exact le_antisymm (by simpa [h] using (physical_leakage_bounds X hX).1)
      (norm_nonneg _)
  · intro h
    subst X
    exact leakage_eq_zero_iff.mpr (fun _ => by simp)

private theorem trace_rotate_four {n : Type*} [Fintype n]
    (A B C D : Matrix n n ℂ) :
    Matrix.trace (A * B * C * D) = Matrix.trace (B * C * D * A) := by
  rw [show A * B * C * D = A * (B * C * D) by simp only [mul_assoc]]
  exact Matrix.trace_mul_comm _ _

/-- Polarization of the actual trace square for one unitary commutator. -/
theorem trace_commutator_square {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℂ)) (X : Matrix n n ℂ) :
    Matrix.trace (star (X * (U : Matrix n n ℂ) - (U : Matrix n n ℂ) * X) *
      (X * (U : Matrix n n ℂ) - (U : Matrix n n ℂ) * X)) =
    2 * Matrix.trace (star X * X) -
      Matrix.trace (star X * ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ))) -
      star (Matrix.trace (star X * ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)))) := by
  have hu := Unitary.star_mul_self_of_mem U.property
  have hv := Unitary.mul_star_self_of_mem U.property
  have hfirst : Matrix.trace (star (U : Matrix n n ℂ) * star X * X * (U : Matrix n n ℂ)) =
      Matrix.trace (star X * X) := by
    rw [trace_rotate_four]
    simp only [mul_assoc, hv, mul_one]
  have hcross : Matrix.trace (star (U : Matrix n n ℂ) * star X * (U : Matrix n n ℂ) * X) =
      Matrix.trace (star X * ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ))) := by
    rw [trace_rotate_four]
    simp only [mul_assoc]
  have hconj : Matrix.trace (star X * star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ)) =
      star (Matrix.trace (star X * ((U : Matrix n n ℂ) * X * star (U : Matrix n n ℂ)))) := by
    rw [← Matrix.trace_conjTranspose]
    simp only [← Matrix.star_eq_conjTranspose, star_mul, star_star]
    rw [show ((U : Matrix n n ℂ) * star X * star (U : Matrix n n ℂ)) * X =
        (U : Matrix n n ℂ) * star X * star (U : Matrix n n ℂ) * X by rfl,
      trace_rotate_four]
  have hpoly : star (X * (U : Matrix n n ℂ) - (U : Matrix n n ℂ) * X) *
      (X * (U : Matrix n n ℂ) - (U : Matrix n n ℂ) * X) =
      star (U : Matrix n n ℂ) * star X * X * (U : Matrix n n ℂ) -
      star (U : Matrix n n ℂ) * star X * (U : Matrix n n ℂ) * X -
      star X * star (U : Matrix n n ℂ) * X * (U : Matrix n n ℂ) + star X * X := by
    simp only [star_sub, star_mul]
    have hlast : star X * star (U : Matrix n n ℂ) * (U : Matrix n n ℂ) * X =
        star X * X := by simp only [mul_assoc, hu, one_mul]
    noncomm_ring [hlast]
  rw [hpoly, Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub,
    hfirst, hcross, hconj]
  ring

/-- Exact unnormalized Hilbert-Schmidt square identity for every centered
bipartite matrix, including non-Hermitian matrices. -/
theorem trace_square_sum
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (hX : partialTraceA X = 0) :
    (∑ p : ZMod M × ZMod M,
      Matrix.trace (star (X * localWord p - localWord p * X) *
        (X * localWord p - localWord p * X))) =
      2 * (M : ℂ)^2 * Matrix.trace (star X * X) := by
  classical
  have hc : (∑ p : ZMod M × ZMod M,
      Matrix.trace (star X * (localWord p * X * star (localWord p)))) = 0 := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum]
    change Matrix.trace (star X * twirlSum X) = 0
    rw [twirlSum_partialTrace, hX, Matrix.kronecker_zero, smul_zero,
      mul_zero, Matrix.trace_zero]
  have hd : (∑ p : ZMod M × ZMod M,
      star (Matrix.trace (star X * (localWord p * X * star (localWord p))))) = 0 := by
    rw [← star_sum, hc, star_zero]
  have hi (p : ZMod M × ZMod M) := trace_commutator_square (localUnitary (b := b) p) X
  simp only [localUnitary, Subtype.coe_mk] at hi
  simp_rw [hi, Finset.sum_sub_distrib]
  rw [hc, hd]
  simp only [sub_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, ZMod.card, Nat.cast_mul]
  ring

/-- The normalized Hilbert-Schmidt square, distinct from the operator norm. -/
def normalizedHSSq {n : Type*} [Fintype n] (X : Matrix n n ℂ) : ℝ :=
  (Matrix.trace (star X * X)).re / (Fintype.card n : ℝ)

/-- All factors match the 1/(2 M^2) normalized certificate in the theory. -/
theorem normalized_hs_leakage_identity
    (X : Matrix (ZMod M × b) (ZMod M × b) ℂ) (hX : partialTraceA X = 0) :
    (∑ p : ZMod M × ZMod M,
      normalizedHSSq (X * localWord p - localWord p * X)) / (2 * (M : ℝ)^2) =
        normalizedHSSq X := by
  have hm : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have ht := congrArg Complex.re (trace_square_sum X hX)
  simp only [map_sum] at ht
  have hre : (2 * (M : ℂ)^2 * Matrix.trace (star X * X)).re =
      2 * (M : ℝ)^2 * (Matrix.trace (star X * X)).re := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre] at ht
  unfold normalizedHSSq
  rw [← Finset.sum_div, ht]
  field_simp [hm] <;> ring

#print axioms weyl_completeness
#print axioms twirlSum_partialTrace
#print axioms physical_leakage_bounds
#print axioms physical_zero_leakage_iff
#print axioms normalized_hs_leakage_identity
end D5.S3.Quantum.Thermal.WeylPartialTraceLeakage
