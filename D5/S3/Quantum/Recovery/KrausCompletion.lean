/- GID: D5/S3/Quantum/Recovery/KrausCompletion
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/KrausCompletion
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Explicit row-reset Kraus operators complete a support decoder to the canonical CPTP channel. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Reduction.IsometricCompression

/-!
# Constructive Kraus completion

Library-first: the existing `finite_kraus_quantum_channel` supplies the actual
all-amplification completely-positive and trace-preserving interface. This file
only constructs finite Kraus families and proves their normalisation and action.
It does not assume an unexplained recovery map or replace complete positivity
with a new predicate. The reset contribution is evaluated on every matrix, not
only on density matrices. Support inverses and their smoothness are separate
obligations, not hypotheses secretly asserting recovery.
-/

noncomputable section
open scoped Matrix BigOperators

namespace D5.S3.Quantum.Recovery.KrausCompletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Reduction.IsometricCompression

variable {a b c s : Type*}
  [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
  [Fintype c] [DecidableEq c] [Fintype s]

/-- Send each row of B to the fixed output basis state v. -/
def rowReset (v : b) (B : Matrix c a ℂ) (j : c) : Matrix b a ℂ :=
  Matrix.single v j (1 : ℂ) * B

/-- Resetting the rows is exactly a measure-and-prepare map. -/
theorem row_reset_action (v : b) (B : Matrix c a ℂ) (X : Matrix a a ℂ) :
    (∑ j, rowReset v B j * X * (rowReset v B j)ᴴ) =
      Matrix.trace (B * X * Bᴴ) • Matrix.single v v (1 : ℂ) := by
  calc
    _ = ∑ j : c, Matrix.single v j (1 : ℂ) * (B * X * Bᴴ) *
        (Matrix.single v j (1 : ℂ))ᴴ := by
      simp only [rowReset, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = ∑ j : c, (B * X * Bᴴ) j j • Matrix.single v v (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      calc
        Matrix.single v j (1 : ℂ) * (B * X * Bᴴ) *
            (Matrix.single v j (1 : ℂ))ᴴ =
            Matrix.single v v ((B * X * Bᴴ) j j) := by
          simp [Matrix.conjTranspose_single]
        _ = _ := by simp [Matrix.smul_single]
    _ = Matrix.trace (B * X * Bᴴ) • Matrix.single v v (1 : ℂ) := by
      change (∑ j, (B * X * Bᴴ) j j • Matrix.single v v (1 : ℂ)) =
        (∑ j, (B * X * Bᴴ) j j) • Matrix.single v v (1 : ℂ)
      rw [Finset.sum_smul]

/-- Add an explicit pure-state reset on the complement of a support projection. -/
def completeKraus (K : s → Matrix b a ℂ) (P : Matrix a a ℂ) (v : b) :
    s ⊕ a → Matrix b a ℂ :=
  Sum.elim K (rowReset v (1 - P))

/-- The complete action has the advertised support term plus its missing trace. -/
theorem complete_kraus_action (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P) (X : Matrix a a ℂ) :
    (∑ i, completeKraus K P v i * X * (completeKraus K P v i)ᴴ) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v (1 : ℂ) := by
  simp only [completeKraus, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [row_reset_action]
  have hs : (1 - P)ᴴ = 1 - P := by simp [hP]
  have hi : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  have ht : Matrix.trace ((1 - P) * X * (1 - P)ᴴ) =
      Matrix.trace ((1 - P) * X) := by
    rw [hs, Matrix.trace_mul_comm ((1 - P) * X) (1 - P),
      ← Matrix.mul_assoc, hi]
  rw [ht]

/-- A support-restricted decoder with its explicit complement reset is a genuine canonical quantum channel. -/
theorem complete_quantum_channel (K : s → Matrix b a ℂ) (P : Matrix a a ℂ)
    (v : b) (hP : Pᴴ = P) (hPP : P * P = P)
    (hK : (∑ i, (K i)ᴴ * K i) = P) :
    ∃ channel : QuantumChannel a b, ∀ X : Matrix a a ℂ,
      CStarMatrix.ofMatrix.symm
        (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) =
      (∑ i, K i * X * (K i)ᴴ) +
        Matrix.trace ((1 - P) * X) • Matrix.single v v (1 : ℂ) := by
  have hRowUnit :
      (∑ j : a, (Matrix.single v j (1 : ℂ))ᴴ * Matrix.single v j (1 : ℂ)) =
        (1 : Matrix a a ℂ) := by
    classical
    calc
      _ = ∑ j : a, Matrix.single j j (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        simpa only [Matrix.conjTranspose_single, star_one, one_mul] using
          (Matrix.single_mul_single_same (c := (1 : ℂ)) j v j (1 : ℂ))
      _ = 1 := Matrix.sum_single_one
  have hRowGram :
      (∑ j : a, (rowReset v (1 - P) j)ᴴ * rowReset v (1 - P) j) =
        (1 - P)ᴴ * (1 - P) := by
    calc
      _ = (1 - P)ᴴ * (∑ j : a,
          (Matrix.single v j (1 : ℂ))ᴴ * Matrix.single v j (1 : ℂ)) *
          (1 - P) := by
        simp only [rowReset, Matrix.conjTranspose_mul, Matrix.mul_sum,
          Matrix.sum_mul, Matrix.mul_assoc]
      _ = (1 - P)ᴴ * (1 - P) := by rw [hRowUnit, Matrix.mul_one]
  have hComp : (1 - P)ᴴ * (1 - P) = 1 - P := by
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hPP, sub_self, sub_zero]
  have hNormal :
      (∑ i, (completeKraus K P v i)ᴴ * completeKraus K P v i) = 1 := by
    simp only [completeKraus, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
    rw [hK, hRowGram, hComp]
    abel
  obtain ⟨channel, hc⟩ := finite_kraus_quantum_channel
    (completeKraus K P v) hNormal
  refine ⟨channel, fun X => ?_⟩
  rw [hc X, complete_kraus_action K P v hP hPP]

#print axioms row_reset_action
#print axioms complete_kraus_action
#print axioms complete_quantum_channel

end D5.S3.Quantum.Recovery.KrausCompletion
