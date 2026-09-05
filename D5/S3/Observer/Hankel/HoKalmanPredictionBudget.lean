/- GID: D5/S3/Observer/Hankel/HoKalmanPredictionBudget
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/HoKalmanPredictionBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Noisy finite-sample reconstruction gives a computable bound at every prediction horizon. -/

import D5.S3.Observer.Hankel.NoisyHoKalmanRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.HoKalmanPredictionBudget

open D5.S3.Observer.Hankel.FiniteHoKalmanBlocks
open D5.S3.Observer.Hankel.ExecutableHoKalman
open D5.S3.Observer.Hankel.NoisyHoKalmanRecovery
open scoped Matrix.Norms.Operator

/-- Scalar error propagation, executable over the rationals. -/
def stateBudget {F : Type*} [Semiring F] (a da b db : F) : Nat → F
  | 0 => db
  | n + 1 => (a + da) * stateBudget a da b db n + da * (a ^ n * b)

/-- Scalar Markov-parameter prediction budget. No asymptotic stability is assumed. -/
def markovBudget {F : Type*} [Semiring F] (a da b db c dc : F) (n : Nat) : F :=
  (c + dc) * stateBudget a da b db n + dc * (a ^ n * b)

/-- The numeric certificate produced from the finite samples and the returned model. -/
def outputErrorBudget {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (out : Result h p m r) (n : Nat) : ℚ :=
  markovBudget (absSum out.A) (aErrorBudget s ε out.pivot)
    (absSum out.B) (bErrorBudget s ε out.pivot)
    (absSum out.C) (cErrorBudget r ε) n

noncomputable section

@[simp] theorem cast_stateBudget (a da b db : ℚ) (n : Nat) :
    (stateBudget a da b db n : ℝ) =
      stateBudget (a : ℝ) (da : ℝ) (b : ℝ) (db : ℝ) n := by
  induction n with
  | zero => simp [stateBudget]
  | succ n ih => simp [stateBudget, ih]

@[simp] theorem cast_markovBudget (a da b db c dc : ℚ) (n : Nat) :
    (markovBudget a da b db c dc n : ℝ) =
      markovBudget (a : ℝ) (da : ℝ) (b : ℝ) (db : ℝ) (c : ℝ) (dc : ℝ) n := by
  simp [markovBudget]

@[simp] theorem realMatrix_pow {r : Nat} (A : Matrix (Fin r) (Fin r) ℚ) (n : Nat) :
    realMatrix (A ^ n) = realMatrix A ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- Parameter uncertainty is propagated through the actual powers of two systems.
The scalar recurrence is proved by induction, rather than assumed as an error model. -/
theorem markov_error_le {p m r : Nat}
    (A Ah : Matrix (Fin r) (Fin r) ℝ)
    (B Bh : Matrix (Fin r) (Fin m) ℝ)
    (C Ch : Matrix (Fin p) (Fin r) ℝ)
    (a da b db c dc : ℝ)
    (ha : ‖Ah‖ ≤ a) (hda : ‖Ah - A‖ ≤ da)
    (hb : ‖Bh‖ ≤ b) (hdb : ‖Bh - B‖ ≤ db)
    (hc : ‖Ch‖ ≤ c) (hdc : ‖Ch - C‖ ≤ dc) (n : Nat) :
    ‖Ch * Ah ^ n * Bh - C * A ^ n * B‖ ≤ markovBudget a da b db c dc n := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans ha
  have hda0 : 0 ≤ da := (norm_nonneg _).trans hda
  have hb0 : 0 ≤ b := (norm_nonneg _).trans hb
  have hdc0 : 0 ≤ dc := (norm_nonneg _).trans hdc
  have hAt : ‖A‖ ≤ a + da := by
    calc
      ‖A‖ = ‖Ah - (Ah - A)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Ah‖ + ‖Ah - A‖ := norm_sub_le _ _
      _ ≤ a + da := add_le_add ha hda
  have hCt : ‖C‖ ≤ c + dc := by
    calc
      ‖C‖ = ‖Ch - (Ch - C)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Ch‖ + ‖Ch - C‖ := norm_sub_le _ _
      _ ≤ c + dc := add_le_add hc hdc
  have hstates : ∀ k : Nat, ‖Ah ^ k * Bh‖ ≤ a ^ k * b ∧
      ‖Ah ^ k * Bh - A ^ k * B‖ ≤ stateBudget a da b db k := by
    intro k
    induction k with
    | zero => simpa [stateBudget] using And.intro hb hdb
    | succ k ih =>
      constructor
      · calc
          ‖Ah ^ (k + 1) * Bh‖ = ‖Ah * (Ah ^ k * Bh)‖ := by
            rw [pow_succ', Matrix.mul_assoc]
          _ ≤ ‖Ah‖ * ‖Ah ^ k * Bh‖ := Matrix.linfty_opNorm_mul _ _
          _ ≤ a * (a ^ k * b) := mul_le_mul ha ih.1 (norm_nonneg _) ha0
          _ = a ^ (k + 1) * b := by rw [pow_succ', mul_assoc]
      · have he : Ah ^ (k + 1) * Bh - A ^ (k + 1) * B =
            A * (Ah ^ k * Bh - A ^ k * B) + (Ah - A) * (Ah ^ k * Bh) := by
          simp only [pow_succ', Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
          abel
        rw [he, stateBudget]
        calc
          ‖A * (Ah ^ k * Bh - A ^ k * B) + (Ah - A) * (Ah ^ k * Bh)‖ ≤
              ‖A * (Ah ^ k * Bh - A ^ k * B)‖ + ‖(Ah - A) * (Ah ^ k * Bh)‖ :=
            norm_add_le _ _
          _ ≤ ‖A‖ * ‖Ah ^ k * Bh - A ^ k * B‖ + ‖Ah - A‖ * ‖Ah ^ k * Bh‖ :=
            add_le_add (Matrix.linfty_opNorm_mul _ _) (Matrix.linfty_opNorm_mul _ _)
          _ ≤ (a + da) * stateBudget a da b db k + da * (a ^ k * b) := by
            apply add_le_add
            · exact mul_le_mul hAt ih.2 (norm_nonneg _) ((norm_nonneg _).trans hAt)
            · exact mul_le_mul hda ih.1 (norm_nonneg _) hda0
  have he : Ch * Ah ^ n * Bh - C * A ^ n * B =
      C * (Ah ^ n * Bh - A ^ n * B) + (Ch - C) * (Ah ^ n * Bh) := by
    simp only [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [he, markovBudget]
  calc
    ‖C * (Ah ^ n * Bh - A ^ n * B) + (Ch - C) * (Ah ^ n * Bh)‖ ≤
        ‖C * (Ah ^ n * Bh - A ^ n * B)‖ + ‖(Ch - C) * (Ah ^ n * Bh)‖ :=
      norm_add_le _ _
    _ ≤ ‖C‖ * ‖Ah ^ n * Bh - A ^ n * B‖ + ‖Ch - C‖ * ‖Ah ^ n * Bh‖ :=
      add_le_add (Matrix.linfty_opNorm_mul _ _) (Matrix.linfty_opNorm_mul _ _)
    _ ≤ (c + dc) * stateBudget a da b db n + dc * (a ^ n * b) := by
      apply add_le_add
      · exact mul_le_mul hCt (hstates n).2 (norm_nonneg _) ((norm_nonneg _).trans hCt)
      · exact mul_le_mul hdc (hstates n).1 (norm_nonneg _) hdc0

/-- Finite noisy data yield a wholly rational certificate for every predicted Markov parameter.
The unknown real realization is used only in this universal correctness statement. -/
theorem run_prediction_error_bound {h p m r : Nat}
    (sh : Samples ℚ h p m) (ε : ℚ) (out : Result h p m r)
    (ho : run r sh ε = some out)
    (s : Samples ℝ h p m)
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin r) ℝ)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B)
    (he : ∀ k i j, |(sh k i j : ℝ) - s k i j| ≤ (ε : ℝ)) (n : Nat) :
    ‖realMatrix (out.C * out.A ^ n * out.B) - C * A ^ n * B‖ ≤
      (outputErrorBudget sh ε out n : ℝ) := by
  obtain ⟨_, htrue, hA, hB, hC⟩ := run_noisy_recovery sh ε out ho s A B C hs he
  have hh := markov_error_le (fittedA s out.pivot) (realMatrix out.A)
    (fittedB s out.pivot) (realMatrix out.B) (fittedC s out.pivot) (realMatrix out.C)
    (absSum out.A : ℝ) (aErrorBudget sh ε out.pivot : ℝ)
    (absSum out.B : ℝ) (bErrorBudget sh ε out.pivot : ℝ)
    (absSum out.C : ℝ) (cErrorBudget r ε : ℝ)
    (norm_realMatrix_le_absSum _) hA (norm_realMatrix_le_absSum _) hB
    (norm_realMatrix_le_absSum _) hC n
  rw [htrue n] at hh
  simpa only [outputErrorBudget, cast_markovBudget, realMatrix_mul, realMatrix_pow] using hh

#print axioms run_prediction_error_bound

end
end D5.S3.Observer.Hankel.HoKalmanPredictionBudget
