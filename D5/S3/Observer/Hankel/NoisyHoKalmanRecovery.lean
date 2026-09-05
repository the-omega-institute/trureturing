/- GID: D5/S3/Observer/Hankel/NoisyHoKalmanRecovery
   generality: G
   mirror-B: D5/B/S3/Observer/Hankel/NoisyHoKalmanRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The rational executable output has explicit error bounds against real finite-order systems. -/

import D5.S3.Observer.Hankel.ExecutableHoKalman
import D5.S3.Observer.Hankel.HoKalmanPerturbation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Hankel.NoisyHoKalmanRecovery

open D5.S3.Observer.Hankel.FiniteHoKalmanBlocks
open D5.S3.Observer.Hankel.ExecutableHoKalman
open D5.S3.Observer.Hankel.HoKalmanPerturbation
open scoped Matrix.Norms.Operator

/-- Computable conservative inverse norm budget. -/
def inverseBudget {h p m r : Nat} (s : Samples ℚ h p m) (q : Pivot h p m r) : ℚ :=
  absSum (adjInverse (baseBlock s q))

/-- Computable transition error budget in the selected true reachable coordinates. -/
def aErrorBudget {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (q : Pivot h p m r) : ℚ :=
  inverseBudget s q * ((r : ℚ) * ε + (r : ℚ) * ε * absSum (fittedA s q)) /
    (1 - inverseBudget s q * ((r : ℚ) * ε))

/-- Computable input-map error budget. The input block has `m`, not `r`, columns. -/
def bErrorBudget {h p m r : Nat} (s : Samples ℚ h p m) (ε : ℚ)
    (q : Pivot h p m r) : ℚ :=
  inverseBudget s q * ((m : ℚ) * ε + (r : ℚ) * ε * absSum (fittedB s q)) /
    (1 - inverseBudget s q * ((r : ℚ) * ε))

/-- Computable output-map error budget. -/
def cErrorBudget (r : Nat) (ε : ℚ) : ℚ := (r : ℚ) * ε

noncomputable section

/-- Semantic interpretation of the executable rational matrix in the real field. -/
def realMatrix {a b : Nat} (M : Matrix (Fin a) (Fin b) ℚ) :
    Matrix (Fin a) (Fin b) ℝ := fun i j => (M i j : ℝ)

/-- Real interpretation preserves matrix multiplication. -/
@[simp] theorem realMatrix_mul {a b c : Nat}
    (M : Matrix (Fin a) (Fin b) ℚ) (N : Matrix (Fin b) (Fin c) ℚ) :
    realMatrix (M * N) = realMatrix M * realMatrix N := by
  ext i j
  simp [realMatrix, Matrix.mul_apply]

@[simp] theorem realMatrix_one (r : Nat) :
    realMatrix (1 : Matrix (Fin r) (Fin r) ℚ) = 1 := by
  ext i j
  simp [realMatrix, Matrix.one_apply]

/-- Interpret all finite samples without changing the input indexing. -/
def realSamples {h p m : Nat} (s : Samples ℚ h p m) : Samples ℝ h p m :=
  fun k => realMatrix (s k)

/-- The total rational absolute sum soundly bounds the real operator norm. -/
theorem norm_realMatrix_le_absSum {a b : Nat} (M : Matrix (Fin a) (Fin b) ℚ) :
    ‖realMatrix M‖ ≤ (absSum M : ℝ) := by
  have h0 : 0 ≤ absSum M := by
    unfold absSum
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  apply norm_le_of_row_sum_le _ _ (by exact_mod_cast h0)
  intro i
  have hrow : (∑ j, |M i j|) ≤ absSum M := by
    unfold absSum
    exact Finset.single_le_sum
      (fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg (M k j))
      (Finset.mem_univ i)
  have hh : (∑ j, |(M i j : ℝ)|) ≤ (absSum M : ℝ) := by exact_mod_cast hrow
  simpa only [realMatrix, Real.norm_eq_abs] using hh

/-- Each data-block error is derived from the same finite sample uncertainty.
The four dimension factors are explicit and work for MIMO data. -/
theorem sample_noise_blocks {h p m r : Nat}
    (s sh : Samples ℝ h p m) (q : Pivot h p m r) (ε : ℝ)
    (hε : 0 ≤ ε) (he : ∀ k i j, |sh k i j - s k i j| ≤ ε) :
    ‖baseBlock sh q - baseBlock s q‖ ≤ (r : ℝ) * ε ∧
    ‖shiftBlock sh q - shiftBlock s q‖ ≤ (r : ℝ) * ε ∧
    ‖inputBlock sh q - inputBlock s q‖ ≤ (m : ℝ) * ε ∧
    ‖outputBlock sh q - outputBlock s q‖ ≤ (r : ℝ) * ε := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply norm_le_of_entrywise_le _ ε hε
    intro i j
    exact he _ _ _
  · apply norm_le_of_entrywise_le _ ε hε
    intro i j
    exact he _ _ _
  · apply norm_le_of_entrywise_le _ ε hε
    intro i j
    exact he _ _ _
  · apply norm_le_of_entrywise_le _ ε hε
    intro i j
    exact he _ _ _

/-- End-to-end deterministic noisy recovery for the actual rational program output.
The real reference behavior is required to have order r. The algorithm itself only sees
finite rational samples, the order, and the noise budget. The comparison model is
constructed from the true samples in the selected reachable coordinate chart. -/
theorem run_noisy_recovery {h p m r : Nat}
    (sh : Samples ℚ h p m) (ε : ℚ) (out : Result h p m r)
    (ho : run r sh ε = some out)
    (s : Samples ℝ h p m)
    (A : Matrix (Fin r) (Fin r) ℝ) (B : Matrix (Fin r) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin r) ℝ)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B)
    (he : ∀ k i j, |(sh k i j : ℝ) - s k i j| ≤ (ε : ℝ)) :
    (baseBlock s out.pivot).det ≠ 0 ∧
    (∀ n : Nat, fittedC s out.pivot * fittedA s out.pivot ^ n * fittedB s out.pivot =
      C * A ^ n * B) ∧
    ‖realMatrix out.A - fittedA s out.pivot‖ ≤ (aErrorBudget sh ε out.pivot : ℝ) ∧
    ‖realMatrix out.B - fittedB s out.pivot‖ ≤ (bErrorBudget sh ε out.pivot : ℝ) ∧
    ‖realMatrix out.C - fittedC s out.pivot‖ ≤ (cErrorBudget r ε : ℝ) := by
  obtain ⟨hchoose, hA, hB, hC⟩ := run_fields sh ε out ho
  obtain ⟨hkhat, hε, hm⟩ := choosePivot_certificate sh ε out.pivot hchoose
  let Q := realMatrix (adjInverse (baseBlock sh out.pivot))
  have hQ : Q * baseBlock (realSamples sh) out.pivot = 1 := by
    have hh := congrArg (@realMatrix r r) (adjInverse_mul (baseBlock sh out.pivot) hkhat)
    simpa only [realMatrix_mul, realMatrix_one] using hh
  have hq : ‖Q‖ ≤ (inverseBudget sh out.pivot : ℝ) :=
    norm_realMatrix_le_absSum _
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  have hmQ : inverseBudget sh out.pivot * ((r : ℚ) * ε) < 1 := by
    simpa only [inverseBudget, mul_assoc] using hm
  have hmR : (inverseBudget sh out.pivot : ℝ) * ((r : ℝ) * (ε : ℝ)) < 1 := by
    exact_mod_cast hmQ
  obtain ⟨hK, hL, hV, hW⟩ := sample_noise_blocks s (realSamples sh) out.pivot
    (ε : ℝ) hεR he
  have hk : (baseBlock s out.pivot).det ≠ 0 :=
    true_det_ne_zero_of_inverse_margin _ _ Q _ _ hQ hq hK hmR
  have hXA : baseBlock s out.pivot * fittedA s out.pivot = shiftBlock s out.pivot := by
    dsimp only [fittedA]
    rw [← Matrix.mul_assoc, mul_adjInverse _ hk, Matrix.one_mul]
  have hXB : baseBlock s out.pivot * fittedB s out.pivot = inputBlock s out.pivot := by
    dsimp only [fittedB]
    rw [← Matrix.mul_assoc, mul_adjInverse _ hk, Matrix.one_mul]
  have hFA : realMatrix (fittedA sh out.pivot) = Q * shiftBlock (realSamples sh) out.pivot :=
    realMatrix_mul _ _
  have hFB : realMatrix (fittedB sh out.pivot) = Q * inputBlock (realSamples sh) out.pivot :=
    realMatrix_mul _ _
  have hHA : ‖Q * shiftBlock (realSamples sh) out.pivot‖ ≤
      (absSum (fittedA sh out.pivot) : ℝ) := by
    rw [← hFA]
    exact norm_realMatrix_le_absSum _
  have hHB : ‖Q * inputBlock (realSamples sh) out.pivot‖ ≤
      (absSum (fittedB sh out.pivot) : ℝ) := by
    rw [← hFB]
    exact norm_realMatrix_le_absSum _
  have hEA := solve_error_le (baseBlock s out.pivot) (baseBlock (realSamples sh) out.pivot)
    Q (shiftBlock s out.pivot) (shiftBlock (realSamples sh) out.pivot)
    (fittedA s out.pivot) (inverseBudget sh out.pivot : ℝ)
    ((r : ℝ) * (ε : ℝ)) ((r : ℝ) * (ε : ℝ))
    (absSum (fittedA sh out.pivot) : ℝ) hQ hXA hq hK hL hHA hmR
  have hEB := solve_error_le (baseBlock s out.pivot) (baseBlock (realSamples sh) out.pivot)
    Q (inputBlock s out.pivot) (inputBlock (realSamples sh) out.pivot)
    (fittedB s out.pivot) (inverseBudget sh out.pivot : ℝ)
    ((r : ℝ) * (ε : ℝ)) ((m : ℝ) * (ε : ℝ))
    (absSum (fittedB sh out.pivot) : ℝ) hQ hXB hq hK hV hHB hmR
  refine ⟨hk, fun n => finite_samples_exact_recovery s out.pivot A B C hs hk n, ?_, ?_, ?_⟩
  · rw [hA, hFA]
    simpa [aErrorBudget] using hEA
  · rw [hB, hFB]
    simpa [bErrorBudget] using hEB
  · rw [hC]
    simpa only [fittedC, cErrorBudget, Rat.cast_mul, Rat.cast_natCast] using hW

/-- A successful noisy-data certificate excludes every compatible model of
strictly smaller state dimension. The candidate dimension d need not equal r. -/
theorem run_order_lower_bound {h p m r d : Nat}
    (sh : Samples ℚ h p m) (ε : ℚ) (out : Result h p m r)
    (ho : run r sh ε = some out)
    (s : Samples ℝ h p m)
    (A : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin m) ℝ)
    (C : Matrix (Fin p) (Fin d) ℝ)
    (hs : ∀ k : Fin (2 * h), s k = C * A ^ k.val * B)
    (he : ∀ k i j, |(sh k i j : ℝ) - s k i j| ≤ (ε : ℝ)) : r ≤ d := by
  have hchoose := (run_fields sh ε out ho).1
  obtain ⟨hkhat, hε, hm⟩ := choosePivot_certificate sh ε out.pivot hchoose
  let Q := realMatrix (adjInverse (baseBlock sh out.pivot))
  have hQ : Q * baseBlock (realSamples sh) out.pivot = 1 := by
    have hh := congrArg (@realMatrix r r) (adjInverse_mul (baseBlock sh out.pivot) hkhat)
    simpa only [realMatrix_mul, realMatrix_one] using hh
  have hq : ‖Q‖ ≤ (inverseBudget sh out.pivot : ℝ) := norm_realMatrix_le_absSum _
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  have hmQ : inverseBudget sh out.pivot * ((r : ℚ) * ε) < 1 := by
    simpa only [inverseBudget, mul_assoc] using hm
  have hmR : (inverseBudget sh out.pivot : ℝ) * ((r : ℝ) * (ε : ℝ)) < 1 := by
    exact_mod_cast hmQ
  have hK := (sample_noise_blocks s (realSamples sh) out.pivot (ε : ℝ) hεR he).1
  exact finite_samples_order_lower_bound s out.pivot A B C hs
    (true_det_ne_zero_of_inverse_margin _ _ Q _ _ hQ hq hK hmR)

#print axioms run_noisy_recovery
#print axioms run_order_lower_bound

end
end D5.S3.Observer.Hankel.NoisyHoKalmanRecovery
