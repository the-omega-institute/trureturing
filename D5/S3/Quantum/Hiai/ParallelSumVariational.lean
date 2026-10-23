/- GID: D5/S3/Quantum/Hiai/ParallelSumVariational
   generality: G
   mirror-B: D5/B/S3/Quantum/Hiai/ParallelSumVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The matrix parallel sum is the attained Loewner minimum of quadratic split energies. -/

import D5.S3.Quantum.Hiai.InverseMeanVariational

noncomputable section
namespace D5.S3.Quantum.Hiai.ParallelSumVariational
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual matrix parallel sum, using nonsingular matrix inverses. -/
def parallelSum (P Q : Matrix d d ℂ) : Matrix d d ℂ := (P⁻¹ + Q⁻¹)⁻¹

/-- A split is a pair of complex matrices; its energy retains both adjoints. -/
def splitEnergy (P Q : Matrix d d ℂ) (W : Matrix d d ℂ × Matrix d d ℂ) : Matrix d d ℂ :=
  W.1ᴴ * P * W.1 + W.2ᴴ * Q * W.2

private lemma parallel_posDef {P Q : Matrix d d ℂ} (hP : P.PosDef) (hQ : Q.PosDef) :
    (parallelSum P Q).PosDef := (hP.inv.add hQ.inv).inv

private lemma optimal_split {P Q : Matrix d d ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (K : Matrix d d ℂ) :
    P⁻¹ * parallelSum P Q * K + Q⁻¹ * parallelSum P Q * K = K := by
  letI := (hP.inv.add hQ.inv).isUnit.invertible
  simp only [← add_mul, parallelSum]
  simp

private lemma split_residual {P Q U V K : Matrix d d ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) (hUV : U + V = K) :
    Uᴴ * P * U + Vᴴ * Q * V - Kᴴ * parallelSum P Q * K =
      (U - P⁻¹ * parallelSum P Q * K)ᴴ * P *
        (U - P⁻¹ * parallelSum P Q * K) +
      (V - Q⁻¹ * parallelSum P Q * K)ᴴ * Q *
        (V - Q⁻¹ * parallelSum P Q * K) := by
  let H := parallelSum P Q
  let U₀ := P⁻¹ * H * K
  let V₀ := Q⁻¹ * H * K
  have hH : H.PosDef := parallel_posDef hP hQ
  letI := hP.isUnit.invertible
  letI := hQ.isUnit.invertible
  have hPU : P * U₀ = H * K := by simp [U₀, mul_assoc]
  have hQV : Q * V₀ = H * K := by simp [V₀, mul_assoc]
  have hUP : U₀ᴴ * P = Kᴴ * H := by
    simpa only [Matrix.conjTranspose_mul, hP.isHermitian.eq, hH.isHermitian.eq,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose hPU
  have hVQ : V₀ᴴ * Q = Kᴴ * H := by
    simpa only [Matrix.conjTranspose_mul, hQ.isHermitian.eq, hH.isHermitian.eq,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose hQV
  have hsum : U₀ + V₀ = K := optimal_split hP hQ K
  have henergy : U₀ᴴ * P * U₀ + V₀ᴴ * Q * V₀ = Kᴴ * H * K := by
    rw [hUP, hVQ, ← mul_add, hsum]
  change Uᴴ * P * U + Vᴴ * Q * V - Kᴴ * H * K =
    (U - U₀)ᴴ * P * (U - U₀) + (V - V₀)ᴴ * Q * (V - V₀)
  simp only [Matrix.conjTranspose_sub, sub_mul, mul_sub]
  have hcross : Uᴴ * P * U₀ + Vᴴ * Q * V₀ = Kᴴ * H * K := by
    simp only [mul_assoc, hPU, hQV]
    rw [← add_mul, ← Matrix.conjTranspose_add, hUV]
  have hcross' : U₀ᴴ * P * U + V₀ᴴ * Q * V = Kᴴ * H * K := by
    rw [hUP, hVQ, ← mul_add, hUV]
  calc
    Uᴴ * P * U + Vᴴ * Q * V - Kᴴ * H * K =
        Uᴴ * P * U + Vᴴ * Q * V - (Uᴴ * P * U₀ + Vᴴ * Q * V₀) -
          (U₀ᴴ * P * U + V₀ᴴ * Q * V) +
          (U₀ᴴ * P * U₀ + V₀ᴴ * Q * V₀) := by
      rw [hcross, hcross', henergy]
      abel
    _ = _ := by abel

/-- The parallel sum supplies a lower bound for every split, attained at the explicit split.
All inequalities use the genuine Loewner order, with arbitrary complex split matrices. -/
theorem parallel_sum_minimum {P Q : Matrix d d ℂ} (hP : P.PosDef) (hQ : Q.PosDef)
    (K : Matrix d d ℂ) :
    ∃ W₀ : Matrix d d ℂ × Matrix d d ℂ,
      W₀.1 = P⁻¹ * parallelSum P Q * K ∧ W₀.2 = Q⁻¹ * parallelSum P Q * K ∧
      W₀.1 + W₀.2 = K ∧ splitEnergy P Q W₀ = Kᴴ * parallelSum P Q * K ∧
      ∀ W : Matrix d d ℂ × Matrix d d ℂ, W.1 + W.2 = K →
        Kᴴ * parallelSum P Q * K ≤ splitEnergy P Q W := by
  refine ⟨(P⁻¹ * parallelSum P Q * K, Q⁻¹ * parallelSum P Q * K),
    rfl, rfl, optimal_split hP hQ K, ?_, ?_⟩
  · have he := split_residual hP hQ (optimal_split hP hQ K)
    simp only [sub_self, Matrix.conjTranspose_zero, zero_mul, mul_zero, zero_add] at he
    exact sub_eq_zero.mp he
  · intro W hUV
    apply Matrix.le_iff.mpr
    unfold splitEnergy
    rw [split_residual hP hQ hUV]
    exact (hP.posSemidef.conjTranspose_mul_mul_same _).add
      (hQ.posSemidef.conjTranspose_mul_mul_same _)

#print axioms parallel_sum_minimum
end D5.S3.Quantum.Hiai.ParallelSumVariational
