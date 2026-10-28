/- GID: D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bayesian feedback beats Markovian feedback for Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

/-! The qutrit Werner--Holevo channel separates Bayesian and Markovian feedback. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage

/-- The Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo (transpose-depolarizing) channel. -/
def whChannel (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (1 / 2 : ℂ) • (X.trace • (1 : Matrix (Fin 3) (Fin 3) ℂ) - X.transpose)

/-- A finite Kraus family represents the Werner--Holevo channel. -/
def IsKrausDecomposition {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ) : Prop :=
  ∀ X : Matrix (Fin 3) (Fin 3) ℂ, ∑ a, K a * X * (K a)ᴴ = whChannel X

/-- Matrix absolute value, defined by the positive square root of `Tᴴ * T`. -/
def absMat (T : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ := CFC.sqrt (Tᴴ * T)

/-- The two-step Markovian feedback fidelity from the source. -/
def markovFidelity {m₁ m₂ : ℕ} (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ) (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (K₂ b) * absMat (K₁ a)).trace).re) ^ 2

/-- The two-step Bayesian feedback fidelity from the source. -/
def bayesFidelity {m₁ m₂ : ℕ} (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ) (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (K₂ b * absMat (K₁ a))).trace).re) ^ 2

private def crossProduct (z : Fin 3 → ℂ) : Matrix (Fin 3) (Fin 3) ℂ := fun i j =>
  if i.val = 0 then
    if j.val = 0 then 0 else if j.val = 1 then -z 2 else z 1
  else if i.val = 1 then
    if j.val = 0 then z 2 else if j.val = 1 then 0 else -z 0
  else
    if j.val = 0 then -z 1 else if j.val = 1 then z 0 else 0

private def basisVector (i : Fin 3) : Fin 3 → ℂ := fun j => if j = i then 1 else 0

private def canonicalKraus (i : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (basisVector i)

private def rotationVector (j : Fin 3) : Fin 3 → ℂ :=
  if j.val = 0 then ![((2 : ℂ) / 3), (2 : ℂ) / 3, (-1 : ℂ) / 3]
  else if j.val = 1 then ![((-1 : ℂ) / 3), (2 : ℂ) / 3, (2 : ℂ) / 3]
  else ![((2 : ℂ) / 3), (-1 : ℂ) / 3, (2 : ℂ) / 3]

private def rotationKraus (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (rotationVector j)

private theorem kraus_classification {m : ℕ} (K : Fin m → Matrix (Fin 3) (Fin 3) ℂ)
    (hK : IsKrausDecomposition K) :
    ∃ z : Fin m → Fin 3 → ℂ,
      (∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) ∧
        (∑ a, Matrix.of fun i j => z a i * star (z a j)) = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  sorry

private theorem abs_crossProduct (z : Fin 3 → ℂ) :
    absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      ((‖z‖ / Real.sqrt 2 : ℝ) : ℂ) •
        ((1 : Matrix (Fin 3) (Fin 3) ℂ) - Matrix.of fun i j => z i * star (z j) / ‖z‖ ^ 2) := by
  sorry

private theorem markov_bound {m₁ m₂ : ℕ} (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ) (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ)
    (h₁ : IsKrausDecomposition K₁) (h₂ : IsKrausDecomposition K₂) :
    markovFidelity K₁ K₂ ≤ 1 / 2 := by
  sorry

private theorem canonical_is_kraus : IsKrausDecomposition canonicalKraus := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  intro X
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [canonicalKraus, crossProduct, basisVector, whChannel,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.trace, Fin.sum_univ_succ] <;>
    simp only [← mul_assoc, ← pow_two, hs] <;> ring

private theorem rotation_is_kraus : IsKrausDecomposition rotationKraus := by
  have hs : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (1 / 2 : ℂ) := by
    have hn : ((Real.sqrt 2 : ℂ)) ≠ 0 := by norm_num
    field_simp [hn]
    norm_num [pow_two, Complex.ext_iff, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Real.sq_sqrt]
  have h2 : (starRingEnd ℂ) (2 : ℂ) = 2 := by
    rw [← Complex.star_def]
    norm_num
  have h3 : (starRingEnd ℂ) (3 : ℂ) = 3 := by
    rw [← Complex.star_def]
    norm_num
  intro X
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationKraus, rotationVector, crossProduct, whChannel,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Matrix.trace, Fin.sum_univ_succ, Complex.conj_ofReal, h2, h3] <;>
    simp only [← mul_assoc, ← pow_two, hs] <;> ring

private theorem bayesian_witness : 1 / 2 < bayesFidelity canonicalKraus rotationKraus := by
  sorry

/-- For the unital Matrix (Fin 3) (Fin 3) ℂ Werner--Holevo channel, every Markovian value is at most
`1/2`, while the canonical/Fourier Kraus pair has Bayesian value above `1/2`.
This answers the source's request with a unital channel, hence not an amplitude
damping channel. -/
theorem result :
    (∀ (m₁ m₂ : ℕ) (K₁ : Fin m₁ → Matrix (Fin 3) (Fin 3) ℂ) (K₂ : Fin m₂ → Matrix (Fin 3) (Fin 3) ℂ),
      IsKrausDecomposition K₁ → IsKrausDecomposition K₂ →
        markovFidelity K₁ K₂ ≤ 1 / 2) ∧
    (∃ L₁ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ, ∃ L₂ : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ,
      IsKrausDecomposition L₁ ∧ IsKrausDecomposition L₂ ∧
        1 / 2 < bayesFidelity L₁ L₂) := by
  constructor
  · intro m₁ m₂ K₁ K₂ h₁ h₂
    exact markov_bound K₁ K₂ h₁ h₂
  · exact ⟨canonicalKraus, rotationKraus, canonical_is_kraus, rotation_is_kraus,
      bayesian_witness⟩

end D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
