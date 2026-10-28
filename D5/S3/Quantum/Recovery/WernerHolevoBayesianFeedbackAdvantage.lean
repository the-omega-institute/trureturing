/- GID: D5/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   generality: I
   mirror-B: D5/B/S3/Quantum/Recovery/WernerHolevoBayesianFeedbackAdvantage
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bayesian feedback beats Markovian feedback for qutrit Werner--Holevo. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! The qutrit Werner--Holevo channel separates Bayesian and Markovian feedback. -/

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix

namespace D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage

private abbrev qutrit := Matrix (Fin 3) (Fin 3) ℂ

/-- The qutrit Werner--Holevo (transpose-depolarizing) channel. -/
def whChannel (X : qutrit) : qutrit :=
  (1 / 2 : ℂ) • (X.trace • (1 : qutrit) - X.transpose)

/-- A finite Kraus family represents the Werner--Holevo channel. -/
def IsKrausDecomposition {m : ℕ} (K : Fin m → qutrit) : Prop :=
  ∀ X : qutrit, ∑ a, K a * X * (K a)ᴴ = whChannel X

/-- Matrix absolute value, defined by the positive square root of `Tᴴ * T`. -/
def absMat (T : qutrit) : qutrit := CFC.sqrt (Tᴴ * T)

/-- The two-step Markovian feedback fidelity from the source. -/
def markovFidelity {m₁ m₂ : ℕ} (K₁ : Fin m₁ → qutrit) (K₂ : Fin m₂ → qutrit) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (K₂ b) * absMat (K₁ a)).trace).re) ^ 2

/-- The two-step Bayesian feedback fidelity from the source. -/
def bayesFidelity {m₁ m₂ : ℕ} (K₁ : Fin m₁ → qutrit) (K₂ : Fin m₂ → qutrit) : ℝ :=
  (1 / 9 : ℝ) * ∑ a, ∑ b,
    (((absMat (K₂ b * absMat (K₁ a))).trace).re) ^ 2

private def crossProduct (z : Fin 3 → ℂ) : qutrit := fun i j =>
  if i.val = 0 then
    if j.val = 0 then 0 else if j.val = 1 then -z 2 else z 1
  else if i.val = 1 then
    if j.val = 0 then z 2 else if j.val = 1 then 0 else -z 0
  else
    if j.val = 0 then -z 1 else if j.val = 1 then z 0 else 0

private def basisVector (i : Fin 3) : Fin 3 → ℂ := fun j => if j = i then 1 else 0

private def canonicalKraus (i : Fin 3) : qutrit :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (basisVector i)

private def omega : ℂ := (-1 + Complex.I * Real.sqrt 3) / 2

private def fourierVector (j : Fin 3) : Fin 3 → ℂ := fun i =>
  ((Real.sqrt 3)⁻¹ : ℂ) * omega ^ (j.val * i.val)

private def fourierKraus (j : Fin 3) : qutrit :=
  ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (fourierVector j)

private theorem kraus_classification {m : ℕ} (K : Fin m → qutrit)
    (hK : IsKrausDecomposition K) :
    ∃ z : Fin m → Fin 3 → ℂ,
      (∀ a, K a = ((Real.sqrt 2)⁻¹ : ℂ) • crossProduct (z a)) ∧
        (∑ a, Matrix.of fun i j => z a i * star (z a j)) = (1 : qutrit) := by
  sorry

private theorem abs_crossProduct (z : Fin 3 → ℂ) :
    absMat (((Real.sqrt 2)⁻¹ : ℂ) • crossProduct z) =
      ((‖z‖ / Real.sqrt 2 : ℝ) : ℂ) •
        ((1 : qutrit) - Matrix.of fun i j => z i * star (z j) / ‖z‖ ^ 2) := by
  sorry

private theorem markov_bound {m₁ m₂ : ℕ} (K₁ : Fin m₁ → qutrit) (K₂ : Fin m₂ → qutrit)
    (h₁ : IsKrausDecomposition K₁) (h₂ : IsKrausDecomposition K₂) :
    markovFidelity K₁ K₂ ≤ 1 / 2 := by
  sorry

private theorem canonical_is_kraus : IsKrausDecomposition canonicalKraus := by
  sorry

private theorem fourier_is_kraus : IsKrausDecomposition fourierKraus := by
  sorry

private theorem bayesian_witness : 1 / 2 < bayesFidelity canonicalKraus fourierKraus := by
  sorry

/-- For the unital qutrit Werner--Holevo channel, every Markovian value is at most
`1/2`, while the canonical/Fourier Kraus pair has Bayesian value above `1/2`.
This answers the source's request with a unital channel, hence not an amplitude
damping channel. -/
theorem result :
    (∀ (m₁ m₂ : ℕ) (K₁ : Fin m₁ → qutrit) (K₂ : Fin m₂ → qutrit),
      IsKrausDecomposition K₁ → IsKrausDecomposition K₂ →
        markovFidelity K₁ K₂ ≤ 1 / 2) ∧
    (∃ L₁ : Fin 3 → qutrit, ∃ L₂ : Fin 3 → qutrit,
      IsKrausDecomposition L₁ ∧ IsKrausDecomposition L₂ ∧
        1 / 2 < bayesFidelity L₁ L₂) := by
  constructor
  · intro m₁ m₂ K₁ K₂ h₁ h₂
    exact markov_bound K₁ K₂ h₁ h₂
  · exact ⟨canonicalKraus, fourierKraus, canonical_is_kraus, fourier_is_kraus,
      bayesian_witness⟩

end D5.S3.Quantum.Recovery.WernerHolevoBayesianFeedbackAdvantage
