/- GID: D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergDefs
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveKuperbergDefs
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Smooth real weights specify exponential sum moments and their finite sieve coordinates. -/

import D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve.SieveAnalyticDefs
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-! The real-weight, third- and fourth-order specialization of Kuperberg's Theorem 1.3. -/

open scoped BigOperators Topology
open Set MeasureTheory

namespace D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
noncomputable section
set_option autoImplicit false

/-- Smooth real weights with compact support contained in the positive half-line. -/
def SmoothPositiveWeight (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ioi 0

/-- The Fourier transform with negative phase and the factor `2 * pi`. -/
def fourierAt (f : ℝ → ℝ) (ξ : ℝ) : ℂ :=
  ∫ x : ℝ, (f x : ℂ) * Complex.exp ((-(2 * Real.pi * x * ξ) : ℂ) * Complex.I)

/-- Two-sided quadratic Fourier decay outside the unit interval. -/
def QuadraticFourierDecay (f : ℝ → ℝ) : Prop := ∃ C : ℝ, 0 ≤ C ∧
  ∀ ξ : ℝ, 1 ≤ |ξ| → ‖fourierAt f ξ‖ ≤ C / ξ ^ 2

/-- The positive additive phase `exp (2 * pi * I * t)`. -/
def unitCharacter (t : ℝ) : ℂ := Complex.exp ((2 * Real.pi * t : ℂ) * Complex.I)

/-- The weighted exponential sum in equation (12), using integer samples. -/
def weightedExponentialSum (h : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℂ :=
  ∑ᶠ d : ℤ, (f ((d : ℝ) / h) : ℂ) * unitCharacter ((d : ℝ) * t)

/-- Equation (11), including the integral total-frequency constraint. -/
def kuperbergRawMoment {k : ℕ} (Q : ℕ+) (h : ℕ) (f : Fin k → ℝ → ℝ) : ℂ := by
  classical
  exact ∑ q ∈ Fintype.piFinset (fun _ : Fin k => (Q : ℕ).divisors.erase 1),
    (∏ i, (ArithmeticFunction.moebius (q i) : ℂ) / (Nat.totient (q i) : ℂ)) *
      ∑ r ∈ Fintype.piFinset (fun i =>
          (Finset.range (q i)).filter (fun r => r.Coprime (q i))),
        if (∑ i, (r i : ℚ) / (q i : ℚ)) ∈ Set.range (fun z : ℤ => (z : ℚ)) then
          ∏ i, weightedExponentialSum h (f i) ((r i : ℝ) / q i)
        else 0

/-- The fourth exponential-sum moment minus its three bilinear pairings. -/
def kuperbergRawWickDefect (Q : ℕ+) (h : ℕ) (f : Fin 4 → ℝ → ℝ) : ℂ :=
  kuperbergRawMoment Q h f - (kuperbergRawMoment Q h ![f 0,f 1] * kuperbergRawMoment Q h ![f 2,f 3] +
    kuperbergRawMoment Q h ![f 0,f 2] * kuperbergRawMoment Q h ![f 1,f 3] +
    kuperbergRawMoment Q h ![f 0,f 3] * kuperbergRawMoment Q h ![f 1,f 2])

/-- The real-weight `k = 3, 4` specialization of arXiv:2301.06095v1, Theorem 1.3.
The constants depend on the fixed weights and are uniform in the modulus and scale. -/
structure KuperbergRaw : Prop where
  third : ∀ f : Fin 3 → ℝ → ℝ, (∀ i, SmoothPositiveWeight (f i)) →
    (∀ i, QuadraticFourierDecay (f i)) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : ℕ+, Squarefree (Q : ℕ) → ∀ h : ℕ, 3 ≤ h →
        ‖kuperbergRawMoment Q h f‖ ≤ C * (h : ℝ) ^ (3 / 2 - 1 / 21 : ℝ) *
          sieveDensity Q ^ (19 / 2 : ℝ)
  fourth : ∀ f : Fin 4 → ℝ → ℝ, (∀ i, SmoothPositiveWeight (f i)) →
    (∀ i, QuadraticFourierDecay (f i)) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ Q : ℕ+, Squarefree (Q : ℕ) → ∀ h : ℕ, 3 ≤ h →
        ‖kuperbergRawWickDefect Q h f‖ ≤ C * (h : ℝ) ^ (2 - 1 / 28 : ℝ) * sieveDensity Q ^ 18

end
end D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer
