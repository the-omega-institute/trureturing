/- GID: D5/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation
   generality: G
   mirror-B: D5/B/S3/Quantum/Contextuality/SymmetricSatwapMaximalViolation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Identical TW measurements attain the symmetric SATWAP value in every dimension. -/

import D5.S3.Quantum.Measurements.CliffordJointMeasurability.ShiftedFourierOperatorCertificate
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Kronecker

set_option autoImplicit false

noncomputable section

open scoped BigOperators ComplexConjugate
open Complex Matrix

namespace D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation

def omegaPow (d : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * I * (t : ℂ) / d)

def twMatrix (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i.val = 0 then -1 else 1) *
    (fun i j => (1 : ℂ) / ((d : ℂ) *
      (Real.sin (((i.val : ℝ) - j.val - 1 / 2) * Real.pi / d) : ℂ)))

private def basisProjector (d : ℕ) (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => if i = a ∧ j = a then 1 else 0

def measurement (d : ℕ) (x : Fin 2) (a : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  if x = 0 then basisProjector d a
  else twMatrix d * basisProjector d a * (twMatrix d)ᴴ

def prob (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (x y : Fin 2) (a b : Fin d) : ℂ :=
  inner ℂ ψ (WithLp.toLp 2
    ((measurement d x a ⊗ₖ measurement d y b).mulVec ψ))

def correlator (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d))
    (x y : Fin 2) (k : ℕ) : ℂ :=
  ∑ a : Fin d, ∑ b : Fin d,
    omegaPow d (-((k : ℝ) * ((a.val : ℝ) + b.val))) * prob d ψ x y a b

def satwapValue (d : ℕ) (ψ : EuclideanSpace ℂ (Fin d × Fin d)) : ℂ :=
  ∑ k ∈ Finset.Icc 1 (d - 1),
    let a := (1 - I) / 2 * omegaPow d ((k : ℝ) / 4)
    omegaPow d (-2 * (k : ℝ)) *
      (a * correlator d ψ 0 0 k + conj a * correlator d ψ 0 1 k +
        conj a * correlator d ψ 1 0 k) +
      omegaPow d (-3 * (k : ℝ)) * a * correlator d ψ 1 1 k

def swap {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij => ψ (ij.2, ij.1))

def reducedState {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d × Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i i' => ∑ j, ψ (i, j) * conj (ψ (i', j))

def claim : Prop := ∀ d : ℕ, 2 ≤ d →
  ∃ ψ : EuclideanSpace ℂ (Fin d × Fin d),
    ‖ψ‖ = 1 ∧ swap ψ = ψ ∧
    reducedState ψ = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) ∧
    satwapValue d ψ = 2 * ((d : ℂ) - 1)

private def offset (x : Fin 2) : ℝ := if x = 0 then 7 / 8 else 11 / 8

private def fourierBasis (d : ℕ) (x : Fin 2) : Matrix (Fin d) (Fin d) ℂ :=
  fun j a => omegaPow d ((j.val : ℝ) * ((a.val : ℝ) + offset x)) / Real.sqrt d

private def gaugeD (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun a => omegaPow d ((a.val : ℝ) / 2))

private def gaugeF (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun b => -I * omegaPow d (-((b.val : ℝ) + 1 / 2) / 2))

private def transport (d : ℕ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal (fun i => if i.val = 0 then -1 else 1) *
    (gaugeD d)ᴴ * (fourierBasis d 0)ᴴ

private def state (d : ℕ) : EuclideanSpace ℂ (Fin d × Fin d) :=
  WithLp.toLp 2 (fun ij =>
    (∑ m, transport d ij.1 m * transport d ij.2 m) / Real.sqrt d)

private lemma fourier_unitary (d : ℕ) (hd : 2 ≤ d) (x : Fin 2) :
    (fourierBasis d x)ᴴ * fourierBasis d x = 1 := by
  sorry

private lemma gauge_identity (d : ℕ) (hd : 2 ≤ d) :
    (fourierBasis d 0)ᴴ * fourierBasis d 1 =
      gaugeD d * (fun a b => (1 : ℂ) / ((d : ℂ) *
        (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d := by
  sorry

private lemma transport_unitary (d : ℕ) (hd : 2 ≤ d)
    (hf : (fourierBasis d 0)ᴴ * fourierBasis d 0 = 1) :
    transport d * (transport d)ᴴ = 1 := by
  sorry

private lemma state_norm (d : ℕ) (hd : 2 ≤ d)
    (hl : transport d * (transport d)ᴴ = 1) : ‖state d‖ = 1 := by
  sorry

private lemma state_swap (d : ℕ) : swap (state d) = state d := by
  sorry

private lemma state_reduced (d : ℕ) (hd : 2 ≤ d)
    (hl : transport d * (transport d)ᴴ = 1) :
    reducedState (state d) = (1 / (d : ℂ)) • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  sorry

private lemma fourier_probability (d : ℕ) (hd : 2 ≤ d)
    (hf : ∀ x, (fourierBasis d x)ᴴ * fourierBasis d x = 1)
    (hg : (fourierBasis d 0)ᴴ * fourierBasis d 1 =
      gaugeD d * (fun a b => (1 : ℂ) / ((d : ℂ) *
        (Real.sin (((a.val : ℝ) - b.val - 1 / 2) * Real.pi / d) : ℂ))) * gaugeF d)
    (x y : Fin 2) (a b : Fin d) :
    prob d (state d) x y a b =
      (↑(‖∑ j : Fin d, omegaPow d (-((j.val : ℝ) *
        ((a.val : ℝ) + b.val + offset x + offset y)))‖ ^ 2) : ℂ) / (d : ℂ) ^ 3 := by
  sorry

private lemma fourier_correlator (d : ℕ) (hd : 2 ≤ d)
    (hp : ∀ x y a b, prob d (state d) x y a b =
      (↑(‖∑ j : Fin d, omegaPow d (-((j.val : ℝ) *
        ((a.val : ℝ) + b.val + offset x + offset y)))‖ ^ 2) : ℂ) / (d : ℂ) ^ 3)
    (x y : Fin 2) (k : ℕ) (hk : k ∈ Finset.Icc 1 (d - 1)) :
    correlator d (state d) x y k =
      omegaPow d ((k : ℝ) * (offset x + offset y)) *
        (((d : ℂ) - k) + k * omegaPow d (-(d : ℝ) * (offset x + offset y))) / d := by
  sorry

private lemma satwap_sum (d : ℕ) (hd : 2 ≤ d)
    (hc : ∀ x y k, k ∈ Finset.Icc 1 (d - 1) →
      correlator d (state d) x y k =
        omegaPow d ((k : ℝ) * (offset x + offset y)) *
          (((d : ℂ) - k) + k * omegaPow d (-(d : ℝ) * (offset x + offset y))) / d) :
    satwapValue d (state d) = 2 * ((d : ℂ) - 1) := by
  sorry

theorem result : claim := by
  intro d hd
  have hf := fourier_unitary d hd
  have hl := transport_unitary d hd (hf 0)
  refine ⟨state d, state_norm d hd hl, state_swap d, state_reduced d hd hl, ?_⟩
  exact satwap_sum d hd
    (fourier_correlator d hd (fourier_probability d hd hf (gauge_identity d hd)))

end D5.S3.Quantum.Contextuality.SymmetricSatwapMaximalViolation
