/- GID: D5/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/DeferredInstrumentUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal upper-boundary meter, channel, instrument, and uniqueness claim. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness

open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf

def Q {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (U : Matrix (Fin d) (Fin d) ℂ) * Matrix.single x x (1 : ℂ) *
    (U : Matrix (Fin d) (Fin d) ℂ).conjTranspose

def Qs {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (s : ℝ) (x : Fin d) :
    Matrix (Fin d) (Fin d) ℂ :=
  (s : ℂ) • Q U x + (((1 - s) / (d : ℝ) : ℝ) : ℂ) • 1

def It {d : ℕ} (t : ℝ) : MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := (t : ℂ) • ρ +
    ((((1 - t) / (d : ℝ) : ℝ) : ℂ) * Matrix.trace ρ) • 1
  map_add' ρ σ := by
    ext i j
    simp only [Matrix.trace_add, smul_add, add_smul, Matrix.add_apply,
      Matrix.smul_apply, Matrix.one_apply]
    ring_nf
  map_smul' c ρ := by
    ext i j
    simp [Matrix.trace_smul, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> ring

def sMax (d : ℕ) (t : ℝ) : ℝ :=
  (((d : ℝ) ^ 2 - 2) * (1 - t) +
      2 * Real.sqrt ((1 - (d : ℝ) ^ 2) * t ^ 2 + ((d : ℝ) ^ 2 - 2) * t + 1)) /
    (d : ℝ) ^ 2

def a2 (d : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt (t * ((d : ℝ) ^ 2 - 1) + 1) - Real.sqrt (1 - t)) / (d : ℝ)

def b (t : ℝ) : ℝ := Real.sqrt (1 - t)

def Itilde {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℂ) (t : ℝ) (x : Fin d) :
    MatrixMap (Fin d) (Fin d) ℂ where
  toFun ρ := (1 / (d : ℂ)) •
    (((((b t) ^ 2 : ℝ) : ℂ) * Matrix.trace (ρ * Q U x)) • 1 +
      (((a2 d t * b t : ℝ) : ℂ) • (ρ * Q U x + Q U x * ρ)) +
      (((a2 d t) ^ 2 : ℝ) : ℂ) • ρ)
  map_add' ρ σ := by
    ext i j
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, smul_add, add_smul,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    ring_nf
  map_smul' c ρ := by
    ext i j
    simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_apply,
      Matrix.add_apply, Matrix.one_apply]
    split_ifs <;> ring

def claim : Prop :=
  ∀ (d : ℕ), 2 ≤ d →
    ∀ (U : Matrix.unitaryGroup (Fin d) ℂ),
    ∀ (t : ℝ), -1 / ((d : ℝ) ^ 2 - 1) ≤ t → t ≤ 1 →
    ∀ (J : Fin d → MatrixMap (Fin d) (Fin d) ℂ),
      ((∀ x, (J x).IsCompletelyPositive) ∧
        (∑ x, J x = It t) ∧
        (∀ x ρ, Matrix.trace (J x ρ) = Matrix.trace (ρ * Qs U (sMax d t) x))) ↔
      (∀ x, J x = Itilde U t x)

end D5.S3.Quantum.Measurement.DeferredInstrumentUniqueness
