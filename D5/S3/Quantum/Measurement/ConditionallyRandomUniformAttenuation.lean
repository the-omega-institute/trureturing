/- GID: D5/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/ConditionallyRandomUniformAttenuation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Conditional randomness implies uniform attenuation for all finite observables. -/

import D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality

/-! Conditional randomness and uniform attenuation of finite quantum observables. -/

noncomputable section

open scoped ComplexOrder MatrixOrder

namespace D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation

variable {d m n : ℕ}

def seqProduct (A B : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality.luders A B

def IsObservable (A : Fin m → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation.IsPOVM A

def conditioned (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (y : Fin n) :
    Matrix (Fin d) (Fin d) ℂ := ∑ x, seqProduct (A x) (B y)

def UniformAttenuation (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ x y, seqProduct (A x) (B y) = (1 / n : ℂ) • A x ∧
    seqProduct (B y) (A x) = (1 / m : ℂ) • B y

def ConditionallyRandom (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ y, conditioned A B y = (1 / n : ℂ) • 1) ∧
    (∀ x, conditioned B A x = (1 / m : ℂ) • 1)

def claim : Prop :=
  ∀ (d m n : ℕ) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
    0 < m → 0 < n → IsObservable A → IsObservable B →
    ConditionallyRandom A B → UniformAttenuation A B

private lemma sqrt_sandwich_trace (K X : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.PosSemidef) (hX : X.IsHermitian) :
    (X * (K * X * K)).trace =
      ((CFC.sqrt K * X * CFC.sqrt K).conjTranspose *
        (CFC.sqrt K * X * CFC.sqrt K)).trace := by
  let R := CFC.sqrt K
  have hR : R.conjTranspose = R :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg K)).isHermitian.eq
  have hRR : R * R = K := CFC.sqrt_mul_sqrt_self K hK.nonneg
  have hY : (R * X * R).conjTranspose = R * X * R := by
    simp only [Matrix.conjTranspose_mul, hR, hX.eq, mul_assoc]
  change (X * (K * X * K)).trace = ((R * X * R).conjTranspose * (R * X * R)).trace
  rw [hY]
  calc
    (X * (K * X * K)).trace = (X * (K * X * R) * R).trace := by
      simp only [mul_assoc, hRR]
    _ = (R * X * (K * X * R)).trace := Matrix.trace_mul_cycle _ _ _
    _ = ((R * X * R) * (R * X * R)).trace := by
      conv_lhs => rw [← hRR]
      simp only [mul_assoc]

private lemma psd_sum_sandwich_zero
    (K : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (hK : ∀ x, (K x).PosSemidef) (X : Matrix (Fin d) (Fin d) ℂ)
    (hX : X.IsHermitian) (hsum : ∑ x, K x * X * K x = 0) :
    ∀ x, K x * X * K x = 0 := by
  sorry

private lemma attenuation_of_conditioned
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : IsObservable A)
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian)
    (c : ℂ) (hc : IsSelfAdjoint c)
    (hcond : ∑ x, seqProduct (A x) B = c • 1) :
    ∀ x, seqProduct (A x) B = c • A x := by
  sorry

theorem result : claim := by
  intro d m n A B _hm _hn hA hB h x y
  exact ⟨attenuation_of_conditioned A hA (B y) (hB.1 y).isHermitian
      (1 / n) (by simp [IsSelfAdjoint]) (h.1 y) x,
    attenuation_of_conditioned B hB (A x) (hA.1 x).isHermitian
      (1 / m) (by simp [IsSelfAdjoint]) (h.2 x) y⟩

end D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
