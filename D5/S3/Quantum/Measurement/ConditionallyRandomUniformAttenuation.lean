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
open D5.S3.Quantum.Measurements.CalibratedJointMeasurabilityOptimality (luders)
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation

variable {d m n : ℕ}

def conditioned (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) (y : Fin n) :
    Matrix (Fin d) (Fin d) ℂ :=
  D5.S3.Observer.Conditioning.unreadState (fun x => CFC.sqrt (A x)) (B y)

def UniformAttenuation (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ x y, luders (A x) (B y) = (1 / n : ℂ) • A x ∧
    luders (B y) (A x) = (1 / m : ℂ) • B y

def ConditionallyRandom (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ y, conditioned A B y = (1 / n : ℂ) • 1) ∧
    (∀ x, conditioned B A x = (1 / m : ℂ) • 1)

def claim : Prop :=
  ∀ (d m n : ℕ) (A : Fin m → Matrix (Fin d) (Fin d) ℂ)
    (B : Fin n → Matrix (Fin d) (Fin d) ℂ),
    0 < m → 0 < n → IsPOVM A → IsPOVM B →
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
    simpa only [hR] using (Matrix.isHermitian_mul_mul_conjTranspose R hX).eq
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
  have hnonneg (x : Fin m) : 0 ≤ (X * (K x * X * K x)).trace := by
    rw [sqrt_sandwich_trace (K x) X (hK x) hX]
    exact (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have htrace : ∑ x, (X * (K x * X * K x)).trace = 0 := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, hsum, mul_zero, Matrix.trace_zero]
  intro x
  have htx := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hnonneg x)).mp
    htrace x (Finset.mem_univ x)
  have hy : CFC.sqrt (K x) * X * CFC.sqrt (K x) = 0 := by
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rwa [← sqrt_sandwich_trace (K x) X (hK x) hX]
  have hroot := CFC.sqrt_mul_sqrt_self (K x) (hK x).nonneg
  calc
    K x * X * K x = (CFC.sqrt (K x) * CFC.sqrt (K x)) * X *
        (CFC.sqrt (K x) * CFC.sqrt (K x)) := by simp only [hroot]
    _ = CFC.sqrt (K x) * (CFC.sqrt (K x) * X * CFC.sqrt (K x)) *
        CFC.sqrt (K x) := by simp only [mul_assoc]
    _ = 0 := by rw [hy, mul_zero, zero_mul]

private lemma attenuation_of_conditioned
    (A : Fin m → Matrix (Fin d) (Fin d) ℂ) (hA : IsPOVM A)
    (B : Matrix (Fin d) (Fin d) ℂ) (hB : B.IsHermitian)
    (c : ℂ) (hc : IsSelfAdjoint c)
    (hcond : ∑ x, luders (A x) B = c • 1) :
    ∀ x, luders (A x) B = c • A x := by
  have hroot (x : Fin m) : CFC.sqrt (A x) * CFC.sqrt (A x) = A x :=
    CFC.sqrt_mul_sqrt_self (A x) (hA.1 x).nonneg
  have hcenter (x : Fin m) :
      CFC.sqrt (A x) * (B - c • 1) * CFC.sqrt (A x) =
        luders (A x) B - c • A x := by
    unfold luders
    rw [mul_sub, sub_mul, mul_smul_comm, mul_one, smul_mul_assoc, hroot x]
  have hsum : ∑ x, CFC.sqrt (A x) * (B - c • 1) * CFC.sqrt (A x) = 0 := by
    simp_rw [hcenter]
    rw [Finset.sum_sub_distrib, ← Finset.smul_sum, hcond, hA.2, sub_self]
  have hz := psd_sum_sandwich_zero (fun x => CFC.sqrt (A x))
    (fun x => Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (A x)))
    (B - c • 1) (hB.sub (Matrix.isHermitian_one.smul hc)) hsum
  intro x
  exact sub_eq_zero.mp ((hcenter x).symm.trans (hz x))

theorem result : claim := by
  intro d m n A B _hm _hn hA hB h x y
  exact ⟨attenuation_of_conditioned A hA (B y) (hB.1 y).isHermitian
      (1 / n) (by unfold IsSelfAdjoint; simp) (h.1 y) x,
    attenuation_of_conditioned B hB (A x) (hA.1 x).isHermitian
      (1 / m) (by unfold IsSelfAdjoint; simp) (h.2 x) y⟩

end D5.S3.Quantum.Measurement.ConditionallyRandomUniformAttenuation
