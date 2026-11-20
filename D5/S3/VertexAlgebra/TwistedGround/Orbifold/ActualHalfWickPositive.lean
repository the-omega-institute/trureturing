/- GID: D5/S3/VertexAlgebra/TwistedGround/Orbifold/ActualHalfWickPositive
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Orbifold/ActualHalfWickPositive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MvPolynomial.Basic]
   utility: none
   digest: Reflection and conjugation identify the signed half-Wick pairing
   with the original oscillator metric. -/

import D5.S3.VertexAlgebra.OriginalCurrentMetric
import D5.S3.VertexAlgebra.SourceBPZ.OriginalMatterHermitian
import D5.S3.VertexAlgebra.TwistedGround.SignedOscillatorWick

/-! The signed half-oscillator Wick form becomes the original Hermitian form
after reflection and coefficient conjugation. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open ComplexConjugate

namespace D5.S3.VertexAlgebra.SignedOscillatorWick

open LatticeActualAnnihilation LatticeGeneratingFieldLocality LatticeHalfFock
open LatticeInvolution MvPolynomial OriginalCurrentMetric OriginalGram
open SourceBPZ.OriginalMatterHermitian (kappaOsc kappaOsc_C kappaOsc_X kappaOsc_add kappaOsc_mul)

private theorem U_coeff_zero (D : LatticeData) (hpos : (gramReal D).PosDef)
    (p : Oscillator D) : (U D hpos p).coeff 0 = p.coeff 0 := by
  classical
  change constantCoeff (U D hpos p) = constantCoeff p
  induction p using MvPolynomial.induction_on with
  | C c => rw [show U D hpos (C c) = C c from (U D hpos).commutes c]
  | add p r hp hr => simp only [map_add, hp, hr]
  | mul_X p x hp =>
    rcases x with ⟨i, k⟩
    rw [map_mul, map_mul, map_mul, hp, U_X]
    simp [map_sum]

/-- Oscillator reflection and coefficient conjugation recover the positive half-Fock pairing. -/
theorem wick_sigma_kappa_eq_oscillatorInner (D : LatticeData) (hpos : (gramReal D).PosDef)
    (p q : Oscillator D) :
    wick D (sigma D (kappaOsc (D := D) p)) q = oscillatorInner D hpos p q := by
  classical
  induction p using MvPolynomial.induction_on generalizing q with
  | C c =>
    rw [kappaOsc_C, sigma_C, wick_constant_left]
    unfold oscillatorInner
    rw [show U D hpos (C c) = C c from (U D hpos).commutes c]
    change conj c * q.coeff 0 = FactorialFockMetric.inner (monomial 0 c) (U D hpos q)
    rw [FactorialFockMetric.inner_monomial_left, U_coeff_zero]
    simp [FactorialFockMetric.weight]
  | add p r hp hr =>
    simp only [kappaOsc_add, map_add, LinearMap.add_apply, oscillatorInner_add_first, hp, hr]
  | mul_X p x ih =>
    rcases x with ⟨i, k⟩
    have hcurrent : current D i (k : ℤ) q = frequency (k : ℤ) • annihilate D i k q := by
      simp only [current, ite_eq_right (not_lt.mpr (Int.natCast_nonneg k)), Int.toNat_natCast,
        LinearMap.smul_apply]
    have hadjoint : oscillatorInner D hpos (X (i, k) * p) q =
        oscillatorInner D hpos p (frequency (k : ℤ) • annihilate D i k q) := by
      simpa only [current_negative, LinearMap.mulLeft_apply, hcurrent] using
        oscillator_negative_positive_pairing D hpos i k p q
    -- Reflection cancels the negative half-frequency in the Wick recurrence.
    rw [mul_comm p (X (i, k)), kappaOsc_mul, kappaOsc_X, map_mul, sigma_X, neg_mul,
      map_neg, LinearMap.neg_apply, wick_creation]
    simp only [neg_smul, map_neg, neg_neg]
    exact (ih (frequency (k : ℤ) • annihilate D i k q)).trans hadjoint.symm

#print axioms wick_sigma_kappa_eq_oscillatorInner

end D5.S3.VertexAlgebra.SignedOscillatorWick
