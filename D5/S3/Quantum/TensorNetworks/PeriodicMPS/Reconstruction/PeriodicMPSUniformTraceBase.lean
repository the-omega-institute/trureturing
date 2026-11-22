/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceBase
   generality: I
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformTraceBase
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: []
   utility: none
   digest: Zero locus in the trace-one chart. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.SevenSiteTraceBase
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformHardCoreBaseLocus
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.PeriodicMPSUniformTracePowerBoundary

/-! The common zero locus of the length-`n` trace-word polynomials in the trace-one chart. -/

set_option autoImplicit false

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceBase

open Polynomial
open scoped Matrix
open SevenSiteTraceBase (Bond Word wordPolynomial wordPolynomial_eq_trace)
open PeriodicMPSFiveSiteCoordinates (exists_trace_coordinates)
open PeriodicMPSUniformHardCoreBaseLocus
  (BaseInvariants tracePowerPolynomial trace_pow_eq_eval traceWord_zero_iff_baseInvariants)
open PeriodicMPSUniformTracePowerBoundary (trace_pow_eq_eval_dickson)
open UniformMPSExpectedDimensionRefutation (traceWord)

noncomputable section

/-- The literal polynomial tensor for all binary words of length `n`. -/
def amplitude {R : Type*} [CommRing R] (n : ℕ) (p : Fin 5 → R) (w : Word n) : R :=
  wordPolynomial (p 0) (p 1) (p 2) (p 3) (p 4) (List.ofFn w)

theorem amplitude_actual (n : ℕ) (A : Fin 2 → Bond ℂ) :
    amplitude n ![(A 0).trace, (A 1).trace, (A 0).det, (A 1).det, (A 0 * A 1).trace] =
      traceWord 2 2 n A :=
  funext fun w => wordPolynomial_eq_trace A w

/-- The first-kind Dickson power trace at trace one, as a polynomial in the determinant. -/
def normalizedTracePower (n : ℕ) : ℂ[X] :=
  (dickson 1 (X : ℂ[X]) n).eval 1

theorem eval_normalizedTracePower (n : ℕ) (a : ℂ) :
    (normalizedTracePower n).eval a = (dickson 1 a n).eval 1 := by
  let f : ℂ[X] →+* ℂ := Polynomial.evalRingHom a
  have h := Polynomial.eval_map_apply (p := dickson 1 (X : ℂ[X]) n) f 1
  rw [map_dickson, map_one] at h
  change (dickson 1 ((X : ℂ[X]).eval a) n).eval 1 = (normalizedTracePower n).eval a at h
  rw [eval_X] at h
  exact h.symm

/-- The Dickson normalization agrees with the determinant recurrence used by the base theorem. -/
theorem normalizedTracePower_eq_tracePowerPolynomial (n : ℕ) :
    normalizedTracePower n = tracePowerPolynomial 1 n := by
  apply Polynomial.funext
  intro a
  let A : Bond ℂ := !![0, -a; 1, 1]
  have ht : A.trace = 1 := by simp [A, Matrix.trace_fin_two]
  have hd : A.det = a := by simp [A, Matrix.det_fin_two]
  calc
    (normalizedTracePower n).eval a = (dickson 1 a n).eval 1 := eval_normalizedTracePower n a
    _ = (A ^ n).trace := by
      rw [trace_pow_eq_eval_dickson A n, ht, hd]
    _ = (tracePowerPolynomial 1 n).eval a := by
      rw [trace_pow_eq_eval A n, ht, hd]

private theorem baseInvariants_first_iff (n : ℕ) (s d e k : ℂ) :
    BaseInvariants n 1 s d e k ↔
      (normalizedTracePower n).IsRoot d ∧ e = d * s ^ 2 ∧ k = (1 - 2 * d) * s := by
  rw [normalizedTracePower_eq_tracePowerPolynomial]
  unfold BaseInvariants Polynomial.IsRoot
  constructor
  · rintro (⟨_, a, ha, hd, he, hk⟩ | ⟨ht, _, _⟩)
    · have hda : d = a := by simpa only [one_pow, mul_one] using hd
      rw [hda]
      exact ⟨ha, he, by simpa only [mul_one] using hk⟩
    · exact (one_ne_zero ht).elim
  · rintro ⟨hd, he, hk⟩
    exact Or.inl ⟨Or.inl one_ne_zero, d, hd, by simp, he, by simpa only [mul_one] using hk⟩

/-- The trace-one classification for an actual pair of bond-two matrices. -/
theorem traceWord_eq_zero_iff_of_trace_eq_one (n : ℕ) (hn : 2 ≤ n) (A : Fin 2 → Bond ℂ)
    (ht : (A 0).trace = 1) :
    traceWord 2 2 n A = 0 ↔
      (normalizedTracePower n).IsRoot (A 0).det ∧
        (A 1).det = (A 0).det * (A 1).trace ^ 2 ∧
        (A 0 * A 1).trace = (1 - 2 * (A 0).det) * (A 1).trace := by
  have h := traceWord_zero_iff_baseInvariants A (show 0 < n by omega)
  rw [ht] at h
  exact h.trans (baseInvariants_first_iff n _ _ _ _)

/-- The entire base in the trace-one chart for each period `n ≥ 2`.
The root parameter is the first determinant `d`. -/
theorem amplitude_first_eq_zero_iff (n : ℕ) (hn : 2 ≤ n) (s d e k : ℂ) :
    amplitude n (![1, s, d, e, k] : Fin 5 → ℂ) = 0 ↔
      (normalizedTracePower n).IsRoot d ∧ e = d * s ^ 2 ∧ k = (1 - 2 * d) * s := by
  obtain ⟨A, ht, hs, hd, he, hk⟩ := exists_trace_coordinates 1 s d e k
  have hA := amplitude_actual n A
  rw [ht, hs, hd, he, hk] at hA
  rw [hA]
  simpa only [hs, hd, he, hk] using traceWord_eq_zero_iff_of_trace_eq_one n hn A ht

end

end D5.S3.Quantum.TensorNetworks.PeriodicMPSUniformTraceBase
