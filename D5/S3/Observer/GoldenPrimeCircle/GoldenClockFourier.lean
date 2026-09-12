/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockFourier
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-integral-identities)
   anchors: []
   digest: Actual interval Fourier coefficients conjugate under reflection, retain power, and have translation-invariant cross coefficients. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockFourier

open GoldenClockLattice

noncomputable section

/-- Oriented interval integral. Physical intervals can always be supplied with a <= b. -/
def box (c : ℂ) (a b : ℝ) : ℂ :=
  ∫ x in a..b, Complex.exp (c * (x : ℂ))

/-- Angular frequency, with the negative-exponential Fourier convention. -/
def rate (ω : ℝ) : ℂ := -Complex.I * (ω : ℂ)

def coefficient (ω a b : ℝ) : ℂ := box (rate ω) a b

def cross (z w : ℂ) : ℂ := z * (starRingEnd ℂ) w

lemma rate_ne_zero {ω : ℝ} (hω : ω ≠ 0) : rate ω ≠ 0 := by
  unfold rate
  exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (by exact_mod_cast hω)

lemma rate_conj (ω : ℝ) : (starRingEnd ℂ) (rate ω) = -rate ω := by
  simp [rate]

/-- The expression is bound to an integral, rather than named a Fourier coefficient by fiat. -/
theorem box_eq (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    box c a b = (Complex.exp (c * (b : ℂ)) - Complex.exp (c * (a : ℂ))) / c := by
  exact integral_exp_mul_complex hc

theorem box_translate (c : ℂ) (hc : c ≠ 0) (a b t : ℝ) :
    box c (a + t) (b + t) = Complex.exp (c * (t : ℂ)) * box c a b := by
  rw [box_eq c hc, box_eq c hc]
  push_cast
  simp only [mul_add, Complex.exp_add]
  ring

lemma box_conj (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    box ((starRingEnd ℂ) c) a b = (starRingEnd ℂ) (box c a b) := by
  have hc' : (starRingEnd ℂ) c ≠ 0 := by simpa using hc
  rw [box_eq _ hc', box_eq c hc]
  simp only [map_div₀, map_sub, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]

lemma box_reflect (c : ℂ) (hc : c ≠ 0) (a b : ℝ) :
    box c (-b) (-a) = box (-c) a b := by
  rw [box_eq c hc, box_eq (-c) (neg_ne_zero.mpr hc)]
  simp only [Complex.ofReal_neg, mul_neg, neg_mul, div_neg]
  ring

/-- Reflection of the entire measured interval conjugates every nonzero Fourier coefficient. -/
theorem coefficient_reflect (ω : ℝ) (hω : ω ≠ 0) (a b : ℝ) :
    coefficient ω (-b) (-a) = (starRingEnd ℂ) (coefficient ω a b) := by
  unfold coefficient
  rw [box_reflect _ (rate_ne_zero hω), ← rate_conj, box_conj _ (rate_ne_zero hω)]

/-- Power alone loses the reflection sign for any interval, at every nonzero frequency. -/
theorem reflection_power_equal (ω : ℝ) (hω : ω ≠ 0) (a b : ℝ) :
    Complex.normSq (coefficient ω (-b) (-a)) =
      Complex.normSq (coefficient ω a b) := by
  rw [coefficient_reflect ω hω]
  exact Complex.normSq_conj _

lemma unit_phase (ω t : ℝ) :
    Complex.exp (rate ω * (t : ℂ)) *
      (starRingEnd ℂ) (Complex.exp (rate ω * (t : ℂ))) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp only [map_mul, rate_conj, Complex.conj_ofReal]
  rw [show rate ω * (t : ℂ) + -rate ω * (t : ℂ) = 0 by ring]
  exact Complex.exp_zero

/-- A common change of origin cancels in the cross coefficient. Independent shifts do not. -/
theorem cross_common_translate (ω : ℝ) (hω : ω ≠ 0) (a b c d t : ℝ) :
    cross (coefficient ω (a + t) (b + t)) (coefficient ω (c + t) (d + t)) =
      cross (coefficient ω a b) (coefficient ω c d) := by
  unfold coefficient
  rw [box_translate _ (rate_ne_zero hω), box_translate _ (rate_ne_zero hω)]
  unfold cross
  rw [map_mul]
  calc
    _ = (Complex.exp (rate ω * (t : ℂ)) *
        (starRingEnd ℂ) (Complex.exp (rate ω * (t : ℂ)))) *
        (box (rate ω) a b * (starRingEnd ℂ) (box (rate ω) c d)) := by ring
    _ = _ := by rw [unit_phase, one_mul]

/-- Reflection reverses the imaginary part of the cross coefficient. This is not a claim
that it is nonzero at every frequency; zero or real modes need a separate separation test. -/
theorem cross_reflect_im (ω : ℝ) (hω : ω ≠ 0) (a b c d : ℝ) :
    (cross (coefficient ω (-b) (-a)) (coefficient ω (-d) (-c))).im =
      -(cross (coefficient ω a b) (coefficient ω c d)).im := by
  rw [coefficient_reflect ω hω, coefficient_reflect ω hω]
  have hz (z w : ℂ) : cross ((starRingEnd ℂ) z) ((starRingEnd ℂ) w) =
      (starRingEnd ℂ) (cross z w) := by
    simp [cross]
  rw [hz]
  exact Complex.conj_im _

/-- Real representatives of the centers of the signed golden trigger arcs. -/
def center (L : ℕ) : ℝ := signedWidth L / 2

/-- On any pair of distinct resolutions, one real translation cannot absorb both reflections.
Circle-quotient and sampled-orbit claims additionally require their integer/seam bridges. -/
theorem no_common_center_translation (L r : ℕ) (hr : 0 < r) :
    ¬ ∃ t : ℝ, -center L = center L + t ∧
      -center (L + r) = center (L + r) + t := by
  rintro ⟨t, h₁, h₂⟩
  apply relativeSeparation_ne_zero L r hr
  unfold relativeSeparation
  unfold center at h₁ h₂
  linarith

/-- The geometric phase-separation coordinate at arbitrary angular frequency. -/
def phaseSeparation (ω : ℝ) (L r : ℕ) : ℝ :=
  -ω * (center L - center (L + r))

theorem phaseSeparation_nonzero (ω : ℝ) (hω : ω ≠ 0) (L r : ℕ) (hr : 0 < r) :
    phaseSeparation ω L r ≠ 0 := by
  have hcenter : center L - center (L + r) ≠ 0 := by
    intro h
    apply relativeSeparation_ne_zero L r hr
    unfold relativeSeparation
    unfold center at h
    linarith
  exact mul_ne_zero (neg_ne_zero.mpr hω) hcenter

theorem phaseSeparation_succ (ω : ℝ) (L r : ℕ) :
    phaseSeparation ω (L + 1) r = -alpha * phaseSeparation ω L r := by
  unfold phaseSeparation center
  rw [signedWidth_succ,
    show L + 1 + r = (L + r) + 1 by omega, signedWidth_succ]
  ring

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockFourier
