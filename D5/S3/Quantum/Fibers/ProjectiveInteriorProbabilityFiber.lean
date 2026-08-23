/- GID: D5/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber
   generality: G
   mirror-B: D5/B/S3/Quantum/Fibers/ProjectiveInteriorProbabilityFiber
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Squared amplitudes on complex projective space have torus-shaped interior fibers. -/

import D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber
import Mathlib.LinearAlgebra.Projectivization.Basic

/- Library-search audit trail (2026-08-23):
   * The repository's exact `InteriorProbability` hit supplies the canonical strict finite-simplex
     family primitive and is imported rather than redeclared. Its frozen quotient carrier is not
     used.
   * Pinned Mathlib's exact `Projectivization`, `Projectivization.lift`,
     `Projectivization.lift_mk`, `Projectivization.rep`, and
     `Projectivization.mk_eq_mk_iff'` supply the actual complex projective-state carrier and its
     representative API.
   * Pinned Mathlib's exact `Circle`, `Circle.coe_mul`, `Circle.coe_div`,
     `Circle.coe_ne_zero`, and `Circle.normSq_coe` supply the torus factors. Repository and pinned
     Mathlib searches found no exact normalized squared-amplitude fiber equivalence. -/

noncomputable section

namespace D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber

open scoped BigOperators
open D5.S3.Quantum.Fibers.InteriorProbabilityPhaseFiber

set_option autoImplicit false
set_option relaxedAutoImplicit false

private def squaredAmplitudeTotal (n : Nat) (vector : Fin (n + 1) -> ℂ) : ℝ :=
  ∑ i, Complex.normSq (vector i)

private theorem squared_amplitude_total_pos
    (n : Nat) (vector : Fin (n + 1) -> ℂ) (hvector : vector ≠ 0) :
    0 < squaredAmplitudeTotal n vector := by
  obtain ⟨i, hi⟩ : ∃ i, vector i ≠ 0 := by
    by_contra h
    apply hvector
    funext i
    exact not_ne_iff.mp (not_exists.mp h i)
  exact Finset.sum_pos' (fun i _ => Complex.normSq_nonneg (vector i))
    ⟨i, Finset.mem_univ i, Complex.normSq_pos.mpr hi⟩

/-- The basis measurement on complex projective space, evaluated as normalized squared
amplitudes of any nonzero representative. For a unit representative, the denominator is one. -/
def basisProbabilityMap (n : Nat) :
    Projectivization ℂ (Fin (n + 1) -> ℂ) -> Fin (n + 1) -> ℝ :=
  Projectivization.lift
    (fun vector i =>
      Complex.normSq (vector.1 i) / squaredAmplitudeTotal n vector.1)
    (by
      intro first second scalar hscale
      have hscalar : scalar ≠ 0 := by
        intro hzero
        apply first.2
        funext i
        have hi := congrFun hscale i
        simpa [hzero] using hi
      funext i
      have hcoordinate (j : Fin (n + 1)) :
          first.1 j = scalar * second.1 j := by
        have hj := congrFun hscale j
        simpa [Pi.smul_apply, smul_eq_mul] using hj
      have htotal :
          squaredAmplitudeTotal n first.1 =
            Complex.normSq scalar * squaredAmplitudeTotal n second.1 := by
        simp only [squaredAmplitudeTotal]
        calc
          ∑ j, Complex.normSq (first.1 j) =
              ∑ j, Complex.normSq scalar * Complex.normSq (second.1 j) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hcoordinate j, Complex.normSq_mul]
          _ = Complex.normSq scalar *
              ∑ j, Complex.normSq (second.1 j) := by rw [Finset.mul_sum]
      rw [hcoordinate i, Complex.normSq_mul, htotal]
      exact mul_div_mul_left _ _ (Complex.normSq_pos.mpr hscalar).ne')

@[simp]
theorem basis_probability_map_on_mk
    (n : Nat) (vector : Fin (n + 1) -> ℂ) (hvector : vector ≠ 0) :
    basisProbabilityMap n (Projectivization.mk ℂ vector hvector) =
      fun i => Complex.normSq (vector i) / squaredAmplitudeTotal n vector := by
  rfl

/-- The literal fiber of the squared-amplitude map on complex projective space over one strict
probability vector. -/
def BasisProbabilityFiber (n : Nat) (probability : InteriorProbability n) :=
  {state : Projectivization ℂ (Fin (n + 1) -> ℂ) //
    basisProbabilityMap n state = probability.weight}

private def gaugeFixedAmplitude (n : Nat) (probability : InteriorProbability n)
    (relative : Fin n -> Circle) : Fin (n + 1) -> ℂ :=
  Fin.cases
    (Real.sqrt (probability.weight 0))
    (fun i => Real.sqrt (probability.weight i.succ) * (relative i : ℂ))

private theorem gauge_fixed_amplitude_nonzero
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n -> Circle) :
    gaugeFixedAmplitude n probability relative ≠ 0 := by
  intro hzero
  have hatZero := congrFun hzero (0 : Fin (n + 1))
  have hsqrt : Real.sqrt (probability.weight 0) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr (probability.positive 0)
  exact hsqrt (by
    exact_mod_cast (by
      simpa [gaugeFixedAmplitude] using hatZero))

private theorem gauge_fixed_amplitude_norm_sq
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n -> Circle)
    (i : Fin (n + 1)) :
    Complex.normSq (gaugeFixedAmplitude n probability relative i) =
      probability.weight i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [gaugeFixedAmplitude, Complex.normSq_ofReal,
      Real.mul_self_sqrt (probability.positive 0).le]
  · simp [gaugeFixedAmplitude, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (probability.positive j.succ).le]

/-- Gauge fixing the reference amplitude to a positive real reconstructs a point of the actual
complex projective space from all relative phases. -/
def stateFromRelativePhases (n : Nat) (probability : InteriorProbability n)
    (relative : Fin n -> Circle) : Projectivization ℂ (Fin (n + 1) -> ℂ) :=
  Projectivization.mk ℂ (gaugeFixedAmplitude n probability relative)
    (gauge_fixed_amplitude_nonzero n probability relative)

private theorem state_from_relative_phases_has_probability
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n -> Circle) :
    basisProbabilityMap n (stateFromRelativePhases n probability relative) =
      probability.weight := by
  rw [stateFromRelativePhases, basis_probability_map_on_mk]
  funext i
  rw [gauge_fixed_amplitude_norm_sq]
  have htotal :
      squaredAmplitudeTotal n (gaugeFixedAmplitude n probability relative) = 1 := by
    simp only [squaredAmplitudeTotal]
    simpa only [gauge_fixed_amplitude_norm_sq] using probability.total
  rw [htotal, div_one]

/-- The projective fiber point reconstructed from a tuple of relative phases. -/
def fiberStateFromRelativePhases (n : Nat) (probability : InteriorProbability n) :
    (Fin n -> Circle) -> BasisProbabilityFiber n probability :=
  fun relative =>
    ⟨stateFromRelativePhases n probability relative,
      state_from_relative_phases_has_probability n probability relative⟩

private def scaledAffineRatios (n : Nat) (probability : InteriorProbability n) :
    Projectivization ℂ (Fin (n + 1) -> ℂ) -> Fin n -> ℂ :=
  Projectivization.lift
    (fun vector i =>
      (Real.sqrt (probability.weight 0) * vector.1 i.succ) /
        (Real.sqrt (probability.weight i.succ) * vector.1 0))
    (by
      intro first second scalar hscale
      have hscalar : scalar ≠ 0 := by
        intro hzero
        apply first.2
        funext i
        have hi := congrFun hscale i
        simpa [hzero] using hi
      funext i
      have hcoordinate (j : Fin (n + 1)) :
          first.1 j = scalar * second.1 j := by
        have hj := congrFun hscale j
        simpa [Pi.smul_apply, smul_eq_mul] using hj
      rw [hcoordinate i.succ, hcoordinate 0]
      rw [show (Real.sqrt (probability.weight 0) : ℂ) *
              (scalar * second.1 i.succ) =
            scalar * ((Real.sqrt (probability.weight 0) : ℂ) * second.1 i.succ) by
          ring]
      rw [show (Real.sqrt (probability.weight i.succ) : ℂ) *
              (scalar * second.1 0) =
            scalar * ((Real.sqrt (probability.weight i.succ) : ℂ) * second.1 0) by
          ring]
      exact mul_div_mul_left _ _ hscalar)

private theorem basis_probability_map_on_rep
    (n : Nat) (state : Projectivization ℂ (Fin (n + 1) -> ℂ)) :
    basisProbabilityMap n state =
      fun i => Complex.normSq (state.rep i) / squaredAmplitudeTotal n state.rep := by
  conv_lhs => rw [← Projectivization.mk_rep state]
  exact basis_probability_map_on_mk n state.rep state.rep_nonzero

private theorem fiber_rep_norm_sq
    (n : Nat) (probability : InteriorProbability n)
    (state : BasisProbabilityFiber n probability) (i : Fin (n + 1)) :
    Complex.normSq (state.1.rep i) =
      probability.weight i * squaredAmplitudeTotal n state.1.rep := by
  have hcoordinate := congrFun state.2 i
  rw [basis_probability_map_on_rep] at hcoordinate
  exact (div_eq_iff (squared_amplitude_total_pos n state.1.rep
    state.1.rep_nonzero).ne').mp hcoordinate

private theorem fiber_rep_coordinate_nonzero
    (n : Nat) (probability : InteriorProbability n)
    (state : BasisProbabilityFiber n probability) (i : Fin (n + 1)) :
    state.1.rep i ≠ 0 := by
  apply Complex.normSq_pos.mp
  rw [fiber_rep_norm_sq n probability state i]
  exact mul_pos (probability.positive i)
    (squared_amplitude_total_pos n state.1.rep state.1.rep_nonzero)

private theorem scaled_affine_ratio_norm_sq
    (n : Nat) (probability : InteriorProbability n)
    (state : BasisProbabilityFiber n probability) (i : Fin n) :
    Complex.normSq (scaledAffineRatios n probability state.1 i) = 1 := by
  conv_lhs =>
    rw [← Projectivization.mk_rep state.1]
  change Complex.normSq
      (((Real.sqrt (probability.weight 0) : ℂ) * state.1.rep i.succ) /
        ((Real.sqrt (probability.weight i.succ) : ℂ) * state.1.rep 0)) = 1
  rw [Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul]
  rw [Complex.normSq_ofReal, Complex.normSq_ofReal]
  rw [Real.mul_self_sqrt (probability.positive 0).le,
    Real.mul_self_sqrt (probability.positive i.succ).le]
  rw [fiber_rep_norm_sq n probability state i.succ,
    fiber_rep_norm_sq n probability state 0]
  rw [show probability.weight 0 *
          (probability.weight i.succ * squaredAmplitudeTotal n state.1.rep) =
        probability.weight i.succ *
          (probability.weight 0 * squaredAmplitudeTotal n state.1.rep) by ring]
  exact div_self (by positivity [probability.positive 0,
    probability.positive i.succ,
    squared_amplitude_total_pos n state.1.rep state.1.rep_nonzero])

/-- Relative phase coordinates on the literal projective probability fiber, obtained from scaled
affine ratios with the reference coordinate as gauge. -/
def relativePhaseCoordinates (n : Nat) (probability : InteriorProbability n) :
    BasisProbabilityFiber n probability -> Fin n -> Circle :=
  fun state i =>
    ⟨scaledAffineRatios n probability state.1 i,
      mem_sphere_zero_iff_norm.mpr (by
        have hnormSq := scaled_affine_ratio_norm_sq n probability state i
        rw [Complex.normSq_eq_norm_sq] at hnormSq
        nlinarith [norm_nonneg (scaledAffineRatios n probability state.1 i)])⟩

private theorem relative_phases_after_reconstruction
    (n : Nat) (probability : InteriorProbability n) (relative : Fin n -> Circle) :
    relativePhaseCoordinates n probability
        (fiberStateFromRelativePhases n probability relative) = relative := by
  funext i
  apply Circle.ext
  change
    (Real.sqrt (probability.weight 0) : ℂ) *
          gaugeFixedAmplitude n probability relative i.succ /
        ((Real.sqrt (probability.weight i.succ) : ℂ) *
          gaugeFixedAmplitude n probability relative 0) =
      (relative i : ℂ)
  simp only [gaugeFixedAmplitude, Fin.cases_succ, Fin.cases_zero]
  have hsqrtZero : (Real.sqrt (probability.weight 0) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (probability.positive 0)
  have hsqrtSucc : (Real.sqrt (probability.weight i.succ) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.mpr (probability.positive i.succ)
  field_simp

private theorem reconstruct_from_relative_phases
    (n : Nat) (probability : InteriorProbability n)
    (state : BasisProbabilityFiber n probability) :
    stateFromRelativePhases n probability
        (relativePhaseCoordinates n probability state) = state.1 := by
  rw [stateFromRelativePhases, ← Projectivization.mk_rep state.1]
  apply (Projectivization.mk_eq_mk_iff' ℂ
    (gaugeFixedAmplitude n probability
      (relativePhaseCoordinates n probability state))
    state.1.rep
    (gauge_fixed_amplitude_nonzero n probability
      (relativePhaseCoordinates n probability state))
    state.1.rep_nonzero).mpr
  refine ⟨(Real.sqrt (probability.weight 0) : ℂ) / state.1.rep 0, ?_⟩
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · change
      ((Real.sqrt (probability.weight 0) : ℂ) / state.1.rep 0) *
          state.1.rep 0 =
        Real.sqrt (probability.weight 0)
    exact div_mul_cancel₀ _ (fiber_rep_coordinate_nonzero n probability state 0)
  · change
      ((Real.sqrt (probability.weight 0) : ℂ) / state.1.rep 0) *
          state.1.rep j.succ =
        (Real.sqrt (probability.weight j.succ) : ℂ) *
          scaledAffineRatios n probability state.1 j
    conv_rhs =>
      rw [← Projectivization.mk_rep state.1]
    change
      ((Real.sqrt (probability.weight 0) : ℂ) / state.1.rep 0) *
          state.1.rep j.succ =
        (Real.sqrt (probability.weight j.succ) : ℂ) *
          (((Real.sqrt (probability.weight 0) : ℂ) * state.1.rep j.succ) /
            ((Real.sqrt (probability.weight j.succ) : ℂ) * state.1.rep 0))
    have hsqrtSucc : (Real.sqrt (probability.weight j.succ) : ℂ) ≠ 0 := by
      exact_mod_cast Real.sqrt_ne_zero'.mpr (probability.positive j.succ)
    have href := fiber_rep_coordinate_nonzero n probability state 0
    field_simp

/-- On the actual complex projective-state carrier, normalized squared basis amplitudes have one
circle of relative phase for each non-reference coordinate: every strict probability fiber is
bijectively coordinatized by the `n`-torus. -/
theorem projective_interior_probability_fiber_equiv_torus
    (n : Nat) (probability : InteriorProbability n) :
    Function.Bijective (relativePhaseCoordinates n probability) := by
  constructor
  · intro first second hrelative
    apply Subtype.ext
    calc
      first.1 = stateFromRelativePhases n probability
          (relativePhaseCoordinates n probability first) :=
        (reconstruct_from_relative_phases n probability first).symm
      _ = stateFromRelativePhases n probability
          (relativePhaseCoordinates n probability second) := by rw [hrelative]
      _ = second.1 := reconstruct_from_relative_phases n probability second
  · intro relative
    exact ⟨fiberStateFromRelativePhases n probability relative,
      relative_phases_after_reconstruction n probability relative⟩

/-- The explicit equivalence carried by the relative-phase coordinates. -/
def projectiveInteriorProbabilityFiberEquivTorus
    (n : Nat) (probability : InteriorProbability n) :
    BasisProbabilityFiber n probability ≃ (Fin n -> Circle) :=
  Equiv.ofBijective (relativePhaseCoordinates n probability)
    (projective_interior_probability_fiber_equiv_torus n probability)

#print axioms projective_interior_probability_fiber_equiv_torus

end D5.S3.Quantum.Fibers.ProjectiveInteriorProbabilityFiber
