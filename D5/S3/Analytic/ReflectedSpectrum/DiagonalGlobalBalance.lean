/- GID: D5/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/DiagonalGlobalBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A shared orientation bit balances every orbit while coupling every nonzero pair. -/

import D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

/- Library-search audit trail (2026-09-06):
   * Whole-statement and carrier-shape searches in `D5/` found no theorem for
     the half-half law on the two constant binary configurations. The related
     frozen `ParityConditionedMoments` module treats uniform parity fibers, not
     this two-atom diagonal law; its canonical `paritySign` is reused here.
   * Pinned Mathlib provides `PMF.uniformOfFintype`, `PMF.toMeasure_map`,
     `PMF.integral_eq_sum`, `covariance_eq_sub`, `variance_eq_sub`,
     `iIndepFun.comp`, and `IndepFun.covariance_eq_zero`, but no packaged
     diagonal-law global-balance theorem.
   * The host has no `loogle` or `leansearch` executable. GitHub Lean-code
     searches for the covariance/independence and uniform-binary-law shapes
     completed without an exact third-party result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

namespace D5.S3.Analytic.ReflectedSpectrum.DiagonalGlobalBalance

open D5.S3.Analytic.ReflectedSpectrum.ParityConditionedMoments

/-- The half-half law on the two constant binary configurations of a finite
orbit window. This is the source's global diagonal reflection state. -/
def diagonalLaw (T : Type*) [Fintype T] : Measure (T → Fin 2) :=
  ((PMF.uniformOfFintype (Fin 2)).map
    (fun bit : Fin 2 => fun _ : T => bit)).toMeasure

instance diagonalLaw_isProbabilityMeasure (T : Type*) [Fintype T] :
    IsProbabilityMeasure (diagonalLaw T) := by
  unfold diagonalLaw
  infer_instance

/-- The signed displacement read from one orbit in a binary configuration. -/
def orbitReadout {T : Type*} (delta : T → ℝ) (orbit : T)
    (configuration : T → Fin 2) : ℝ :=
  (paritySign (configuration orbit) : ℝ) * delta orbit

private lemma abs_paritySign (bit : Fin 2) : |(paritySign bit : ℝ)| = 1 := by
  fin_cases bit <;> simp [paritySign]

private lemma integral_diagonalLaw {T : Type*} [Fintype T]
    (f : (T → Fin 2) → ℝ) :
    (∫ configuration, f configuration ∂diagonalLaw T) =
      (f (fun _ => (0 : Fin 2)) + f (fun _ => (1 : Fin 2))) / 2 := by
  rw [diagonalLaw,
    ← PMF.toMeasure_map (p := PMF.uniformOfFintype (Fin 2))
      (f := fun bit : Fin 2 => fun _ : T => bit) (by fun_prop),
    integral_map (by fun_prop) (by fun_prop), PMF.integral_eq_sum]
  simp [PMF.uniformOfFintype_apply]
  ring

private lemma orbitReadout_memLp_two {T : Type*} [Fintype T]
    (delta : T → ℝ) (orbit : T) :
    MemLp (orbitReadout delta orbit) 2 (diagonalLaw T) := by
  have htop : MemLp (orbitReadout delta orbit) ⊤ (diagonalLaw T) := by
    apply memLp_top_of_bound (μ := diagonalLaw T) (by fun_prop) |delta orbit|
    filter_upwards with configuration
    rw [Real.norm_eq_abs, orbitReadout, abs_mul, abs_paritySign, one_mul]
  exact htop.mono_exponent le_top

/-- Under the shared orientation bit, every pair of orbit readouts has joint
second moment equal to the product of its two displacement magnitudes. -/
lemma diagonal_joint_second_moment {T : Type*} [Fintype T]
    (delta : T → ℝ) (orbit orbit' : T) :
    (∫ configuration,
      orbitReadout delta orbit configuration * orbitReadout delta orbit' configuration
      ∂diagonalLaw T) = delta orbit * delta orbit' := by
  rw [integral_diagonalLaw]
  simp [orbitReadout, paritySign]

/-- Every orbit readout is centered under the global diagonal law. Distinct
orbit readouts have covariance equal to the product of their displacements and
saturate the covariance-variance bound. When that product is nonzero, the
coordinate projections are not jointly independent, so the state is not a
product state. -/
theorem diagonal_global_balance {T : Type*} [Fintype T] (delta : T → ℝ) :
    (∀ orbit : T,
      (∫ configuration, orbitReadout delta orbit configuration ∂diagonalLaw T) = 0) ∧
    (∀ orbit orbit' : T, orbit ≠ orbit' →
      covariance (orbitReadout delta orbit) (orbitReadout delta orbit') (diagonalLaw T) =
          delta orbit * delta orbit' ∧
      covariance (orbitReadout delta orbit) (orbitReadout delta orbit') (diagonalLaw T) ^ 2 =
          variance (orbitReadout delta orbit) (diagonalLaw T) *
            variance (orbitReadout delta orbit') (diagonalLaw T) ∧
      (delta orbit * delta orbit' ≠ 0 →
        ¬iIndepFun (fun index configuration => configuration index) (diagonalLaw T))) := by
  have hmean : ∀ orbit : T,
      (∫ configuration, orbitReadout delta orbit configuration ∂diagonalLaw T) = 0 := by
    intro orbit
    rw [integral_diagonalLaw]
    simp [orbitReadout, paritySign]
  refine ⟨hmean, ?_⟩
  intro orbit orbit' horbits
  have hcov :
      covariance (orbitReadout delta orbit) (orbitReadout delta orbit') (diagonalLaw T) =
        delta orbit * delta orbit' := by
    rw [covariance_eq_sub (orbitReadout_memLp_two delta orbit)
      (orbitReadout_memLp_two delta orbit'), hmean orbit, hmean orbit', mul_zero, sub_zero]
    exact diagonal_joint_second_moment delta orbit orbit'
  have hvar : ∀ index : T,
      variance (orbitReadout delta index) (diagonalLaw T) = delta index ^ 2 := by
    intro index
    rw [variance_eq_sub (orbitReadout_memLp_two delta index), hmean index]
    rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero]
    simpa [pow_two] using diagonal_joint_second_moment delta index index
  refine ⟨hcov, ?_, ?_⟩
  · rw [hcov, hvar orbit, hvar orbit']
    ring
  · intro hnonzero hindependent
    have hcoordinates := hindependent.indepFun horbits
    have hpair := hcoordinates.comp
      (φ := fun bit => (paritySign bit : ℝ) * delta orbit)
      (ψ := fun bit => (paritySign bit : ℝ) * delta orbit')
      (by fun_prop) (by fun_prop)
    change orbitReadout delta orbit ⟂ᵢ[diagonalLaw T] orbitReadout delta orbit' at hpair
    have hzero := hpair.covariance_eq_zero (orbitReadout_memLp_two delta orbit)
      (orbitReadout_memLp_two delta orbit')
    rw [hcov] at hzero
    exact hnonzero hzero

/-- The finite configuration domain used by the theorem is inhabited. -/
example : Fin 2 → Fin 2 := fun _ => 0

/-- The theorem's finite-window scope is realized by a concrete two-orbit
window with arbitrary real displacement data. -/
example (delta : Fin 2 → ℝ) := diagonal_global_balance delta

#print axioms diagonal_joint_second_moment
#print axioms diagonal_global_balance

end D5.S3.Analytic.ReflectedSpectrum.DiagonalGlobalBalance
