/- GID: D5/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/NullConeGravity/ConformalMaxwellSelection4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Conformal Maxwell transport and transverse and longitudinal Proca identities. -/

import OmegaBuild.Commands
import D5.S3.Analysis.InverseTimeRescaling
import D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState
import D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! Conformal Maxwell transport and weighted Proca mode equations. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace NullConeGravity

open Filter MeasureTheory Set
open scoped BigOperators ComplexOrder InnerProductSpace Topology

/-- Volume scaling with the two inverse metric factors of the Maxwell density. -/
def maxwellConformalWeight (D : ℕ) (Ω : ℝ) : ℝ := Ω ^ ((D : ℤ) - 4)

theorem maxwell_density_scaling (D : ℕ) {Ω : ℝ} (hΩ : 0 < Ω) :
    Ω ^ D * Ω ^ (-2 : ℤ) * Ω ^ (-2 : ℤ) = maxwellConformalWeight D Ω := by
  rw [← zpow_natCast, ← zpow_add₀ hΩ.ne', ← zpow_add₀ hΩ.ne']
  congr 1
  ring

theorem maxwellConformalWeight_eq_one_at_iff (D : ℕ) {Ω : ℝ} (hΩ : 0 < Ω) (h₁ : Ω ≠ 1) :
    maxwellConformalWeight D Ω = 1 ↔ D = 4 := by
  rw [maxwellConformalWeight, zpow_eq_one_iff_right₀ hΩ.le h₁]
  omega

theorem maxwellConformalWeight_eq_one_iff (D : ℕ) :
    (∀ Ω : ℝ, 0 < Ω → maxwellConformalWeight D Ω = 1) ↔ D = 4 := by
  refine ⟨fun h => (maxwellConformalWeight_eq_one_at_iff D (by norm_num : 0 < (2 : ℝ))
    (by norm_num)).mp (h 2 (by norm_num)), ?_⟩
  rintro rfl Ω _
  norm_num [maxwellConformalWeight]

/-- The contraction of a covariant field strength with both indices raised by a diagonal metric.
The input `q` consists of the inverse diagonal components. -/
def maxwellFieldContraction {D : ℕ} (q : Fin D → ℝ) (F : Fin D → Fin D → ℝ) : ℝ :=
  ∑ i, ∑ j, q i * q j * F i j ^ 2

/-- Diagonal-metric components of the Maxwell stress tensor. -/
def maxwellStress {D : ℕ} (q : Fin D → ℝ) (F : Fin D → Fin D → ℝ) (i j : Fin D) : ℝ :=
  (∑ k, q k * F i k * F j k) -
    (if i = j then (q i)⁻¹ else 0) * maxwellFieldContraction q F / 4

theorem maxwell_stress_trace {D : ℕ} (q : Fin D → ℝ) (F : Fin D → Fin D → ℝ)
    (hq : ∀ i, q i ≠ 0) :
    (∑ i, q i * maxwellStress q F i i) =
      (4 - (D : ℝ)) / 4 * maxwellFieldContraction q F := by
  have hdiag (i : Fin D) : maxwellStress q F i i =
      (∑ k, q k * F i k * F i k) - (q i)⁻¹ * maxwellFieldContraction q F / 4 := by
    simp [maxwellStress]
  simp_rw [hdiag, mul_sub, Finset.sum_sub_distrib]
  have hs (i : Fin D) :
      q i * ((q i)⁻¹ * maxwellFieldContraction q F / 4) =
        maxwellFieldContraction q F / 4 := by field_simp [hq i]
  simp_rw [hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
  have hc : (∑ i : Fin D, ∑ j : Fin D, q i * (q j * F i j * F i j)) =
      maxwellFieldContraction q F := by
    unfold maxwellFieldContraction
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hc]
  ring

theorem maxwell_stress_trace_eq_zero_iff {D : ℕ} (q : Fin D → ℝ)
    (F : Fin D → Fin D → ℝ) (hq : ∀ i, q i ≠ 0)
    (hF : maxwellFieldContraction q F ≠ 0) :
    (∑ i, q i * maxwellStress q F i i) = 0 ↔ D = 4 := by
  rw [maxwell_stress_trace q F hq, mul_eq_zero, or_iff_left hF, div_eq_zero_iff]
  norm_num
  exact_mod_cast (sub_eq_zero.trans eq_comm : (4 : ℤ) - D = 0 ↔ (D : ℤ) = 4)

/-- The divergence in density coordinates, with the reference contravariant field strength
supplied in the same coordinates. -/
def maxwellChartDivergence {D : ℕ} (Ω : (Fin D → ℝ) → ℝ)
    (raisedF : (Fin D → ℝ) → Fin D → Fin D → ℝ) (x : Fin D → ℝ) (j : Fin D) : ℝ :=
  (Ω x ^ D)⁻¹ * ∑ i, deriv (fun t : ℝ =>
    let y := Function.update x i (x i + t)
    maxwellConformalWeight D (Ω y) * raisedF y i j) 0

theorem maxwell4D_divergence (Ω : (Fin 4 → ℝ) → ℝ)
    (raisedF : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) (j : Fin 4) :
    maxwellChartDivergence Ω raisedF x j =
      (Ω x ^ 4)⁻¹ * ∑ i, deriv (fun t : ℝ =>
        raisedF (Function.update x i (x i + t)) i j) 0 := by
  norm_num [maxwellChartDivergence, maxwellConformalWeight]

theorem maxwell4D_vacuum_equals_reference (Ω : (Fin 4 → ℝ) → ℝ)
    (raisedF : (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ) (x : Fin 4 → ℝ) (hΩ : 0 < Ω x) :
    (∀ j, maxwellChartDivergence Ω raisedF x j = 0) ↔
      ∀ j, (∑ i, deriv (fun t : ℝ => raisedF (Function.update x i (x i + t)) i j) 0) = 0 := by
  simp_rw [maxwell4D_divergence, mul_eq_zero, inv_eq_zero, pow_eq_zero_iff (by decide : 4 ≠ 0),
    hΩ.ne', false_or]

/-- Cross-section volume scales in dimension D − 2 and the inverse screen metric has weight −2. -/
theorem maxwell_screen_density_scaling (D : ℕ) {Ω : ℝ} (hΩ : 0 < Ω) :
    Ω ^ ((D : ℤ) - 2) * Ω ^ (-2 : ℤ) = maxwellConformalWeight D Ω := by
  rw [← zpow_add₀ hΩ.ne', maxwellConformalWeight]
  congr 1
  ring

/-- The characteristic flux in fixed generator and angular coordinates. The reference
density and inverse screen metric are combined in `screen`. Use the plus-sign
convention for the oriented integral. -/
def maxwellCharacteristicFlux {D : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (ℝ × X)) (Ω : ℝ × X → ℝ)
    (screen : ℝ × X → Fin (D - 2) → Fin (D - 2) → ℝ)
    (A B : ℝ → X → Fin (D - 2) → ℝ) : ℝ :=
  ∫ p, (Ω p ^ ((D : ℤ) - 2) * Ω p ^ (-2 : ℤ)) * ∑ i, ∑ j, screen p i j *
    (A p.1 p.2 i * deriv (fun t => B t p.2 j) p.1 -
      B p.1 p.2 i * deriv (fun t => A t p.2 j) p.1) ∂μ

theorem maxwell4D_conformal_symplectic_invariant {X : Type*} [MeasurableSpace X]
    (μ : Measure (ℝ × X)) (Ω : ℝ × X → ℝ) (hΩ : ∀ p, 0 < Ω p)
    (screen : ℝ × X → Fin 2 → Fin 2 → ℝ) (A B : ℝ → X → Fin 2 → ℝ) :
    maxwellCharacteristicFlux (D := 4) μ Ω screen A B =
      maxwellCharacteristicFlux (D := 4) μ (fun _ => 1) screen A B := by
  unfold maxwellCharacteristicFlux
  simp_rw [fun p => maxwell_screen_density_scaling 4 (hΩ p),
    maxwell_screen_density_scaling 4 (by norm_num : 0 < (1 : ℝ))]
  norm_num [maxwellConformalWeight]

/-- The regulated radiative pairing of Appendix B.1, Eq. (125), in common generator
and angular coordinates. The measure supplies the coordinate volume, and the profiles
are the constrained radiative data. -/
def maxwellRadiativeKernel {X : Type*} [MeasurableSpace X]
    (μ : Measure ((ℝ × ℝ) × X)) (Ω : ℝ → X → ℝ) (screen : X → Fin 2 → Fin 2 → ℝ)
    (f g : ℝ → X → Fin 2 → ℝ) (ε : ℝ) : ℂ :=
  -(Real.pi : ℂ)⁻¹ * ∫ p, (∑ i : Fin 2, ∑ j : Fin 2,
    ((maxwellConformalWeight 4 (Ω p.1.1 p.2) * maxwellConformalWeight 4 (Ω p.1.2 p.2) *
      screen p.2 i j * f p.1.1 p.2 i * g p.1.2 p.2 j : ℝ) : ℂ)) /
    ((p.1.1 : ℂ) - (p.1.2 : ℂ) - (ε : ℂ) * Complex.I) ^ 2 ∂μ

theorem maxwell4D_radiative_kernel_invariant {X : Type*} [MeasurableSpace X]
    (μ : Measure ((ℝ × ℝ) × X)) (Ω : ℝ → X → ℝ) (screen : X → Fin 2 → Fin 2 → ℝ)
    (f g : ℝ → X → Fin 2 → ℝ) (ε : ℝ) :
    maxwellRadiativeKernel μ Ω screen f g ε =
      maxwellRadiativeKernel μ (fun _ _ => 1) screen f g ε := by
  norm_num [maxwellRadiativeKernel, maxwellConformalWeight]

private theorem radiative_boundary_eq {X : Type*} [MeasurableSpace X]
    (μ : Measure ((ℝ × ℝ) × X)) (Ω : ℝ → X → ℝ) (screen : X → Fin 2 → Fin 2 → ℝ)
    (f g : ℝ → X → Fin 2 → ℝ) {v r : ℂ}
    (hv : Tendsto (maxwellRadiativeKernel μ Ω screen f g) (𝓝[>] (0 : ℝ)) (𝓝 v))
    (hr : Tendsto (maxwellRadiativeKernel μ (fun _ _ => 1) screen f g)
      (𝓝[>] (0 : ℝ)) (𝓝 r)) : v = r := by
  have hkernel : maxwellRadiativeKernel μ Ω screen f g =
      maxwellRadiativeKernel μ (fun _ _ => 1) screen f g :=
    funext (maxwell4D_radiative_kernel_invariant μ Ω screen f g)
  rw [hkernel] at hv
  exact tendsto_nhds_unique hv hr

open D5.S3.Quantum.Analysis.NullConeGravity.CCRWeylState in
/-- The transported and reference boundary covariances determine the same normalized
Gaussian state on the identified characteristic Weyl algebra. -/
theorem maxwell4D_conformal_states_equal {X S A : Type*} [MeasurableSpace X]
    [AddCommGroup S] [Module ℝ S] [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {σ : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} (W : WeylSystem (A := A) σ)
    (μ : Measure ((ℝ × ℝ) × X)) (Ω : ℝ → X → ℝ) (screen : X → Fin 2 → Fin 2 → ℝ)
    (profile : S → ℝ → X → Fin 2 → ℝ) (v r : S → ℂ)
    (vacuum reference : A →ₚ[ℂ] ℂ) (hv₁ : vacuum 1 = 1) (hr₁ : reference 1 = 1)
    (hvlim : ∀ f, Tendsto (maxwellRadiativeKernel μ Ω screen (profile f) (profile f))
      (𝓝[>] (0 : ℝ)) (𝓝 (v f)))
    (hrlim : ∀ f, Tendsto
      (maxwellRadiativeKernel μ (fun _ _ => 1) screen (profile f) (profile f))
      (𝓝[>] (0 : ℝ)) (𝓝 (r f)))
    (hv : ∀ f, vacuum (W.weyl f) = Complex.exp (-(v f) / 2))
    (hr : ∀ f, reference (W.weyl f) = Complex.exp (-(r f) / 2)) :
    vacuum = reference := by
  let V : A →L[ℂ] ℂ := ⟨vacuum.toLinearMap, state_continuous vacuum hv₁⟩
  let R : A →L[ℂ] ℂ := ⟨reference.toLinearMap, state_continuous reference hr₁⟩
  have heq : V = R := weyl_determines W V R fun f => by
    change vacuum (W.weyl f) = reference (W.weyl f)
    rw [hv f, hr f, radiative_boundary_eq μ Ω screen _ _ (hvlim f) (hrlim f)]
  ext a
  exact congrArg (fun L : A →L[ℂ] ℂ => L a) heq

open HilbertSchmidt D5.S3.Quantum.Analysis.NullConeGravity.QuarterPowerSqrtHilbertSchmidt in
/-- Bounded covariance representatives of the two transported pairings have zero root defect. -/
theorem maxwell4D_covariance_defect_zero {X K : Type*} [MeasurableSpace X]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (μ : Measure ((ℝ × ℝ) × X)) (Ω : ℝ → X → ℝ) (screen : X → Fin 2 → Fin 2 → ℝ)
    (profile : K → ℝ → X → Fin 2 → ℝ) (V R : K →L[ℂ] K)
    (hv : ∀ x y, Tendsto (maxwellRadiativeKernel μ Ω screen (profile x) (profile y))
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪x, V y⟫_ℂ))
    (hr : ∀ x y, Tendsto
      (maxwellRadiativeKernel μ (fun _ _ => 1) screen (profile x) (profile y))
      (𝓝[>] (0 : ℝ)) (𝓝 ⟪x, R y⟫_ℂ)) :
    ∃ h : IsHilbertSchmidt (CFC.sqrt V - CFC.sqrt R), hsSq _ h = 0 := by
  have heq : V = R := by
    ext y
    apply ext_inner_left ℂ
    intro x
    exact radiative_boundary_eq μ Ω screen _ _ (hv x y) (hr x y)
  subst V
  simp only [sub_self]
  obtain ⟨ι, ⟨b, _⟩⟩ := exists_hilbertBasis ℂ K
  exact ⟨⟨ι, b, by simp⟩, by simp [hsSq]⟩

/-- The exponent of the transverse Proca rescaling. -/
def procaBeta (D : ℕ) : ℝ := ((D : ℝ) - 4) / 2

/-- The dimension-dependent curvature coefficient in the rescaled equation. -/
def procaCurvaturePotential (D : ℕ) : ℝ := procaBeta D * (procaBeta D + 1)

theorem proca_curvature_potential_eq (D : ℕ) :
    procaCurvaturePotential D = ((D : ℝ) - 4) * ((D : ℝ) - 2) / 4 := by
  unfold procaCurvaturePotential procaBeta
  ring

theorem proca_curvature_potential_zero_iff (D : ℕ) (hD : 3 ≤ D) :
    procaCurvaturePotential D = 0 ↔ D = 4 := by
  have hD' : (3 : ℝ) ≤ D := by exact_mod_cast hD
  rw [proca_curvature_potential_eq, div_eq_zero_iff, mul_eq_zero]
  have h₂ : (D : ℝ) - 2 ≠ 0 := by linarith
  simp only [h₂, or_false, OfNat.ofNat_ne_zero]
  rw [sub_eq_zero]
  exact Nat.cast_inj

theorem proca_transverse_rescaled_ode (D : ℕ) {H t : ℝ} (hH : 0 < H) (ht : t < 0)
    (k m : ℝ) (A : ℝ → ℝ) (hA : ∀ s < 0, DifferentiableAt ℝ A s)
    (hA' : DifferentiableAt ℝ (deriv A) t) :
    let Ω := Omega.inverseTimeScale H
    let v := fun s => Ω s ^ procaBeta D * A s
    deriv (fun s => maxwellConformalWeight D (Ω s) * deriv A s) t +
        maxwellConformalWeight D (Ω t) * (k ^ 2 + Ω t ^ 2 * m ^ 2) * A t =
      Ω t ^ procaBeta D *
        (deriv (deriv v) t +
          (k ^ 2 + Ω t ^ 2 * m ^ 2 - procaCurvaturePotential D / t ^ 2) * v t) := by
  dsimp only
  have hw {s : ℝ} (hs : s < 0) :
      (Omega.inverseTimeScale H s ^ procaBeta D) ^ 2 =
        maxwellConformalWeight D (Omega.inverseTimeScale H s) := by
    have hp : 0 < Omega.inverseTimeScale H s :=
      Omega.inverseTimeScale_pos hH hs
    rw [pow_two, ← Real.rpow_add hp, maxwellConformalWeight, ← Real.rpow_intCast]
    congr 1
    push_cast
    unfold procaBeta
    ring
  have hd : (fun s => maxwellConformalWeight D (Omega.inverseTimeScale H s) * deriv A s)
      =ᶠ[nhds t] (fun s => (Omega.inverseTimeScale H s ^ procaBeta D) ^ 2 * deriv A s) := by
    filter_upwards [Iio_mem_nhds ht] with s hs using congrArg (· * deriv A s) (hw hs).symm
  rw [hd.deriv_eq, ← hw ht]
  exact Omega.inverseTime_rescaled_ode hH ht (procaBeta D) A
    (fun s => k ^ 2 + Omega.inverseTimeScale H s ^ 2 * m ^ 2) hA hA'

/-- The longitudinal quadratic density, before eliminating the temporal component. -/
def procaLongitudinalDensity (D : ℕ) (Ω k m a u : ℝ) : ℝ :=
  maxwellConformalWeight D Ω / 2 * (u - k * a) ^ 2 +
    Ω ^ ((D : ℤ) - 2) / 2 * m ^ 2 * a ^ 2

/-- Completing the square gives the exact kinetic weight and a unique global minimizer. -/
theorem proca_longitudinal_kinetic_weight (D : ℕ) {Ω k m : ℝ}
    (hΩ : 0 < Ω) (hk : 0 < k) (hm : 0 < m) (u : ℝ) :
    let c := k ^ 2 + Ω ^ 2 * m ^ 2
    let a₀ := k / c * u
    let reduced := maxwellConformalWeight D Ω * Ω ^ 2 * m ^ 2 / (2 * c) * u ^ 2
    procaLongitudinalDensity D Ω k m a₀ u = reduced ∧
      (∀ a, procaLongitudinalDensity D Ω k m a u =
        reduced + maxwellConformalWeight D Ω * c / 2 * (a - a₀) ^ 2) ∧
      ∀ a, procaLongitudinalDensity D Ω k m a₀ u ≤ procaLongitudinalDensity D Ω k m a u ∧
        (procaLongitudinalDensity D Ω k m a u =
          procaLongitudinalDensity D Ω k m a₀ u ↔ a = a₀) := by
  dsimp only
  let c := k ^ 2 + Ω ^ 2 * m ^ 2
  let a₀ := k / c * u
  let w := maxwellConformalWeight D Ω
  let reduced := w * Ω ^ 2 * m ^ 2 / (2 * c) * u ^ 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hw : 0 < w := zpow_pos hΩ _
  have hmass : Ω ^ ((D : ℤ) - 2) = w * Ω ^ 2 := by
    rw [show (D : ℤ) - 2 = (D : ℤ) - 4 + 2 by ring, zpow_add₀ hΩ.ne']
    rfl
  have hsq (a : ℝ) : procaLongitudinalDensity D Ω k m a u =
      reduced + w * c / 2 * (a - a₀) ^ 2 := by
    rw [procaLongitudinalDensity, hmass]
    change w / 2 * (u - k * a) ^ 2 + w * Ω ^ 2 / 2 * m ^ 2 * a ^ 2 = _
    dsimp only [reduced, a₀]
    field_simp [hc.ne']
    dsimp [c]
    ring
  have hmin : procaLongitudinalDensity D Ω k m a₀ u = reduced := by
    rw [hsq a₀, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]
  refine ⟨hmin, hsq, fun a => ⟨?_, ?_⟩⟩
  · rw [hmin, hsq a]
    exact le_add_of_nonneg_right (by positivity)
  · rw [hmin, hsq a]
    constructor
    · intro ha
      have hz : w * c / 2 * (a - a₀) ^ 2 = 0 := by linarith only [ha]
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by decide : 2 ≠ 0)).mp
        ((mul_eq_zero.mp hz).resolve_left (by positivity : w * c / 2 ≠ 0)))
    · rintro rfl
      rw [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero]

end NullConeGravity
