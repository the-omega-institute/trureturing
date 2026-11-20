/- GID: D5/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/LinearGroups/OneParameterGenerators
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One-parameter generators of a locally compact linear group form a Lie subalgebra. -/

import D5.S3.Quantum.Analysis.LinearGroups.OneParameterEscape
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# One-parameter generators form a Lie subalgebra

Let `A` be a finite-dimensional real normed algebra, `G` a locally compact topological group and
`ρ : G →* Aˣ` a continuous injective homomorphism. The one-parameter generators of `G` in `A`
(`IsOneParameterGenerator`) are closed under sums and commutators, and therefore form a Lie
subalgebra `generatorSubalgebra` of `A` with the commutator bracket.

* Sums: if a curve `c` in `G` through `1` has `ρ ∘ c` differentiable at `0` with velocity `D`,
  then the local logarithms of `ρ (c s)` approach `0` along the direction of `D`, and the escape
  lemma shows that `D` is a generator. The product of the curves of `X` and `Y` has velocity
  `X + Y`.
* Commutators: conjugating the curve of `Y` by the curve of `X` at time `s` lifts
  `exp (s • X) * Y * exp (s • -X)`, so these elements are generators; their difference
  quotients at `s = 0` are generators and converge to `X * Y - Y * X`, and the set of generators
  is closed.
-/

namespace D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators

open Filter
open scoped Topology
open D5.S3.Quantum.Analysis.LinearGroups.OneParameterEscape

section Generators

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]
  {G : Type*} [TopologicalSpace G] [Group G]

/-- The zero element is a generator, lifted by the constant curve at `1`. -/
private theorem isOneParameterGenerator_zero (ρ : G →* Aˣ) :
    IsOneParameterGenerator ρ (0 : A) :=
  ⟨fun _ => 1, continuous_const, fun t => by simp⟩

variable [FiniteDimensional ℝ A] [IsTopologicalGroup G] [LocallyCompactSpace G]

/-- Velocity lemma: if a curve `c` in `G` is continuous at `0` with `ρ (c 0) = 1` and
`s ↦ ρ (c s)` has derivative `D` at `0`, then `D` is a generator. -/
private theorem isOneParameterGenerator_of_hasDerivAt {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {c : ℝ → G} (hcc : ContinuousAt c 0)
    (h1 : ((ρ (c 0) : Aˣ) : A) = 1) {D : A}
    (hD : HasDerivAt (fun s => ((ρ (c s) : Aˣ) : A)) D 0) : IsOneParameterGenerator ρ D := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  by_cases hD0 : D = 0
  · rw [hD0]
    exact isOneParameterGenerator_zero ρ
  have hc0 : c 0 = 1 := hi (Units.ext (by rw [h1, map_one, Units.val_one]))
  -- a local logarithm: the local inverse of `exp` at `0`
  have hexp : HasStrictFDerivAt (NormedSpace.exp : A → A)
      ((ContinuousLinearEquiv.refl ℝ A : A ≃L[ℝ] A) : A →L[ℝ] A) 0 := by
    convert hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := A) using 1
    ext
    simp
  set ell : A → A := hexp.localInverse NormedSpace.exp _ 0
  have hell0 : ell 1 = 0 := by
    simpa [ell, NormedSpace.exp_zero] using hexp.localInverse_apply_image
  have hell : HasFDerivAt ell (ContinuousLinearMap.id ℝ A) 1 := by
    simpa [ell, NormedSpace.exp_zero] using hexp.to_localInverse.hasFDerivAt
  have hinv : ∀ᶠ y in 𝓝 (1 : A), NormedSpace.exp (ell y) = y := by
    simpa [ell, NormedSpace.exp_zero] using hexp.eventually_right_inverse
  -- the logarithm `Z` of the curve has derivative `D` at `0`
  set Z : ℝ → A := fun s => ell ((ρ (c s) : Aˣ) : A)
  have hZ : HasDerivAt Z D 0 := by
    simpa [Z, Function.comp_def] using hell.comp_hasDerivAt_of_eq (0 : ℝ) hD h1.symm
  have hZ0 : Z 0 = 0 := by simp [Z, h1, hell0]
  have hslope : Tendsto (fun s : ℝ => s⁻¹ • Z s) (𝓝[>] 0) (𝓝 D) := by
    simpa [hZ0] using hZ.tendsto_slope_zero_right
  have hval : Tendsto (fun s : ℝ => ((ρ (c s) : Aˣ) : A)) (𝓝[>] 0) (𝓝 1) := by
    simpa [h1] using hD.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hP : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      ((ρ (c s) : Aˣ) : A) = NormedSpace.exp (Z s) ∧ Z s ≠ 0 := by
    filter_upwards [hval.eventually hinv, hslope.eventually_ne hD0] with s hs hs'
    refine ⟨hs.symm, fun h => hs' ?_⟩
    rw [h, smul_zero]
  have hdir : Tendsto (fun s : ℝ => ‖Z s‖⁻¹ • Z s) (𝓝[>] 0) (𝓝 (‖D‖⁻¹ • D)) := by
    refine ((hslope.norm.inv₀ (norm_ne_zero_iff.2 hD0)).smul hslope).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [norm_smul, norm_inv, Real.norm_of_nonneg (le_of_lt hs), smul_smul, mul_inv, inv_inv,
      mul_comm s, mul_assoc, mul_inv_cancel₀ (ne_of_gt hs), mul_one]
  -- a sequence of times along which all conditions hold
  have hu : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun k => Set.mem_Ioi.2 (by positivity)⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hu.eventually hP)
  set v : ℕ → ℝ := fun k => 1 / (((k + N : ℕ) : ℝ) + 1)
  have hv : Tendsto v atTop (𝓝[>] 0) := (tendsto_add_atTop_iff_nat N).2 hu
  have hPv : ∀ k, ((ρ (c (v k)) : Aˣ) : A) = NormedSpace.exp (Z (v k)) ∧ Z (v k) ≠ 0 :=
    fun k => hN (k + N) (Nat.le_add_left N k)
  have hg : Tendsto (fun k => c (v k)) atTop (𝓝 1) := by
    have h := hcc.tendsto.comp (hv.mono_right nhdsWithin_le_nhds)
    rw [hc0] at h
    exact h
  have hY0 : Tendsto (fun k => Z (v k)) atTop (𝓝 0) := by
    have h := hZ.continuousAt.tendsto.comp (hv.mono_right nhdsWithin_le_nhds)
    rw [hZ0] at h
    exact h
  have hgen := isOneParameterGenerator_of_mapClusterPt ρ hc hi hg hY0 (fun k => (hPv k).1)
    (fun k => (hPv k).2) (hdir.comp hv).mapClusterPt
  have hgen' := hgen.smul ‖D‖
  rwa [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hD0), one_smul] at hgen'

/-- The sum of two one-parameter generators is a one-parameter generator. -/
theorem IsOneParameterGenerator.add {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {X Y : A} (hX : IsOneParameterGenerator ρ X)
    (hY : IsOneParameterGenerator ρ Y) : IsOneParameterGenerator ρ (X + Y) := by
  obtain ⟨γ, hγc, hγ⟩ := hX
  obtain ⟨β, hβc, hβ⟩ := hY
  refine isOneParameterGenerator_of_hasDerivAt hc hi (c := fun s => γ s * β s)
    (hγc.mul hβc).continuousAt (by simp [hγ, hβ]) ?_
  have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul
    (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y 0)
  simp only [map_mul, Units.val_mul, hγ, hβ]
  convert h using 1
  simp

/-- The commutator of two one-parameter generators is a one-parameter generator. -/
theorem IsOneParameterGenerator.commutator {ρ : G →* Aˣ} (hc : Continuous ρ)
    (hi : Function.Injective ρ) {X Y : A} (hX : IsOneParameterGenerator ρ X)
    (hY : IsOneParameterGenerator ρ Y) :
    IsOneParameterGenerator ρ (X * Y - Y * X) := by
  let _ : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  obtain ⟨γ, hγc, hγ⟩ := hX
  have hinv : ∀ s : ℝ, (((ρ (γ s))⁻¹ : Aˣ) : A) = NormedSpace.exp (s • -X) := fun s =>
    Units.inv_eq_of_mul_eq_one_right (by
      rw [hγ, ← NormedSpace.exp_add_of_commute
        (((Commute.refl X).neg_right.smul_left s).smul_right s), ← smul_add, add_neg_cancel,
        smul_zero, NormedSpace.exp_zero])
  -- conjugates of `Y` by the curve of `X` are generators
  have hconj : ∀ s : ℝ, IsOneParameterGenerator ρ
      (NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X)) := by
    intro s
    obtain ⟨β, hβc, hβ⟩ := hY
    refine ⟨fun t => γ s * β t * (γ s)⁻¹, (continuous_const.mul hβc).mul continuous_const,
      fun t => ?_⟩
    rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, hβ,
      ← NormedSpace.exp_units_conj, ← hγ s, ← hinv s, mul_smul_comm, smul_mul_assoc]
  -- the derivative of the conjugates at `0` is the commutator
  have hderiv : HasDerivAt (fun s : ℝ => NormedSpace.exp (s • X) * Y * NormedSpace.exp (s • -X))
      (X * Y - Y * X) 0 := by
    have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0).mul_const Y).mul
      (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0)
    convert h using 1
    simp [sub_eq_add_neg]
  have hlim := hderiv.tendsto_slope_zero
  simp only [zero_add, zero_smul, NormedSpace.exp_zero, one_mul, mul_one] at hlim
  refine (isClosed_setOf_isOneParameterGenerator hc hi).mem_of_tendsto hlim
    (Eventually.of_forall fun t => ?_)
  rw [sub_eq_add_neg, ← neg_one_smul ℝ Y]
  exact (IsOneParameterGenerator.add hc hi (hconj t) (hY.smul (-1))).smul t⁻¹

section LieSubalgebra

attribute [local instance] LieRing.ofAssociativeRing

/-- The Lie subalgebra of one-parameter generators. -/
noncomputable def generatorSubalgebra (ρ : G →* Aˣ) (hc : Continuous ρ)
    (hi : Function.Injective ρ) : LieSubalgebra ℝ A where
  carrier := {X | IsOneParameterGenerator ρ X}
  add_mem' := fun hX hY => IsOneParameterGenerator.add hc hi hX hY
  zero_mem' := isOneParameterGenerator_zero ρ
  smul_mem' := fun c _ hX => hX.smul c
  lie_mem' := fun hX hY => by
    rw [Ring.lie_def]
    exact IsOneParameterGenerator.commutator hc hi hX hY

end LieSubalgebra

end Generators

end D5.S3.Quantum.Analysis.LinearGroups.OneParameterGenerators
