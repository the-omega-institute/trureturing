/- GID: D5/S3/Observer/Linear/FrameNonCancellation
   generality: G
   mirror-B: D5/B/S3/Observer/Linear/FrameNonCancellation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A positive frame floor excludes blind modes while unbounded tails can evade uniform control. -/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
Library-search audit trail (2026-09-06):
* D5 exact-name, frame, blind-kernel, and body-shape searches found
  `RobustFrameBounds.robust_observer_frame_bounds`,
  `PositiveWeightedReadoutGramKernel.positive_weighted_readout_gram`, and
  `FiniteWindowGlobalBoundary.finite_window_positive_global_boundary` as
  partial carriers, but no public theorem combining the positive-frame
  implication, a one-channel blind mode, and a complete tail family without a
  uniform lower bound.
* Pinned Mathlib supplies `csInf_le`, `lp.evalₗ`, `lp.single`,
  `lp.hasSum_norm`, `tsum_eq_single`, and
  `tendsto_one_div_add_atTop_nhds_zero_nat`; no packaged theorem states the
  combined frame/non-cancellation boundary.
* GitHub code search found `TauCeti.LowerFrameBound.injective` in
  `AIQ-Kitware/aiq-dkps-formalization` at
  `dd65ae73c6845d96e238a7dc3876ebd5b6a722ec` (Apache-2.0), but that project
  is pinned to Lean `v4.34.0-rc1`, so spec A17.2 rules out dependency form.
  Its theorem assumes a supplied lower bound and does not carry the source's
  infimum coefficient or either contrast construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Linear.FrameNonCancellation

open Filter Topology

/-- The source frame coefficient: the infimum of the nonzero squared-norm
Rayleigh ratios of an analysis map. -/
def frameLowerCoefficient
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace Real H]
    [NormedAddCommGroup K] [NormedSpace Real K]
    (analysis : H →ₗ[Real] K) : Real :=
  sInf {r : Real | exists d : H, d ≠ 0 /\
    r = ‖analysis d‖ ^ 2 / ‖d‖ ^ 2}

/-- The source offline-mode carrier specialized to countably many real modes. -/
abbrev OfflineModeSpace := lp (fun _ : Nat => Real) 2

/-- Coordinate `n` is tested with attenuation `1 / (n + 1)`. -/
def attenuatedCoordinateReadout (n : Nat) :
    OfflineModeSpace →ₗ[Real] Real :=
  (1 / ((n : Real) + 1)) •
    lp.evalₗ (fun _ : Nat => Real) 2 n

/-- The total squared analysis energy of the attenuated coordinate family. -/
def attenuatedAnalysisEnergy (d : OfflineModeSpace) : Real :=
  ∑' n, (attenuatedCoordinateReadout n d) ^ 2

private theorem attenuated_coordinate_energy_formula (n : Nat) :
    ‖lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)‖ = 1 /\
    attenuatedAnalysisEnergy
        (lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)) =
      (1 / ((n : Real) + 1)) ^ 2 := by
  constructor
  · rw [lp.norm_single (p := (2 : ENNReal)) (by positivity)]
    simp
  · rw [attenuatedAnalysisEnergy, tsum_eq_single n]
    · simp [attenuatedCoordinateReadout, lp.evalₗ_apply]
    · intro m hmn
      simp only [attenuatedCoordinateReadout, LinearMap.smul_apply,
        smul_eq_mul, lp.evalₗ_apply, mul_pow]
      rw [lp.single_apply_ne (E := fun _ : Nat => Real)
        (p := (2 : ENNReal)) n (1 : Real) hmn]
      simp

/-- The attenuated countable coordinate family is complete and has summable,
nonnegative squared analysis energy, yet its unit coordinate modes escape to
the tail with energy tending to zero. Consequently it has no positive uniform
lower frame bound. -/
theorem attenuated_coordinate_family_tail_escape :
    (forall d : OfflineModeSpace,
      (forall n, attenuatedCoordinateReadout n d = 0) -> d = 0) /\
    (forall d : OfflineModeSpace,
      Summable fun n => (attenuatedCoordinateReadout n d) ^ 2) /\
    (forall d : OfflineModeSpace, 0 <= attenuatedAnalysisEnergy d) /\
    Tendsto
      (fun n => attenuatedAnalysisEnergy
        (lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)))
      atTop (nhds 0) /\
    (forall alpha : Real, 0 < alpha -> exists d : OfflineModeSpace,
      ‖d‖ = 1 /\
        attenuatedAnalysisEnergy d < alpha) := by
  have tailLimit :
      Tendsto
        (fun n => attenuatedAnalysisEnergy
          (lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)))
        atTop (nhds 0) := by
    convert
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := Real)).pow 2 using 1
    ext n
    exact (attenuated_coordinate_energy_formula n).2
    simp
  refine ⟨?_, ?_, ?_, tailLimit, ?_⟩
  · intro d hreadout
    apply lp.ext
    funext n
    have hn := hreadout n
    simp [attenuatedCoordinateReadout, lp.evalₗ_apply] at hn
    exact hn.resolve_left (by positivity)
  · intro d
    have baseSummable : Summable (fun n => ‖d n‖ ^ 2) := by
      simpa using
        (lp.hasSum_norm (p := (2 : ENNReal)) (by simp) d).summable
    refine baseSummable.of_nonneg_of_le (fun n => sq_nonneg _) ?_
    intro n
    simp only [attenuatedCoordinateReadout, LinearMap.smul_apply,
      smul_eq_mul, lp.evalₗ_apply, Real.norm_eq_abs]
    have weightNonnegative : 0 <= 1 / ((n : Real) + 1) := by positivity
    have weightAtMostOne : 1 / ((n : Real) + 1) <= 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.le_add_left 1 n
    have weightSquareAtMostOne : (1 / ((n : Real) + 1)) ^ 2 <= 1 := by
      nlinarith
    calc
      (1 / ((n : Real) + 1) * d n) ^ 2 =
          (1 / ((n : Real) + 1)) ^ 2 * (d n) ^ 2 := by ring
      _ <= 1 * (d n) ^ 2 :=
        mul_le_mul_of_nonneg_right weightSquareAtMostOne (sq_nonneg _)
      _ = |d n| ^ 2 := by simp
  · intro d
    unfold attenuatedAnalysisEnergy
    exact tsum_nonneg fun _ => sq_nonneg _
  · intro alpha halpha
    have eventuallySmall :
        ∀ᶠ n in atTop,
          attenuatedAnalysisEnergy
            (lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)) < alpha :=
      (tendsto_order.1 tailLimit).2 alpha halpha
    rcases eventuallySmall.exists with ⟨n, hn⟩
    exact ⟨lp.single (E := fun _ : Nat => Real) 2 n (1 : Real),
      (attenuated_coordinate_energy_formula n).1, hn⟩

/-- A positive frame coefficient excludes nonzero blind modes. In contrast, a
single positive-square channel can have a nontrivial kernel, and a complete
countable test family without a uniform lower frame bound can have unit modes
whose analysis energy escapes to the infinite tail. -/
theorem frame_non_cancellation
    {H K : Type*}
    [NormedAddCommGroup H] [NormedSpace Real H]
    [NormedAddCommGroup K] [NormedSpace Real K]
    (analysis : H →ₗ[Real] K)
    (alphaPositive : 0 < frameLowerCoefficient analysis) :
    (forall d : H, analysis d = 0 -> d = 0) /\
    (exists channel : (Real × Real) →ₗ[Real] Real,
      exists blind : Real × Real,
        blind ≠ 0 /\
        (forall x, 0 <= (channel x) ^ 2) /\
        channel blind = 0) /\
    (forall d : OfflineModeSpace,
      (forall n, attenuatedCoordinateReadout n d = 0) -> d = 0) /\
    (forall d : OfflineModeSpace,
      Summable fun n => (attenuatedCoordinateReadout n d) ^ 2) /\
    (forall d : OfflineModeSpace, 0 <= attenuatedAnalysisEnergy d) /\
    Tendsto
      (fun n => attenuatedAnalysisEnergy
        (lp.single (E := fun _ : Nat => Real) 2 n (1 : Real)))
      atTop (nhds 0) /\
    (forall alpha : Real, 0 < alpha -> exists d : OfflineModeSpace,
      ‖d‖ = 1 /\
        attenuatedAnalysisEnergy d < alpha) := by
  have quotientBounded : BddBelow
      {r : Real | exists d : H, d ≠ 0 /\
        r = ‖analysis d‖ ^ 2 / ‖d‖ ^ 2} := by
    refine ⟨0, ?_⟩
    rintro r ⟨d, hd, rfl⟩
    positivity
  have injectiveConclusion : forall d : H, analysis d = 0 -> d = 0 := by
    intro d hd
    by_contra dNonzero
    have lowerAtD : frameLowerCoefficient analysis <=
        ‖analysis d‖ ^ 2 / ‖d‖ ^ 2 := by
      apply csInf_le quotientBounded
      exact ⟨d, dNonzero, rfl⟩
    rw [hd] at lowerAtD
    simp at lowerAtD
    exact (not_lt_of_ge lowerAtD) alphaPositive
  let channel : (Real × Real) →ₗ[Real] Real :=
    { toFun := Prod.fst
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }
  have singleChannelBlind :
      exists blind : Real × Real,
        blind ≠ 0 /\
        (forall x, 0 <= (channel x) ^ 2) /\
        channel blind = 0 := by
    refine ⟨(0, 1), by simp, ?_, rfl⟩
    intro x
    exact sq_nonneg _
  exact ⟨injectiveConclusion, ⟨channel, singleChannelBlind⟩,
    attenuated_coordinate_family_tail_escape⟩

/-- The positive-frame hypothesis is satisfiable on the identity map. -/
example :
    0 < frameLowerCoefficient (LinearMap.id : Real →ₗ[Real] Real) := by
  have valueSet :
      {r : Real | exists d : Real, d ≠ 0 /\
        r = ‖(LinearMap.id : Real →ₗ[Real] Real) d‖ ^ 2 / ‖d‖ ^ 2} =
        {1} := by
    ext r
    constructor
    · rintro ⟨d, hd, rfl⟩
      simp only [LinearMap.id_apply, Set.mem_singleton_iff]
      exact div_self (pow_ne_zero 2 (norm_ne_zero_iff.mpr hd))
    · intro hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      exact ⟨1, one_ne_zero, by simp⟩
  rw [frameLowerCoefficient, valueSet, csInf_singleton]
  simp

#print axioms attenuated_coordinate_family_tail_escape
#print axioms frame_non_cancellation

end D5.S3.Observer.Linear.FrameNonCancellation
