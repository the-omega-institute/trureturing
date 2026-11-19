/- GID: D5/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Divergence/GeneralConvexReverseTestAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Original whole-L1 normal reverse tests and posterior extended attainment. -/

import D5.S3.Quantum.Analysis.NormalMomentFamily
import D5.S3.Quantum.Analysis.ConcreteCoefficientSeries
import D5.S3.Quantum.Divergence.PosteriorSourceNormalization
import D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest
import D5.S3.Analytic.Convexity.PosteriorCurvatureCost

/-! Original source universes and operator-algebra universes are independent.
Preparations are algebraic on the entire complex L1 space; boundedness is not
an input condition. Normality means the intrinsic all-directed order condition. -/

noncomputable section
universe u v

open Set MeasureTheory Filter
open scoped ComplexOrder ENNReal NNReal Topology
open D5.S3.Analytic.Convexity.CurvatureHingeRepresentation
open D5.S3.Analytic.Convexity.PosteriorCurvatureCost
open D5.S3.Quantum.Analysis.NormalFunctionals
open D5.S3.Quantum.Analysis.NormalMomentFamily
open D5.S3.Quantum.Divergence.PosteriorSourceNormalization
open D5.S3.Quantum.Divergence.MaximalHockeyStickL1ReverseTest

namespace D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

variable {A : Type v} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The original admissible preparation, with no continuity or norm hypothesis. -/
structure NormalL1Preparation {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  toLinearMap : (X →₁[μ] ℂ) →ₗ[ℂ] StrongDual ℂ A
  positive : ∀ h, (∀ᵐ x ∂μ, 0 ≤ h x) → ∀ a : A, 0 ≤ a → 0 ≤ toLinearMap h a
  mass : ∀ h, toLinearMap h 1 = ∫ x, h x ∂μ
  normal : ∀ h, IsOrderNormal (toLinearMap h)

/-- Measurable real representatives of the two nonnegative original L1 inputs. -/
structure NormalL1ReverseTest (ρ σ : StrongDual ℂ A)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  preparation : NormalL1Preparation (A := A) μ
  p : X → ℝ
  q : X → ℝ
  p_measurable : Measurable p
  q_measurable : Measurable q
  p_integrable : Integrable p μ
  q_integrable : Integrable q μ
  p_nonneg : ∀ᵐ x ∂μ, 0 ≤ p x
  q_nonneg : ∀ᵐ x ∂μ, 0 ≤ q x
  prepares_left : preparation.toLinearMap (p_integrable.ofReal.toL1 (fun x => (p x : ℂ))) = ρ
  prepares_right : preparation.toLinearMap (q_integrable.ofReal.toL1 (fun x => (q x : ℂ))) = σ

/-- All actual sigma-finite source spaces of the fixed universe u. -/
def representativeCosts {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (ρ σ : StrongDual ℂ A) : Set EReal :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI := m
    ∃ μ : Measure X, SigmaFinite μ ∧ ∃ R : NormalL1ReverseTest ρ σ μ,
      z = closedPerspectiveCost hf μ R.p R.q}

/-- Arbitrary nonnegative original complex L1 inputs keep their exact preparation
and representative-independent literal cost in the fixed-universe source class. -/
theorem representativeCosts_of_positive_L1 {X : Type u} [MeasurableSpace X]
    {μ : Measure X} [SigmaFinite μ] (Γ : NormalL1Preparation (A := A) μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (p q : X →₁[μ] ℂ) (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x) :
    closedPerspectiveCost hf μ (fun x => (p x).re) (fun x => (q x).re) ∈
      representativeCosts.{u} hf (Γ.toLinearMap p) (Γ.toLinearMap q) := by
  obtain ⟨p', hp', hpm, hpn, hpe, hpr⟩ := measurable_positive_L1_input p hp
  obtain ⟨q', hq', hqm, hqn, hqe, hqr⟩ := measurable_positive_L1_input q hq
  exact ⟨X, inferInstance, μ, inferInstance,
    { preparation := Γ, p := p', q := q', p_measurable := hpm, q_measurable := hqm,
      p_integrable := hp', q_integrable := hq', p_nonneg := hpn, q_nonneg := hqn,
      prepares_left := congrArg Γ.toLinearMap hpe,
      prepares_right := congrArg Γ.toLinearMap hqe },
    (cost_congr_ae hf hpr hqr).symm⟩

/-- The literal original class: arbitrary nonnegative elements of the entire
complex L1 space, in the prescribed source universe and independent of A. -/
def attainableCosts {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (ρ σ : StrongDual ℂ A) : Set EReal :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI := m
    ∃ μ : Measure X, SigmaFinite μ ∧ ∃ Γ : NormalL1Preparation (A := A) μ,
      ∃ p q : X →₁[μ] ℂ,
        (∀ᵐ x ∂μ, 0 ≤ p x) ∧ (∀ᵐ x ∂μ, 0 ≤ q x) ∧
        Γ.toLinearMap p = ρ ∧ Γ.toLinearMap q = σ ∧
        z = closedPerspectiveCost hf μ (fun x => (p x).re) (fun x => (q x).re)}

/-- Measurable representatives preserve the full original cost set, the original
preparation and both exact L1 inputs. This equality is consumed by attainment. -/
theorem attainableCosts_eq_representativeCosts
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) (ρ σ : StrongDual ℂ A) :
    attainableCosts.{u} hf ρ σ = representativeCosts.{u} hf ρ σ := by
  ext z
  constructor
  · rintro ⟨X, m, μ, hμ, Γ, p, q, hp, hq, hl, hr, rfl⟩
    letI := m
    letI := hμ
    simpa only [hl, hr] using representativeCosts_of_positive_L1 Γ hf p q hp hq
  · rintro ⟨X, m, μ, hμ, R, rfl⟩
    letI := m
    let P : X →₁[μ] ℂ := R.p_integrable.ofReal.toL1 (fun x => (R.p x : ℂ))
    let Q : X →₁[μ] ℂ := R.q_integrable.ofReal.toL1 (fun x => (R.q x : ℂ))
    have hP : P =ᵐ[μ] (fun x => (R.p x : ℂ)) :=
      (R.p_integrable.ofReal : Integrable (fun x => (R.p x : ℂ)) μ).coeFn_toL1
    have hQ : Q =ᵐ[μ] (fun x => (R.q x : ℂ)) :=
      (R.q_integrable.ofReal : Integrable (fun x => (R.q x : ℂ)) μ).coeFn_toL1
    have hpn : ∀ᵐ x ∂μ, 0 ≤ P x := by
      filter_upwards [hP, R.p_nonneg] with x he hn
      rw [he]
      exact_mod_cast hn
    have hqn : ∀ᵐ x ∂μ, 0 ≤ Q x := by
      filter_upwards [hQ, R.q_nonneg] with x he hn
      rw [he]
      exact_mod_cast hn
    have hpr : (fun x => (P x).re) =ᵐ[μ] R.p := by
      filter_upwards [hP] with x he
      simp only [he, Complex.ofReal_re]
    have hqr : (fun x => (Q x).re) =ᵐ[μ] R.q := by
      filter_upwards [hQ] with x he
      simp only [he, Complex.ofReal_re]
    exact ⟨X, m, μ, hμ, R.preparation, P, Q, hpn, hqn,
      R.prepares_left, R.prepares_right, (cost_congr_ae hf hpr hqr).symm⟩

/-- The full literal posterior objective. -/
def familyCost {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {ρ σ : StrongDual ℂ A} (F : Family ρ σ) : EReal :=
  closedPerspectiveCost hf (scalarMeasure F) (fun t => t.val) (fun t => 1 - t.val)

private theorem sum_input {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {p q : X → ℝ} (hp : Integrable p μ) (hq : Integrable q μ) :
    (hp.add hq).ofReal.toL1 (fun x => ((p x + q x : ℝ) : ℂ)) =
      hp.ofReal.toL1 (fun x => (p x : ℂ)) + hq.ofReal.toL1 (fun x => (q x : ℂ)) := by
  let hpC : Integrable (fun x => (p x : ℂ)) μ := hp.ofReal
  let hqC : Integrable (fun x => (q x : ℂ)) μ := hq.ofReal
  let hrC : Integrable (fun x => ((p x + q x : ℝ) : ℂ)) μ := (hp.add hq).ofReal
  apply Lp.ext
  filter_upwards [hrC.coeFn_toL1, hpC.coeFn_toL1,
    hqC.coeFn_toL1, Lp.coeFn_add
      (hp.ofReal.toL1 (fun x => (p x : ℂ))) (hq.ofReal.toL1 (fun x => (q x : ℂ)))]
    with x hsum hpx hqx hadd
  rw [hsum, hadd, Pi.add_apply, hpx, hqx, Complex.ofReal_add]

/-- Every original algebraic preparation gives an actual compatible family point. -/
def posteriorFamily {ρ σ : StrongDual ℂ A} {X : Type*} [MeasurableSpace X]
    {μ : Measure X} (R : NormalL1ReverseTest ρ σ μ) : Family ρ σ := by
  let P := pullContinuous R.p_measurable R.q_measurable R.p_integrable R.q_integrable
  let J := R.preparation.toLinearMap.comp P.toLinearMap
  apply ofLinearMap J
  · intro g hg a ha
    exact R.preparation.positive _
      (pullContinuous_positive R.p_measurable R.q_measurable
        R.p_integrable R.q_integrable g hg) a ha
  · change R.preparation.toLinearMap (P 1) = _
    rw [(pullContinuous_moments R.p_measurable R.q_measurable
      R.p_integrable R.q_integrable R.p_nonneg R.q_nonneg).1,
      sum_input R.p_integrable R.q_integrable, map_add, R.prepares_left, R.prepares_right]
  · change R.preparation.toLinearMap (P posterior) = _
    have he : posterior = coordinate := by ext t; rfl
    rw [he, (pullContinuous_moments R.p_measurable R.q_measurable
      R.p_integrable R.q_integrable R.p_nonneg R.q_nonneg).2.1, R.prepares_left]

/-- The Riesz measure is the actual weighted pushforward of the original source. -/
theorem posteriorFamily_scalarMeasure {ρ σ : StrongDual ℂ A}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (R : NormalL1ReverseTest ρ σ μ) :
    scalarMeasure (posteriorFamily R) = posteriorMeasure μ R.p R.q := by
  letI := (posteriorMeasure_finite_regular R.p_integrable R.q_integrable).1
  have he : finiteMeasure (posteriorFamily R) =
      (⟨posteriorMeasure μ R.p R.q, inferInstance⟩ : FiniteMeasure Interval) := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro g
    let gC : C(Interval, ℂ) := ⟨fun t => (g t : ℂ), by fun_prop⟩
    have h := integral_complex (posteriorFamily R) gC
    change R.preparation.toLinearMap
      (pullContinuous R.p_measurable R.q_measurable R.p_integrable R.q_integrable gC) 1 = _ at h
    rw [R.preparation.mass, ← integral_pullContinuous R.p_measurable R.q_measurable
      R.p_integrable R.q_integrable] at h
    change (∫ t, (g t : ℂ) ∂posteriorMeasure μ R.p R.q) =
      ∫ t, (g t : ℂ) ∂scalarMeasure (posteriorFamily R) at h
    rw [integral_complex_ofReal, integral_complex_ofReal] at h
    exact congrArg Complex.re h.symm
  exact congrArg (fun ν : FiniteMeasure Interval => (ν : Measure Interval)) he

/-- Exact forward preservation, with no finiteness premise on the extended cost. -/
theorem source_cost_eq_familyCost {ρ σ : StrongDual ℂ A}
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (R : NormalL1ReverseTest ρ σ μ)
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    closedPerspectiveCost hf μ R.p R.q = familyCost hf (posteriorFamily R) := by
  rw [familyCost, posteriorFamily_scalarMeasure R]
  exact closedPerspectiveCost_posterior R.p_measurable R.q_measurable R.p_nonneg R.q_nonneg hf

/-- The posterior source placed in the originally fixed source universe. -/
def liftedMeasure (ν : Measure Interval) : Measure (ULift.{u} Interval) :=
  ν.map ULift.up

instance liftedMeasure_isFinite (ν : Measure Interval) [IsFiniteMeasure ν] :
    IsFiniteMeasure (liftedMeasure.{u} ν) :=
  inferInstanceAs (IsFiniteMeasure (ν.map (ULift.up : Interval → ULift.{u} Interval)))

private theorem up_preserving (ν : Measure Interval) :
    MeasurePreserving (ULift.up : Interval → ULift.{u} Interval) ν (liftedMeasure ν) :=
  ⟨measurable_up, rfl⟩

private abbrev upPull (ν : Measure Interval) :
    (ULift.{u} Interval →₁[liftedMeasure ν] ℂ) →L[ℂ] (Interval →₁[ν] ℂ) :=
  (Lp.compMeasurePreservingₗᵢ ℂ ULift.up (up_preserving ν)).toContinuousLinearMap

private theorem upPull_positive (ν : Measure Interval)
    (h : ULift.{u} Interval →₁[liftedMeasure ν] ℂ)
    (hp : ∀ᵐ x ∂liftedMeasure ν, 0 ≤ h x) : ∀ᵐ t ∂ν, 0 ≤ upPull ν h t := by
  have he : upPull ν h =ᵐ[ν] (fun t => h (ULift.up t)) :=
    Lp.coeFn_compMeasurePreserving h (up_preserving ν)
  have hn := ae_of_ae_map measurable_up.aemeasurable hp
  filter_upwards [he, hn] with t ht hn
  rw [ht]
  exact hn

private theorem upPull_mass (ν : Measure Interval)
    (h : ULift.{u} Interval →₁[liftedMeasure ν] ℂ) :
    ∫ t, upPull ν h t ∂ν = ∫ x, h x ∂liftedMeasure ν := by
  have he : upPull ν h =ᵐ[ν] (fun t => h (ULift.up t)) :=
    Lp.coeFn_compMeasurePreserving h (up_preserving ν)
  rw [integral_congr_ae he]
  exact (up_preserving ν).integral_comp (MeasurableEquiv.ulift.symm.measurableEmbedding) h

private theorem lifted_integrable (ν : Measure Interval) [IsFiniteMeasure ν]
    (w : C(Interval, ℝ)) : Integrable (fun x : ULift.{u} Interval => w x.down) (liftedMeasure ν) := by
  apply MeasurableEquiv.ulift.symm.measurableEmbedding.integrable_map_iff.mpr
  exact w.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace w)

private theorem upPull_input (ν : Measure Interval) [IsFiniteMeasure ν]
    (w : C(Interval, ℝ)) :
    upPull ν ((lifted_integrable ν w).ofReal.toL1
      (fun x : ULift.{u} Interval => (w x.down : ℂ))) =
      ContinuousMap.toLp 1 ν ℂ (⟨fun t => (w t : ℂ), by fun_prop⟩ : C(Interval, ℂ)) := by
  apply Lp.ext
  let hwC : Integrable (fun x : ULift.{u} Interval => (w x.down : ℂ))
      (liftedMeasure ν) := (lifted_integrable ν w).ofReal
  have hw := ae_of_ae_map measurable_up.aemeasurable hwC.coeFn_toL1
  filter_upwards [Lp.coeFn_compMeasurePreserving
      ((lifted_integrable ν w).ofReal.toL1
        (fun x : ULift.{u} Interval => (w x.down : ℂ))) (up_preserving ν), hw,
    ContinuousMap.coeFn_toLp (p := 1) (𝕜 := ℂ) ν
      (⟨fun t => (w t : ℂ), by fun_prop⟩ : C(Interval, ℂ))] with t ht hs hg
  exact ht.trans (hs.trans hg.symm)

/-- Transport of an actual whole-L1 normal realization; no new realization is assumed. -/
def liftedReverseTest {ρ σ : StrongDual ℂ A} (F : Family ρ σ)
    (Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ A)
    (hn : ∀ h, IsOrderNormal (Γ h))
    (hp : ∀ h, (∀ᵐ t ∂scalarMeasure F, 0 ≤ h t) → ∀ a : A, 0 ≤ a → 0 ≤ Γ h a)
    (hm : ∀ h, Γ h 1 = ∫ t, h t ∂scalarMeasure F)
    (hl : Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ)
    (hr : Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ) :
    NormalL1ReverseTest ρ σ (liftedMeasure.{u} (scalarMeasure F)) := by
  let w : C(Interval, ℝ) := ⟨fun t => t.val, by fun_prop⟩
  let w' : C(Interval, ℝ) := 1 - w
  refine
    { preparation :=
        { toLinearMap := Γ.toLinearMap.comp (upPull (scalarMeasure F)).toLinearMap
          positive := fun h hh => hp _ (upPull_positive _ h hh)
          mass := fun h => (hm _).trans (upPull_mass _ h)
          normal := fun h => hn _ }
      p := fun x => x.down.val
      q := fun x => 1 - x.down.val
      p_measurable := measurable_subtype_coe.comp measurable_down
      q_measurable := measurable_const.sub (measurable_subtype_coe.comp measurable_down)
      p_integrable := lifted_integrable _ w
      q_integrable := lifted_integrable _ w'
      p_nonneg := Eventually.of_forall fun x => x.down.property.1
      q_nonneg := Eventually.of_forall fun x => sub_nonneg.mpr x.down.property.2
      prepares_left := ?_
      prepares_right := ?_ }
  · change Γ (upPull _ ((lifted_integrable _ w).ofReal.toL1
      (fun x : ULift.{u} Interval => (w x.down : ℂ)))) = ρ
    rw [upPull_input (scalarMeasure F) w]
    exact hl
  · change Γ (upPull _ ((lifted_integrable _ w').ofReal.toL1
      (fun x : ULift.{u} Interval => (w' x.down : ℂ)))) = σ
    rw [upPull_input (scalarMeasure F) w']
    have he : (⟨fun t => (w' t : ℂ), by fun_prop⟩ : C(Interval, ℂ)) = 1 - posterior := by
      ext t
      simp [w', w, posterior]
    rw [he]
    exact hr

private theorem lifted_cost {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (ν : Measure Interval) :
    closedPerspectiveCost hf (liftedMeasure.{u} ν)
      (fun x => x.down.val) (fun x => 1 - x.down.val) =
      closedPerspectiveCost hf ν (fun t => t.val) (fun t => 1 - t.val) := by
  let e : Interval ≃ᵐ ULift.{u} Interval := MeasurableEquiv.ulift.symm
  change closedPerspectiveCost hf (ν.map e) _ _ = _
  unfold closedPerspectiveCost
  rw [e.measurableEmbedding.integral_map, e.measurableEmbedding.lintegral_map]
  rfl

/-- Literal affine part shared by every actual posterior family point. -/
def affineCost (f : ℝ → ℝ) (ρ σ : StrongDual ℂ A) : ℝ :=
  f 1 * (σ 1).re + rightDeriv f 1 * ((ρ 1).re - (σ 1).re)

/-- The original full objective is a fixed finite affine term plus the actual
nonnegative curvature cost in the weak finite-measure topology. -/
theorem familyCost_eq_affine {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    {ρ σ : StrongDual ℂ A} (F : Family ρ σ) :
    familyCost hf F = (affineCost f ρ σ : EReal) +
      (posteriorCurvatureCost hf (finiteMeasure F) : EReal) := by
  have ht : Integrable (fun t : Interval => t.val) (scalarMeasure F) :=
    continuous_subtype_val.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun t : Interval => 1 - t.val) (scalarMeasure F) :=
    (continuous_const.sub continuous_subtype_val).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hleft : ∫ t : Interval, t.val ∂scalarMeasure F = (ρ 1).re := by
    have h := integral_complex F posterior
    rw [posterior_value] at h
    change ρ 1 = ∫ t, (t.val : ℂ) ∂scalarMeasure F at h
    rw [integral_complex_ofReal] at h
    exact (congrArg Complex.re h).symm
  have hright : ∫ t : Interval, (1 - t.val) ∂scalarMeasure F = (σ 1).re := by
    have h := integral_complex F (1 - posterior)
    rw [map_sub, unit_value, posterior_value] at h
    have he : (ρ + σ) - ρ = σ := by abel
    rw [he] at h
    have hg : (fun t : Interval => (1 - posterior) t) =
        (fun t => ((1 - t.val : ℝ) : ℂ)) := by ext t; simp [posterior]
    rw [hg, integral_complex_ofReal] at h
    simpa only [Complex.ofReal_re] using (congrArg Complex.re h).symm
  have hsub : (∫ t : Interval, t.val - (1 - t.val) ∂scalarMeasure F) =
      (∫ t : Interval, t.val ∂scalarMeasure F) -
        ∫ t : Interval, 1 - t.val ∂scalarMeasure F := integral_sub ht hs
  have ha : (∫ t : Interval, f 1 * (1 - t.val) +
      rightDeriv f 1 * (t.val - (1 - t.val)) ∂scalarMeasure F) = affineCost f ρ σ := by
    calc
      _ = (∫ t : Interval, f 1 * (1 - t.val) ∂scalarMeasure F) +
          ∫ t : Interval, rightDeriv f 1 * (t.val - (1 - t.val)) ∂scalarMeasure F :=
        integral_add (hs.const_mul _) ((ht.sub hs).const_mul _)
      _ = _ := by rw [integral_const_mul, integral_const_mul, hsub, hleft, hright]; rfl
  unfold familyCost closedPerspectiveCost posteriorCurvatureCost
  rw [ha]
  rfl


section Concrete

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H) (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hn : IsOrderNormal (ρ + σ))

include hρ hσ hn

/-- Equality of actual extended attainable costs, before taking either infimum. -/
theorem attainableCosts_eq_range {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    attainableCosts.{u} hf ρ σ = Set.range (familyCost hf (ρ := ρ) (σ := σ)) := by
  obtain ⟨_, _, _, _, hrealize⟩ := compact_normal_posterior_family M ρ σ hρ hσ hn
  rw [attainableCosts_eq_representativeCosts]
  ext z
  constructor
  · rintro ⟨X, m, μ, hμ, R, rfl⟩
    letI := m
    exact ⟨posteriorFamily R, (source_cost_eq_familyCost R hf).symm⟩
  · rintro ⟨F, rfl⟩
    obtain ⟨Γ, _, hnormal, hp, hm, _, hl, hr⟩ := (hrealize F).2.2.2
    letI : IsFiniteMeasure (liftedMeasure.{u} (scalarMeasure F)) :=
      inferInstanceAs (IsFiniteMeasure ((scalarMeasure F).map (ULift.up : Interval → ULift.{u} Interval)))
    exact ⟨ULift.{u} Interval, inferInstance, liftedMeasure (scalarMeasure F), inferInstance,
      liftedReverseTest F Γ hnormal hp hm hl hr, (lifted_cost hf (scalarMeasure F)).symm⟩

/-- Full original-source extended attainment for an arbitrary concrete von Neumann
algebra. Every source at Type u is included; the attaining source is finite and
regular on the posterior interval, transported to Type u. No finite-cost branch
or nonzero-mass premise is used. The infimum is never minus infinity. -/
theorem original_reverse_test_extended_attainment
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    ∃ F : Family ρ σ,
      familyCost hf F = sInf (attainableCosts.{u} hf ρ σ) ∧
      sInf (attainableCosts.{u} hf ρ σ) ≠ ⊥ ∧
      (ρ = 0 → σ = 0 → sInf (attainableCosts.{u} hf ρ σ) = 0) ∧
      (scalarMeasure F).Regular ∧
      IsFiniteMeasure (liftedMeasure.{u} (scalarMeasure F)) ∧
      (∃ R : NormalL1ReverseTest ρ σ (liftedMeasure.{u} (scalarMeasure F)),
        R.p = (fun x => x.down.val) ∧ R.q = (fun x => 1 - x.down.val) ∧
        closedPerspectiveCost hf (liftedMeasure (scalarMeasure F)) R.p R.q =
          sInf (attainableCosts.{u} hf ρ σ)) ∧
      ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
        (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) = linearMap F g) ∧
        (∀ h, IsOrderNormal (Γ h)) ∧
        (∀ h, (∀ᵐ t ∂scalarMeasure F, 0 ≤ h t) → ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a) ∧
        (∀ h, Γ h 1 = ∫ t, h t ∂scalarMeasure F) ∧ ‖Γ‖ ≤ 1 ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
        Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ := by
  obtain ⟨hc, hne, hcont, _, hrealize⟩ := compact_normal_posterior_family M ρ σ hρ hσ hn
  letI : CompactSpace (Family ρ σ) := isCompact_iff_compactSpace.mp hc
  letI : Nonempty (Family ρ σ) := hne
  have hlsc : LowerSemicontinuous (fun F : Family ρ σ =>
      posteriorCurvatureCost hf (finiteMeasure F)) :=
    (posteriorCurvatureCost_lowerSemicontinuous hf).comp hcont
  obtain ⟨F, _, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (Set.univ_nonempty : (Set.univ : Set (Family ρ σ)).Nonempty) isCompact_univ
      (hlsc.lowerSemicontinuousOn univ)
  have hle (G : Family ρ σ) : familyCost hf F ≤ familyCost hf G := by
    rw [familyCost_eq_affine, familyCost_eq_affine]
    exact add_le_add le_rfl (EReal.coe_ennreal_le_coe_ennreal_iff.mpr
      ((isMinOn_iff.mp hmin) G (mem_univ G)))
  have heq : familyCost hf F = sInf (attainableCosts.{u} hf ρ σ) := by
    rw [attainableCosts_eq_range M ρ σ hρ hσ hn hf]
    apply le_antisymm
    · exact le_sInf fun z hz => by obtain ⟨G, rfl⟩ := hz; exact hle G
    · exact sInf_le (mem_range_self F)
  have hbot : sInf (attainableCosts.{u} hf ρ σ) ≠ ⊥ := by
    rw [← heq, familyCost_eq_affine]
    exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, EReal.coe_ennreal_ne_bot _⟩
  have hzero : ρ = 0 → σ = 0 → sInf (attainableCosts.{u} hf ρ σ) = 0 := by
    intro hρ0 hσ0
    have hmass : scalarMeasure F univ = 0 := by
      simpa [hρ0, hσ0] using (hrealize F).2.1
    have hν : scalarMeasure F = 0 := Measure.measure_univ_eq_zero.mp hmass
    rw [← heq, familyCost, hν]
    simp [closedPerspectiveCost]
  obtain ⟨Γ, hagree, hnormal, hp, hm, hb, hl, hr⟩ := (hrealize F).2.2.2
  refine ⟨F, heq, hbot, hzero, (hrealize F).1, inferInstance,
    ?_, Γ, hagree, hnormal, hp, hm, hb, hl, hr⟩
  exact ⟨liftedReverseTest F Γ hnormal hp hm hl hr, rfl, rfl,
    (lifted_cost hf (scalarMeasure F)).trans heq⟩

end Concrete

section StandardConcrete

open D5.S3.Quantum.Analysis.ConcreteCoefficientPredual
open D5.S3.Quantum.Analysis.ConcreteCoefficientSeries

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (M : VonNeumannAlgebra H)

/-- The independent standard concrete source class. Outputs are actual
square-summable coefficient series, not a renamed intrinsic-normal predicate. -/
structure StandardL1Preparation {X : Type*} [MeasurableSpace X] (μ : Measure X) where
  toLinearMap : (X →₁[μ] ℂ) →ₗ[ℂ] StrongDual ℂ M.toStarSubalgebra
  positive : ∀ h, (∀ᵐ x ∂μ, 0 ≤ h x) →
    ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ toLinearMap h a
  mass : ∀ h, toLinearMap h 1 = ∫ x, h x ∂μ
  series : ∀ h, IsCoefficientSeries M (toLinearMap h)

/-- The proved forward interface, without a converse-normality assumption. -/
def StandardL1Preparation.toNormal {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (Γ : StandardL1Preparation M μ) : NormalL1Preparation (A := M.toStarSubalgebra) μ where
  toLinearMap := Γ.toLinearMap
  positive := Γ.positive
  mass := Γ.mass
  normal := fun h => series_order_normal M (Γ.series h)

/-- All original nonnegative complex L1 inputs, all actual sigma-finite sources
in Type u, and the literal original extended cost, with standard-series outputs. -/
def standardAttainableCosts {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f)
    (ρ σ : StrongDual ℂ M.toStarSubalgebra) : Set EReal :=
  {z | ∃ (X : Type u) (m : MeasurableSpace X),
    letI := m
    ∃ μ : Measure X, SigmaFinite μ ∧ ∃ Γ : StandardL1Preparation M μ,
      ∃ p q : X →₁[μ] ℂ,
        (∀ᵐ x ∂μ, 0 ≤ p x) ∧ (∀ᵐ x ∂μ, 0 ≤ q x) ∧
        Γ.toLinearMap p = ρ ∧ Γ.toLinearMap q = σ ∧
        z = closedPerspectiveCost hf μ (fun x => (p x).re) (fun x => (q x).re)}

private theorem standard_cost_of_series_reverseTest
    {ρ σ : StrongDual ℂ M.toStarSubalgebra}
    {X : Type u} [MeasurableSpace X] {μ : Measure X} [SigmaFinite μ]
    (R : NormalL1ReverseTest ρ σ μ)
    (hs : ∀ h, IsCoefficientSeries M (R.preparation.toLinearMap h))
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    closedPerspectiveCost hf μ R.p R.q ∈ standardAttainableCosts.{u} M hf ρ σ := by
  let Γ : StandardL1Preparation M μ :=
    { toLinearMap := R.preparation.toLinearMap
      positive := R.preparation.positive
      mass := R.preparation.mass
      series := hs }
  let P := R.p_integrable.ofReal.toL1 (fun x => (R.p x : ℂ))
  let Q := R.q_integrable.ofReal.toL1 (fun x => (R.q x : ℂ))
  have hP : P =ᵐ[μ] (fun x => (R.p x : ℂ)) :=
    (R.p_integrable.ofReal : Integrable (fun x => (R.p x : ℂ)) μ).coeFn_toL1
  have hQ : Q =ᵐ[μ] (fun x => (R.q x : ℂ)) :=
    (R.q_integrable.ofReal : Integrable (fun x => (R.q x : ℂ)) μ).coeFn_toL1
  have hp : ∀ᵐ x ∂μ, 0 ≤ P x := by
    filter_upwards [hP, R.p_nonneg] with x he hn
    rw [he]
    exact_mod_cast hn
  have hq : ∀ᵐ x ∂μ, 0 ≤ Q x := by
    filter_upwards [hQ, R.q_nonneg] with x he hn
    rw [he]
    exact_mod_cast hn
  have hpr : (fun x => (P x).re) =ᵐ[μ] R.p := by
    filter_upwards [hP] with x he
    simp only [he, Complex.ofReal_re]
  have hqr : (fun x => (Q x).re) =ᵐ[μ] R.q := by
    filter_upwards [hQ] with x he
    simp only [he, Complex.ofReal_re]
  exact ⟨X, inferInstance, μ, inferInstance, Γ, P, Q, hp, hq,
    R.prepares_left, R.prepares_right, (cost_congr_ae hf hpr hqr).symm⟩

variable (ρ σ : StrongDual ℂ M.toStarSubalgebra)
    (hρ : ∀ a, 0 ≤ a → 0 ≤ ρ a) (hσ : ∀ a, 0 ≤ a → 0 ≤ σ a)
    (hρs : IsCoefficientSeries M ρ) (hσs : IsCoefficientSeries M σ)

include hρ hσ hρs hσs

/-- The realized map itself takes values in the concrete predual. Its
codRestriction retains every value, positivity, all masses and both moments. -/
theorem standard_posterior_realization (F : Family ρ σ) :
    ∃ Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra,
      (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) = linearMap F g) ∧
      (∀ h, IsOrderNormal (Γ h)) ∧
      (∀ h, (∀ᵐ t ∂scalarMeasure F, 0 ≤ h t) →
        ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a) ∧
      (∀ h, Γ h 1 = ∫ t, h t ∂scalarMeasure F) ∧ ‖Γ‖ ≤ 1 ∧
      Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ ∧
      Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ ∧
      ∃ hΓE : ∀ h, Γ h ∈ coefficientSpace M,
        let ΓE := Γ.codRestrict (coefficientSpace M) hΓE
        (∀ h, (ΓE h).val = Γ h) ∧ ‖ΓE‖ ≤ 1 ∧
        (∀ h, IsCoefficientSeries M (ΓE h).val) := by
  have hsum : ρ + σ ∈ coefficientSpace M :=
    (coefficientSpace M).add_mem (series_mem_coefficientSpace M hρs)
      (series_mem_coefficientSpace M hσs)
  have hn := coefficientSpace_le_normalDual M hsum
  obtain ⟨_, _, _, _, hrealize⟩ := compact_normal_posterior_family M ρ σ hρ hσ hn
  obtain ⟨Γ, hagree, hnormal, hp, hm, hb, hl, hr⟩ := (hrealize F).2.2.2
  have hΓE := posterior_L1_range M hsum F Γ hagree
  let ΓE := Γ.codRestrict (coefficientSpace M) hΓE
  have hbound : ‖ΓE‖ ≤ 1 := by
    apply ΓE.opNorm_le_bound (by norm_num)
    intro h
    change ‖Γ h‖ ≤ 1 * ‖h‖
    exact (Γ.le_opNorm h).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg h))
  exact ⟨Γ, hagree, hnormal, hp, hm, hb, hl, hr, hΓE,
    fun _ => rfl, hbound,
    fun h => (mem_coefficientSpace_iff_series M _).mp (ΓE h).property⟩

/-- The standard-original and posterior cost sets agree before taking infima. -/
theorem standardAttainableCosts_eq_range
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    standardAttainableCosts.{u} M hf ρ σ =
      Set.range (familyCost hf (ρ := ρ) (σ := σ)) := by
  have hsum : ρ + σ ∈ coefficientSpace M :=
    (coefficientSpace M).add_mem (series_mem_coefficientSpace M hρs)
      (series_mem_coefficientSpace M hσs)
  have hn := coefficientSpace_le_normalDual M hsum
  ext z
  constructor
  · rintro ⟨X, m, μ, hμ, Γ, p, q, hp, hq, hl, hr, rfl⟩
    letI := m
    have hz : closedPerspectiveCost hf μ (fun x => (p x).re) (fun x => (q x).re) ∈
        attainableCosts.{u} hf ρ σ :=
      ⟨X, m, μ, hμ, Γ.toNormal, p, q, hp, hq, hl, hr, rfl⟩
    rwa [attainableCosts_eq_range M ρ σ hρ hσ hn hf] at hz
  · rintro ⟨F, rfl⟩
    obtain ⟨Γ, _, hnormal, hp, hm, _, hl, hr, hΓE, _⟩ :=
      standard_posterior_realization M ρ σ hρ hσ hρs hσs F
    let R := liftedReverseTest.{u} F Γ hnormal hp hm hl hr
    have hs (h) : IsCoefficientSeries M (R.preparation.toLinearMap h) :=
      coefficientSpace_series M ⟨Γ (upPull _ h), hΓE _⟩
    have hc := standard_cost_of_series_reverseTest M R hs hf
    change closedPerspectiveCost hf (liftedMeasure (scalarMeasure F))
      (fun x => x.down.val) (fun x => 1 - x.down.val) ∈ _ at hc
    rwa [lifted_cost] at hc

/-- Exact standard-concrete-predual whole-L1 attainment, including infinite costs.
The attaining lifted preparation is explicitly built from this very Gamma. -/
theorem standard_original_reverse_test_extended_attainment
    {f : ℝ → ℝ} (hf : ConvexOn ℝ (Ioi 0) f) :
    ∃ F : Family ρ σ,
      familyCost hf F = sInf (standardAttainableCosts.{u} M hf ρ σ) ∧
      sInf (standardAttainableCosts.{u} M hf ρ σ) ≠ ⊥ ∧
      (ρ = 0 → σ = 0 → sInf (standardAttainableCosts.{u} M hf ρ σ) = 0) ∧
      (scalarMeasure F).Regular ∧
      IsFiniteMeasure (liftedMeasure.{u} (scalarMeasure F)) ∧
      (liftedMeasure.{u} (scalarMeasure F)).Regular ∧
      ∃ (Γ : (Interval →₁[scalarMeasure F] ℂ) →L[ℂ] StrongDual ℂ M.toStarSubalgebra)
        (hn : ∀ h, IsOrderNormal (Γ h))
        (hp : ∀ h, (∀ᵐ t ∂scalarMeasure F, 0 ≤ h t) →
          ∀ a : M.toStarSubalgebra, 0 ≤ a → 0 ≤ Γ h a)
        (hm : ∀ h, Γ h 1 = ∫ t, h t ∂scalarMeasure F)
        (hl : Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ posterior) = ρ)
        (hr : Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ (1 - posterior)) = σ)
        (hΓE : ∀ h, Γ h ∈ coefficientSpace M),
        (∀ g : C(Interval, ℂ), Γ (ContinuousMap.toLp 1 (scalarMeasure F) ℂ g) = linearMap F g) ∧
        ‖Γ‖ ≤ 1 ∧
        (let ΓE := Γ.codRestrict (coefficientSpace M) hΓE
         (∀ h, (ΓE h).val = Γ h) ∧ ‖ΓE‖ ≤ 1 ∧
           ∀ h, IsCoefficientSeries M (ΓE h).val) ∧
        (let R := liftedReverseTest.{u} F Γ hn hp hm hl hr
         R.p = (fun x => x.down.val) ∧ R.q = (fun x => 1 - x.down.val) ∧
         (∀ h, IsCoefficientSeries M (R.preparation.toLinearMap h)) ∧
         closedPerspectiveCost hf (liftedMeasure (scalarMeasure F)) R.p R.q =
           sInf (standardAttainableCosts.{u} M hf ρ σ)) := by
  have hsum : ρ + σ ∈ coefficientSpace M :=
    (coefficientSpace M).add_mem (series_mem_coefficientSpace M hρs)
      (series_mem_coefficientSpace M hσs)
  have hn := coefficientSpace_le_normalDual M hsum
  have hcost : standardAttainableCosts.{u} M hf ρ σ = attainableCosts.{u} hf ρ σ := by
    rw [standardAttainableCosts_eq_range M ρ σ hρ hσ hρs hσs hf,
      attainableCosts_eq_range M ρ σ hρ hσ hn hf]
  obtain ⟨F, heq, hbot, hzero, hreg, hfin, _, _⟩ :=
    original_reverse_test_extended_attainment.{u} M ρ σ hρ hσ hn hf
  obtain ⟨Γ, hagree, hnormal, hp, hm, hb, hl, hr, hΓE, hrest⟩ :=
    standard_posterior_realization M ρ σ hρ hσ hρs hσs F
  letI : (scalarMeasure F).Regular := hreg
  have hreglift : (liftedMeasure.{u} (scalarMeasure F)).Regular :=
    Measure.Regular.map (μ := scalarMeasure F)
      (Homeomorph.ulift.symm : Interval ≃ₜ ULift.{u} Interval)
  refine ⟨F, hcost ▸ heq, hcost ▸ hbot, hcost ▸ hzero, hreg, hfin, hreglift,
    Γ, hnormal, hp, hm, hl, hr, hΓE, hagree, hb, hrest, rfl, rfl, ?_, ?_⟩
  · intro h
    exact coefficientSpace_series M ⟨Γ (upPull _ h), hΓE _⟩
  · exact (lifted_cost hf (scalarMeasure F)).trans (hcost ▸ heq)

end StandardConcrete

#print axioms representativeCosts_of_positive_L1
#print axioms attainableCosts_eq_representativeCosts
#print axioms posteriorFamily_scalarMeasure
#print axioms source_cost_eq_familyCost
#print axioms familyCost_eq_affine
#print axioms attainableCosts_eq_range
#print axioms original_reverse_test_extended_attainment
#print axioms standard_posterior_realization
#print axioms standardAttainableCosts_eq_range
#print axioms standard_original_reverse_test_extended_attainment

end D5.S3.Quantum.Divergence.GeneralConvexReverseTestAttainment
