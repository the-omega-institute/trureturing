/- GID: D5/S3/Weil/Probability/CircleHerglotzCompletion
   generality: I
   mirror-B: D5/B/S3/Weil/Probability/CircleHerglotzCompletion
   mirror-E: none(waiver:analytic-proof-source)
   anchors: []
   utility: none
   digest: Complete the existing finite Toeplitz witnesses into one unique circle probability measure and identify weak convergence by all original moments. -/

import D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
import D5.S3.Weil.TestFunctions.LiCurvatureCriterion
import D5.S3.Observer.MeasureSeparation.FourierModeDetermination
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
Reuse the original circleMoment and toeplitzMatrix conventions. The finite
representation theorem already constructs a measure for every finite order.
Compactness of probability measures gives a common witness, without requiring
compatibility of separately selected finite witnesses. Uniqueness is transported
from the existing AddCircle Fourier-mode theorem; it is not assumed.
This is a general representation bridge. No arithmetic positivity is asserted.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Probability.CircleHerglotzCompletion

open MeasureTheory Set Filter Topology
open D5.S3.Weil.TestFunctions.LiCurvatureCriterion
open D5.S3.Weil.CayleyLaguerre.TruncatedCircleMomentBridge
open D5.S3.Observer.MeasureSeparation.FourierModeDetermination
open scoped ComplexConjugate ComplexOrder ENNReal

noncomputable local instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle
local instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

private def momentTest (n : ℤ) : C(Circle, ℂ) :=
  ⟨fun z => (z : ℂ) ^ (-n), by
    apply Continuous.zpow₀ continuous_subtype_val
    intro z
    exact Or.inl (Circle.coe_ne_zero z)⟩

/-- Every original circle moment is continuous for weak convergence. -/
theorem circleMoment_continuous (n : ℤ) :
    Continuous (fun μ : ProbabilityMeasure Circle => circleMoment (μ : Measure Circle) n) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (tendsto_id : Tendsto (fun ν : ProbabilityMeasure Circle => ν) (𝓝 μ) (𝓝 μ))
    (ContinuousMap.equivBoundedOfCompact _ _ (momentTest n))

/-- The existing AddCircle determination theorem also determines measures in
the multiplicative Circle carrier, with the original negative-power convention. -/
theorem circle_moment_ext (μ ν : Measure Circle) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (same : ∀ n : ℤ, circleMoment μ n = circleMoment ν n) : μ = ν := by
  let e : AddCircle (2 * Real.pi) ≃ₜ Circle :=
    AddCircle.homeomorphCircle (by positivity)
  have hcoordinate : MeasurableEmbedding e.symm :=
    e.symm.continuous.measurableEmbedding e.symm.injective
  have hchar (n : ℤ) (z : Circle) :
      fourier n (e.symm z) = (z : ℂ) ^ n := by
    rw [fourier_apply, AddCircle.toCircle_zsmul]
    have hcircle : AddCircle.toCircle (e.symm z) = z := by
      rw [← AddCircle.homeomorphCircle_apply (by positivity)]
      exact e.apply_symm_apply z
    rw [hcircle]
    rfl
  have hmap (ρ : Measure Circle) [IsFiniteMeasure ρ] (n : ℤ) :
      fourierMoment (Measure.map e.symm ρ) n = circleMoment ρ (-n) := by
    unfold fourierMoment circleMoment
    rw [integral_map hcoordinate.measurable.aemeasurable
      (fourier n).continuous.aestronglyMeasurable]
    simp only [hchar, neg_neg]
  apply hcoordinate.map_injective
  apply all_fourier_modes_determine_measure
  intro n
  rw [hmap, hmap, same]

/-- All Toeplitz orders already force the Hermitian symmetry of the sequence. -/
theorem hermitian_of_all_toeplitz (c : ℤ → ℂ)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef) :
    ∀ n : ℤ, c (-n) = star (c n) := by
  have hnat (k : ℕ) : c (-(k : ℤ)) = star (c (k : ℤ)) := by
    have hmatrix : (toeplitzMatrix c k).conjTranspose = toeplitzMatrix c k :=
      (positive k).isHermitian
    have hentry := congrArg
      (fun A : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ => A 0 ⟨k, Nat.lt_succ_self k⟩)
      hmatrix
    simpa [toeplitzMatrix] using hentry.symm
  intro n
  rcases n.eq_nat_or_neg with ⟨k, rfl | rfl⟩
  · exact hnat k
  · simpa only [neg_neg, star_star] using (congrArg star (hnat k)).symm

/-- A normalized sequence with positive Toeplitz matrices at every order has
one probability measure realizing every integer moment. -/
theorem circle_herglotz_exists (c : ℤ → ℂ) (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef) :
    ∃ μ : ProbabilityMeasure Circle, ∀ n : ℤ, circleMoment (μ : Measure Circle) n = c n := by
  classical
  let K (N : ℕ) : Set (ProbabilityMeasure Circle) :=
    {μ | ∀ n : ℤ, n.natAbs ≤ N → circleMoment (μ : Measure Circle) n = c n}
  have hclosed (N : ℕ) : IsClosed (K N) := by
    simp only [K, setOf_forall]
    exact isClosed_iInter fun n => isClosed_iInter fun _ =>
      isClosed_eq (circleMoment_continuous n) continuous_const
  have hnonempty (N : ℕ) : (K N).Nonempty := by
    obtain ⟨σ, hσ⟩ := truncated_circle_moment_of_posSemidef N c
      (hermitian_of_all_toeplitz c positive) (positive N)
    have hzero := hσ 0 (by simp)
    rw [normalized] at hzero
    have hmass : (σ : Measure Circle).real Set.univ = 1 := by
      simpa using congrArg Complex.re hzero
    have hprob : IsProbabilityMeasure (σ : Measure Circle) := by
      constructor
      rw [← ENNReal.ofReal_toReal (measure_ne_top (σ : Measure Circle) Set.univ)]
      change ENNReal.ofReal ((σ : Measure Circle).real Set.univ) = 1
      rw [hmass, ENNReal.ofReal_one]
    exact ⟨⟨σ, hprob⟩, hσ⟩
  have hstep (N : ℕ) : K (N + 1) ⊆ K N := by
    intro μ hμ n hn
    exact hμ n (Nat.le_trans hn (Nat.le_succ N))
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    K hstep hnonempty (hclosed 0).isCompact hclosed
  refine ⟨μ, fun n => ?_⟩
  exact (Set.mem_iInter.mp hμ n.natAbs) n le_rfl

/-- The common probability measure exists uniquely exactly when the normalized
sequence passes all finite Toeplitz positivity tests. -/
theorem circle_herglotz_iff (c : ℤ → ℂ) (normalized : c 0 = 1) :
    (∀ N : ℕ, (toeplitzMatrix c N).PosSemidef) ↔
      ∃! μ : ProbabilityMeasure Circle,
        ∀ n : ℤ, circleMoment (μ : Measure Circle) n = c n := by
  constructor
  · intro positive
    obtain ⟨μ, hμ⟩ := circle_herglotz_exists c normalized positive
    refine ⟨μ, hμ, ?_⟩
    intro ν hν
    apply ProbabilityMeasure.toMeasure_injective
    exact circle_moment_ext _ _ (fun n => (hν n).trans (hμ n).symm)
  · rintro ⟨μ, hμ, _⟩ N
    have hseq : circleMoment (μ : Measure Circle) = c := funext hμ
    rw [← hseq]
    exact circle_moment_toeplitz_posSemidef _ N

private theorem moment_profile_isEmbedding :
    IsEmbedding (fun μ : ProbabilityMeasure Circle =>
      fun n : ℤ => circleMoment (μ : Measure Circle) n) := by
  have hcontinuous : Continuous (fun μ : ProbabilityMeasure Circle =>
      fun n : ℤ => circleMoment (μ : Measure Circle) n) :=
    continuous_pi fun n => circleMoment_continuous n
  have hinjective : Function.Injective (fun μ : ProbabilityMeasure Circle =>
      fun n : ℤ => circleMoment (μ : Measure Circle) n) := by
    intro μ ν h
    apply ProbabilityMeasure.toMeasure_injective
    exact circle_moment_ext _ _ (fun n => congrFun h n)
  exact (hcontinuous.isClosedEmbedding hinjective).isEmbedding

/-- On circle probability measures, continuity of all moments is equivalent
to weak continuity of the family. Compactness upgrades the existing exact
uniqueness theorem to a topological embedding. -/
theorem continuous_iff_circleMoments {X : Type*} [TopologicalSpace X]
    (μ : X → ProbabilityMeasure Circle) :
    Continuous μ ↔ ∀ n : ℤ, Continuous (fun x => circleMoment (μ x : Measure Circle) n) := by
  constructor
  · intro h n
    exact (circleMoment_continuous n).comp h
  · intro h
    apply moment_profile_isEmbedding.continuous_iff.mpr
    exact continuous_pi h

/-- All original moments characterize weak convergence along any filter. -/
theorem tendsto_iff_circleMoments {ι : Type*} (F : Filter ι)
    (ν : ι → ProbabilityMeasure Circle) (μ : ProbabilityMeasure Circle) :
    Tendsto ν F (𝓝 μ) ↔ ∀ n : ℤ,
      Tendsto (fun i => circleMoment (ν i : Measure Circle) n)
        F (𝓝 (circleMoment (μ : Measure Circle) n)) := by
  rw [moment_profile_isEmbedding.tendsto_nhds_iff]
  exact tendsto_pi_nhds

/-- Any choice of exact finite-order probability witnesses converges as a
whole sequence to the unique common measure. No consistency between consecutive
witnesses and no convergence-rate premise is required. -/
theorem finite_moment_witnesses_tendsto
    (c : ℤ → ℂ) (normalized : c 0 = 1)
    (positive : ∀ N : ℕ, (toeplitzMatrix c N).PosSemidef)
    (ν : ℕ → ProbabilityMeasure Circle)
    (finiteMoments : ∀ (N : ℕ) (n : ℤ), n.natAbs ≤ N → circleMoment (ν N : Measure Circle) n = c n) :
    ∃ μ : ProbabilityMeasure Circle,
      (∀ n : ℤ, circleMoment (μ : Measure Circle) n = c n) ∧
      Tendsto ν atTop (𝓝 μ) := by
  obtain ⟨μ, hμ⟩ := circle_herglotz_exists c normalized positive
  refine ⟨μ, hμ, (tendsto_iff_circleMoments atTop ν μ).mpr ?_⟩
  intro n
  rw [hμ n]
  have eventuallyExact : (fun N => circleMoment (ν N : Measure Circle) n) =ᶠ[atTop]
      (fun _ : ℕ => c n) := by
    filter_upwards [eventually_ge_atTop n.natAbs] with N hN
    exact finiteMoments N n hN
  exact (tendsto_congr' eventuallyExact).mpr tendsto_const_nhds

#print axioms circle_herglotz_exists
#print axioms circle_herglotz_iff
#print axioms continuous_iff_circleMoments
#print axioms finite_moment_witnesses_tendsto

end D5.S3.Weil.Probability.CircleHerglotzCompletion
