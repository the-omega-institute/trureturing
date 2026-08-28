/- GID: D5/S3/Analytic/Adelic/ToroidalCechCompletion
   generality: I
   mirror-B: D5/B/S3/Analytic/Adelic/ToroidalCechCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Period ratios glue uniquely to the completed-zeta amplitude. -/

import D5.S3.ConceptDynamics.Gluing.ContinuousLocalFactorGluing
import D5.S3.Zeros.CompletedZeta

/- Library-search audit trail (2026-08-28):
   * Exact repository searches for toroidal periods, quadratic-twist charts,
     period/twist ratios, and a completed-zeta gluing theorem found no whole-
     statement owner.
   * The frozen theorem `continuous_local_factors_glue_uniquely` is the exact
     general continuous-gluing constituent and is applied below. It has no
     completed-zeta or period-ratio specialization, so it is not a bind target.
   * Pinned Mathlib searches found no completed-zeta period atlas theorem.
     `Continuous.div` supplies continuity of the constructed local ratios.
   * Body-shape searches for a nonvanishing subtype chart and for a continuous
     quotient on that chart found no D5 definition. The three definitions below
     construct the source objects from the period and twist functions; none is
     defined by the theorem's compatibility or uniqueness conclusions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Adelic.ToroidalCechCompletion

open D5.S3.ConceptDynamics.Gluing.ContinuousLocalFactorGluing
open D5.S3.Zeros.CompletedZeta

/-- The chart on which one quadratic twist is nonzero. -/
def nonvanishingDomain {Index : Type*} (Omega : Set ℂ)
    (twist : Index -> ℂ -> ℂ) (index : Index) : Set Omega :=
  {point | twist index point.1 ≠ 0}

/-- The period divided by its twist on the corresponding nonvanishing chart. -/
noncomputable def localPeriodRatio {Index : Type*} (Omega : Set ℂ)
    (period twist : Index -> ℂ -> ℂ)
    (periodContinuous : ∀ index, Continuous (period index))
    (twistContinuous : ∀ index, Continuous (twist index))
    (index : Index) : C(nonvanishingDomain Omega twist index, ℂ) where
  toFun point := period index point.1.1 / twist index point.1.1
  continuous_toFun := by
    have valueContinuous :
        Continuous (fun point : nonvanishingDomain Omega twist index => point.1.1) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((periodContinuous index).comp valueContinuous).div
      ((twistContinuous index).comp valueContinuous) fun point => point.2

/-- The canonical completed-zeta amplitude restricted to the spectral domain. -/
noncomputable def restrictedXi (Omega : Set ℂ) : C(Omega, ℂ) where
  toFun point := xiReading point.1
  continuous_toFun := xi_reading_differentiable.continuous.comp continuous_subtype_val

/--
On a spectral domain covered by quadratic-twist nonvanishing charts, the local
period/twist ratios agree on every overlap. The canonical completed-zeta
amplitude restricts to every local ratio, and any continuous map with those
restrictions is that amplitude.
-/
theorem toroidal_cech_completion {Index : Type*} (Omega : Set ℂ)
    (period twist : Index -> ℂ -> ℂ)
    (periodContinuous : ∀ index, Continuous (period index))
    (twistContinuous : ∀ index, Continuous (twist index))
    (factorization : ∀ index point,
      period index point = xiReading point * twist index point)
    (cover : ∀ point ∈ Omega, ∃ index, twist index point ≠ 0) :
    (∀ first second point
        (inFirst : point ∈ nonvanishingDomain Omega twist first)
        (inSecond : point ∈ nonvanishingDomain Omega twist second),
      localPeriodRatio Omega period twist periodContinuous twistContinuous first
          ⟨point, inFirst⟩ =
        localPeriodRatio Omega period twist periodContinuous twistContinuous second
          ⟨point, inSecond⟩) ∧
      (∀ index (point : nonvanishingDomain Omega twist index),
        restrictedXi Omega point =
          localPeriodRatio Omega period twist periodContinuous twistContinuous index point) ∧
      ∀ candidate : C(Omega, ℂ),
        (∀ index (point : nonvanishingDomain Omega twist index),
          candidate point =
            localPeriodRatio Omega period twist periodContinuous twistContinuous index point) ->
        candidate = restrictedXi Omega := by
  have openDomain : ∀ index, IsOpen (nonvanishingDomain Omega twist index) := by
    intro index
    have continuousOnSubtype : Continuous (fun point : Omega => twist index point.1) :=
      (twistContinuous index).comp continuous_subtype_val
    have domainAsPreimage :
        nonvanishingDomain Omega twist index =
          (fun point : Omega => twist index point.1) ⁻¹' ({0}ᶜ : Set ℂ) := by
      ext point
      simp [nonvanishingDomain]
    rw [domainAsPreimage]
    exact isOpen_compl_singleton.preimage continuousOnSubtype
  have domainCover : ⋃ index, nonvanishingDomain Omega twist index = Set.univ := by
    apply Set.eq_univ_of_forall
    intro point
    obtain ⟨index, nonzero⟩ := cover point.1 point.2
    exact Set.mem_iUnion.mpr ⟨index, nonzero⟩
  have restricts :
      ∀ index (point : nonvanishingDomain Omega twist index),
        restrictedXi Omega point =
          localPeriodRatio Omega period twist periodContinuous twistContinuous index point := by
    intro index point
    change xiReading point.1.1 = period index point.1.1 / twist index point.1.1
    rw [factorization]
    exact (mul_div_cancel_right₀ _ point.2).symm
  have glued := continuous_local_factors_glue_uniquely
    (q := id) (target := restrictedXi Omega)
    (domain := nonvanishingDomain Omega twist)
    openDomain domainCover
    (localPeriodRatio Omega period twist periodContinuous twistContinuous)
    Function.surjective_id
    (fun index point membership => restricts index ⟨point, membership⟩)
  refine ⟨glued.1, restricts, ?_⟩
  intro candidate candidateRestricts
  have candidateFactors :
      (restrictedXi Omega : Omega -> ℂ) = candidate ∘ id := by
    funext point
    obtain ⟨index, nonzero⟩ := cover point.1 point.2
    calc
      restrictedXi Omega point =
          localPeriodRatio Omega period twist periodContinuous twistContinuous index
            ⟨point, nonzero⟩ := restricts index ⟨point, nonzero⟩
      _ = candidate point := (candidateRestricts index ⟨point, nonzero⟩).symm
      _ = (candidate ∘ id) point := rfl
  exact glued.2.unique ⟨candidateRestricts, candidateFactors⟩ ⟨restricts, rfl⟩

#print axioms nonvanishingDomain
#print axioms localPeriodRatio
#print axioms restrictedXi
#print axioms toroidal_cech_completion

end D5.S3.Analytic.Adelic.ToroidalCechCompletion
