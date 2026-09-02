/- GID: D5/S3/Analytic/Toroidal/GoldenToroidalIndexExtension
   generality: I
   mirror-B: D5/B/S3/Analytic/Toroidal/GoldenToroidalIndexExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A golden toroidal channel preserves nonvanishing, common zeros, and the RH criterion. -/

import D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus
import D5.S3.Analytic.Adelic.ToroidalTemperednessCriterion

/- Library-search audit trail (2026-09-02):
   * Exact D5 searches for `golden_toroidal_index_extension`,
     `Sum Index Unit`, and `extendedTwist` found no declaration. Shape searches
     found the two frozen owners used below: `toroidal_common_zero_locus` for
     the window common-zero equality and
     `rh_iff_all_toroidal_eisenstein_tempered` for the RH-side equivalence.
   * Pinned Mathlib searches found generic `Sum.elim` infrastructure but no
     theorem extending a pointwise nonvanishing family or preserving this
     completed-zeta common-zero predicate under `Sum Index Unit`.
   * The theorem adds no Euler-germ nonvanishing, O-5 factorization, or
     identification of the golden twist with an Euler germ or Zqc. It does not
     strengthen RH and does not import or use `o5_independence`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Toroidal.GoldenToroidalIndexExtension

open D5.S3.Zeros.CompletedZeta
open D5.S3.Analytic.Adelic.ToroidalCommonZeroLocus
open D5.S3.Analytic.Adelic.ToroidalTemperednessCriterion
open Zeta23
open Zeta23.RvM

/-- Adding an arbitrary golden candidate channel preserves pointwise twist
nonvanishing. When its period factors through the same `xiReading`, the
extended and original common-period-zero loci agree on the window. -/
theorem golden_toroidal_index_extension
    {Index : Type*} (Omega : Set ℂ)
    (period twist : Index -> ℂ -> ℂ)
    (factorization : ∀ index point,
      period index point = xiReading point * twist index point)
    (pointwiseNonvanishing : ∀ point, point ∈ Omega ->
      ∃ index, twist index point ≠ 0)
    (goldenPeriod goldenTwist : ℂ -> ℂ)
    (goldenFactorization : ∀ point,
      goldenPeriod point = xiReading point * goldenTwist point) :
    (∀ point, point ∈ Omega -> ∃ index : Sum Index Unit,
      Sum.elim twist (fun _ => goldenTwist) index point ≠ 0) ∧
    {point : Omega | ∀ index : Sum Index Unit,
      Sum.elim period (fun _ => goldenPeriod) index point.1 = 0} =
      {point : Omega | ∀ index, period index point.1 = 0} := by
  have extendedNonvanishing : ∀ point, point ∈ Omega ->
      ∃ index : Sum Index Unit,
        Sum.elim twist (fun _ => goldenTwist) index point ≠ 0 := by
    intro point pointInOmega
    obtain ⟨index, twistNonzero⟩ :=
      pointwiseNonvanishing point pointInOmega
    exact ⟨Sum.inl index, twistNonzero⟩
  refine ⟨extendedNonvanishing, ?_⟩
  have extendedFactorization : ∀ (index : Sum Index Unit) point,
      Sum.elim period (fun _ => goldenPeriod) index point =
        xiReading point *
          Sum.elim twist (fun _ => goldenTwist) index point := by
    intro index point
    cases index with
    | inl originalIndex => exact factorization originalIndex point
    | inr _ => exact goldenFactorization point
  have extendedLocus := toroidal_common_zero_locus Omega
    (Sum.elim period (fun _ => goldenPeriod))
    (Sum.elim twist (fun _ => goldenTwist))
    extendedFactorization extendedNonvanishing
  have originalLocus := toroidal_common_zero_locus Omega period twist
    factorization pointwiseNonvanishing
  exact extendedLocus.trans originalLocus.symm

/-- Under global pointwise nonvanishing of the original family, the exact
right-hand common-zero condition in the frozen toroidal temperedness criterion
is invariant under adjoining an arbitrary golden twist channel. -/
theorem golden_toroidal_temperedness_rhs_iff
    {Index : Type*} (twist : Index -> ℂ -> ℂ)
    (pointwiseNonvanishing : ∀ point,
      ∃ index, twist index point ≠ 0)
    (goldenTwist : ℂ -> ℂ) :
    (∀ point,
      (∀ index : Sum Index Unit,
        completedRiemannZeta point *
          Sum.elim twist (fun _ => goldenTwist) index point = 0) ->
        (point - (1 / 2 : ℂ)).re = 0) <->
    (∀ point,
      (∀ index,
        completedRiemannZeta point * twist index point = 0) ->
        (point - (1 / 2 : ℂ)).re = 0) := by
  have extendedNonvanishing : ∀ point,
      ∃ index : Sum Index Unit,
        Sum.elim twist (fun _ => goldenTwist) index point ≠ 0 := by
    intro point
    obtain ⟨index, twistNonzero⟩ := pointwiseNonvanishing point
    exact ⟨Sum.inl index, twistNonzero⟩
  have extendedCriterion := rh_iff_all_toroidal_eisenstein_tempered
    (Sum.elim twist (fun _ => goldenTwist)) extendedNonvanishing
  have originalCriterion := rh_iff_all_toroidal_eisenstein_tempered
    twist pointwiseNonvanishing
  exact extendedCriterion.symm.trans originalCriterion

-- Concrete data witnessing simultaneous satisfiability of the hypotheses.
example :
    let Omega : Set ℂ := Set.univ
    let period : Unit -> ℂ -> ℂ := fun _ point => xiReading point
    let twist : Unit -> ℂ -> ℂ := fun _ _ => 1
    let goldenPeriod : ℂ -> ℂ := xiReading
    let goldenTwist : ℂ -> ℂ := fun _ => 1
    (∀ index point,
      period index point = xiReading point * twist index point) ∧
    (∀ point, point ∈ Omega -> ∃ index, twist index point ≠ 0) ∧
    (∀ point,
      goldenPeriod point = xiReading point * goldenTwist point) := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro index point
    simp
  · intro point pointInOmega
    exact ⟨(), one_ne_zero⟩
  · intro point
    simp

-- The extended index carrier is inhabited independently of the theorem data.
example : Nonempty (Sum Unit Unit) := ⟨Sum.inl ()⟩

#print axioms golden_toroidal_index_extension
#print axioms golden_toroidal_temperedness_rhs_iff

end D5.S3.Analytic.Toroidal.GoldenToroidalIndexExtension
