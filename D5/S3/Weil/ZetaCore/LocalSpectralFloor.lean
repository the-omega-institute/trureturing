/- GID: D5/S3/Weil/ZetaCore/LocalSpectralFloor
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaCore/LocalSpectralFloor
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Parity decomposition and cone margins determine local spectral floors. -/

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 searches for parity spectral decompositions, Rayleigh infima, cone
     margins, and white-noise floors found no existing theorem with either
     public statement.
   * The freshly frozen positivity and matrix owners were inspected; they
     provide adjacent positive-semidefinite tools but no exact spectral-floor
     identity on this carrier.
   * Pinned Mathlib has no exact parity-Rayleigh theorem.  Its exact
     `csSup_lowerBounds_eq_csInf` theorem is applied directly in the cone-margin
     proof. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Weil.ZetaCore.LocalSpectralFloor

open Set

/-- When the quadratic energy and squared norm split into their even and odd
parts, the full Rayleigh infimum is the smaller parity-sector infimum. -/
theorem parity_spectral_infimum
    {Even Odd : Type*}
    [Zero Even] [Zero Odd] [Nontrivial Even] [Nontrivial Odd]
    (evenEnergy evenNormSq : Even -> Real)
    (oddEnergy oddNormSq : Odd -> Real)
    (evenEnergyZero : evenEnergy 0 = 0)
    (oddEnergyZero : oddEnergy 0 = 0)
    (evenNormZero : evenNormSq 0 = 0)
    (oddNormZero : oddNormSq 0 = 0)
    (evenNormPositive : forall e, e ≠ 0 -> 0 < evenNormSq e)
    (oddNormPositive : forall o, o ≠ 0 -> 0 < oddNormSq o)
    (evenBounded : BddBelow
      {r : Real | exists e, e ≠ 0 /\ r = evenEnergy e / evenNormSq e})
    (oddBounded : BddBelow
      {r : Real | exists o, o ≠ 0 /\ r = oddEnergy o / oddNormSq o}) :
    let fullValues := {r : Real | exists e o, (e, o) ≠ 0 /\
      r = (evenEnergy e + oddEnergy o) / (evenNormSq e + oddNormSq o)}
    let evenValues :=
      {r : Real | exists e, e ≠ 0 /\ r = evenEnergy e / evenNormSq e}
    let oddValues :=
      {r : Real | exists o, o ≠ 0 /\ r = oddEnergy o / oddNormSq o}
    sInf fullValues = min (sInf evenValues) (sInf oddValues) := by
  dsimp only
  let evenValues : Set Real :=
    {r | exists e, e ≠ 0 /\ r = evenEnergy e / evenNormSq e}
  let oddValues : Set Real :=
    {r | exists o, o ≠ 0 /\ r = oddEnergy o / oddNormSq o}
  let fullValues : Set Real := {r | exists e o, (e, o) ≠ 0 /\
    r = (evenEnergy e + oddEnergy o) / (evenNormSq e + oddNormSq o)}
  have evenNonempty : evenValues.Nonempty := by
    obtain ⟨e, eNonzero⟩ := exists_ne (0 : Even)
    exact ⟨evenEnergy e / evenNormSq e, e, eNonzero, rfl⟩
  have oddNonempty : oddValues.Nonempty := by
    obtain ⟨o, oNonzero⟩ := exists_ne (0 : Odd)
    exact ⟨oddEnergy o / oddNormSq o, o, oNonzero, rfl⟩
  have fullNonempty : fullValues.Nonempty := by
    obtain ⟨e, eNonzero⟩ := exists_ne (0 : Even)
    refine ⟨(evenEnergy e + oddEnergy 0) / (evenNormSq e + oddNormSq 0),
      e, 0, ?_, rfl⟩
    simpa using eNonzero
  have fullLowerBound : min (sInf evenValues) (sInf oddValues) ∈
      lowerBounds fullValues := by
    rintro value ⟨e, o, pairNonzero, rfl⟩
    by_cases eNonzero : e ≠ 0
    · by_cases oNonzero : o ≠ 0
      · have evenRatioBound : min (sInf evenValues) (sInf oddValues) <=
            evenEnergy e / evenNormSq e :=
          (min_le_left _ _).trans (csInf_le evenBounded ⟨e, eNonzero, rfl⟩)
        have oddRatioBound : min (sInf evenValues) (sInf oddValues) <=
            oddEnergy o / oddNormSq o :=
          (min_le_right _ _).trans (csInf_le oddBounded ⟨o, oNonzero, rfl⟩)
        have evenScaled := (le_div_iff₀ (evenNormPositive e eNonzero)).mp evenRatioBound
        have oddScaled := (le_div_iff₀ (oddNormPositive o oNonzero)).mp oddRatioBound
        apply (le_div_iff₀ (add_pos (evenNormPositive e eNonzero)
          (oddNormPositive o oNonzero))).2
        linarith
      · have oZero : o = 0 := not_ne_iff.mp oNonzero
        subst o
        simpa [oddEnergyZero, oddNormZero] using
          (min_le_left (sInf evenValues) (sInf oddValues)).trans
            (csInf_le evenBounded ⟨e, eNonzero, rfl⟩)
    · have eZero : e = 0 := not_ne_iff.mp eNonzero
      subst e
      have oNonzero : o ≠ 0 := by
        intro oZero
        subst o
        exact pairNonzero rfl
      simpa [evenEnergyZero, evenNormZero] using
        (min_le_right (sInf evenValues) (sInf oddValues)).trans
          (csInf_le oddBounded ⟨o, oNonzero, rfl⟩)
  have fullBounded : BddBelow fullValues :=
    ⟨min (sInf evenValues) (sInf oddValues), fullLowerBound⟩
  apply le_antisymm
  · apply le_min
    · apply le_csInf evenNonempty
      rintro value ⟨e, eNonzero, rfl⟩
      apply csInf_le fullBounded
      refine ⟨e, 0, ?_, ?_⟩
      · simpa using eNonzero
      · simp [oddEnergyZero, oddNormZero]
    · apply le_csInf oddNonempty
      rintro value ⟨o, oNonzero, rfl⟩
      apply csInf_le fullBounded
      refine ⟨0, o, ?_, ?_⟩
      · simpa using oNonzero
      · simp [evenEnergyZero, evenNormZero]
  · exact le_csInf fullNonempty fullLowerBound

/-- Subtracting a white-noise floor `lambda * normSq` is nonnegative exactly
when `lambda` is a lower bound for every nonzero Rayleigh quotient. -/
theorem white_noise_cone_margin
    {H : Type*}
    [Zero H] [Nontrivial H]
    (quadratic normSq : H -> Real)
    (quadraticZero : quadratic 0 = 0)
    (normZero : normSq 0 = 0)
    (normPositive : forall f, f ≠ 0 -> 0 < normSq f)
    (rayleighBounded : BddBelow
      {r : Real | exists f, f ≠ 0 /\ r = quadratic f / normSq f}) :
    let rayleighValues :=
      {r : Real | exists f, f ≠ 0 /\ r = quadratic f / normSq f}
    let admissibleFloors :=
      {lambda : Real | forall f, 0 <= quadratic f - lambda * normSq f}
    sInf rayleighValues = sSup admissibleFloors := by
  dsimp only
  let rayleighValues : Set Real :=
    {r | exists f, f ≠ 0 /\ r = quadratic f / normSq f}
  let admissibleFloors : Set Real :=
    {lambda | forall f, 0 <= quadratic f - lambda * normSq f}
  have rayleighNonempty : rayleighValues.Nonempty := by
    obtain ⟨f, fNonzero⟩ := exists_ne (0 : H)
    exact ⟨quadratic f / normSq f, f, fNonzero, rfl⟩
  have admissible_eq_lowerBounds : admissibleFloors = lowerBounds rayleighValues := by
    ext lambda
    constructor
    · intro admissible value valueMembership
      rcases valueMembership with ⟨f, fNonzero, rfl⟩
      apply (le_div_iff₀ (normPositive f fNonzero)).2
      linarith [admissible f]
    · intro lowerBound f
      by_cases fNonzero : f ≠ 0
      · have quotientBound : lambda <= quadratic f / normSq f :=
          lowerBound ⟨f, fNonzero, rfl⟩
        have scaledBound := (le_div_iff₀ (normPositive f fNonzero)).mp quotientBound
        linarith
      · have fZero : f = 0 := not_ne_iff.mp fNonzero
        subst f
        simp [quadraticZero, normZero]
  change sInf rayleighValues = sSup admissibleFloors
  rw [admissible_eq_lowerBounds,
    csSup_lowerBounds_eq_csInf rayleighBounded rayleighNonempty]

#print axioms parity_spectral_infimum
#print axioms white_noise_cone_margin

end D5.S3.Weil.ZetaCore.LocalSpectralFloor
