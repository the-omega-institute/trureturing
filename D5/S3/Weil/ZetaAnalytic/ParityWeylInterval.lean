/- GID: D5/S3/Weil/ZetaAnalytic/ParityWeylInterval
   generality: G
   mirror-B: D5/B/S3/Weil/ZetaAnalytic/ParityWeylInterval
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Parity channel quotients cut out an invariant resolvent interval and its completions. -/

import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic

/- Library-search audit trail (2026-08-29):
   * D5 searches for parity Weyl intervals, affine channel positivity,
     particular-solution invariance, and real-axis positive completions found
     no exact theorem.
   * `ZetaCore.ResolventParitySignatures` constructs the source's opposite
     affine signs, but does not package the supremum/infimum endpoint bridge.
   * Pinned Mathlib supplies `le_csSup`, `csSup_le`, `le_csInf`, and `csInf_le`;
     no theorem combines the two channel rays or proves coordinate invariance.
   * The completion carrier uses Mathlib's positive `Measure Real`; evenness is
     the canonical reflection equation `Measure.map (fun x => -x) nu = nu`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory Set

namespace D5.S3.Weil.ZetaAnalytic.ParityWeylInterval

/-- The two parity-channel Rayleigh boundaries determine the complete local
resolvent interval.  Recentring the particular solution preserves the
admissible set, and a two-sided positive-extension interface identifies the
same interval with even real-axis spectral completions. -/
theorem parity_weyl_interval
    {Even Odd Source : Type*}
    (evenBase evenBoundary : Even -> Real)
    (oddBase oddBoundary : Odd -> Real)
    (referenceBudget : Real)
    (source : Source)
    (spectralReading : Measure Real -> Source)
    (resolventMoment : Measure Real -> Real)
    (evenBoundaryNonnegative : forall e, 0 <= evenBoundary e)
    (oddBoundaryNonnegative : forall o, 0 <= oddBoundary o)
    (evenKernelNonnegative : forall e, evenBoundary e = 0 -> 0 <= evenBase e)
    (oddKernelNonnegative : forall o, oddBoundary o = 0 -> 0 <= oddBase o)
    (evenChannelNontrivial : exists e, evenBoundary e ≠ 0)
    (oddChannelNontrivial : exists o, oddBoundary o ≠ 0)
    (evenRatiosBounded : BddAbove
      {q : Real | exists e, evenBoundary e ≠ 0 /\
        q = -evenBase e / evenBoundary e})
    (oddRatiosBounded : BddBelow
      {q : Real | exists o, oddBoundary o ≠ 0 /\
        q = oddBase o / oddBoundary o}) :
    let evenRatios := {q : Real | exists e, evenBoundary e ≠ 0 /\
      q = -evenBase e / evenBoundary e}
    let oddRatios := {q : Real | exists o, oddBoundary o ≠ 0 /\
      q = oddBase o / oddBoundary o}
    let lower := referenceBudget + sSup evenRatios
    let upper := referenceBudget + sInf oddRatios
    let admissible := fun R : Real =>
      0 <= R /\
      (forall e, 0 <= evenBase e + (R - referenceBudget) * evenBoundary e) /\
      (forall o, 0 <= oddBase o - (R - referenceBudget) * oddBoundary o)
    let shiftedAdmissible := fun delta R : Real =>
      0 <= R /\
      (forall e, 0 <= evenBase e + delta * evenBoundary e +
        (R - (referenceBudget + delta)) * evenBoundary e) /\
      (forall o, 0 <= oddBase o - delta * oddBoundary o -
        (R - (referenceBudget + delta)) * oddBoundary o)
    let completion := fun R : Real => exists nu : Measure Real,
      Measure.map (fun x : Real => -x) nu = nu /\
      spectralReading nu = source /\ resolventMoment nu = R
    (forall R, admissible R <-> R ∈ Icc (max 0 lower) upper) /\
    (lower > upper -> ¬ exists R, admissible R) /\
    (forall delta,
      {R : Real | shiftedAdmissible delta R} = {R : Real | admissible R}) /\
    (((forall R, admissible R -> completion R) /\
      (forall nu : Measure Real,
        Measure.map (fun x : Real => -x) nu = nu ->
        spectralReading nu = source -> admissible (resolventMoment nu))) ->
      forall R, R ∈ Icc (max 0 lower) upper <-> completion R) := by
  let evenRatios : Set Real := {q | exists e, evenBoundary e ≠ 0 /\
    q = -evenBase e / evenBoundary e}
  let oddRatios : Set Real := {q | exists o, oddBoundary o ≠ 0 /\
    q = oddBase o / oddBoundary o}
  let lower := referenceBudget + sSup evenRatios
  let upper := referenceBudget + sInf oddRatios
  let admissible := fun R : Real =>
    0 <= R /\
    (forall e, 0 <= evenBase e + (R - referenceBudget) * evenBoundary e) /\
    (forall o, 0 <= oddBase o - (R - referenceBudget) * oddBoundary o)
  let shiftedAdmissible := fun delta R : Real =>
    0 <= R /\
    (forall e, 0 <= evenBase e + delta * evenBoundary e +
      (R - (referenceBudget + delta)) * evenBoundary e) /\
    (forall o, 0 <= oddBase o - delta * oddBoundary o -
      (R - (referenceBudget + delta)) * oddBoundary o)
  let completion := fun R : Real => exists nu : Measure Real,
    Measure.map (fun x : Real => -x) nu = nu /\
    spectralReading nu = source /\ resolventMoment nu = R
  change
    (forall R, admissible R <-> R ∈ Icc (max 0 lower) upper) /\
    (lower > upper -> ¬ exists R, admissible R) /\
    (forall delta,
      {R : Real | shiftedAdmissible delta R} = {R : Real | admissible R}) /\
    (((forall R, admissible R -> completion R) /\
      (forall nu : Measure Real,
        Measure.map (fun x : Real => -x) nu = nu ->
        spectralReading nu = source -> admissible (resolventMoment nu))) ->
      forall R, R ∈ Icc (max 0 lower) upper <-> completion R)
  have evenRatiosNonempty : evenRatios.Nonempty := by
    obtain ⟨e, he⟩ := evenChannelNontrivial
    exact ⟨-evenBase e / evenBoundary e, e, he, rfl⟩
  have oddRatiosNonempty : oddRatios.Nonempty := by
    obtain ⟨o, ho⟩ := oddChannelNontrivial
    exact ⟨oddBase o / oddBoundary o, o, ho, rfl⟩
  have even_iff (R : Real) :
      (forall e, 0 <= evenBase e + (R - referenceBudget) * evenBoundary e) <->
        lower <= R := by
    constructor
    · intro hEven
      have supBound : sSup evenRatios <= R - referenceBudget := by
        apply csSup_le evenRatiosNonempty
        rintro q ⟨e, he, rfl⟩
        have hPositive : 0 < evenBoundary e :=
          lt_of_le_of_ne (evenBoundaryNonnegative e) (Ne.symm he)
        apply (div_le_iff₀ hPositive).2
        linarith [hEven e]
      dsimp only [lower]
      linarith
    · intro hLower e
      by_cases he : evenBoundary e = 0
      · simpa [he] using evenKernelNonnegative e he
      · have hPositive : 0 < evenBoundary e :=
          lt_of_le_of_ne (evenBoundaryNonnegative e) (Ne.symm he)
        have quotientLeSup :
            -evenBase e / evenBoundary e <= sSup evenRatios :=
          le_csSup evenRatiosBounded ⟨e, he, rfl⟩
        have ratioBound :
            -evenBase e / evenBoundary e <= R - referenceBudget := by
          dsimp only [lower] at hLower
          linarith
        have scaled := (div_le_iff₀ hPositive).mp ratioBound
        linarith
  have odd_iff (R : Real) :
      (forall o, 0 <= oddBase o - (R - referenceBudget) * oddBoundary o) <->
        R <= upper := by
    constructor
    · intro hOdd
      have infBound : R - referenceBudget <= sInf oddRatios := by
        apply le_csInf oddRatiosNonempty
        rintro q ⟨o, ho, rfl⟩
        have hPositive : 0 < oddBoundary o :=
          lt_of_le_of_ne (oddBoundaryNonnegative o) (Ne.symm ho)
        apply (le_div_iff₀ hPositive).2
        linarith [hOdd o]
      dsimp only [upper]
      linarith
    · intro hUpper o
      by_cases ho : oddBoundary o = 0
      · simpa [ho] using oddKernelNonnegative o ho
      · have hPositive : 0 < oddBoundary o :=
          lt_of_le_of_ne (oddBoundaryNonnegative o) (Ne.symm ho)
        have infLeQuotient :
            sInf oddRatios <= oddBase o / oddBoundary o :=
          csInf_le oddRatiosBounded ⟨o, ho, rfl⟩
        have ratioBound :
            R - referenceBudget <= oddBase o / oddBoundary o := by
          dsimp only [upper] at hUpper
          linarith
        have scaled := (le_div_iff₀ hPositive).mp ratioBound
        linarith
  have intervalCharacterization :
      forall R, admissible R <-> R ∈ Icc (max 0 lower) upper := by
    intro R
    dsimp only [admissible]
    rw [even_iff, odd_iff]
    simp only [mem_Icc, max_le_iff]
    tauto
  refine ⟨intervalCharacterization, ?_, ?_, ?_⟩
  · intro endpointsCross ⟨R, hR⟩
    have intervalMem := (intervalCharacterization R).mp hR
    exact (not_le_of_gt endpointsCross)
      ((le_max_right 0 lower).trans intervalMem.1 |>.trans intervalMem.2)
  · intro delta
    ext R
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hR, hEven, hOdd⟩
      refine ⟨hR, ?_, ?_⟩
      · intro e
        nlinarith [hEven e]
      · intro o
        nlinarith [hOdd o]
    · rintro ⟨hR, hEven, hOdd⟩
      refine ⟨hR, ?_, ?_⟩
      · intro e
        nlinarith [hEven e]
      · intro o
        nlinarith [hOdd o]
  · rintro ⟨completionOfPositive, positiveOfCompletion⟩ R
    constructor
    · intro hR
      exact completionOfPositive R ((intervalCharacterization R).mpr hR)
    · rintro ⟨nu, hEven, hReading, hMoment⟩
      subst R
      exact (intervalCharacterization (resolventMoment nu)).mp
        (positiveOfCompletion nu hEven hReading)

example :
    let evenBase : Unit -> Real := fun _ => 0
    let evenBoundary : Unit -> Real := fun _ => 1
    let oddBase : Unit -> Real := fun _ => 1
    let oddBoundary : Unit -> Real := fun _ => 1
    (forall e, 0 <= evenBoundary e) /\
    (forall o, 0 <= oddBoundary o) /\
    (forall e, evenBoundary e = 0 -> 0 <= evenBase e) /\
    (forall o, oddBoundary o = 0 -> 0 <= oddBase o) /\
    (exists e, evenBoundary e ≠ 0) /\
    (exists o, oddBoundary o ≠ 0) := by
  simp

#print axioms parity_weyl_interval

end D5.S3.Weil.ZetaAnalytic.ParityWeylInterval
