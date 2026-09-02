/- GID: D5/S3/ContinuousObservables/PermutationReadoutRefinementHorizon
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/PermutationReadoutRefinementHorizon
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Readout refinement grows permutation horizons within the full cyclic-orbit bound. -/

import D5.S3.ContinuousObservables.PermutationOrbitHorizon

/- Library-search audit trail (2026-09-02):
   * Six-route searches covered readout subfamilies, restricted suprema, horizon
     monotonicity, strict horizon enlargement, orbit inclusion, digestion receipts,
     theorem-body generalizations, and every in-flight lane. The frozen owners
     `ObserverHorizonRefinement`, `PermutationOrbitHorizon`, and
     `AsymmetricPermutationDistances` provide separate ingredients but no theorem
     about permutation-admissible readout subfamilies or the strict example below.
   * `permutation_observer_horizon_eq_orbit_complement` is reused for the full-family
     upper bound and for action change. Pinned Mathlib supplies complete-lattice
     supremum laws, `iSup_eq_top`, cyclic subgroup orbits, and bounded finite ranges.
   * A literal singleton indicator family cannot create infinite distance: its one
     finite oscillation has finite supremum. The strict source example is therefore
     corrected to adjoin all real scalar multiples of the orbit indicator. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set
open scoped ENNReal

namespace D5.S3.ContinuousObservables.PermutationReadoutRefinementHorizon

open D5.S3.ContinuousObservables.ObserverDistanceClassification
open D5.S3.ContinuousObservables.PermutationOrbitHorizon

/-- A readout bundled with the fixed permutation's bounded unit-edge condition. -/
abbrev PermutationReadout {I : Type*} (tau : Equiv.Perm I) :=
  {f : I -> Real // edgeAdmissible tau f}

/-- Observer distance restricted to an explicitly chosen admissible readout family. -/
noncomputable def familyObserverDistance {I : Type*} (tau : Equiv.Perm I)
    (family : Set (PermutationReadout tau)) (x y : I) : ENNReal :=
  ⨆ f : family, ENNReal.ofReal (dist (f.1.1 x) (f.1.1 y))

/-- The infinite-distance horizon of an explicitly chosen readout family. -/
def familyHorizon {I : Type*} (tau : Equiv.Perm I)
    (family : Set (PermutationReadout tau)) (o : I) : Set I :=
  {x | familyObserverDistance tau family o x = ⊤}

private theorem familyObserverDistance_mono {I : Type*} (tau : Equiv.Perm I)
    {oldFamily newFamily : Set (PermutationReadout tau)}
    (familyInclusion : oldFamily ⊆ newFamily) (x y : I) :
    familyObserverDistance tau oldFamily x y <=
      familyObserverDistance tau newFamily x y := by
  unfold familyObserverDistance
  apply iSup_le
  intro f
  exact le_iSup_of_le
    (⟨f.1, familyInclusion f.2⟩ : newFamily) le_rfl

private theorem familyObserverDistance_le_full {I : Type*}
    (tau : Equiv.Perm I) (family : Set (PermutationReadout tau)) (x y : I) :
    familyObserverDistance tau family x y <= observerDistance tau x y := by
  unfold familyObserverDistance observerDistance
  apply iSup_le
  intro f
  exact le_iSup_of_le f.1 le_rfl

private theorem familyObserverDistance_univ {I : Type*}
    (tau : Equiv.Perm I) (x y : I) :
    familyObserverDistance tau Set.univ x y = observerDistance tau x y := by
  apply le_antisymm
  · exact familyObserverDistance_le_full tau Set.univ x y
  · unfold familyObserverDistance observerDistance
    apply iSup_le
    intro f
    exact le_iSup_of_le (⟨f, Set.mem_univ f⟩ : (Set.univ :
      Set (PermutationReadout tau))) le_rfl

private theorem family_horizon_mono {I : Type*} (tau : Equiv.Perm I)
    {oldFamily newFamily : Set (PermutationReadout tau)}
    (familyInclusion : oldFamily ⊆ newFamily) (o : I) :
    familyHorizon tau oldFamily o ⊆ familyHorizon tau newFamily o := by
  intro x oldInfinite
  have distanceMonotone :=
    familyObserverDistance_mono tau familyInclusion o x
  change familyObserverDistance tau oldFamily o x = ⊤ at oldInfinite
  change familyObserverDistance tau newFamily o x = ⊤
  rw [oldInfinite] at distanceMonotone
  exact top_unique distanceMonotone

private theorem family_horizon_subset_orbit_complement {I : Type*}
    (tau : Equiv.Perm I) (family : Set (PermutationReadout tau)) (o : I) :
    familyHorizon tau family o ⊆
      (MulAction.orbit (Subgroup.zpowers tau) o)ᶜ := by
  intro x restrictedInfinite
  have distanceComparison := familyObserverDistance_le_full tau family o x
  change familyObserverDistance tau family o x = ⊤ at restrictedInfinite
  rw [restrictedInfinite] at distanceComparison
  have fullInfinite : observerDistance tau o x = ⊤ := top_unique distanceComparison
  have fullHorizonEquality :=
    (permutation_observer_horizon_eq_orbit_complement tau o x o).2.2.1
  rw [← fullHorizonEquality]
  exact fullInfinite

private theorem full_family_horizon {I : Type*}
    (tau : Equiv.Perm I) (o : I) :
    familyHorizon tau Set.univ o =
      (MulAction.orbit (Subgroup.zpowers tau) o)ᶜ := by
  ext x
  change familyObserverDistance tau Set.univ o x = ⊤ ↔ _
  rw [familyObserverDistance_univ]
  have fullHorizonEquality :=
    (permutation_observer_horizon_eq_orbit_complement tau o x o).2.2.1
  exact Set.ext_iff.mp fullHorizonEquality x

/-- The strictness claim has a concrete two-orbit witness. The refined family
contains every real multiple of one orbit indicator; the empty family has no
horizon, while the scaled indicator sends the other orbit to infinite distance. -/
theorem scaled_orbit_indicator_strictly_enlarges_horizon :
    exists (tau : Equiv.Perm Bool)
      (oldFamily newFamily : Set (PermutationReadout tau)),
      oldFamily ⊆ newFamily /\
      familyHorizon tau oldFamily false = ∅ /\
      true ∈ familyHorizon tau newFamily false := by
  let tau : Equiv.Perm Bool := Equiv.refl Bool
  let oldFamily : Set (PermutationReadout tau) := ∅
  let newFamily : Set (PermutationReadout tau) :=
    {f | exists c : Real, f.1 = fun b => if b = true then c else 0}
  refine ⟨tau, oldFamily, newFamily, Set.empty_subset _, ?_, ?_⟩
  · ext b
    simp [familyHorizon, familyObserverDistance, oldFamily]
  · change familyObserverDistance tau newFamily false true = ⊤
    apply (iSup_eq_top).2
    intro bound boundBelowTop
    have boundNeTop : bound ≠ ⊤ := ne_of_lt boundBelowTop
    obtain ⟨n, nLarge⟩ := exists_nat_gt bound.toReal
    let readout : PermutationReadout tau :=
      ⟨fun b => if b = true then (n : Real) else 0, by
        constructor
        · rw [Metric.isBounded_range_iff]
          refine ⟨(n : Real), ?_⟩
          intro i j
          cases i <;> cases j <;> simp [Real.dist_eq]
        · intro i
          cases i <;> norm_num [tau]⟩
    have readoutInFamily : readout ∈ newFamily := by
      refine ⟨(n : Real), ?_⟩
      funext b
      cases b <;> rfl
    refine ⟨⟨readout, readoutInFamily⟩, ?_⟩
    change bound < ENNReal.ofReal (dist (readout.1 false) (readout.1 true))
    have nPositive : 0 < (n : Real) := by
      exact lt_of_le_of_lt ENNReal.toReal_nonneg nLarge
    rw [show dist (readout.1 false) (readout.1 true) = (n : Real) by
      simp [readout, Real.dist_eq, abs_of_nonneg nPositive.le]]
    rw [← ENNReal.ofReal_toReal boundNeTop]
    exact (ENNReal.ofReal_lt_ofReal_iff nPositive).2 nLarge

/-- Arbitrary readout refinement is monotone but never crosses the full
cyclic-orbit upper bound. The full family attains that bound. If a second
permutation makes a formerly external point part of the origin orbit, that
point moves from the old full horizon into the new finite-distance ball. The
last conjunct supplies the corrected strict-refinement witness. -/
theorem permutation_readout_refinement_horizon
    {I : Type*} (tau tau' : Equiv.Perm I) (o : I) :
    (forall family : Set (PermutationReadout tau),
      familyHorizon tau family o ⊆
        (MulAction.orbit (Subgroup.zpowers tau) o)ᶜ) /\
    (forall oldFamily newFamily : Set (PermutationReadout tau),
      oldFamily ⊆ newFamily ->
        familyHorizon tau oldFamily o ⊆ familyHorizon tau newFamily o) /\
    familyHorizon tau Set.univ o =
      (MulAction.orbit (Subgroup.zpowers tau) o)ᶜ /\
    (forall y, y ∈ MulAction.orbit (Subgroup.zpowers tau') o ->
      y ∉ MulAction.orbit (Subgroup.zpowers tau) o ->
        y ∈ familyHorizon tau Set.univ o /\
          y ∈ finiteDistanceBall tau' o) /\
    (exists (exampleTau : Equiv.Perm Bool)
      (oldFamily newFamily : Set (PermutationReadout exampleTau)),
      oldFamily ⊆ newFamily /\
      familyHorizon exampleTau oldFamily false = ∅ /\
      true ∈ familyHorizon exampleTau newFamily false) := by
  refine ⟨(fun family => family_horizon_subset_orbit_complement tau family o), ?_,
    full_family_horizon tau o, ?_, scaled_orbit_indicator_strictly_enlarges_horizon⟩
  · intro oldFamily newFamily inclusion
    exact family_horizon_mono tau inclusion o
  · intro y inNewOrbit outsideOldOrbit
    constructor
    · rw [full_family_horizon]
      exact outsideOldOrbit
    · rw [(permutation_observer_horizon_eq_orbit_complement
        tau' o y o).2.2.2]
      exact inNewOrbit

#print axioms scaled_orbit_indicator_strictly_enlarges_horizon
#print axioms permutation_readout_refinement_horizon

end D5.S3.ContinuousObservables.PermutationReadoutRefinementHorizon
