/- GID: D5/S3/ContinuousObservables/SelfDescriptionDistanceClassification
   generality: I
   mirror-B: D5/B/S3/ContinuousObservables/SelfDescriptionDistanceClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Self-description pairs split into zero, finite-reachable, and horizon distances. -/

import D5.S3.ContinuousObservables.PermutationOrbitHorizon

/- Library-search audit trail (2026-08-28):
   * Repository body-shape searches found the canonical `observerDistance` and
     `edgeAdmissible` in `ObserverDistanceClassification`; both are imported through
     `PermutationOrbitHorizon` rather than redeclared.
   * `permutation_observer_horizon_eq_orbit_complement` is the exact frozen owner for
     the top-distance/orbit-complement equivalence and the signed-path distance bound.
   * `DualObserverDistanceReadings` supplies adjacent ENNReal branch semantics on a
     bounded-function carrier, but it does not state the permutation bookkeeping
     conditional assembled here.
   * Pinned Mathlib contains no declaration named `observerDistance` or
     `edgeAdmissible`; `loogle` and `leansearch` executables are absent from PATH. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace D5.S3.ContinuousObservables.SelfDescriptionDistanceClassification

open D5.S3.ContinuousObservables.ObserverDistanceClassification
open D5.S3.ContinuousObservables.PermutationOrbitHorizon

private theorem observer_distance_eq_zero_iff_readout_agreement
    {I : Type*} (tau : Equiv.Perm I) (x y : I) :
    observerDistance tau x y = 0 ↔
      ∀ f : I -> Real, edgeAdmissible tau f -> f x = f y := by
  constructor
  · intro distanceZero f admissible
    have termLeDistance :
        ENNReal.ofReal (dist (f x) (f y)) <= observerDistance tau x y := by
      unfold observerDistance
      exact le_iSup
        (fun observable : {g : I -> Real // edgeAdmissible tau g} =>
          ENNReal.ofReal (dist (observable.1 x) (observable.1 y)))
        ⟨f, admissible⟩
    have termZero : ENNReal.ofReal (dist (f x) (f y)) = 0 :=
      le_antisymm (termLeDistance.trans_eq distanceZero) bot_le
    apply dist_eq_zero.mp
    apply le_antisymm
    · exact ENNReal.ofReal_eq_zero.mp termZero
    · exact dist_nonneg
  · intro agreement
    apply le_antisymm
    · unfold observerDistance
      apply iSup_le
      intro observable
      simp [agreement observable.1 observable.2]
    · exact bot_le

private theorem top_distance_has_no_signed_path
    {I : Type*} (tau : Equiv.Perm I) (x y : I)
    (distanceTop : observerDistance tau x y = ⊤) :
    ∀ n : Int, y ≠ (tau ^ n) x := by
  intro n path
  have bound :=
    (permutation_observer_horizon_eq_orbit_complement tau x y x).2.1 n path
  rw [distanceTop] at bound
  simp at bound

private theorem finite_distance_has_bookkeeping_witness
    {I : Type*} (tau : Equiv.Perm I) (x y : I)
    (distancePositive : 0 < observerDistance tau x y)
    (distanceFinite : observerDistance tau x y < ⊤) :
    ∃ (f : I -> Real) (n : Int),
      edgeAdmissible tau f ∧
        f x ≠ f y ∧
        y = (tau ^ n) x ∧
        observerDistance tau x y <= (n.natAbs : ENNReal) := by
  have readoutSeparates :
      ∃ f : I -> Real, edgeAdmissible tau f ∧ f x ≠ f y := by
    by_contra noSeparator
    push Not at noSeparator
    have distanceZero : observerDistance tau x y = 0 :=
      (observer_distance_eq_zero_iff_readout_agreement tau x y).2 noSeparator
    exact (ne_of_gt distancePositive) distanceZero
  have yInFiniteBall : y ∈ finiteDistanceBall tau x := distanceFinite.ne
  have yInOrbit :
      y ∈ MulAction.orbit (Subgroup.zpowers tau) x := by
    rw [← (permutation_observer_horizon_eq_orbit_complement tau x y x).2.2.2]
    exact yInFiniteBall
  rcases yInOrbit with ⟨g, action⟩
  obtain ⟨n, power⟩ := Subgroup.mem_zpowers_iff.mp g.2
  have path : y = (tau ^ n) x := by
    simpa [MulAction.subgroup_smul_def, Equiv.Perm.smul_def, power] using action.symm
  rcases readoutSeparates with ⟨f, admissible, separates⟩
  refine ⟨f, n, admissible, separates, path, ?_⟩
  exact (permutation_observer_horizon_eq_orbit_complement tau x y x).2.1 n path

/-- For every self-description difference, the outside observer's canonical
permutation distance is zero, finite positive, or infinite.  If every such
difference is externally hidden, no admissible readout can distinguish it along
any finite signed update path.  Every finite-positive difference has both an
admissible separating readout and a signed path whose length bounds its distance. -/
theorem self_description_distance_classification
    {I SelfReadout : Type*} (tau : Equiv.Perm I)
    (selfReadout : SelfReadout -> I -> Real) :
    let SelfDifference :=
      {pair : I × I //
        ∃ self : SelfReadout,
          selfReadout self pair.1 ≠ selfReadout self pair.2}
    (∀ pair : SelfDifference,
      (observerDistance tau pair.1.1 pair.1.2 = 0 ∧
          ∀ f : I -> Real,
            edgeAdmissible tau f -> f pair.1.1 = f pair.1.2) ∨
        (0 < observerDistance tau pair.1.1 pair.1.2 ∧
          observerDistance tau pair.1.1 pair.1.2 < ⊤) ∨
        (observerDistance tau pair.1.1 pair.1.2 = ⊤ ∧
          ∀ n : Int, pair.1.2 ≠ (tau ^ n) pair.1.1)) ∧
    ((∀ pair : SelfDifference,
        observerDistance tau pair.1.1 pair.1.2 = 0 ∨
          observerDistance tau pair.1.1 pair.1.2 = ⊤) ->
      ∀ pair : SelfDifference,
        ¬∃ (f : I -> Real) (n : Int),
          edgeAdmissible tau f ∧
            f pair.1.1 ≠ f pair.1.2 ∧
            pair.1.2 = (tau ^ n) pair.1.1) ∧
    (∀ pair : SelfDifference,
      0 < observerDistance tau pair.1.1 pair.1.2 ∧
        observerDistance tau pair.1.1 pair.1.2 < ⊤ ->
      ∃ (f : I -> Real) (n : Int),
        edgeAdmissible tau f ∧
          f pair.1.1 ≠ f pair.1.2 ∧
          pair.1.2 = (tau ^ n) pair.1.1 ∧
          observerDistance tau pair.1.1 pair.1.2 <=
            (n.natAbs : ENNReal)) := by
  dsimp only
  have classification :
      ∀ pair : {pair : I × I //
          ∃ self : SelfReadout,
            selfReadout self pair.1 ≠ selfReadout self pair.2},
        (observerDistance tau pair.1.1 pair.1.2 = 0 ∧
            ∀ f : I -> Real,
              edgeAdmissible tau f -> f pair.1.1 = f pair.1.2) ∨
          (0 < observerDistance tau pair.1.1 pair.1.2 ∧
            observerDistance tau pair.1.1 pair.1.2 < ⊤) ∨
          (observerDistance tau pair.1.1 pair.1.2 = ⊤ ∧
            ∀ n : Int, pair.1.2 ≠ (tau ^ n) pair.1.1) := by
    intro pair
    by_cases distanceZero : observerDistance tau pair.1.1 pair.1.2 = 0
    · exact Or.inl
        ⟨distanceZero,
          (observer_distance_eq_zero_iff_readout_agreement
            tau pair.1.1 pair.1.2).1 distanceZero⟩
    · rcases eq_top_or_lt_top (observerDistance tau pair.1.1 pair.1.2) with
        distanceTop | distanceFinite
      · exact Or.inr (Or.inr
          ⟨distanceTop,
            top_distance_has_no_signed_path
              tau pair.1.1 pair.1.2 distanceTop⟩)
      · exact Or.inr (Or.inl
          ⟨bot_lt_iff_ne_bot.mpr distanceZero, distanceFinite⟩)
  refine ⟨classification, ?_, ?_⟩
  · intro allHidden pair
    rintro ⟨f, n, admissible, separates, path⟩
    rcases allHidden pair with distanceZero | distanceTop
    · exact separates
        ((observer_distance_eq_zero_iff_readout_agreement
          tau pair.1.1 pair.1.2).1 distanceZero f admissible)
    · exact top_distance_has_no_signed_path
        tau pair.1.1 pair.1.2 distanceTop n path
  · intro pair finiteDistance
    exact finite_distance_has_bookkeeping_witness
      tau pair.1.1 pair.1.2 finiteDistance.1 finiteDistance.2

#print axioms self_description_distance_classification

end D5.S3.ContinuousObservables.SelfDescriptionDistanceClassification
