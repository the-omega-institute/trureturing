/- GID: D5/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels
   generality: G
   mirror-B: D5/B/S3/Observer/MetricGeometryLaws/DualSupremumPseudometricKernels
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Evaluation-row and evaluation-column suprema are exact pseudometrics. -/

import Mathlib.Topology.MetricSpace.Basic

/- Library-search audit trail (2026-08-28):
   * Body-shape searches for a D5 definition of either `sup_p dist (e x p)
     (e y p)` or its transposed protocol form were misses. The two definitions
     below therefore construct the source's named canonical objects directly.
   * Nearby D5 pseudometric results concern trajectories, finite horizons, or
     weighted discrete readouts and do not state both static evaluation suprema
     with both row and column zero kernels.
   * Pinned Mathlib's bounded-continuous-map `dist_eq_iSup` is adjacent but
     imposes a different function carrier. The proof instead applies `le_ciSup`,
     `ciSup_le`, `dist_triangle`, and `dist_eq_zero` directly.
   * No nonemptiness premise is added: `iSup_of_empty'` and `Real.sSup_empty`
     handle empty state or protocol carriers exactly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.MetricGeometryLaws.DualSupremumPseudometricKernels

/-- The largest law distance between two states over all protocols. -/
noncomputable def stateObservationDistance
    {State Protocol Law : Type*} [MetricSpace Law]
    (evaluation : State -> Protocol -> Law) (first second : State) : Real :=
  ⨆ protocol, dist (evaluation first protocol) (evaluation second protocol)

/-- The largest law distance between two protocols over all states. -/
noncomputable def protocolResponseDistance
    {State Protocol Law : Type*} [MetricSpace Law]
    (evaluation : State -> Protocol -> Law) (first second : Protocol) : Real :=
  ⨆ state, dist (evaluation state first) (evaluation state second)

private theorem distance_terms_bddAbove
    {Point Index Law : Type*} [MetricSpace Law]
    (readout : Point -> Index -> Law)
    (bounded : forall a b : Law, dist a b <= 1)
    (first second : Point) :
    BddAbove (Set.range fun index =>
      dist (readout first index) (readout second index)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨index, rfl⟩
  exact bounded _ _

private theorem bounded_supremum_distance_laws
    {Point Index Law : Type*} [MetricSpace Law]
    (readout : Point -> Index -> Law)
    (bounded : forall a b : Law, dist a b <= 1) :
    forall first second third : Point,
      0 <= (⨆ index, dist (readout first index) (readout second index)) /\
      (⨆ index, dist (readout first index) (readout first index)) = 0 /\
      (⨆ index, dist (readout first index) (readout second index)) =
        ⨆ index, dist (readout second index) (readout first index) /\
      (⨆ index, dist (readout first index) (readout second index)) <=
        (⨆ index, dist (readout first index) (readout third index)) +
          ⨆ index, dist (readout third index) (readout second index) := by
  intro first second third
  cases isEmpty_or_nonempty Index with
  | inl empty =>
      letI : IsEmpty Index := empty
      simp [iSup_of_empty', Real.sSup_empty]
  | inr nonempty =>
      letI : Nonempty Index := nonempty
      have nonnegative :
          0 <= (⨆ index, dist (readout first index) (readout second index)) :=
        dist_nonneg.trans
          (le_ciSup (distance_terms_bddAbove readout bounded first second)
            (Classical.choice nonempty))
      have diagonal :
          (⨆ index, dist (readout first index) (readout first index)) = 0 := by
        simp
      have symmetric :
          (⨆ index, dist (readout first index) (readout second index)) =
            ⨆ index, dist (readout second index) (readout first index) := by
        congr 1
        funext index
        exact dist_comm _ _
      have triangle :
          (⨆ index, dist (readout first index) (readout second index)) <=
            (⨆ index, dist (readout first index) (readout third index)) +
              ⨆ index, dist (readout third index) (readout second index) := by
        apply ciSup_le
        intro index
        calc
          dist (readout first index) (readout second index) <=
              dist (readout first index) (readout third index) +
                dist (readout third index) (readout second index) :=
            dist_triangle _ _ _
          _ <= (⨆ other, dist (readout first other) (readout third other)) +
                ⨆ other, dist (readout third other) (readout second other) :=
            add_le_add
              (le_ciSup (distance_terms_bddAbove readout bounded first third) index)
              (le_ciSup (distance_terms_bddAbove readout bounded third second) index)
      exact ⟨nonnegative, diagonal, symmetric, triangle⟩

private theorem bounded_supremum_distance_zero_iff
    {Point Index Law : Type*} [MetricSpace Law]
    (readout : Point -> Index -> Law)
    (bounded : forall a b : Law, dist a b <= 1)
    (first second : Point) :
    (⨆ index, dist (readout first index) (readout second index)) = 0 <->
      (fun index => readout first index) = fun index => readout second index := by
  constructor
  · intro zeroDistance
    funext index
    letI : Nonempty Index := ⟨index⟩
    apply dist_eq_zero.mp
    apply le_antisymm
    · exact (le_ciSup
        (distance_terms_bddAbove readout bounded first second) index).trans_eq
          zeroDistance
    · exact dist_nonneg
  · intro equalReadouts
    cases isEmpty_or_nonempty Index with
    | inl empty =>
        letI : IsEmpty Index := empty
        simp [iSup_of_empty', Real.sSup_empty]
    | inr nonempty =>
        letI : Nonempty Index := nonempty
        simp only [congrFun equalReadouts, dist_self]
        exact ciSup_const

/-- Both evaluation suprema obey the pseudometric laws, and distance zero is
exactly equality of the corresponding evaluation rows or columns. Hence the
two exact extensional quotients use precisely these zero-distance relations. -/
theorem dual_supremum_pseudometric_kernels
    {State Protocol Law : Type*} [MetricSpace Law]
    (evaluation : State -> Protocol -> Law)
    (bounded : forall a b : Law, dist a b <= 1) :
    (forall x y z : State,
      0 <= stateObservationDistance evaluation x y /\
      stateObservationDistance evaluation x x = 0 /\
      stateObservationDistance evaluation x y =
        stateObservationDistance evaluation y x /\
      stateObservationDistance evaluation x y <=
        stateObservationDistance evaluation x z +
          stateObservationDistance evaluation z y) /\
    (forall p q r : Protocol,
      0 <= protocolResponseDistance evaluation p q /\
      protocolResponseDistance evaluation p p = 0 /\
      protocolResponseDistance evaluation p q =
        protocolResponseDistance evaluation q p /\
      protocolResponseDistance evaluation p q <=
        protocolResponseDistance evaluation p r +
          protocolResponseDistance evaluation r q) /\
    (forall x y : State,
      stateObservationDistance evaluation x y = 0 <->
        Setoid.ker (fun state => evaluation state) x y) /\
    (forall p q : Protocol,
      protocolResponseDistance evaluation p q = 0 <->
        Setoid.ker (fun protocol state => evaluation state protocol) p q) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [stateObservationDistance] using
      bounded_supremum_distance_laws evaluation bounded
  · simpa only [protocolResponseDistance] using
      bounded_supremum_distance_laws (fun protocol state => evaluation state protocol) bounded
  · intro x y
    simpa only [stateObservationDistance, Setoid.ker_def] using
      bounded_supremum_distance_zero_iff evaluation bounded x y
  · intro p q
    simpa only [protocolResponseDistance, Setoid.ker_def] using
      bounded_supremum_distance_zero_iff
        (fun protocol state => evaluation state protocol) bounded p q

#print axioms dual_supremum_pseudometric_kernels

end D5.S3.Observer.MetricGeometryLaws.DualSupremumPseudometricKernels
