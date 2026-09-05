/- GID: D5/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective orbit windows are jointly sufficient and coarsest by factorization. -/

import D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/- Library-search audit trail (2026-09-04):
   * Repository searches found the exact existing owners `Refines`, `orbitTarget`,
     `finiteWindow`, and `multi_target_minimal_sufficiency`; all are imported and
     reused. The older frozen finite-window theorem adds `[Nonempty X]` because it
     maps into target images from the raw window carrier, whereas source Definition
     1.2 restricts both interfaces to their realized images.
   * The second clause stays on the same effective-image carrier as the first:
     applying `multi_target_minimal_sufficiency` to canonical target readouts
     gives a dependent-product factor through `canonicalTargetReadout r`, and the
     final factor into the window image is constructed on `TargetImage r`.
   * Pinned Mathlib searches found `Function.FactorsThrough`,
     `Function.factorsThrough_iff`, and `Function.iterate`. Loogle returned adjacent
     factor-through declarations but no result more exact than the repository
     dependent-product theorem. LeanSearch returned HTTP 405, GitHub code search
     returned HTTP 401, and installed non-Mathlib packages had no relevant hit. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.FutureWindows.FiniteWindowMinimalSufficiency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
open D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- The realized finite orbit window is sufficient for every observation through
time `n`. Moreover, every interface whose realized image is sufficient for all
those observations determines the realized window, so the window is coarsest in
the source's factor-through order. This is source Theorem 3.2, using the
effective-image convention of Definition 1.2 for both clauses. -/
theorem finite_future_window_minimal_sufficiency
    {X O : Type _} (q : Concept X O) (F : X -> X) (n : Nat) :
    (forall i : Fin (n + 1),
      Refines
        (canonicalTargetReadout (orbitTarget q F i.1))
        (canonicalTargetReadout (finiteWindow q F n))) /\
    (forall {C : Type _} (r : Concept X C),
      (forall i : Fin (n + 1),
        Refines
          (canonicalTargetReadout (orbitTarget q F i.1))
          (canonicalTargetReadout r)) ->
      Refines
        (canonicalTargetReadout (finiteWindow q F n))
        (canonicalTargetReadout r)) := by
  let targets : Fin (n + 1) -> Concept X O :=
    fun i => orbitTarget q F i.1
  have projections : forall i, Refines (targets i) (finiteWindow q F n) := by
    simpa only [targets, finiteWindow] using
      (multi_target_minimal_sufficiency targets (finiteWindow q F n)).2.1
  constructor
  · intro i
    obtain ⟨rawFactor, rawFactorization⟩ := projections i
    let imageFactor : TargetImage (finiteWindow q F n) ->
        TargetImage (orbitTarget q F i.1) := fun windowValue =>
      ⟨rawFactor windowValue.1, by
        obtain ⟨state, represents⟩ := windowValue.2
        refine ⟨state, ?_⟩
        calc
          orbitTarget q F i.1 state = rawFactor (finiteWindow q F n state) :=
            congrFun rawFactorization state
          _ = rawFactor windowValue.1 := congrArg rawFactor represents⟩
    refine ⟨imageFactor, ?_⟩
    funext state
    apply Subtype.ext
    exact congrFun rawFactorization state
  · intro C r sufficient
    let effectiveTargets : forall i : Fin (n + 1),
        Concept X (TargetImage (targets i)) :=
      fun i => canonicalTargetReadout (targets i)
    obtain ⟨factor, factorization⟩ :=
      (multi_target_minimal_sufficiency effectiveTargets
        (canonicalTargetReadout r)).2.2 (canonicalTargetReadout r) sufficient
    let imageFactor : TargetImage r -> TargetImage (finiteWindow q F n) :=
      fun rValue =>
        ⟨fun i => (factor rValue i).1, by
          obtain ⟨state, represents⟩ := rValue.2
          have represented : canonicalTargetReadout r state = rValue := by
            apply Subtype.ext
            exact represents
          refine ⟨state, ?_⟩
          funext i
          have coordinate := congrFun (congrFun factorization state) i
          have representedCoordinate := congrArg (fun value => (value i).1)
            (congrArg factor represented)
          change finiteWindow q F n state i = (factor rValue i).1
          calc
            finiteWindow q F n state i = targets i state := rfl
            _ = (factor (canonicalTargetReadout r state) i).1 :=
              congrArg Subtype.val coordinate
            _ = (factor rValue i).1 := representedCoordinate⟩
    refine ⟨imageFactor, ?_⟩
    funext state
    apply Subtype.ext
    funext i
    have coordinate := congrFun (congrFun factorization state) i
    change finiteWindow q F n state i = (factor (canonicalTargetReadout r state) i).1
    calc
      finiteWindow q F n state i = targets i state := rfl
    _ = (factor (canonicalTargetReadout r state) i).1 :=
        congrArg Subtype.val coordinate

/- At `n = 1`, the second clause expands to the source's Theorem 3.1:
if `q = a after r` and `q after F = b after r`, the two-entry window's
realized image factors through the realized image of `r`. -/
example {X O C : Type} (q : Concept X O) (F : X -> X) (r : Concept X C)
    (a b : C -> O) (current : q = a ∘ r)
    (next : orbitTarget q F 1 = b ∘ r) :
    Refines
        (canonicalTargetReadout (finiteWindow q F 1))
        (canonicalTargetReadout r) /\
      finiteWindow q F 1 =
        (fun value i => Fin.cases (a value) (fun _ => b value) i) ∘ r := by
  constructor
  · apply (finite_future_window_minimal_sufficiency q F 1).2 r
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Refines (canonicalTargetReadout q) (canonicalTargetReadout r)
      refine ⟨fun value => ⟨a value.1, ?_⟩, ?_⟩
      · obtain ⟨state, represents⟩ := value.2
        refine ⟨state, ?_⟩
        calc
          q state = a (r state) := by
            have h := congrFun current state
            change q state = a (r state) at h
            exact h
          _ = a value.1 := congrArg a represents
      · funext state
        apply Subtype.ext
        exact congrFun current state
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change Refines
        (canonicalTargetReadout (orbitTarget q F 1))
        (canonicalTargetReadout r)
      refine ⟨fun value => ⟨b value.1, ?_⟩, ?_⟩
      · obtain ⟨state, represents⟩ := value.2
        refine ⟨state, ?_⟩
        calc
          orbitTarget q F 1 state = b (r state) := by
            have h := congrFun next state
            change orbitTarget q F 1 state = b (r state) at h
            exact h
          _ = b value.1 := congrArg b represents
      · funext state
        apply Subtype.ext
        exact congrFun next state
  · funext state i
    refine Fin.cases ?_ (fun j => ?_) i
    · change q state = a (r state)
      exact congrFun current state
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change orbitTarget q F 1 state = b (r state)
      exact congrFun next state

/- The source's effective-image carrier admits the Empty/Unit edge case even
when the raw codomain factor does not exist: the only interface
`r : Empty -> Unit` is sufficient through its empty realized image, while
the old raw universal premise would require a function `Unit -> Empty`. -/
example :
    let q : Concept Empty Empty := fun x => Empty.elim x
    let r : Concept Empty Unit := fun x => Empty.elim x
    (forall i : Fin (0 + 1),
      Refines
        (canonicalTargetReadout (orbitTarget q id i.1))
        (canonicalTargetReadout r)) /\
    (Not (forall i : Fin (0 + 1), Refines (orbitTarget q id i.1) r)) := by
  classical
  dsimp
  constructor
  · intro i
    refine ⟨fun value => ?_, ?_⟩
    · exact Empty.elim (Classical.choose value.2)
    · funext state
      exact Empty.elim state
  · intro rawPremise
    rcases rawPremise 0 with ⟨factor, _⟩
    exact Empty.elim (factor ())

/- Concrete witnesses exercise both clauses at horizons one and two. -/
example :
    (forall i : Fin 2,
      Refines
        (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 1))) /\
    (forall {C : Type} (r : Concept Bool C),
      (forall i : Fin 2,
        Refines
          (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
          (canonicalTargetReadout r)) ->
      Refines
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 1))
        (canonicalTargetReadout r)) :=
  finite_future_window_minimal_sufficiency (id : Bool -> Bool) Bool.not 1

example :
    (forall i : Fin 3,
      Refines
        (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 2))) /\
    (forall {C : Type} (r : Concept Bool C),
      (forall i : Fin 3,
        Refines
          (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
          (canonicalTargetReadout r)) ->
      Refines
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 2))
        (canonicalTargetReadout r)) :=
  finite_future_window_minimal_sufficiency (id : Bool -> Bool) Bool.not 2

/- The concrete horizon-one carrier is not collapsed: its time-zero coordinate
already separates the two Boolean states. -/
example :
    Not (finiteWindow (id : Bool -> Bool) Bool.not 1 false =
      finiteWindow (id : Bool -> Bool) Bool.not 1 true) := by
  intro sameWindow
  have atZero := congrFun sameWindow (0 : Fin 2)
  change false = true at atZero
  exact Bool.noConfusion atZero

/- Reverse probe for source Definition 1.2: the public A1 clause produces an
explicit factor between the two realized images. -/
example {X O : Type} (q : Concept X O) (F : X -> X) (n : Nat)
    (i : Fin (n + 1)) :
    exists factor : TargetImage (finiteWindow q F n) ->
        TargetImage (orbitTarget q F i.1),
      canonicalTargetReadout (orbitTarget q F i.1) =
        factor ∘ canonicalTargetReadout (finiteWindow q F n) := by
  exact (finite_future_window_minimal_sufficiency.{0, 0, 0} q F n).1 i

#print axioms finite_future_window_minimal_sufficiency

end D5.S3.ConceptDynamics.FutureWindows.FiniteWindowMinimalSufficiency
