/- GID: D5/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/FutureWindows/FiniteWindowMinimalSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Effective orbit windows are jointly sufficient and coarsest by factorization. -/

import D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

/- Library-search audit trail (2026-09-03):
   * Repository searches found the exact existing owners `Refines`, `orbitTarget`,
     `finiteWindow`, and `multi_target_minimal_sufficiency`; all are imported and
     reused. The older frozen finite-window theorem adds `[Nonempty X]` because it
     maps into target images from the raw window carrier, whereas source Definition
     1.2 restricts both interfaces to their realized images.
   * The effective-image bridge
     `realized_image_unique_factorization_iff_reverse_kernel` was inspected, but
     its state and both coordinate types share one universe. Restricting the source
     theorem to that universe would be unsourced, so the imported raw projection is
     restricted to the realized window image directly below.
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
time `n`. Moreover, any interface through which all those observations factor also
determines the whole window, so the window is coarsest in the source's factor-through
order. This is source Theorem 3.2, using the effective-image convention of Definition
1.2 for sufficiency and the explicit universal property of Theorem 3.1 for coarseness. -/
theorem finite_future_window_minimal_sufficiency
    {X O : Type _} (q : Concept X O) (F : X -> X) (n : Nat) :
    (forall i : Fin (n + 1),
      Refines
        (canonicalTargetReadout (orbitTarget q F i.1))
        (canonicalTargetReadout (finiteWindow q F n))) /\
    (forall {C : Type _} (r : Concept X C),
      (forall i : Fin (n + 1), Refines (orbitTarget q F i.1) r) ->
      Refines (finiteWindow q F n) r) := by
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
    simpa only [targets, finiteWindow] using
      (multi_target_minimal_sufficiency targets r).2.2 r sufficient

/- At `n = 1`, the second clause expands to the source's Theorem 3.1:
if `q = a after r` and `q after F = b after r`, the two-entry window factors
through `r` (the factor is the dependent-product form of `(a, b)`). -/
example {X O C : Type} (q : Concept X O) (F : X -> X) (r : Concept X C)
    (a b : C -> O) (current : q = a ∘ r)
    (next : orbitTarget q F 1 = b ∘ r) :
    Refines (finiteWindow q F 1) r /\
      finiteWindow q F 1 =
        (fun value i => Fin.cases (a value) (fun _ => b value) i) ∘ r := by
  constructor
  · apply (finite_future_window_minimal_sufficiency q F 1).2 r
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change Refines q r
      exact ⟨a, current⟩
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change Refines (orbitTarget q F 1) r
      exact ⟨b, next⟩
  · funext state i
    refine Fin.cases ?_ (fun j => ?_) i
    · change q state = a (r state)
      exact congrFun current state
    · have hj : j = 0 := Subsingleton.elim _ _
      subst j
      change orbitTarget q F 1 state = b (r state)
      exact congrFun next state

/- Concrete witnesses exercise both clauses at horizons one and two. -/
example :
    (forall i : Fin 2,
      Refines
        (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 1))) /\
    (forall {C : Type} (r : Concept Bool C),
      (forall i : Fin 2, Refines (orbitTarget (id : Bool -> Bool) Bool.not i.1) r) ->
      Refines (finiteWindow (id : Bool -> Bool) Bool.not 1) r) :=
  finite_future_window_minimal_sufficiency (id : Bool -> Bool) Bool.not 1

example :
    (forall i : Fin 3,
      Refines
        (canonicalTargetReadout (orbitTarget (id : Bool -> Bool) Bool.not i.1))
        (canonicalTargetReadout (finiteWindow (id : Bool -> Bool) Bool.not 2))) /\
    (forall {C : Type} (r : Concept Bool C),
      (forall i : Fin 3, Refines (orbitTarget (id : Bool -> Bool) Bool.not i.1) r) ->
      Refines (finiteWindow (id : Bool -> Bool) Bool.not 2) r) :=
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
