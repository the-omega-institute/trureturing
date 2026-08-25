/- GID: D5/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Sufficiency/FiniteWindowMinimalSufficiency
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The orbit window through time n is sufficient for every observed iterate and is coarsest when Refines means the coarse readout factors through the fine one; [Nonempty X] is necessary because X = Empty and O = Unit leaves an inhabited window carrier but an empty canonical target image, while n = 0 and singleton outputs need no further assumptions, and semiconjugate descents compose. -/

import Mathlib.Logic.Function.Conjugate
import Mathlib.Logic.Function.Iterate
import D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
import D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/- Library-search audit trail (2026-08-24):
   * `rg -n -F 'finite_window_minimal_sufficiency' D5 Golden/Frozen/accepted`
     and the corresponding search for `descent_composes` returned no hits.
   * Semantic repository searches found the public general theorem
     `MultiTargetMinimalSufficiency.multi_target_minimal_sufficiency`, which is
     specialized below to the orbit targets, and no private finite-window result.
   * The three existing modules in the target directory were read by digest;
     none treats finite orbit windows. `UniversalSufficiencyFactorization` supplies
     the required equivalence between canonical sufficiency and fiber constancy.
   * Pinned Mathlib contains the exact composition theorem
     `Function.Semiconj.trans`; `descent_composes` reuses it directly. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency

open D5.S3.ConceptDynamics.ConceptFiberDecomposition
open D5.S3.ConceptDynamics.ConceptJoinUniversal
open D5.S3.ConceptDynamics.Refinement.MultiTargetMinimalSufficiency
open D5.S3.ConceptDynamics.Sufficiency.UniversalSufficiencyFactorization

/-- The target observed after exactly `i` applications of the update. -/
def orbitTarget {X O : Type _} (q : Concept X O) (F : X -> X) (i : Nat) :
    Concept X O :=
  fun x => q (F^[i] x)

/-- The finite-window interface records the observations from time zero through time `n`. -/
def finiteWindow {X O : Type _} (q : Concept X O) (F : X -> X) (n : Nat) :
    Concept X (Fin (n + 1) -> O) :=
  jointTarget (fun i : Fin (n + 1) => orbitTarget q F i.1)

/-- `q` semiconjugates `F` to `Fbar`: one updated readout is determined by `Fbar`. -/
def Semiconjugates {X B : Type _} (q : X -> B) (F : X -> X) (Fbar : B -> B) : Prop :=
  forall x, q (F x) = Fbar (q x)

/-- Semiconjugate descents compose without finiteness or nonemptiness assumptions. -/
theorem descent_composes {X B C : Type _} (F : X -> X) (Fbar : B -> B)
    (Ftilde : C -> C) (q : X -> B) (r : B -> C)
    (hq : Semiconjugates q F Fbar) (hr : Semiconjugates r Fbar Ftilde) :
    Semiconjugates (r ∘ q) F Ftilde := by
  exact Function.Semiconj.trans hq hr

/-- The orbit window is sufficient for every target through time `n`, and every
simultaneously sufficient interface refines it. Thus it is coarsest in the convention
`Refines coarse fine` when the coarse readout factors through the fine readout. -/
theorem finite_window_minimal_sufficiency {X O : Type _} [Nonempty X]
    (q : Concept X O) (F : X -> X) (n : Nat) :
    (forall i : Fin (n + 1),
      Refines (canonicalTargetReadout (orbitTarget q F i.1)) (finiteWindow q F n)) /\
    (forall {C : Type _} (p : Concept X C),
      (forall i : Fin (n + 1),
        Refines (canonicalTargetReadout (orbitTarget q F i.1)) p) ->
      Refines (finiteWindow q F n) p) := by
  let targets : Fin (n + 1) -> Concept X O :=
    fun i => orbitTarget q F i.1
  have projections : forall i, Refines (targets i) (finiteWindow q F n) := by
    simpa only [targets, finiteWindow] using
      (multi_target_minimal_sufficiency targets (finiteWindow q F n)).2.1
  constructor
  · intro i
    rcases projections i with ⟨factor, hfactor⟩
    have fiberConstant : forall ⦃x y : X⦄,
        finiteWindow q F n x = finiteWindow q F n y ->
          orbitTarget q F i.1 x = orbitTarget q F i.1 y := by
      intro x y hxy
      calc
        orbitTarget q F i.1 x = factor (finiteWindow q F n x) :=
          congrFun hfactor x
        _ = factor (finiteWindow q F n y) := congrArg factor hxy
        _ = orbitTarget q F i.1 y := (congrFun hfactor y).symm
    have universal :=
      universal_sufficiency_factorization
        (finiteWindow q F n) (orbitTarget q F i.1)
    exact universal.1.mpr (universal.2.mpr fiberConstant)
  · intro C p sufficient
    have rawSufficient : forall i, Refines (targets i) p := by
      intro i
      rcases sufficient i with ⟨factor, hfactor⟩
      refine ⟨Subtype.val ∘ factor, ?_⟩
      funext x
      have hpoint := congrArg Subtype.val (congrFun hfactor x)
      unfold Function.comp at hpoint ⊢
      simpa only [targets, canonicalTargetReadout] using hpoint
    simpa only [targets, finiteWindow] using
      (multi_target_minimal_sufficiency targets p).1.mp rawSufficient

example :
    forall i : Fin 2,
      Refines
        (canonicalTargetReadout (orbitTarget (fun b : Bool => b) id i.1))
        (finiteWindow (fun b : Bool => b) id 1) := by
  exact
    (finite_window_minimal_sufficiency.{0, 0, 0}
      (fun b : Bool => b) id 1).1

#print axioms descent_composes
#print axioms finite_window_minimal_sufficiency

end D5.S3.ConceptDynamics.Sufficiency.FiniteWindowMinimalSufficiency
