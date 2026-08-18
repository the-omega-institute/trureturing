/- GID: D5/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/InverseLimits/CompletionIsomorphismCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The completion map is an equivalence exactly under separation and unique realization. -/

import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Nat.Order.Lemmas
import Mathlib.Order.Defs.PartialOrder

/- Library-search audit trail (2026-08-18):
   * Exact pinned-Mathlib hit `Equiv.ofBijective` packages a proved bijection as
     an equivalence; it is imported and applied below.
   * Repository search found `completion_criterion`, which concerns a kernel
     quotient and realizability but does not state joint separation of the
     candidate object. Finite itinerary results are special instances.
   * Repository and pinned-Mathlib searches found no theorem packaging the
     canonical compatible-family map with both clauses of this criterion.
   * `loogle` and `leansearch` executables are absent from PATH. -/

namespace D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v w

/-- A type-valued inverse-stage system, built from restriction channels and
their identity and composition laws. -/
structure InverseStageSystem (I : Type u) [Preorder I] where
  Stage : I -> Type v
  restrict : {i j : I} -> i <= j -> Stage j -> Stage i
  restrict_refl : forall (i : I) (value : Stage i),
    restrict (le_refl i) value = value
  restrict_trans : forall {i j k : I} (hij : i <= j) (hjk : j <= k)
      (value : Stage k),
    restrict hij (restrict hjk value) = restrict (le_trans hij hjk) value

/-- A stage family whose coordinates agree with every restriction channel. -/
structure CompatibleStageFamily {I : Type u} [Preorder I]
    (system : InverseStageSystem I) where
  stage : (i : I) -> system.Stage i
  compatible : forall {i j : I} (h : i <= j),
    system.restrict h (stage j) = stage i

@[ext]
theorem CompatibleStageFamily.ext {I : Type u} [Preorder I]
    {system : InverseStageSystem I}
    (first second : CompatibleStageFamily system)
    (hstage : first.stage = second.stage) : first = second := by
  cases first
  cases second
  cases hstage
  rfl

/-- The canonical map induced by a compatible family of stage probes. -/
def completionMap {I : Type u} [Preorder I]
    {X : Type w} (system : InverseStageSystem I)
    (projection : (i : I) -> X -> system.Stage i)
    (hprojection : forall {i j : I} (h : i <= j) (x : X),
      system.restrict h (projection j x) = projection i x) :
    X -> CompatibleStageFamily system :=
  fun x =>
    { stage := fun i => projection i x
      compatible := fun h => hprojection h x }

/-- The canonical completion map is an equivalence exactly when the probes
jointly separate global points and every compatible stage family has a unique
global realization. This is the type-level form of the isomorphism criterion. -/
theorem completion_map_equiv_iff
    {I : Type u} [Preorder I] {X : Type w}
    (system : InverseStageSystem I)
    (projection : (i : I) -> X -> system.Stage i)
    (hprojection : forall {i j : I} (h : i <= j) (x : X),
      system.restrict h (projection j x) = projection i x) :
    (exists equivalence : X ≃ CompatibleStageFamily system,
      equivalence.toFun = completionMap system projection hprojection) <->
    (forall x y : X,
      (forall i : I, projection i x = projection i y) -> x = y) /\
    (forall family : CompatibleStageFamily system,
      ∃! x : X, forall i : I, projection i x = family.stage i) := by
  constructor
  · rintro ⟨equivalence, hequivalence⟩
    constructor
    · intro x y hcoordinates
      apply equivalence.injective
      change equivalence.toFun x = equivalence.toFun y
      rw [hequivalence]
      apply CompatibleStageFamily.ext
      funext i
      exact hcoordinates i
    · intro family
      refine ⟨equivalence.symm family, ?_, ?_⟩
      · intro i
        have hfamily :
            completionMap system projection hprojection
                (equivalence.symm family) = family := by
          rw [← hequivalence]
          exact equivalence.apply_symm_apply family
        exact congrArg (fun coordinates => coordinates.stage i) hfamily
      · intro y hy
        apply equivalence.injective
        have hyfamily :
            completionMap system projection hprojection y = family := by
          apply CompatibleStageFamily.ext
          funext i
          exact hy i
        calc
          equivalence y = completionMap system projection hprojection y :=
            congrFun hequivalence y
          _ = family := hyfamily
          _ = equivalence (equivalence.symm family) :=
            (equivalence.apply_symm_apply family).symm
  · rintro ⟨hseparate, hrealize⟩
    have hbijective :
        Function.Bijective (completionMap system projection hprojection) := by
      constructor
      · intro x y hequal
        apply hseparate x y
        intro i
        exact congrArg (fun coordinates => coordinates.stage i) hequal
      · intro family
        rcases hrealize family with ⟨x, hx, _⟩
        refine ⟨x, ?_⟩
        apply CompatibleStageFamily.ext
        funext i
        exact hx i
    refine ⟨Equiv.ofBijective
      (completionMap system projection hprojection) hbijective, ?_⟩
    rfl

/-- The compatible-family domain is inhabited for a concrete inverse system. -/
example :
    let system : InverseStageSystem Nat :=
      { Stage := fun _ => Unit
        restrict := fun _ value => value
        restrict_refl := by intros; rfl
        restrict_trans := by intros; rfl }
    Nonempty (CompatibleStageFamily system) := by
  dsimp
  exact ⟨
    { stage := fun _ => ()
      compatible := by intros; rfl }⟩

/-- The separation and unique-realization hypotheses have a concrete model. -/
example :
    let system : InverseStageSystem Nat :=
      { Stage := fun _ => Unit
        restrict := fun _ value => value
        restrict_refl := by intros; rfl
        restrict_trans := by intros; rfl }
    let projection : (i : Nat) -> Unit -> system.Stage i :=
      fun _ value => value
    exists _ : forall {i j : Nat} (h : i <= j) (x : Unit),
        system.restrict h (projection j x) = projection i x,
      (forall x y : Unit,
        (forall i : Nat, projection i x = projection i y) -> x = y) /\
      (forall family : CompatibleStageFamily system,
        ∃! x : Unit,
          forall i : Nat, projection i x = family.stage i) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intros
    rfl
  · intro x y _
    exact Subsingleton.elim x y
  · intro family
    refine ⟨(), ?_, ?_⟩
    · intro i
      exact Subsingleton.elim _ _
    · intro x _
      exact Subsingleton.elim x ()

#print axioms completion_map_equiv_iff

end D5.S3.ObserverMemory.InverseLimits.CompletionIsomorphismCriterion
