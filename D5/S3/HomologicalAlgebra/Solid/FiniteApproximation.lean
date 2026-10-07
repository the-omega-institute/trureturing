/- GID: D5/S3/HomologicalAlgebra/Solid/FiniteApproximation
   generality: G
   mirror-B: D5/B/S3/HomologicalAlgebra/Solid/FiniteApproximation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Unbounded solid derived construction with exact protected objects and all quasi-isomorphisms. -/

import Mathlib.Topology.Category.LightProfinite.AsLimit

/-!
Compatible finite-image retractions for every light profinite space, using
the actual pinned sequential finite presentation. The choices work also for
empty and finite spaces; no enumeration of the represented points by N is
asserted. These are the finite-approximation data needed for the concrete
generator retract in Rodriguez Camargo, Notes on Solid Geometry, Lemma 3.3.2.
New proofs, Apache-2.0.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory Limits LightProfinite
attribute [local instance] FintypeCat.botTopology FintypeCat.discreteTopology

namespace CWSolid

local instance (S : LightProfinite) (n : ℕ) : Finite (S.component n) :=
  inferInstanceAs (Finite (S.fintypeDiagram.obj ⟨n⟩))

local instance (S : LightProfinite) (n : ℕ) : DiscreteTopology (S.component n) := by
  change DiscreteTopology (S.fintypeDiagram.obj ⟨n⟩)
  infer_instance

/-- Actual sections of the finite quotient projection. -/
def finiteSectionType (S : LightProfinite) (n : ℕ) :=
  {a : S.component n → S // Function.RightInverse a (S.proj n)}

def initialFiniteSection (S : LightProfinite) : finiteSectionType S 0 :=
  ⟨fun b => (S.proj_surjective 0 b).choose,
    fun b => (S.proj_surjective 0 b).choose_spec⟩

/-- Extend the old representative in its unique new fiber, choosing arbitrary
representatives only for the other fibers. -/
def nextFiniteSection (S : LightProfinite) (n : ℕ)
    (a : finiteSectionType S n) : finiteSectionType S (n + 1) := by
  classical
  refine ⟨fun b => if S.proj (n + 1) (a.val (S.transitionMap n b)) = b
    then a.val (S.transitionMap n b) else (S.proj_surjective (n + 1) b).choose, ?_⟩
  intro b
  dsimp only
  split_ifs with h
  · exact h
  · exact (S.proj_surjective (n + 1) b).choose_spec

theorem nextFiniteSection_preserves (S : LightProfinite) (n : ℕ)
    (a : finiteSectionType S n) (b : S.component n) :
    (nextFiniteSection S n a).val (S.proj (n + 1) (a.val b)) = a.val b := by
  have h : S.transitionMap n (S.proj (n + 1) (a.val b)) = b :=
    (congrFun (S.proj_comp_transitionMap' n) (a.val b)).trans (a.property b)
  classical
  dsimp only [nextFiniteSection]
  rw [h, if_pos rfl]

def compatibleFiniteSection (S : LightProfinite) : (n : ℕ) → finiteSectionType S n
  | 0 => initialFiniteSection S
  | n + 1 => nextFiniteSection S n (compatibleFiniteSection S n)

theorem compatibleFiniteSection_proj (S : LightProfinite) (n : ℕ)
    (b : S.component n) :
    S.proj n ((compatibleFiniteSection S n).val b) = b :=
  (compatibleFiniteSection S n).property b

theorem compatibleFiniteSection_preserves (S : LightProfinite) (n : ℕ)
    (b : S.component n) :
    (compatibleFiniteSection S (n + 1)).val
      (S.proj (n + 1) ((compatibleFiniteSection S n).val b)) =
        (compatibleFiniteSection S n).val b :=
  nextFiniteSection_preserves S n (compatibleFiniteSection S n) b

/-- A genuine continuous finite-image retraction, not a function in a
discrete replacement of S. -/
def finiteApproximation (S : LightProfinite) (n : ℕ) : S ⟶ S :=
  ConcreteCategory.ofHom
    ⟨fun s => (compatibleFiniteSection S n).val (S.proj n s),
      continuous_of_discreteTopology.comp (S.proj n).hom.hom.continuous⟩

theorem finiteApproximation_proj (S : LightProfinite) (n : ℕ) :
    finiteApproximation S n ≫ S.proj n = S.proj n := by
  ext s
  change S.proj n ((compatibleFiniteSection S n).val (S.proj n s)) = S.proj n s
  exact compatibleFiniteSection_proj S n _

theorem finiteApproximation_projLE (S : LightProfinite) {m n : ℕ} (h : m ≤ n) :
    finiteApproximation S n ≫ S.proj m = S.proj m := by
  rw [← S.proj_comp_transitionMapLE h, ← Category.assoc, finiteApproximation_proj]

theorem finiteApproximation_idempotent (S : LightProfinite) (n : ℕ) :
    finiteApproximation S n ≫ finiteApproximation S n = finiteApproximation S n := by
  ext s
  change (compatibleFiniteSection S n).val
      (S.proj n ((compatibleFiniteSection S n).val (S.proj n s))) =
    (compatibleFiniteSection S n).val (S.proj n s)
  exact congrArg (compatibleFiniteSection S n).val (compatibleFiniteSection_proj S n _)

theorem finiteApproximation_succ_absorb (S : LightProfinite) (n : ℕ) :
    finiteApproximation S (n + 1) ≫ finiteApproximation S n = finiteApproximation S n := by
  ext s
  have h := ConcreteCategory.congr_hom
    (finiteApproximation_projLE S (Nat.le_succ n)) s
  change (compatibleFiniteSection S n).val
      (S.proj n (finiteApproximation S (n + 1) s)) =
    (compatibleFiniteSection S n).val (S.proj n s)
  change S.proj n (finiteApproximation S (n + 1) s) = S.proj n s at h
  exact congrArg (compatibleFiniteSection S n).val h

theorem finiteApproximation_succ_preserves (S : LightProfinite) (n : ℕ) :
    finiteApproximation S n ≫ finiteApproximation S (n + 1) = finiteApproximation S n := by
  ext s
  change (compatibleFiniteSection S (n + 1)).val
      (S.proj (n + 1) ((compatibleFiniteSection S n).val (S.proj n s))) =
    (compatibleFiniteSection S n).val (S.proj n s)
  exact compatibleFiniteSection_preserves S n _

theorem finiteApproximation_range_finite (S : LightProfinite) (n : ℕ) :
    (Set.range (finiteApproximation S n)).Finite := by
  apply Set.Finite.subset (Set.finite_range (compatibleFiniteSection S n).val)
  rintro _ ⟨s, rfl⟩
  refine ⟨S.proj n s, ?_⟩
  change (compatibleFiniteSection S n).val (S.proj n s) =
    (compatibleFiniteSection S n).val (S.proj n s)
  rfl

theorem finiteApproximation_ranges_monotone (S : LightProfinite) :
    Monotone (fun n => Set.range (finiteApproximation S n)) := by
  have hstep (n : ℕ) : Set.range (finiteApproximation S n) ⊆
      Set.range (finiteApproximation S (n + 1)) := by
    intro x hx
    rcases hx with ⟨s, rfl⟩
    refine ⟨finiteApproximation S n s, ?_⟩
    change finiteApproximation S (n + 1) (finiteApproximation S n s) =
      finiteApproximation S n s
    have h := ConcreteCategory.congr_hom (finiteApproximation_succ_preserves S n) s
    change finiteApproximation S (n + 1) (finiteApproximation S n s) =
      finiteApproximation S n s at h
    exact h
  exact monotone_nat_of_le_succ hstep

end CWSolid
