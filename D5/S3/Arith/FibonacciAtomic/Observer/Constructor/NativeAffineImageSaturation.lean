/- GID: D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeAffineImageSaturation
   generality: G
   mirror-B: none(waiver:unbounded-symbolic-proof)
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Original native image saturation at the exact guarded affine parameter map. -/

import D5.S3.Arith.FibonacciAtomic.Observer.Constructor.NativeRootLinkNormalization
import D5.S0.Computability.PresburgerSyntax

/-! Finite symbolic terminals are indexed by affine expressions in the original
finite natural parameter tuple. Their natural ranks are derived from the
explicit nonnegativity guards, without independent terminal parameters. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation

open NativeCompletionPrefixLifting NativeGuardedFreeExtension
open NativeGuardedImageSaturation NativeRootLinkNormalization

/-- A purely syntactic original input. None of its fields asserts a semantic
normalization, extension, rationality or correctness property. -/
structure Input (n k m : Nat) where
  equations : System k m
  filters : List (Filter k m)
  indices : Fin k → PresburgerArithmetic.Affine
  guard : PresburgerArithmetic.Formula

def environment {n : Nat} (p : Fin n → Nat) : List Int :=
  List.ofFn fun i => Int.ofNat (p i)

/-- The original Presburger guard and the explicit guards for all affine
atomic indices, evaluated at the same original parameter tuple. -/
def Legal {n k m : Nat} (I : Input n k m) (p : Fin n → Nat) : Prop :=
  I.guard.holds (environment p) ∧ ∀ j, 0 ≤ (I.indices j).eval (environment p)

def ranks {n k m : Nat} (I : Input n k m) (p : Fin n → Nat) : Fin k → Nat :=
  fun j => ((I.indices j).eval (environment p)).toNat

/-- The source equations use the derived affine ranks, not additional freely
chosen natural parameters. The last token is the explicit Omega terminal. -/
def SourceSatisfies {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop := Satisfies I.equations (ranks I p) v

def SourcePasses {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (v : Fin m → CompletionTree) : Prop := Passes (ranks I p) v I.filters

def SourceInMode {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (mode : FreeMode I.equations (threshold I.filters)) (v : Fin m → CompletionTree) : Prop :=
  OriginalInMode I.equations (ranks I p) mode v

noncomputable def sourceCanonical {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (mode : FreeMode I.equations (threshold I.filters)) : Fin m → CompletionTree :=
  originalCanonical I.equations (ranks I p) I.filters mode

private theorem free_modes_partition {k m : Nat} (S : System k m) (p : Fin k → Nat)
    (s : Nat) (v : Fin m → CompletionTree) :
    ∃! mode : FreeMode S s, OriginalInMode S p mode v := by
  classical
  let w := mapValues p (normalForm S).project v
  let mode : FreeMode S s := fun i =>
    if h : ∃ j : Fin (s + 2), w i.val = CompletionHomogeneousFixedPoints.atomic j.val
    then some (Classical.choose h) else none
  have membership : OriginalInMode S p mode v := by
    intro i hi
    simp only [totalMode, dite_eq_left hi]
    change (match mode ⟨i, hi⟩ with
      | some j => w i = CompletionHomogeneousFixedPoints.atomic j.val
      | none => ∀ j, j ≤ s + 1 → w i ≠ CompletionHomogeneousFixedPoints.atomic j)
    by_cases h : ∃ j : Fin (s + 2), w i = CompletionHomogeneousFixedPoints.atomic j.val
    · simp only [mode, dite_eq_left h]
      exact Classical.choose_spec h
    · simp only [mode, dite_eq_right h]
      intro j hj eq
      exact (h ⟨⟨j, by omega⟩, eq⟩).elim
  refine ⟨mode, membership, ?_⟩
  intro other other_membership
  funext i
  have original := membership i.val i.property
  have candidate := other_membership i.val i.property
  simp only [totalMode, dite_eq_left i.property] at original candidate
  change (match mode i with
    | some j => w i.val = CompletionHomogeneousFixedPoints.atomic j.val
    | none => ∀ j, j ≤ s + 1 → w i.val ≠ CompletionHomogeneousFixedPoints.atomic j) at original
  change (match other i with
    | some j => w i.val = CompletionHomogeneousFixedPoints.atomic j.val
    | none => ∀ j, j ≤ s + 1 → w i.val ≠ CompletionHomogeneousFixedPoints.atomic j) at candidate
  cases ho : other i with
  | none =>
    cases hm : mode i with
    | none => rfl
    | some j =>
      simp only [ho] at candidate
      simp only [hm] at original
      exact (candidate j.val (by omega) original).elim
  | some j =>
    cases hm : mode i with
    | none =>
      simp only [ho] at candidate
      simp only [hm] at original
      exact (original j.val (by omega) candidate).elim
    | some l =>
      simp only [ho] at candidate
      simp only [hm] at original
      have same := CompletionPositiveDriftRegion.atomic_injective (candidate.symm.trans original)
      exact congrArg some (Fin.ext same)

/-- Finite-exception completeness at every fixed legal original parameter.
The exact affine map, unique free-mode partition and finite family of canonical
existence tests all refer to the same unrestricted original solution relation. -/
theorem affine_original_saturation {n k m : Nat} (I : Input n k m) (p : Fin n → Nat)
    (legal : Legal I p) (mode : FreeMode I.equations (threshold I.filters)) :
    (∀ j, (ranks I p j : Int) = (I.indices j).eval (environment p)) ∧
    (∀ v, ∃! md : FreeMode I.equations (threshold I.filters), SourceInMode I p md v) ∧
    SourceSatisfies I p (sourceCanonical I p mode) ∧
    SourceInMode I p mode (sourceCanonical I p mode) ∧
    ((∃ v, SourceSatisfies I p v ∧ SourceInMode I p mode v ∧ SourcePasses I p v) ↔
      SourcePasses I p (sourceCanonical I p mode)) ∧
    ((∃ v, SourceSatisfies I p v ∧ SourcePasses I p v) ↔
      ∃ md : FreeMode I.equations (threshold I.filters),
        SourcePasses I p (sourceCanonical I p md)) := by
  have by_mode := original_saturation I.equations (ranks I p) I.filters mode
  have partition := free_modes_partition I.equations (ranks I p) (threshold I.filters)
  refine ⟨?_, partition, by_mode.1, by_mode.2.1, by_mode.2.2, ?_⟩
  · intro j
    exact Int.toNat_of_nonneg (legal.2 j)
  · constructor
    · rintro ⟨v, sat, passes⟩
      obtain ⟨md, vm, _⟩ := partition v
      refine ⟨md, ?_⟩
      exact (original_saturation I.equations (ranks I p) I.filters md).2.2.mp
        ⟨v, sat, vm, passes⟩
    · rintro ⟨md, passes⟩
      exact ⟨sourceCanonical I p md,
        (original_saturation I.equations (ranks I p) I.filters md).1, passes⟩

end D5.S3.Arith.FibonacciAtomic.Observer.NativeAffineImageSaturation
