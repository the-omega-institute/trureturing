/- GID: D5/S3/Observer/Completion/StructuralCompletionSignature
   generality: G
   mirror-B: D5/B/S3/Observer/Completion/StructuralCompletionSignature
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Completion points form a gauge-stable zero-defect set whose one orbit is a signature. -/

/- Library-search audit trail (2026-08-28):
   * Repository searches found genuine uses of `MulAction.orbitRel.Quotient` and
     `MulAction.IsPretransitive`, but no existing OACTC completion vocabulary.
   * Pinned Mathlib's `SubMulAction` is exactly a gauge-stable subset and is used below.
   * Pinned Mathlib's `MulAction.pretransitive_iff_unique_quotient_of_nonempty` exactly
     identifies a nonempty single orbit with a one-element orbit quotient and is reused below.
   * Pinned Mathlib's `Set.eq_singleton_iff_unique_mem` supplies the completion-constant clause.
   * Loogle confirmed both group-action hits. Reservoir and LeanSearch returned no third-party
     exact hit; authenticated GitHub search was unavailable. Full receipt: `/tmp/SEARCH-oe1.md`.
-/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.SubMulAction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Observer.Completion.StructuralCompletionSignature

universe u v w z

/-- The admissible parameters whose structural defect is the distinguished zero. -/
def completionPointSet {A : Type v} {D : Type w}
    (normalization : Set A) (defect : A -> D) (zeroD : D) : Set A :=
  {a | a ∈ normalization ∧ defect a = zeroD}

/-- Completion points equipped with the gauge action that preserves them. -/
def completionPoints {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD) :
    SubMulAction G A where
  carrier := completionPointSet normalization defect zeroD
  smul_mem' := gaugeStable

/-- Membership in the completion subaction is exactly normalized zero defect. -/
@[simp] theorem mem_completionPoints_iff
    {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD)
    (a : A) :
    a ∈ completionPoints normalization defect zeroD gaugeStable <->
      a ∈ normalization ∧ defect a = zeroD :=
  Iff.rfl

/-- The structural completion signature is the canonical quotient by gauge orbits. -/
abbrev CompletionSignature {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD) :=
  MulAction.orbitRel.Quotient G
    (completionPoints normalization defect zeroD gaugeStable)

/-- The naming condition for a structural completion signature: its completion carrier is
nonempty and the gauge action is transitive on it. -/
def HasStructuralCompletionSignature {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD) : Prop :=
  Nonempty (completionPoints normalization defect zeroD gaugeStable) ∧
    MulAction.IsPretransitive G
      (completionPoints normalization defect zeroD gaugeStable)

/-- After gauge fixing, `kappa` is a completion constant exactly when it remains and every
remaining numerical value equals it. -/
def IsCompletionConstant {R : Type z} (fixedValues : Set R) (kappa : R) : Prop :=
  kappa ∈ fixedValues ∧ forall value, value ∈ fixedValues -> value = kappa

/-- A completion problem has the structural-signature naming condition exactly when its
canonical gauge-orbit quotient has one element. -/
theorem has_structural_completion_signature_iff_unique
    {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD) :
    HasStructuralCompletionSignature normalization defect zeroD gaugeStable <->
      Nonempty (Unique
        (CompletionSignature normalization defect zeroD gaugeStable)) := by
  rw [HasStructuralCompletionSignature]
  constructor
  · intro signatureCondition
    letI : Nonempty (completionPoints normalization defect zeroD gaugeStable) :=
      signatureCondition.1
    exact
      (MulAction.pretransitive_iff_unique_quotient_of_nonempty
        G (completionPoints normalization defect zeroD gaugeStable)).mp
          signatureCondition.2
  · intro uniqueSignature
    have signatureNonempty : Nonempty
        (CompletionSignature normalization defect zeroD gaugeStable) :=
      uniqueSignature.map fun uniqueInstance => uniqueInstance.default
    have pointsNonempty : Nonempty
        (completionPoints normalization defect zeroD gaugeStable) :=
      (nonempty_quotient_iff
        (MulAction.orbitRel G
          (completionPoints normalization defect zeroD gaugeStable))).mp
            signatureNonempty
    letI : Nonempty (completionPoints normalization defect zeroD gaugeStable) :=
      pointsNonempty
    exact ⟨pointsNonempty,
      (MulAction.pretransitive_iff_unique_quotient_of_nonempty
        G (completionPoints normalization defect zeroD gaugeStable)).mpr
          uniqueSignature⟩

/-- The OACTC completion vocabulary has three exact clauses: completion points are the
normalized zero-defect parameters; the structural-signature condition is equivalent to the
orbit quotient having one element; and a completion constant is exactly the sole value left by
gauge fixing. -/
theorem completion_vocabulary {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD) :
    (forall a,
      a ∈ completionPoints normalization defect zeroD gaugeStable <->
        a ∈ normalization ∧ defect a = zeroD) ∧
    (HasStructuralCompletionSignature normalization defect zeroD gaugeStable <->
      Nonempty (Unique
        (CompletionSignature normalization defect zeroD gaugeStable))) ∧
    (forall {R : Type z} (fixedValues : Set R) (kappa : R),
      IsCompletionConstant fixedValues kappa <-> fixedValues = {kappa}) := by
  constructor
  · exact mem_completionPoints_iff normalization defect zeroD gaugeStable
  constructor
  · exact has_structural_completion_signature_iff_unique
      normalization defect zeroD gaugeStable
  · intro R fixedValues kappa
    simpa [IsCompletionConstant] using
      (Set.eq_singleton_iff_unique_mem (s := fixedValues) (a := kappa)).symm

/- Reverse probe: the public signature clause forces all signature classes to be equal. -/
example {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (normalization : Set A) (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet normalization defect zeroD ->
        g • a ∈ completionPointSet normalization defect zeroD)
    (signatureCondition :
      HasStructuralCompletionSignature normalization defect zeroD gaugeStable)
    (first second : CompletionSignature normalization defect zeroD gaugeStable) :
    first = second := by
  have uniqueSignature :=
    (has_structural_completion_signature_iff_unique
      normalization defect zeroD gaugeStable).mp
      signatureCondition
  letI : Unique (CompletionSignature normalization defect zeroD gaugeStable) :=
    Classical.choice uniqueSignature
  exact Subsingleton.elim first second

/- Trivialization probe: an empty normalization set cannot acquire the signature name. -/
example {G : Type u} {A : Type v} {D : Type w}
    [Group G] [MulAction G A]
    (defect : A -> D) (zeroD : D)
    (gaugeStable : forall (g : G) {a : A},
      a ∈ completionPointSet (∅ : Set A) defect zeroD ->
        g • a ∈ completionPointSet (∅ : Set A) defect zeroD) :
    ¬ HasStructuralCompletionSignature (∅ : Set A) defect zeroD gaugeStable := by
  rw [HasStructuralCompletionSignature]
  rintro ⟨⟨⟨a, ha⟩⟩, _⟩
  simpa [completionPointSet] using ha.1

/- Trivialization probe: uniqueness alone does not name a constant in an empty value set. -/
example {R : Type z} (kappa : R) :
    ¬ IsCompletionConstant (∅ : Set R) kappa := by
  simp [IsCompletionConstant]

private abbrev TrivialGauge := Equiv.Perm (Fin 1)

private instance : MulAction TrivialGauge Nat where
  smul _ n := n
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

private def twoPointNormalization : Set Nat := {0, 1}

private def twoPointGaugeStable : forall (g : TrivialGauge) {a : Nat},
    a ∈ completionPointSet twoPointNormalization (fun _ => ()) () ->
      g • a ∈ completionPointSet twoPointNormalization (fun _ => ()) () := by
  intro g a ha
  exact ha

private abbrev TwoPointCompletion :=
  completionPoints (G := TrivialGauge) twoPointNormalization
    (fun _ : Nat => ()) () twoPointGaugeStable

private def zeroCompletionPoint : TwoPointCompletion :=
  ⟨0, by simp [twoPointNormalization]⟩

private def oneCompletionPoint : TwoPointCompletion :=
  ⟨1, by simp [twoPointNormalization]⟩

/- Quotient distinction probe: without the single-orbit condition, the genuine orbit quotient
retains two distinct classes rather than collapsing definitionally. -/
example :
    (Quotient.mk'' zeroCompletionPoint :
      CompletionSignature twoPointNormalization (fun _ : Nat => ()) ()
        twoPointGaugeStable) ≠
    Quotient.mk'' oneCompletionPoint := by
  intro classesEqual
  have orbitRelated : MulAction.orbitRel TrivialGauge TwoPointCompletion
      zeroCompletionPoint oneCompletionPoint :=
    Quotient.eq''.mp classesEqual
  have zeroInOrbit : zeroCompletionPoint ∈
      MulAction.orbit TrivialGauge oneCompletionPoint :=
    (MulAction.orbitRel_apply
      (G := TrivialGauge) (α := TwoPointCompletion)).mp orbitRelated
  rcases zeroInOrbit with ⟨g, translated⟩
  have oneEqualsZero : (1 : Nat) = 0 := by
    simpa [zeroCompletionPoint, oneCompletionPoint] using
      congrArg Subtype.val translated
  exact Nat.one_ne_zero oneEqualsZero

end D5.S3.Observer.Completion.StructuralCompletionSignature
