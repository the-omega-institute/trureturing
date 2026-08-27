/- GID: D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zero-sum gauge preserves the global defect and its completion-point orbit class. -/

import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Ring.Real

/- Library-search audit trail (2026-08-28):
   * Repository searches found no prior adelic completion-point or completion-signature model.
   * Pinned Mathlib supplies `Summable.tsum_add`, used for the additive-defect equality.
   * Pinned Mathlib also supplies `AddAction.orbitRel.Quotient` and `Quotient.sound`, used
     directly for the source's structural signature `Sigma(C) = K(C)/G`.
   * The defect codomain is therefore abstracted to a Hausdorff topological additive
     commutative group. `Real` appears only in the concrete reverse-fidelity probe.
   * Both finite and infinite place types are required to be nonempty, matching the source's
     finite-prime channel and real infinite factor. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators

noncomputable section

namespace D5.S3.Analytic.Adelic.ZeroSumGaugeGlobalCompletion

universe u_f u_i u_d

/-- The source's full place type, with inhabited finite and infinite channels. -/
abbrev AdelicPlace (FinitePlace : Type u_f) (InfinitePlace : Type u_i)
    [Nonempty FinitePlace] [Nonempty InfinitePlace] :=
  FinitePlace ⊕ InfinitePlace

/-- A summable family of local contributions in an abstract additive defect space. -/
@[ext]
structure AdelicLocalLedger (FinitePlace : Type u_f) (InfinitePlace : Type u_i)
    (Defect : Type u_d) [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] where
  localContribution : AdelicPlace FinitePlace InfinitePlace → Defect
  summable_localContribution : Summable localContribution

/-- The additive subgroup of summable local shifts whose total defect is zero. -/
def zeroSumGaugeSubgroup (FinitePlace : Type u_f) (InfinitePlace : Type u_i)
    (Defect : Type u_d) [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] [IsTopologicalAddGroup Defect] :
    AddSubgroup (AdelicPlace FinitePlace InfinitePlace → Defect) where
  carrier := { shift | HasSum shift 0 }
  zero_mem' := hasSum_zero
  add_mem' := by
    intro first second firstZero secondZero
    change HasSum (fun place ↦ first place + second place) 0
    simpa only [add_zero] using HasSum.add firstZero secondZero
  neg_mem' := by
    intro shift shiftZero
    change HasSum (fun place ↦ -shift place) 0
    simpa only [neg_zero] using HasSum.neg shiftZero

/-- A local gauge shift `b_v` whose global additive contribution is zero. -/
abbrev ZeroSumGauge (FinitePlace : Type u_f) (InfinitePlace : Type u_i)
    (Defect : Type u_d) [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] [IsTopologicalAddGroup Defect] :=
  zeroSumGaugeSubgroup FinitePlace InfinitePlace Defect

namespace ZeroSumGauge

/-- The local shift family underlying a zero-sum gauge. -/
def shift {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] [IsTopologicalAddGroup Defect]
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    AdelicPlace FinitePlace InfinitePlace → Defect :=
  gauge

/-- The defining zero-sum witness of a gauge. -/
theorem hasSum_zero {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    {Defect : Type u_d} [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] [IsTopologicalAddGroup Defect]
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    HasSum (ZeroSumGauge.shift gauge) 0 :=
  gauge.property

end ZeroSumGauge

/-- Apply the source's local gauge change `L_v ↦ L_v + b_v`. -/
def gaugeTransform {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    {Defect : Type u_d} [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] [IsTopologicalAddGroup Defect]
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    AdelicLocalLedger FinitePlace InfinitePlace Defect where
  localContribution place :=
    ledger.localContribution place + ZeroSumGauge.shift gauge place
  summable_localContribution :=
    ledger.summable_localContribution.add
      (ZeroSumGauge.hasSum_zero gauge).summable

/-- The section-15 global additive defect `Delta_glob = sum_v L_v`. -/
def globalAdditiveDefect {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    {Defect : Type u_d} [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect) : Defect :=
  ∑' place, ledger.localContribution place

/-- The section-15 sum calculation: a zero-sum gauge preserves `Delta_glob`. -/
theorem globalAdditiveDefect_gaugeTransform
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    globalAdditiveDefect (gaugeTransform ledger gauge) =
      globalAdditiveDefect ledger := by
  change (∑' place : AdelicPlace FinitePlace InfinitePlace,
      (ledger.localContribution place + ZeroSumGauge.shift gauge place)) =
    ∑' place : AdelicPlace FinitePlace InfinitePlace,
      ledger.localContribution place
  rw [ledger.summable_localContribution.tsum_add
      (ZeroSumGauge.hasSum_zero gauge).summable,
    (ZeroSumGauge.hasSum_zero gauge).tsum_eq, add_zero]

/-- The normalization condition for the section-15 additive completion problem. -/
def normalizedLedgerSet {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    {Defect : Type u_d} [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] :
    Set (AdelicLocalLedger FinitePlace InfinitePlace Defect) :=
  Set.univ

/-- The source's completion-point set `K(C) = {L in N | Delta_glob(L) = 0}`. -/
def globalCompletionPointSet
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] :
    Set (AdelicLocalLedger FinitePlace InfinitePlace Defect) :=
  normalizedLedgerSet ∩ { ledger | globalAdditiveDefect ledger = 0 }

/-- A point of `K(C)`, bundled with normalization and vanishing global defect. -/
abbrev GlobalCompletionPoint
    (FinitePlace : Type u_f) (InfinitePlace : Type u_i) (Defect : Type u_d)
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect] :=
  globalCompletionPointSet (FinitePlace := FinitePlace)
    (InfinitePlace := InfinitePlace) (Defect := Defect)

/-- A zero-sum gauge maps a completion point to a completion point. -/
def gaugeTransformCompletionPoint
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (completionPoint : GlobalCompletionPoint FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    GlobalCompletionPoint FinitePlace InfinitePlace Defect :=
  ⟨gaugeTransform completionPoint.1 gauge, by
    refine ⟨Set.mem_univ _, ?_⟩
    change globalAdditiveDefect (gaugeTransform completionPoint.1 gauge) = 0
    rw [globalAdditiveDefect_gaugeTransform, completionPoint.property.2]⟩

/-- The zero-sum gauge group acts on the global completion-point set `K(C)`. -/
instance globalCompletionPointAddAction
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect] :
    AddAction (ZeroSumGauge FinitePlace InfinitePlace Defect)
      (GlobalCompletionPoint FinitePlace InfinitePlace Defect) where
  vadd gauge completionPoint := gaugeTransformCompletionPoint completionPoint gauge
  zero_vadd completionPoint := by
    apply Subtype.ext
    apply AdelicLocalLedger.ext
    funext place
    change completionPoint.1.localContribution place + 0 =
      completionPoint.1.localContribution place
    exact add_zero _
  add_vadd first second completionPoint := by
    apply Subtype.ext
    apply AdelicLocalLedger.ext
    funext place
    change completionPoint.1.localContribution place +
        (first.1 place + second.1 place) =
      (completionPoint.1.localContribution place + second.1 place) + first.1 place
    abel

/-- The structural completion signature `Sigma(C) = K(C)/G`. -/
abbrev StructuralCompletionSignature
    (FinitePlace : Type u_f) (InfinitePlace : Type u_i) (Defect : Type u_d)
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect] :=
  AddAction.orbitRel.Quotient (ZeroSumGauge FinitePlace InfinitePlace Defect)
    (GlobalCompletionPoint FinitePlace InfinitePlace Defect)

/-- The orbit class of a completion point in the structural completion signature. -/
def structuralCompletionSignatureClass
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (completionPoint : GlobalCompletionPoint FinitePlace InfinitePlace Defect) :
    StructuralCompletionSignature FinitePlace InfinitePlace Defect :=
  Quotient.mk'' completionPoint

/-- Moving a completion point by a gauge does not change its class in `K(C)/G`. -/
theorem structuralCompletionSignatureClass_gaugeTransform
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (completionPoint : GlobalCompletionPoint FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    structuralCompletionSignatureClass
        (gaugeTransformCompletionPoint completionPoint gauge) =
      structuralCompletionSignatureClass completionPoint := by
  apply Quotient.sound
  exact ⟨gauge, rfl⟩

/-- A zero-sum local gauge preserves both the global additive defect and every structural
completion-signature class in `Sigma(C) = K(C)/G`. -/
theorem zero_sum_gauge_preserves_global_completion
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    globalAdditiveDefect (gaugeTransform ledger gauge) =
        globalAdditiveDefect ledger ∧
      ∀ completionPoint : GlobalCompletionPoint FinitePlace InfinitePlace Defect,
        structuralCompletionSignatureClass
            (gaugeTransformCompletionPoint completionPoint gauge) =
          structuralCompletionSignatureClass completionPoint := by
  exact ⟨globalAdditiveDefect_gaugeTransform ledger gauge,
    fun completionPoint ↦
      structuralCompletionSignatureClass_gaugeTransform completionPoint gauge⟩

private def pairedGauge (r : Real) : ZeroSumGauge Unit Unit Real :=
  ⟨fun place ↦
      (if place = Sum.inl () then r else 0) +
        if place = Sum.inr () then -r else 0,
    by
      change HasSum (fun place : AdelicPlace Unit Unit ↦
        (if place = Sum.inl () then r else 0) +
          if place = Sum.inr () then -r else 0) 0
      simpa using
        (hasSum_ite_eq (Sum.inl () : AdelicPlace Unit Unit) r).add
          (hasSum_ite_eq (Sum.inr () : AdelicPlace Unit Unit) (-r))⟩

/- Reverse-fidelity probe: a nonzero gauge moves defect between the finite and infinite
channels while preserving both the total defect and the completion-point orbit class. -/
example (completionPoint : GlobalCompletionPoint Unit Unit Real)
    (r : Real) (hr : r ≠ 0) :
    (gaugeTransform completionPoint.1 (pairedGauge r)).localContribution (Sum.inl ()) ≠
        completionPoint.1.localContribution (Sum.inl ()) ∧
      globalAdditiveDefect (gaugeTransform completionPoint.1 (pairedGauge r)) =
        globalAdditiveDefect completionPoint.1 ∧
      structuralCompletionSignatureClass
          (gaugeTransformCompletionPoint completionPoint (pairedGauge r)) =
        structuralCompletionSignatureClass completionPoint := by
  constructor
  · intro localUnchanged
    have localUnchanged' : completionPoint.1.localContribution (Sum.inl ()) + r =
        completionPoint.1.localContribution (Sum.inl ()) := by
      simpa [gaugeTransform, pairedGauge, ZeroSumGauge.shift] using localUnchanged
    apply hr
    apply add_left_cancel (a := completionPoint.1.localContribution (Sum.inl ()))
    simpa using localUnchanged'
  · refine ⟨(zero_sum_gauge_preserves_global_completion
      completionPoint.1 (pairedGauge r)).1, ?_⟩
    exact (zero_sum_gauge_preserves_global_completion
      completionPoint.1 (pairedGauge r)).2 completionPoint

/- Nondegeneracy probe: the type constraints provide an actual finite and infinite place. -/
example {FinitePlace : Type u_f} {InfinitePlace : Type u_i}
    [Nonempty FinitePlace] [Nonempty InfinitePlace] :
    (∃ place : AdelicPlace FinitePlace InfinitePlace,
        ∃ finitePlace : FinitePlace, place = Sum.inl finitePlace) ∧
      ∃ place : AdelicPlace FinitePlace InfinitePlace,
        ∃ infinitePlace : InfinitePlace, place = Sum.inr infinitePlace := by
  let finitePlace : FinitePlace := Classical.choice inferInstance
  let infinitePlace : InfinitePlace := Classical.choice inferInstance
  exact ⟨⟨Sum.inl finitePlace, finitePlace, rfl⟩,
    ⟨Sum.inr infinitePlace, infinitePlace, rfl⟩⟩

/- Public-contract probe: the theorem must be scalar-generic, exclude empty finite or
infinite place channels, and expose structural-signature preservation as a conjunct. -/
example
    {FinitePlace InfinitePlace Defect : Type*}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect) :
    globalAdditiveDefect (gaugeTransform ledger gauge) =
        globalAdditiveDefect ledger ∧
      ∀ completionPoint : GlobalCompletionPoint FinitePlace InfinitePlace Defect,
        structuralCompletionSignatureClass
            (gaugeTransformCompletionPoint completionPoint gauge) =
          structuralCompletionSignatureClass completionPoint :=
  zero_sum_gauge_preserves_global_completion ledger gauge

#print axioms zero_sum_gauge_preserves_global_completion

end D5.S3.Analytic.Adelic.ZeroSumGaugeGlobalCompletion
