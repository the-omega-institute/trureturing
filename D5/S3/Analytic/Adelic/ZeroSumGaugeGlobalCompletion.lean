/- GID: D5/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   generality: G
   mirror-B: D5/B/S3/Analytic/Adelic/ZeroSumGaugeGlobalCompletion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A zero-sum gauge preserves the global defect and any gauge-invariant completion set. -/

import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.Ring.Real

/- Library-search audit trail (2026-08-28):
   * Repository searches found no prior adelic completion-point or completion-signature model.
   * Pinned Mathlib supplies `Summable.tsum_add`, used for the additive-defect equality.
   * The defect codomain is therefore abstracted to a Hausdorff topological additive
     commutative group. `Real` appears only in the concrete reverse-fidelity probe.
   * `T2Space Defect` is required by Mathlib's `tsum` representation and is not a
     hypothesis stated in the source atom.
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

/-- The section-15 sum calculation: a zero-sum gauge preserves `Delta_glob`.

`T2Space Defect` is required by Mathlib's `tsum` representation; it is not a source
hypothesis. -/
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

/-- The source's completion-point set `K(C) = {L in N | Delta_glob(L) = 0}`.

The source leaves the normalization constraint `N` abstract, so it is an explicit
parameter rather than being identified with the full ledger space. -/
def globalCompletionPointSet
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    (normalizationSet : Set (AdelicLocalLedger FinitePlace InfinitePlace Defect)) :
    Set (AdelicLocalLedger FinitePlace InfinitePlace Defect) :=
  normalizationSet ∩ { ledger | globalAdditiveDefect ledger = 0 }

/-- A zero-sum local gauge preserves the global additive defect. If both the gauge and its
inverse preserve the source's abstract normalization set `N`, its image on the completion
set is exactly `K(C)`.

`T2Space Defect` is required by Mathlib's `tsum` representation; it is not a source
hypothesis. -/
theorem zero_sum_gauge_preserves_global_completion
    {FinitePlace : Type u_f} {InfinitePlace : Type u_i} {Defect : Type u_d}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (normalizationSet : Set (AdelicLocalLedger FinitePlace InfinitePlace Defect))
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect)
    (normalizationSet_gauge_closed :
      Set.MapsTo (fun localLedger ↦ gaugeTransform localLedger gauge)
        normalizationSet normalizationSet)
    (normalizationSet_neg_gauge_closed :
      Set.MapsTo (fun localLedger ↦ gaugeTransform localLedger (-gauge))
        normalizationSet normalizationSet) :
    globalAdditiveDefect (gaugeTransform ledger gauge) =
        globalAdditiveDefect ledger ∧
      (fun localLedger ↦ gaugeTransform localLedger gauge) ''
          globalCompletionPointSet normalizationSet =
        globalCompletionPointSet normalizationSet := by
  refine ⟨globalAdditiveDefect_gaugeTransform ledger gauge,
    Set.Subset.antisymm ?_ ?_⟩
  · rintro transformedLedger ⟨completionPoint, completionPoint_mem, rfl⟩
    exact ⟨normalizationSet_gauge_closed completionPoint_mem.1,
      (globalAdditiveDefect_gaugeTransform completionPoint gauge).trans
        completionPoint_mem.2⟩
  · intro completionPoint completionPoint_mem
    refine ⟨gaugeTransform completionPoint (-gauge), ?_, ?_⟩
    · exact ⟨normalizationSet_neg_gauge_closed completionPoint_mem.1,
        (globalAdditiveDefect_gaugeTransform completionPoint (-gauge)).trans
          completionPoint_mem.2⟩
    · apply AdelicLocalLedger.ext
      funext place
      change (completionPoint.localContribution place + -gauge.1 place) +
          gauge.1 place = completionPoint.localContribution place
      abel

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
channels while preserving both the total defect and a gauge-invariant completion set. -/
example (ledger : AdelicLocalLedger Unit Unit Real)
    (r : Real) (hr : r ≠ 0) :
    (gaugeTransform ledger (pairedGauge r)).localContribution (Sum.inl ()) ≠
        ledger.localContribution (Sum.inl ()) ∧
      globalAdditiveDefect (gaugeTransform ledger (pairedGauge r)) =
          globalAdditiveDefect ledger ∧
        (fun localLedger ↦ gaugeTransform localLedger (pairedGauge r)) ''
            globalCompletionPointSet
              { localLedger | globalAdditiveDefect localLedger = 0 } =
          globalCompletionPointSet
            { localLedger | globalAdditiveDefect localLedger = 0 } := by
  constructor
  · intro localUnchanged
    have localUnchanged' : ledger.localContribution (Sum.inl ()) + r =
        ledger.localContribution (Sum.inl ()) := by
      simpa [gaugeTransform, pairedGauge, ZeroSumGauge.shift] using localUnchanged
    apply hr
    apply add_left_cancel (a := ledger.localContribution (Sum.inl ()))
    simpa using localUnchanged'
  · refine ⟨globalAdditiveDefect_gaugeTransform ledger (pairedGauge r), ?_⟩
    refine ((zero_sum_gauge_preserves_global_completion
      { localLedger | globalAdditiveDefect localLedger = 0 }
      ledger (pairedGauge r)) ?_ ?_).2
    · intro localLedger localLedger_mem
      exact (globalAdditiveDefect_gaugeTransform localLedger (pairedGauge r)).trans
        localLedger_mem
    · intro localLedger localLedger_mem
      exact (globalAdditiveDefect_gaugeTransform localLedger (-pairedGauge r)).trans
        localLedger_mem

private def zeroLedger : AdelicLocalLedger Unit Unit Real where
  localContribution := 0
  summable_localContribution := hasSum_zero.summable

/- Construction-identity probe: without normalization invariance, the image equality can
fail even though the completion set is built by the same definition. -/
example :
    (fun localLedger ↦ gaugeTransform localLedger (pairedGauge 1)) ''
        globalCompletionPointSet
          ({zeroLedger} : Set (AdelicLocalLedger Unit Unit Real)) ≠
      globalCompletionPointSet
        ({zeroLedger} : Set (AdelicLocalLedger Unit Unit Real)) := by
  have zeroLedger_mem : zeroLedger ∈ globalCompletionPointSet
      ({zeroLedger} : Set (AdelicLocalLedger Unit Unit Real)) := by
    refine ⟨Set.mem_singleton zeroLedger, ?_⟩
    simp [globalAdditiveDefect, zeroLedger]
  have transformed_not_mem : gaugeTransform zeroLedger (pairedGauge 1) ∉
      globalCompletionPointSet
        ({zeroLedger} : Set (AdelicLocalLedger Unit Unit Real)) := by
    intro transformed_mem
    have transformed_eq : gaugeTransform zeroLedger (pairedGauge 1) = zeroLedger :=
      Set.mem_singleton_iff.mp transformed_mem.1
    have local_eq := congrArg
      (fun localLedger ↦ localLedger.localContribution (Sum.inl ())) transformed_eq
    simp only [gaugeTransform, pairedGauge, ZeroSumGauge.shift, zeroLedger,
      Pi.zero_apply, if_pos] at local_eq
    have place_ne : (Sum.inl () : AdelicPlace Unit Unit) ≠ Sum.inr () := by
      simp
    rw [if_neg place_ne] at local_eq
    norm_num at local_eq
  intro image_eq
  apply transformed_not_mem
  rw [← image_eq]
  exact ⟨zeroLedger, zeroLedger_mem, rfl⟩

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

/- Public-contract probe: the theorem is scalar-generic, excludes empty finite or infinite
place channels, keeps normalization abstract, and exposes exact completion-set invariance. -/
example
    {FinitePlace InfinitePlace Defect : Type*}
    [Nonempty FinitePlace] [Nonempty InfinitePlace]
    [AddCommGroup Defect] [TopologicalSpace Defect]
    [IsTopologicalAddGroup Defect] [T2Space Defect]
    (normalizationSet : Set (AdelicLocalLedger FinitePlace InfinitePlace Defect))
    (ledger : AdelicLocalLedger FinitePlace InfinitePlace Defect)
    (gauge : ZeroSumGauge FinitePlace InfinitePlace Defect)
    (normalizationSet_gauge_closed :
      Set.MapsTo (fun localLedger ↦ gaugeTransform localLedger gauge)
        normalizationSet normalizationSet)
    (normalizationSet_neg_gauge_closed :
      Set.MapsTo (fun localLedger ↦ gaugeTransform localLedger (-gauge))
        normalizationSet normalizationSet) :
    globalAdditiveDefect (gaugeTransform ledger gauge) =
        globalAdditiveDefect ledger ∧
      (fun localLedger ↦ gaugeTransform localLedger gauge) ''
          globalCompletionPointSet normalizationSet =
        globalCompletionPointSet normalizationSet :=
  zero_sum_gauge_preserves_global_completion normalizationSet ledger gauge
    normalizationSet_gauge_closed normalizationSet_neg_gauge_closed

#print axioms zero_sum_gauge_preserves_global_completion

end D5.S3.Analytic.Adelic.ZeroSumGaugeGlobalCompletion
