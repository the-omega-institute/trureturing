import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.Measures.NormPreservingLifts

/-!
# Exact original all-lifts source scope

The raw theorem includes arbitrary carrier and index universes, compact
Hausdorff Borel K, Hausdorff Borel L, every filter (including bottom), actual
signed measures, equal variation masses, clopen concentration, and eventual
fibre constancy separately for each locally constant test. No restriction to
finite carriers, Dirac measures, nonempty spaces or a nontrivial filter is made.

This source binds the exact actual-positive theorem and supplies a dependent
source arena with the original carriers, dictionaries, signed measure, map and
test function. The actual readout is the signed functional after pushforward,
and the source bridge, rejected realization, whole-family variation, fixed-role
sensitivity and observational dependence are retained below. The source
selector remains subject to the current dictionary-dependent-coordinate
contract; the producer report is the authority for whether this registration
can be closed as a source binding.
-/

namespace Reg.D5.S3.Topology.Measures.NormPreservingLifts

set_option autoImplicit false

universe u v w

open Set Filter MeasureTheory
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape
open _root_.D5.S3.Topology.Measures.NormPreservingLifts

abbrev arbitraryLiftsScope := type_of% (@arbitrary_lifts_tendsto.{u,v,w})

theorem arbitrary_lifts_actual : arbitraryLiftsScope.{u,v,w} :=
  @arbitrary_lifts_tendsto.{u,v,w}

/-- Exact scopes for the finite positive-difference integration suppliers.
These source bindings supply no four-slot realization or sensitivity evidence. -/
theorem difference_integral_actual :
    type_of% (@signedFunctional_sub_toSignedMeasure.{u}) :=
  @signedFunctional_sub_toSignedMeasure.{u}

theorem difference_variation_actual :
    type_of% (@totalVariation_sub_toSignedMeasure_le.{u}) :=
  @totalVariation_sub_toSignedMeasure_le.{u}

/- Same-delivery source binding for the moved continuous pushforward supplier.
The faithful role selects actual p and g pullback evaluation across arbitrary
compact Borel carriers, including empty carriers. Replacing it by a constant
equality or a finite nonempty carrier specialization would lose the source
telescope; the dependent arena and its proofs below keep the full source
scope. -/
theorem functional_map_actual : type_of% (@functional_map.{u,v}) :=
  @functional_map.{u,v}

abbrev functionalScope := type_of% (@functional_map.{u,v})

/-! A source-faithful dependent registration for `functional_map`.  The
parameter record carries every topology and Borel dictionary from the
original telescope; the state carries the actual signed measure, continuous
map and test function.  The observed value is the signed integral after the
actual pushforward, and the law compares it with the actual pullback value.
No carrier, map, function, or filter is specialized. -/

structure SourceInputs where
  X : Type u
  Y : Type v
  topX : TopologicalSpace X
  compactX : @CompactSpace X topX
  measurableX : MeasurableSpace X
  borelX : @BorelSpace X topX measurableX
  topY : TopologicalSpace Y
  compactY : @CompactSpace Y topY
  measurableY : MeasurableSpace Y
  borelY : @BorelSpace Y topY measurableY

attribute [instance] SourceInputs.topX SourceInputs.compactX
  SourceInputs.measurableX SourceInputs.borelX SourceInputs.topY
  SourceInputs.compactY SourceInputs.measurableY SourceInputs.borelY

def SourceState (p : SourceInputs.{u,v}) :=
  @SignedMeasure p.X p.measurableX ×
    (@ContinuousMap p.X p.Y p.topX p.topY ×
      C(p.Y, ℝ))

abbrev signature : DependentFamily.Signature where
  Params := SourceInputs.{u,v}
  State := SourceState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private noncomputable def observed (p : SourceInputs.{u,v}) (st : SourceState p) :
    ℝ := by
  letI := p.topX
  letI := p.compactX
  letI := p.measurableX
  letI := p.borelX
  letI := p.topY
  letI := p.compactY
  letI := p.measurableY
  letI := p.borelY
  exact signedFunctional (st.1.map st.2.1) st.2.2

noncomputable def actual : DependentFamily.Realization signature.{u,v} :=
  DependentFamily.realize signature.{u,v} (fun _ p st => observed p st)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature.{u,v}
  Law := fun r => ∀ p st,
    letI := p.topX
    letI := p.compactX
    letI := p.measurableX
    letI := p.borelX
    letI := p.topY
    letI := p.compactY
    letI := p.measurableY
    letI := p.borelY
    r.readout () p st = signedFunctional st.1 (st.2.2.comp st.2.1)

theorem source_bridge : functionalScope.{u,v} ↔ arena.{u,v}.Law actual.{u,v} := by
  constructor
  · intro h p st
    letI := p.topX
    letI := p.compactX
    letI := p.measurableX
    letI := p.borelX
    letI := p.topY
    letI := p.compactY
    letI := p.measurableY
    letI := p.borelY
    exact h st.1 st.2.1 st.2.2
  · intro h X Y topX compactX measurableX borelX topY compactY measurableY borelY s p g
    let q : SourceInputs.{u,v} :=
      { X := X, Y := Y, topX := topX, compactX := compactX,
        measurableX := measurableX, borelX := borelX, topY := topY,
        compactY := compactY, measurableY := measurableY, borelY := borelY }
    exact h q (s, p, g)

theorem actual_positive : arena.{u,v}.Law actual.{u,v} :=
  source_bridge.mp (@functional_map.{u,v})

def rejected : DependentFamily.Realization signature.{u,v} :=
  DependentFamily.realize signature.{u,v} (fun _ _ _ => (0 : ℝ))
    (fun a => Empty.elim a)

private abbrev unitInputs : SourceInputs.{u,v} :=
  { X := ULift.{u} Unit, Y := ULift.{v} Unit,
    topX := inferInstance, compactX := inferInstance,
    measurableX := inferInstance, borelX := inferInstance, topY := inferInstance,
    compactY := inferInstance, measurableY := inferInstance, borelY := inferInstance }

private noncomputable def unitStateAt (x : ULift.{u} Unit) (y : ULift.{v} Unit) :
    SourceState unitInputs.{u,v} :=
  ((Measure.dirac (ULift.up ())).toSignedMeasure,
    (ContinuousMap.const _ y, (ContinuousMap.const _ 1)))

private noncomputable abbrev unitState : SourceState unitInputs.{u,v} :=
  unitStateAt (ULift.up () : ULift.{u} Unit) (ULift.up () : ULift.{v} Unit)

private theorem unit_rhs_eq_one (x : ULift.{u} Unit) (y : ULift.{v} Unit) :
    signedFunctional (Measure.dirac x).toSignedMeasure
        ((ContinuousMap.const (ULift.{v} Unit) 1).comp
          (ContinuousMap.const (ULift.{u} Unit) y)) = 1 := by
  have hi := signedFunctional_sub_toSignedMeasure (K := ULift.{u} Unit)
    (Measure.dirac x) 0 (ContinuousMap.const _ 1)
  have hbase : signedFunctional (Measure.dirac x).toSignedMeasure
      (ContinuousMap.const (ULift.{u} Unit) 1) = 1 := by
    simpa [unitInputs, unitState] using hi
  calc
    _ = signedFunctional (Measure.dirac x).toSignedMeasure
        (ContinuousMap.const (ULift.{u} Unit) 1) := by
      apply congrArg (fun f => signedFunctional (Measure.dirac x).toSignedMeasure f)
      apply ContinuousMap.ext
      intro x
      rfl
    _ = 1 := hbase

private theorem unit_observed_ne_zero (x : ULift.{u} Unit) (y : ULift.{v} Unit) :
    observed unitInputs.{u,v} (unitStateAt x y) ≠ 0 := by
  intro h
  have hm : observed unitInputs.{u,v} (unitStateAt x y) = 1 := by
    change signedFunctional ((unitStateAt x y).1.map (unitStateAt x y).2.1)
        (unitStateAt x y).2.2 = 1
    rw [_root_.D5.S3.Topology.Measures.NormPreservingLifts.functional_map
      (unitStateAt x y).1 (unitStateAt x y).2.1 (unitStateAt x y).2.2]
    change signedFunctional (Measure.dirac (ULift.up () : ULift.{u} Unit)).toSignedMeasure
        ((ContinuousMap.const (ULift.{v} Unit) 1).comp
          (ContinuousMap.const (ULift.{u} Unit) y)) = 1
    exact unit_rhs_eq_one x y
  exact zero_ne_one (h.symm.trans hm)

theorem rejected_law : ¬ arena.{u,v}.Law rejected.{u,v} := by
  intro h
  have hz := h unitInputs.{u,v} (unitStateAt
    (ULift.up () : ULift.{u} Unit) (ULift.up () : ULift.{v} Unit))
  change (0 : ℝ) = signedFunctional (Measure.dirac (ULift.up () : ULift.{u} Unit)).toSignedMeasure
      ((ContinuousMap.const (ULift.{v} Unit) 1).comp
        (ContinuousMap.const (ULift.{u} Unit) (ULift.up () : ULift.{v} Unit))) at hz
  exact zero_ne_one (hz.trans
    (unit_rhs_eq_one (ULift.up () : ULift.{u} Unit) (ULift.up () : ULift.{v} Unit)))

private theorem actual_dependence (x : ULift.{u} Unit) (y : ULift.{v} Unit) :
    DependentFamily.ObservationalDependence signature.{u,v} actual.{u,v} := by
  intro i
  let zeroTestState : SourceState unitInputs.{u,v} :=
    ((Measure.dirac (ULift.up ())).toSignedMeasure,
      (ContinuousMap.const _ (ULift.up ()), (ContinuousMap.const _ 0)))
  refine ⟨unitInputs.{u,v}, zeroTestState, unitStateAt x y, ?_⟩
  intro h
  have hzero : observed unitInputs.{u,v} zeroTestState = 0 := by
    change signedFunctional (zeroTestState.1.map zeroTestState.2.1) zeroTestState.2.2 = 0
    rw [_root_.D5.S3.Topology.Measures.NormPreservingLifts.functional_map
      zeroTestState.1 zeroTestState.2.1 zeroTestState.2.2]
    have hi := signedFunctional_sub_toSignedMeasure (K := ULift.{u} Unit)
      (Measure.dirac (ULift.up ())) 0 (ContinuousMap.const _ 0)
    have hbase : signedFunctional (Measure.dirac (ULift.up ())).toSignedMeasure
        (ContinuousMap.const (ULift.{u} Unit) 0) = 0 := by
      simpa [unitInputs, zeroTestState] using hi
    change signedFunctional (Measure.dirac (ULift.up ())).toSignedMeasure
        ((ContinuousMap.const (ULift.{v} Unit) 0).comp
          (ContinuousMap.const (ULift.{u} Unit) (ULift.up ()))) = 0
    calc
      _ = signedFunctional (Measure.dirac (ULift.up ())).toSignedMeasure
          (ContinuousMap.const (ULift.{u} Unit) 0) := by
        apply congrArg (fun f =>
          signedFunctional (Measure.dirac (ULift.up ())).toSignedMeasure f)
        apply ContinuousMap.ext
        intro x
        rfl
      _ = 0 := hbase
  have hm : observed unitInputs.{u,v} (unitStateAt x y) = 1 := by
    change signedFunctional ((unitStateAt x y).1.map (unitStateAt x y).2.1)
        (unitStateAt x y).2.2 = 1
    rw [_root_.D5.S3.Topology.Measures.NormPreservingLifts.functional_map
      (unitStateAt x y).1 (unitStateAt x y).2.1 (unitStateAt x y).2.2]
    change signedFunctional (Measure.dirac x).toSignedMeasure
        ((ContinuousMap.const (ULift.{v} Unit) 1).comp
          (ContinuousMap.const (ULift.{u} Unit) y)) = 1
    exact unit_rhs_eq_one x y
  have : (0 : ℝ) = 1 := by
    have h' : observed unitInputs.{u,v} zeroTestState =
        observed unitInputs.{u,v} (unitStateAt x y) := by
      simpa [actual, DependentFamily.realize] using h
    exact hzero.symm.trans (h'.trans hm)
  norm_num at this

noncomputable def familyRegistration : DependentFamily.Registration arena.{u,v} functionalScope.{u,v} where
  actual := actual.{u,v}
  bridge := source_bridge.{u,v}
  variation := ⟨actual_positive.{u,v}, rejected.{u,v}, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected.{u,v}, ?_, rfl, rejected_law.{u,v}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := actual_dependence.{u,v}
    (ULift.up () : ULift.{u} Unit) (ULift.up () : ULift.{v} Unit)

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@functional_map) (DependentFamily.Realization signature.{u,v}) Type Unit where
  unitName := `D5.S3.Topology.Measures.NormPreservingLifts.functional_map.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.NormPreservingLifts.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature.{u,v}
    (fun _ p st => observed p st) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.NormPreservingLifts
    definition := none
    coordinates := #[0, 1, 10, 11, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

/- The current producer still records any source-selector contract gap for
this target under https://github.com/the-omega-institute/trureturing/issues/24319.
The older finite-family issue 24040 is not used to cover this extension. -/

/-! ## Lossless equality-predicate observation at the original equality prefix

The raw conclusion is `@Eq ℝ lhs rhs`. Its proper application prefix `@Eq ℝ`
has type `ℝ → (ℝ → Prop)`. Function-operand selection therefore observes
`x ↦ (x = ·)`, with no dictionary coordinate: Params is the canonical empty
pack Unit, State is ℝ, and Output is ℝ → Prop. This representation loses no
real value, as `equality_predicate_injective` proves. In the Law its state is
the original signed integral after pushforward, and its remaining argument is
the original continuous pullback integral. Neither integral is replaced by a
proxy or hidden in the observer's parameters.

The complete original telescope is retained below, including both universes,
every dictionary, s, p and g. At actual, the Law reduces to the exact original
equality; at another realization it varies that original equality relation,
without an added equality conjunct. `unit_source_value` additionally checks
that every real state of the observer occurs as an actual source integral.
The earlier integral-family mathematics and its unresolved selector remain
above; this is a distinct source-occurrence registration.
-/
namespace EqualityReadout

abbrev signature : DependentFamily.Signature where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ x => Eq x)
    (fun a => Empty.elim a)

def arena : DependentFamily.Arena where
  signature := signature
  Law := fun r => ∀ {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (s : SignedMeasure X) (p : C(X, Y)) (g : C(Y, ℝ)),
    r.readout () () (signedFunctional (s.map p) g)
      (signedFunctional s (g.comp p))

theorem source_bridge : functionalScope.{u,v} ↔ arena.{u,v}.Law actual :=
  Iff.rfl

theorem actual_positive : arena.{u,v}.Law actual :=
  @functional_map.{u,v}

theorem equality_predicate_injective :
    Function.Injective (fun x : ℝ => (fun y : ℝ => x = y)) := by
  intro x y h
  exact (Eq.mp (congrFun h x) rfl).symm

theorem actual_source_predicate {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (s : SignedMeasure X) (p : C(X, Y)) (g : C(Y, ℝ)) :
    actual.readout () () (signedFunctional (s.map p) g) =
      (fun z : ℝ => signedFunctional (s.map p) g = z) :=
  rfl

theorem unit_source_value (c : ℝ) :
    signedFunctional
      (((Measure.dirac (ULift.up () : ULift.{u} Unit)).toSignedMeasure).map
        (ContinuousMap.const (ULift.{u} Unit) (ULift.up () : ULift.{v} Unit)))
      (ContinuousMap.const (ULift.{v} Unit) c) = c := by
  rw [_root_.D5.S3.Topology.Measures.NormPreservingLifts.functional_map]
  have h := signedFunctional_sub_toSignedMeasure (K := ULift.{u} Unit)
    (Measure.dirac (ULift.up ())) 0 (ContinuousMap.const _ c)
  simpa using h

def rejected : DependentFamily.Realization signature :=
  DependentFamily.realize signature (fun _ _ _ _ => False)
    (fun a => Empty.elim a)

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  exact h (X := ULift.{u} Unit) (Y := ULift.{v} Unit) 0
    (ContinuousMap.const _ (ULift.up ())) (ContinuousMap.const _ 0)

theorem actual_dependence :
    DependentFamily.ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro h
  have heq : (0 : ℝ) = 1 := equality_predicate_injective h
  exact zero_ne_one heq

def familyRegistration : DependentFamily.Registration arena.{u,v} functionalScope.{u,v} where
  actual := actual
  bridge := source_bridge.{u,v}
  variation := ⟨actual_positive.{u,v}, rejected, rejected_law.{u,v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{u,v}⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit _ j i))
    · intro a
      exact Empty.elim a
  dependence := actual_dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@functional_map) (DependentFamily.Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Topology.Measures.NormPreservingLifts.EqualityReadout.__information_unit
  realizationName := `Reg.D5.S3.Topology.Measures.NormPreservingLifts.EqualityReadout.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u,v}⟩
  objectArena := .source ⟨arena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u,v} ⟨familyRegistration.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (DependentFamily.realize signature
    (fun _ _ x => Eq x) (fun a => Empty.elim a))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.Measures.NormPreservingLifts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end EqualityReadout

end Reg.D5.S3.Topology.Measures.NormPreservingLifts
