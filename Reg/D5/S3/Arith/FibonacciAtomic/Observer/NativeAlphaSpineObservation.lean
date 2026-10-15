import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation

open _root_.D5.S3.Arith.FibonacciAtomic
open GenealogicalFiberTransport (Source substitution)
open ActualTreeReadoutAcquisition (Address Reply readout)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation

abbrev signature : Signature where
  Params := Address × Nat × Address × Bool
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature
    (fun _ a s =>
      if a.2.2.2 then readout a.2.2.1 (substitution^[2 * a.2.1] s)
      else readout a.2.2.1 s)
    (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ => .absent) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law F := ∀ (p : Address) (k : Nat), 1 ≤ k →
    let E := fun (p : Address) (x : Source) =>
      p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x
    let U := E p (.of true)
    let V := E p (.of false)
    let W := E p (.mul (.of true) (.of true))
    F.readout () (p, k, p, false) U = .alpha ∧
      F.readout () (p, k, p, false) V = .beta ∧
      F.readout () (p, k, p, false) W = .branch ∧
      (∀ q : Address, ¬ p.IsPrefix q →
        F.readout () (p, k, q, true) U = F.readout () (p, k, q, true) V ∧
        F.readout () (p, k, q, true) V = F.readout () (p, k, q, true) W) ∧
      (∀ q : Address, q.length ≤ p.length + k →
        (F.readout () (p, k, q, true) U ≠ .absent ↔
          F.readout () (p, k, q, true) V ≠ .absent) ∧
        (F.readout () (p, k, q, true) V ≠ .absent ↔
          F.readout () (p, k, q, true) W ≠ .absent)) ∧
      (∀ q : Address,
        ¬(F.readout () (p, k, q, true) U ≠ .absent ↔
          F.readout () (p, k, q, true) V ≠ .absent) →
        p.length + k + 1 ≤ q.length) ∧
      (∀ q : Address,
        ¬(F.readout () (p, k, q, true) V ≠ .absent ↔
          F.readout () (p, k, q, true) W ≠ .absent) →
        p.length + k + 1 ≤ q.length)

theorem actual_law : arena.Law actual := by
  intro p k hk
  simpa [arena, actual, realize] using
    (native_alpha_spine_observation p k hk)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h [] 1 (by omega)
  have hα := hh.1
  change Reply.absent = Reply.alpha at hα
  cases hα

theorem variation : Variation arena actual :=
  ⟨actual_law, rejected, rejected_law⟩

theorem sensitivity : Sensitivity arena actual := by
  exact Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law

theorem dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨([], 1, [], false), (.of true), (.of false), ?_⟩
  change Reply.alpha ≠ Reply.beta
  intro h
  cases h

noncomputable def family : Registration arena (type_of% (@native_alpha_spine_observation)) where
  actual := actual
  bridge := by
    constructor
    · intro h
      simpa [arena, actual, realize] using h
    · intro h
      simpa [arena, actual, realize] using h
  variation := variation
  sensitivity := sensitivity
  dependence := dependence

noncomputable def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_alpha_spine_observation) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation.native_alpha_spine_observation.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "arg", "arg"],
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

open _root_.D5.S3.Arith.FibonacciAtomic.ActualLeafHistoryRigidity (subtree)

abbrev holeSignature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Option Source
  Anchor := Empty
  finiteAnchor := inferInstance

def holeActual : Realization holeSignature :=
  realize holeSignature (fun _ p x => subtree p
    (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x))
    (fun e => nomatch e)

def holeBad : Realization holeSignature :=
  realize holeSignature (fun _ _ _ => none) (fun e => nomatch e)

abbrev holeArena : Arena where
  signature := holeSignature
  Law R := ∀ p x, R.readout () p x = some x

private theorem hole_bad : ¬ holeArena.Law holeBad := by
  intro h
  have he := h [] (.of true)
  cases he

def holeProof : Registration holeArena (type_of% (@native_alpha_spine_at)) where
  actual := holeActual
  bridge := Iff.rfl
  variation := ⟨native_alpha_spine_at, holeBad, hole_bad⟩
  sensitivity := ⟨fun i => ⟨holeBad,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, hole_bad⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨[], .of true, .of false, ?_⟩
    intro he
    cases he

noncomputable def native_alpha_spine_at_registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@native_alpha_spine_at) (Realization holeSignature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation.native_alpha_spine_at.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation.holeProof
  realizationSource := none
  generated := false
  arena := .source ⟨holeArena⟩
  objectArena := .source ⟨holeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source holeArena ⟨holeProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize holeSignature (fun _ p x => subtree p
    (p.foldr (fun b t => if b then .mul (.of true) t else .mul t (.of true)) x))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms holeProof
#print axioms native_alpha_spine_at_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeAlphaSpineObservation
