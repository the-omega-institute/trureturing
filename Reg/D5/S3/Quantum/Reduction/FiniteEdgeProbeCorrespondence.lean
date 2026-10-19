import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
import Reg.Support.DependentFamily

/-! Source-family realizations of the endpoint-probe correspondences. -/

noncomputable section
attribute [local instance] Classical.propDecidable
open Matrix
namespace Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
open _root_.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
open _root_.D5.S3.Quantum.Reduction.ProbeGraphDecomposition
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u v

structure Parameters where
  V : Type u
  E : Type v
  finiteV : Fintype V
  eqV : DecidableEq V
  first : E → V
  second : E → V

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.V ⊕ p.E
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.V → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u,v} :=
  realize signature (fun _ p => letI := p.eqV; probes p.first p.second) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ p : Parameters.{u,v}, letI := p.finiteV; letI := p.eqV;
    (∀ j, star (R.readout () p j) ⬝ᵥ R.readout () p j = 1) ∧
    Submodule.span ℂ (Set.range (R.readout () p)) = ⊤ ∧
    (∀ i j, Relation.EqvGen
      (fun k l => star (R.readout () p k) ⬝ᵥ R.readout () p l ≠ 0) i j ↔
        Connected p.first p.second (anchor p.first i) (anchor p.first j)) ∧
    (∀ j, hilbertComponent (R.readout () p) (component (R.readout () p) j) =
      coordinates p.first p.second (anchor p.first j)) ∧
    (∀ j, Module.finrank ℂ (hilbertComponent (R.readout () p)
        (component (R.readout () p) j)) =
      Fintype.card {a : p.V // Connected p.first p.second (anchor p.first j) a})

theorem source_bridge : (type_of% (@construction.{u,v})) ↔ arena.{u,v}.Law actual := by
  constructor
  · intro h p
    letI := p.finiteV
    letI := p.eqV
    exact h p.first p.second
  · intro h V E fv ev first second
    exact h ⟨V, E, fv, ev, first, second⟩

private def emptyEdges : Parameters.{u,v} where
  V := ULift.{u} (Fin 2)
  E := ULift.{v} Empty
  finiteV := inferInstance
  eqV := inferInstance
  first := fun e => nomatch e.down
  second := fun e => nomatch e.down

private def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hn := (h emptyEdges).1 (Sum.inl (ULift.up (0 : Fin 2)))
  change star (0 : ULift.{u} (Fin 2) → ℂ) ⬝ᵥ 0 = 1 at hn
  simpa using hn

def evidence : Registration arena.{u,v} (type_of% (@construction.{u,v})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@construction.{u,v}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    refine ⟨emptyEdges, Sum.inl (ULift.up (0 : Fin 2)),
      Sum.inl (ULift.up (1 : Fin 2)), ?_⟩
    intro h
    have he := congrFun h (ULift.up (0 : Fin 2))
    change (1 : ℂ) = 0 at he
    exact one_ne_zero he

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@construction.{u,v}) (type_of% (realize signature.{u,v}
      (fun _ p => letI := p.eqV; probes p.first p.second) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence.construction
  realizationName := `Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v}
    (fun _ p => letI := p.eqV; probes p.first p.second) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
    definition := none
    coordinates := #[0,1,2,3,4,5]
    readouts := #[{
      path := #["body","body","body","body","body","body","fn","arg","body","fn","arg","arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

namespace Restriction
structure Parameters where
  A : Type u
  E : Type v
  S : Set A
  first : E → S
  second : E → S
  target : S

abbrev signature : Signature where
  Params := Parameters.{u,v}
  State p := p.S
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev actual : Realization signature.{u,v} :=
  realize signature (fun _ p a => decide (Connected p.first p.second a p.target))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v}
  Law R := ∀ (p : Parameters.{u,v}) (a : p.S),
    R.readout () p a = true ↔
      Connected (fun e => (p.first e).val) (fun e => (p.second e).val) a.val p.target.val

theorem source_bridge : (type_of% (@restricted_endpoint_closure.{u,v})) ↔
    arena.{u,v}.Law actual := by
  constructor
  · intro h p a
    simpa [actual, realize] using h p.S p.first p.second a p.target
  · intro h A E S first second a b
    simpa [actual, realize] using h ⟨A,E,S,first,second,b⟩ a

private def emptyEdges : Parameters.{u,v} where
  A := ULift.{u} (Fin 2)
  E := ULift.{v} Empty
  S := Set.univ
  first := fun e => nomatch e.down
  second := fun e => nomatch e.down
  target := ⟨ULift.up 0, Set.mem_univ _⟩

private def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have he := (h emptyEdges emptyEdges.target).mpr (Relation.EqvGen.refl _)
  simp [rejected, realize] at he

def evidence : Registration arena.{u,v} (type_of% (@restricted_endpoint_closure.{u,v})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨source_bridge.mp (@restricted_endpoint_closure.{u,v}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro i; exact nomatch i
  dependence := by
    intro i
    let p := emptyEdges.{u,v}
    let a : p.S := ⟨ULift.up 0, Set.mem_univ _⟩
    let b : p.S := ⟨ULift.up 1, Set.mem_univ _⟩
    have yes : Connected p.first p.second a p.target := .refl _
    have no : ¬ Connected p.first p.second b p.target := by
      intro h
      have eq : ∀ {x y : p.S}, Connected p.first p.second x y → x = y := by
        intro x y hh
        induction hh with
        | rel x y h => obtain ⟨e, _⟩ := h; exact nomatch e.down
        | refl => rfl
        | symm x y h ih => exact ih.symm
        | trans x y z h1 h2 ih1 ih2 => exact ih1.trans ih2
      have he := congrArg (fun x : p.S => x.val.down) (eq h)
      change (1 : Fin 2) = 0 at he
      exact (by decide : (1 : Fin 2) ≠ 0) he
    refine ⟨p,a,b,?_⟩
    simp [actual, realize, yes, no]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@restricted_endpoint_closure.{u,v})
    (type_of% (realize signature.{u,v}
      (fun _ p a => decide (Connected p.first p.second a p.target))
      (fun e => nomatch e))) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence.restricted_endpoint_closure
  realizationName := `Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence.Restriction.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v}
    (fun _ p a => decide (Connected p.first p.second a p.target))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
    definition := none
    coordinates := #[0,1,2,3,4,6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end Restriction
#print axioms evidence
#print axioms registration
end Reg.D5.S3.Quantum.Reduction.FiniteEdgeProbeCorrespondence
