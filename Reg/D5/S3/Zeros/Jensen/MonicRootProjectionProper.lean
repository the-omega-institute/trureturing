import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.MonicRootProjectionProper
import Reg.Support.DependentFamily

open _root_.D5.S3.Zeros.Jensen.MonicRootProjectionProper
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial

namespace Reg.D5.S3.Zeros.Jensen.MonicRootProjectionProper
noncomputable section
universe u

structure SourceInputs where
  A : Type u
  topology : TopologicalSpace A
  P : A → Polynomial ℂ

abbrev ZeroGraph (p : SourceInputs.{u}) :=
  {e : p.A × ℂ // (p.P e.1).eval e.2 = 0}

instance zeroGraphTopology (p : SourceInputs.{u}) : TopologicalSpace (ZeroGraph p) :=
  letI := p.topology
  inferInstance

abbrev signature : Signature where
  Params := SourceInputs.{u}
  State p := ZeroGraph p → p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p f => letI := p.topology; IsProperMap f)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => False) (fun e => nomatch e)

/-- Every source type, topology, polynomial and premise is retained. The selected
operand is the properness predicate on maps from the same zero graph to A. -/
def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {A : Type u} [top : TopologicalSpace A] [T2Space A]
    [CompactlyCoherentSpace A] (P : A → Polynomial ℂ) (q : ℕ)
    (hmonic : ∀ t, (P t).Monic) (hdegree : ∀ t, (P t).natDegree = q)
    (hc : ∀ i ≤ q, Continuous (fun t => (P t).coeff i)),
    R.readout () ⟨A,top,P⟩ (fun e => e.1.1)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance inferInstance
    (fun _ => (X : Polynomial ℂ)) 1 (fun _ => monic_X)
    (fun _ => by simp) (fun _ _ => continuous_const)

def complexInputs : SourceInputs.{u} :=
  ⟨ULift.{u} ℂ, inferInstance, fun _ => X⟩

private theorem constant_not_proper :
    ¬ IsProperMap (fun _ : ZeroGraph complexInputs.{u} =>
      (⟨0⟩ : ULift.{u} ℂ)) := by
  intro h
  letI : CompactSpace (ZeroGraph complexInputs.{u}) :=
    (isProperMap_const_iff (⟨0⟩ : ULift.{u} ℂ)).mp h
  have hsurj : Function.Surjective
      (fun e : ZeroGraph complexInputs.{u} => e.1.1.down) := by
    intro t
    exact ⟨⟨(⟨t⟩,0),by simp [complexInputs]⟩,rfl⟩
  have hcont : Continuous
      (fun e : ZeroGraph complexInputs.{u} => e.1.1.down) := by fun_prop
  have hcompact : CompactSpace ℂ := hsurj.compactSpace hcont
  exact (not_compactSpace_iff.mpr (inferInstance : NoncompactSpace ℂ)) hcompact

def registration : Registration arena.{u}
    (type_of% (@monic_fixed_degree_root_projection_isProper.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨monic_fixed_degree_root_projection_isProper, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨complexInputs, (fun e => e.1.1), (fun _ => ⟨0⟩), ?_⟩
    change IsProperMap
        (fun e : {p : ULift.{u} ℂ × ℂ // (X : Polynomial ℂ).eval p.2 = 0} => e.1.1) ≠
      IsProperMap
        (fun _ : {p : ULift.{u} ℂ × ℂ // (X : Polynomial ℂ).eval p.2 = 0} =>
          (⟨0⟩ : ULift.{u} ℂ))
    intro he
    have hp := monic_fixed_degree_root_projection_isProper
        (A := ULift.{u} ℂ) (fun _ => X) 1
        (fun _ => monic_X) (fun _ => by simp) (fun _ _ => continuous_const)
    exact constant_not_proper (Eq.mp he hp)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monic_fixed_degree_root_projection_isProper.{u})
    (type_of% (realize signature.{u}
      (fun _ p f => letI := p.topology; IsProperMap f) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Zeros.Jensen.MonicRootProjectionProper.monic_fixed_degree_root_projection_isProper.audit
  realizationName := `Reg.D5.S3.Zeros.Jensen.MonicRootProjectionProper.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p f => letI := p.topology; IsProperMap f) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.MonicRootProjectionProper
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit
end
end Reg.D5.S3.Zeros.Jensen.MonicRootProjectionProper
