import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.CompactEigenbasis
import Reg.Support.DependentFamily
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false
open scoped InnerProductSpace Classical
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit D5.S3.Quantum.Analysis.CompactEigenbasis
noncomputable section
universe u

namespace Reg.D5.S3.Quantum.Analysis.CompactEigenbasis

structure Carrier where
  scalar : Type
  [rclike : RCLike scalar]
  E : Type u
  [normed : NormedAddCommGroup E]
  [inner : InnerProductSpace scalar E]
  [complete : CompleteSpace E]
attribute [instance] Carrier.normed Carrier.inner Carrier.complete

abbrev Operator (p : Carrier.{u}) :=
  letI := p.rclike
  p.E →L[p.scalar] p.E

abbrev signature : Signature where
  Params := Carrier.{u}
  State p := Operator p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def predicate (p : Carrier.{u}) (T : Operator p) : Prop :=
  letI := p.rclike
  ∃ (w : Set p.E) (b : HilbertBasis w p.scalar p.E) (s : w → ℝ),
    ∀ i, T (b i) = (s i : p.scalar) • b i

def actual := realize signature.{u} (fun _ p T => predicate p T) (fun e => nomatch e)
def rejected := realize signature.{u} (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Carrier.{u}) (T : Operator p),
    letI := p.rclike
    IsCompactOperator T → T.IsSymmetric → R.readout () p T

private theorem actual_law : arena.{u}.Law actual := by
  intro p T
  letI := p.rclike
  intro hc hs
  exact exists_setIndex_real_eigenbasis_rclike hc hs

abbrev K := EuclideanSpace ℂ (ULift.{u} Unit)
abbrev sample : Carrier.{u} := ⟨ℂ,K⟩
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h sample 0 isCompactOperator_zero (by intro x y; simp)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨sample,0,Complex.I • (1 : K →L[ℂ] K),?_⟩
  change predicate sample 0 ≠ predicate sample (Complex.I • (1 : K →L[ℂ] K))
  intro h
  have hg : predicate sample 0 := actual_law sample 0 isCompactOperator_zero
    (by intro x y; simp)
  obtain ⟨w,b,s,he⟩ := Eq.mp h hg
  haveI : IsEmpty w := ⟨fun j => by
    have hj := he j
    change Complex.I • b j = (s j : ℂ) • b j at hj
    have heq : Complex.I = (s j : ℂ) :=
      (smul_left_injective ℂ (b.orthonormal.ne_zero j)) hj
    have him := congrArg Complex.im heq
    simp at him⟩
  have hz (x : K) : x = 0 := by
    exact (b.hasSum_repr x).unique hasSum_empty
  have hf := congrArg (fun v : K => v ⟨()⟩) (hz (WithLp.toLp 2 (fun _ => 1)))
  simpa using hf

def familyRegistration : Registration arena
    (type_of% (@exists_setIndex_real_eigenbasis_rclike.{u})) where
  actual := actual
  bridge := by
    constructor
    · intro h p T
      letI := p.rclike
      intro hc hs
      exact h hc hs
    · intro h scalar _ E _ _ _ T hc hs
      exact h ⟨scalar,E⟩ T hc hs
  variation := ⟨actual_law,rejected,rejected_law⟩
  sensitivity := ⟨by
    intro i
    refine ⟨rejected,?_,rfl,rejected_law⟩
    intro j hji
    exact (hji (Subsingleton.elim j i)).elim,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@D5.S3.Quantum.Analysis.CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike.{u})
    (type_of% (realize signature.{u} (fun _ p T => predicate p T) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.CompactEigenbasis.compactBasisUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.CompactEigenbasis.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p T => predicate p T) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.CompactEigenbasis
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.CompactEigenbasis
