import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.Products.LatticeRouting
import Mathlib.Tactic.NormNum

/-! Integer-state readouts for the exact rotation identity. -/

set_option autoImplicit false

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Products.LatticeRouting
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Combinatorics.Graph.Products.LatticeRouting.Rotation

/-- The second input is a parameter; the first is the observed integer state. -/
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ b a => max |a + b| |a - b|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ a b : ℤ, r.readout () b a = |a| + |b|

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h 1 0
  norm_num [rejected, realize] at hbad

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨0, 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena (type_of% rotation_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rotation_identity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim (α := Unit) other role)).elim
    · intro anchor
      exact nomatch anchor
  dependence := actual_dependence

def rotationRegistration :
    Contract.Registration rotation_identity (Realization signature) Type Unit where
  unitName := `D5.S3.Combinatorics.Graph.Products.LatticeRouting.rotation_identity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Products.LatticeRouting.Rotation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b a => max |a + b| |a - b|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Products.LatticeRouting
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.Products.LatticeRouting.Rotation
