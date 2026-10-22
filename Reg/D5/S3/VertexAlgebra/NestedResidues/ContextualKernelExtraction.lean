import D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Mathlib.Algebra.Field.ULift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
/-! Dependent-family audit of complete contextual Hahn extraction. -/

noncomputable section
namespace Reg.D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
open _root_.D5.S3.VertexAlgebra
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.ContextualLaurentKernel
open NestedResidues.ContextualKernelExtraction
open CollisionLaurentKernels.LaurentCollision
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
universe u

structure Parameters where
  scalar : Type u
  field : Field scalar

structure Input (K : Type u) [Field K] where
  pre : ℕ
  post : ℕ
  r : ℤ
  W : HahnSeries (Indices ((pre + 2) + post)) K
  g : Indices ((pre + 2) + post)

def signature : Signature where
  Params := Parameters.{u}
  State p := @Input p.scalar p.field
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.scalar
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature.{u} (fun _ p x =>
  letI := p.field
  (show p.scalar from ∑ᶠ j : ℕ, ((-1 : p.scalar) ^ j * ((Ring.choose x.r j : ℤ) : p.scalar)) *
    x.W.coeff (x.g - pairIndex x.pre x.post (toLex ((j : ℤ), x.r - j)))))
  (fun empty => nomatch empty)

def rejected : Realization signature.{u} := realize signature.{u}
  (fun _ p _ => letI := p.field; (1 : p.scalar)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (x : @Input p.scalar p.field),
    letI := p.field
    Function.HasFiniteSupport (fun j : ℕ =>
      ((-1 : p.scalar) ^ j * ((Ring.choose x.r j : ℤ) : p.scalar)) *
        x.W.coeff (x.g - pairIndex x.pre x.post (toLex ((j : ℤ), x.r - j)))) ∧
    (contextPair p.scalar x.pre x.post (kernelZX p.scalar x.r) * x.W).coeff x.g =
      R.readout () p x

theorem source_bridge :
    (type_of% (@contextual_kernel_extraction.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p x
    letI := p.field
    exact h p.scalar x.pre x.post x.r x.W x.g
  · intro h K field pre post r W g
    exact h ⟨K, field⟩ ⟨pre, post, r, W, g⟩

theorem actual_law : arena.{u}.Law actual := source_bridge.mp (@contextual_kernel_extraction.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let p : Parameters.{u} := ⟨ULift.{u} ℚ, inferInstance⟩
  have bad := (h p ⟨0, 0, 0, 0, 0⟩).2
  have impossible : (0 : p.scalar) = 1 := by simpa [rejected, realize] using bad
  exact zero_ne_one impossible

theorem sensitivity : Sensitivity arena.{u} actual.{u} := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other h
      exact (h (show other = role from Unit.ext _ _)).elim
    · funext empty
      exact nomatch empty
  · intro empty
    exact nomatch empty

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  have role_eq : role = () := Unit.ext _ _
  subst role
  let p : Parameters.{u} := ⟨ULift.{u} ℚ, inferInstance⟩
  let zeroInput : @Input p.scalar p.field := ⟨0, 0, 0, 0, 0⟩
  let oneInput : @Input p.scalar p.field := ⟨0, 0, 0, 1, 0⟩
  refine ⟨p, zeroInput, oneInput, ?_⟩
  intro equal
  have hz := (actual_law p zeroInput).2
  have ho := (actual_law p oneInput).2
  have bad : (0 : p.scalar) = 1 := by
    rw [← hz, ← ho] at equal
    change (contextPair p.scalar 0 0 (kernelZX p.scalar 0) * 0).coeff 0 =
      (contextPair p.scalar 0 0 (kernelZX p.scalar 0) * 1).coeff 0 at equal
    rw [kernelZX_zpow, zpow_zero, map_one, mul_zero, mul_one] at equal
    simpa only [HahnSeries.coeff_zero, HahnSeries.coeff_one, ite_true] using equal
  exact zero_ne_one bad

def familyRegistration : Registration arena.{u} (type_of% (@contextual_kernel_extraction.{u})) where
  actual := actual.{u}
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

/- The packed state preserves the entire source telescope and both conclusions.
The original source occurrence and its escape origin still need a lawful
source-selection binding; the proof record alone supplies no such binding. -/
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contextual_kernel_extraction.{u}) (type_of% (realize signature.{u} actual.{u}.readout actual.{u}.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction.contextual_kernel_extraction
    "__information_unit"
  realizationName := `Reg.D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} actual.{u}.readout actual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
