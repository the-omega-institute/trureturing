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

/- The prior packed family and its proof evidence above are retained.
The source family below observes the original integer binomial on the RHS.
These Reg helpers are audit evidence, not new D5 results. -/
namespace SourceBinomial

def signature : Signature where
  Params := ℤ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ r j => (Ring.choose r j : ℤ)) (fun empty => nomatch empty)

def rejected : Realization signature := realize signature
  (fun _ _ _ => (0 : ℤ)) (fun empty => nomatch empty)

def arena : Arena where
  signature := signature
  Law R := ∀ (K : Type u) [Field K] (pre post : ℕ) (r : ℤ)
    (W : HahnSeries (Indices ((pre + 2) + post)) K)
    (g : Indices ((pre + 2) + post)),
    Function.HasFiniteSupport (fun j : ℕ =>
      ((-1 : K) ^ j * ((Ring.choose r j : ℤ) : K)) *
        W.coeff (g - pairIndex pre post (toLex ((j : ℤ), r - j)))) ∧
    (contextPair K pre post (kernelZX K r) * W).coeff g =
      ∑ᶠ j : ℕ, ((-1 : K) ^ j * (Int.cast (R.readout () r j) : K)) *
        W.coeff (g - pairIndex pre post (toLex ((j : ℤ), r - j)))

theorem source_bridge :
    (type_of% (@contextual_kernel_extraction.{u})) ↔ arena.{u}.Law actual := Iff.rfl

theorem actual_law : arena.{u}.Law actual :=
  source_bridge.mp (@contextual_kernel_extraction.{u})

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let K := ULift.{u} ℚ
  have bad := (h K 0 0 0 (1) 0).2
  rw [kernelZX_zpow, zpow_zero, map_one, mul_one] at bad
  have impossible : (1 : K) = 0 := by
    simpa only [rejected, realize, Int.cast_zero, mul_zero, zero_mul, finsum_zero,
      HahnSeries.coeff_one, ite_true] using bad
  exact one_ne_zero impossible

theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro role
    refine ⟨rejected, ?_, ?_, rejected_law⟩
    · intro other h
      exact (h (show other = role from Unit.ext _ _)).elim
    · funext empty
      exact nomatch empty
  · intro empty
    exact nomatch empty

theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(0 : ℤ), (0 : ℕ), (1 : ℕ), ?_⟩
  change (Ring.choose (0 : ℤ) 0 : ℤ) ≠ Ring.choose (0 : ℤ) 1
  simpa only [Ring.choose_zero_right, Ring.choose_one_right] using
    (one_ne_zero : (1 : ℤ) ≠ 0)

def familyRegistration : Registration arena.{u} (type_of% (@contextual_kernel_extraction.{u})) where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

end SourceBinomial

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@contextual_kernel_extraction.{u})
    (type_of% (realize SourceBinomial.signature
      SourceBinomial.actual.readout SourceBinomial.actual.anchor))
    Type Unit where
  unitName := Lean.Name.str
    `D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction.contextual_kernel_extraction
    "__information_unit"
  realizationName :=
    `Reg.D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction.SourceBinomial.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨SourceBinomial.arena.{u}⟩
  objectArena := .source ⟨SourceBinomial.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source SourceBinomial.arena.{u} ⟨SourceBinomial.familyRegistration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize SourceBinomial.signature
    SourceBinomial.actual.readout SourceBinomial.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[{ name := `autoImplicit, value := .bool false }]

end Reg.D5.S3.VertexAlgebra.NestedResidues.ContextualKernelExtraction
