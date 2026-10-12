import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeDepthPatterns (Pattern Frontier fill)
open D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection

abbrev signature : Signature where
  Params := Σ m : Nat, Σ d : Fin m → Nat, (i : Fin m) → Pattern (d i)
  State p := Fin p.1 → Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := MixedExpr (Fin p.1) → Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => eval z) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : Nat) (d : Fin m → Nat) (p : (i : Fin m) → Pattern (d i))
    (_live : ∀ i, Nonempty (Frontier (p i))) (A B : MixedExpr (Fin m)),
    (∀ w : (i : Fin m) → Frontier (p i) → Source,
      R.readout () ⟨m,d,p⟩ (fun i => fill (p i) (w i)) A =
      R.readout () ⟨m,d,p⟩ (fun i => fill (p i) (w i)) B) →
    ∀ z : Fin m → Source, R.readout () ⟨m,d,p⟩ z A = R.readout () ⟨m,d,p⟩ z B

private theorem bridge : (type_of% (@prefix_identity_reflection)) ↔ arena.Law actual := Iff.rfl
private theorem actual_law : arena.Law actual := @prefix_identity_reflection

private def rootTag : Source → Source
  | .of b => .of b
  | .mul _ _ => .mul (.of true) (.of true)

def bad : Realization signature :=
  realize signature (fun _ _ z E => rootTag (eval z E)) (fun e => nomatch e)

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  let p : (i : Fin 1) → Pattern 1 := fun _ => Sum.inr ((),())
  let A : MixedExpr (Fin 1) := .residual 0 0
  let B : MixedExpr (Fin 1) := .ground (.mul (.of true) (.of true))
  have live : ∀ i, Nonempty (Frontier (p i)) := fun _ => ⟨Sum.inl ()⟩
  have cylinder : ∀ w : (i : Fin 1) → Frontier (p i) → Source,
      bad.readout () ⟨1,(fun _ => 1),p⟩ (fun i => fill (p i) (w i)) A =
      bad.readout () ⟨1,(fun _ => 1),p⟩ (fun i => fill (p i) (w i)) B := by
    intro w; rfl
  have no := h 1 (fun _ => 1) p live A B cylinder (fun _ => .of true)
  change FreeMagma.of true = FreeMagma.mul (.of true) (.of true) at no
  cases no

def proof : Registration arena (type_of% (@prefix_identity_reflection)) where
  actual := actual
  bridge := bridge
  variation := ⟨actual_law,bad,bad_law⟩
  sensitivity := ⟨fun i => ⟨bad,fun j h => (h (Subsingleton.elim j i)).elim,rfl,bad_law⟩,
    fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨⟨1,(fun _ => 0),(fun _ => ())⟩,
      (fun _ => .of true),(fun _ => .of false),?_⟩
    intro eq
    have no := congrFun eq (MixedExpr.residual 0 0)
    change FreeMagma.of true = FreeMagma.of false at no
    cases no

noncomputable def prefix_identity_reflection_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.prefix_identity_reflection)
    (Realization signature) (Nat → Type) Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.prefix_identity_reflection
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection.proof
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => eval z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","fn","arg","fn"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms prefix_identity_reflection_registration

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePrefixIdentityReflection
