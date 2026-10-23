import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open _root_.D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source)
open _root_.D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Address Reply readout)
open PresburgerPatternGrowth (Growth)

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
noncomputable section
set_option autoImplicit false

abbrev signature : Signature where
  Params := Address
  State _ := Source
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Reply
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ a P => readout a P) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => .alpha) (fun e => nomatch e)

abbrev arena.{u,v,w,z} : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {T : Type v} [Finite K] [Finite T]
    {X : K → Type w} {Y : T → Type z}
    (admitted : (k : K) → X k → Prop)
    (Theta : (k : K) → X k → Source)
    (Real : (t : T) → Y t → Address → Prop)
    (f : (k : K) → (t : T) → X k → Y t → Bool)
    (C s : K → T → Nat)
    (_growth : ∀ k t, Growth (f k t) (C k t) (s k t))
    (_source_cover : ∀ P : Source, ∃ k x, admitted k x ∧ Theta k x = P)
    (_address_cover : ∀ a : Address, ∃ t y, Real t y a)
    (_exactness : ∀ k t x y a, admitted k x → Real t y a →
      (f k t x y = true ↔ R.readout () a (Theta k x) = .alpha)), False

theorem rejected_law.{u,v,w,z} : ¬ arena.{u,v,w,z}.Law rejected := by
  intro h
  apply h (K := ULift.{u} Unit) (T := ULift.{v} Unit)
    (X := fun _ => ULift.{w} Source) (Y := fun _ => ULift.{z} Address)
    (fun _ _ => True) (fun _ x => x.down) (fun _ y a => y.down = a)
    (fun _ _ _ _ => true) (fun _ _ => 1) (fun _ _ => 0)
  · intro k t
    exact Growth.constant true
  · intro P
    exact ⟨⟨()⟩, ⟨P⟩, trivial, rfl⟩
  · intro a
    exact ⟨⟨()⟩, ⟨a⟩, rfl⟩
  · intro k t x y a ha hr
    simp [rejected, realize]

def registration.{u,v,w,z} : Registration arena.{u,v,w,z}
    (arena.{u,v,w,z}.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction.growth_obstruction,
    rejected, rejected_law.{u,v,w,z}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law.{u,v,w,z}⟩
      · intro j h
        exact (h (Subsingleton.elim j i)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨[], FreeMagma.of true, FreeMagma.of false, by
      simp [actual, realize, readout]⟩

noncomputable def registration_1.{u,v,w,z} : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction.growth_obstruction.{u,v,w,z})
    (type_of% (realize signature (fun _ a P => readout a P) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction.growth_obstruction.__information_unit,
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction.registration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u,v,w,z}⟩,
  objectArena := .source ⟨arena.{u,v,w,z}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u,v,w,z} ⟨registration.{u,v,w,z}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ a P => readout a P) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
    definition := none
    coordinates := #[19],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false
    }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
#print axioms registration_1
end
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativePolynomialDescriptorObstruction
