import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
import Reg.Support.DependentFamily


set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
open _root_.D5.S3.Arith.FibonacciAtomic
open Observer.NativeControlConjugacy
open Observer.NativeSerialMachine
open GenealogicalFiberTransport (Source)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ C : Type, Σ D : Type, Σ O : Type, Σ _ : C ≃ D, C → Op C O

abbrev signature : Signature where
  Params := Parameters
  State p := Config p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Option (Config p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p => nativeStep p.2.2.2.2) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => none) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {C D O : Type} (e : C ≃ D) (δ : C → Op C O),
    (∀ c, reindex e δ (e c) = mapOp e (δ c)) ∧
    (∀ x, nativeStep (reindex e δ) (mapConfig e x) =
      (R.readout () ⟨C, D, O, e, δ⟩ x).map (mapConfig e)) ∧
    (∀ c j u t o, Run (reindex e δ) (e c) j u t o ↔ Run δ c j u t o) ∧
    (∀ (x y : Config C) (n : Nat),
      (advance (reindex e δ))^[n] (some (mapConfig e x)) = some (mapConfig e y) ↔
        (advance δ)^[n] (some x) = some y) ∧
    (∀ c o, reindex e δ (e c) = .stop o ↔ δ c = .stop o) ∧
    (∀ c j u n o, Remaining (reindex e δ) (e c) j u n o ↔ Remaining δ c j u n o) ∧
    (∀ c j u t s o b, Run δ c j u t o → Run δ c j u s b → t = s ∧ o = b) ∧
    (∀ c j u t s o b m, Run δ c j u t o → Run (reindex e δ) (e c) j u s b →
      t = s ∧ o = b ∧ ∀ i : Fin 5, cost m t i = cost m s i)

private theorem negative : ¬ arena.Law rejected := by
  intro law
  have broken := (law (C := Unit) (D := Unit) (O := Unit) (Equiv.refl Unit)
    (fun _ => Op.applyRho ())).2.1 ((),0,(.of true : Source),[])
  change some ((),1,_,[Event.update 0]) = (none : Option (Config Unit)) at broken
  cases broken

def evidence : Registration arena (type_of% (@native_control_conjugacy)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_control_conjugacy, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, negative⟩
      · intro j different; exact (different (Subsingleton.elim _ _)).elim
      · funext e; exact nomatch e
    · intro e; exact nomatch e
  dependence := by
    intro i
    let p : Parameters := ⟨Unit,Unit,Unit,Equiv.refl Unit,fun _ => Op.applyRho ()⟩
    refine ⟨p, ((),0,(.of true : Source),[]), ((),1,(.of true : Source),[]), ?_⟩
    intro same
    have epochs := congrArg (fun x : Option (Config Unit) => x.map (fun y => y.2.1)) same
    change some 1 = some 2 at epochs
    cases epochs

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_control_conjugacy) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy.native_control_conjugacy.__information_unit
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
    definition := none
    coordinates := #[0,1,2,3,4]
    readouts := #[{ path := #["body","body","body","body","body","arg","fn","arg","body","arg","arg"], stateBinder := 0, functionOperand := false, stateOperand := some #["arg"], booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeControlConjugacy
