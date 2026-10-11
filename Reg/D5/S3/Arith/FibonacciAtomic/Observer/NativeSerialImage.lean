import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport (Source substitution)
open D5.S3.Arith.FibonacciAtomic.ActualTreeReadoutAcquisition (Reply)
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialMachine
open D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage

abbrev traceSignature : Signature where
  Params := Unit
  State _ := Trace
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Trace
  Anchor := Empty
  finiteAnchor := inferInstance

def traceActual : Realization traceSignature :=
  realize traceSignature (fun _ _ t => t) (fun e => nomatch e)

def traceBad : Realization traceSignature :=
  realize traceSignature (fun _ _ _ => [.localStep]) (fun e => nomatch e)

abbrev prefixArena : Arena where
  signature := traceSignature
  Law R := ∀ {C O : Type} {δ : C → Op C O} {c : C} {N : Nat} {u v : Source}
    {t s : Trace} {o p : O}, Run δ c N u t o → Run δ c N v s p →
      answers t <+: answers s → R.readout () () t = s ∧ o = p

private theorem prefix_bad : ¬ prefixArena.Law traceBad := by
  intro h
  have bad := (@h Unit Unit (fun _ => .stop ()) () 0 (.of true) (.of false)
    [] [] () () (Run.stop rfl) (Run.stop rfl) (by simp [answers,reads])).1
  cases bad

def prefixProof : Registration prefixArena (type_of% (@terminal_prefix_free)) where
  actual := traceActual
  bridge := Iff.rfl
  variation := ⟨@terminal_prefix_free,traceBad,prefix_bad⟩
  sensitivity := ⟨fun i => ⟨traceBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,prefix_bad⟩,fun i => nomatch i⟩
  dependence := by intro i; exact ⟨(),[],[.localStep],by simp [traceActual,realize]⟩

abbrev countSignature : Signature where
  Params := Type
  State O := Finset O
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ labels => labels.card) (fun e => nomatch e)

def countBad : Realization countSignature :=
  realize countSignature (fun _ _ labels => labels.card+1) (fun e => nomatch e)

abbrev imageArena : Arena where
  signature := countSignature
  Law R := ∀ {C O : Type} (δ : C → Op C O) (c : C) (N K : Nat)
    (U : Set Source), U.Nonempty → ∀ F : Source → O,
    (∀ u ∈ U, ∃ t, Run δ c N (substitution^[N] u) t (F u) ∧ (answers t).length ≤ K) →
    ∃ labels : Finset O, R.readout () O labels ≤ 4^K ∧ ∀ u ∈ U, F u ∈ labels

private theorem image_bad : ¬ imageArena.Law countBad := by
  intro h
  obtain ⟨labels,bound,cover⟩ := @h Unit Unit (fun _ => .stop ()) () 0 0
    Set.univ ⟨.of true,Set.mem_univ _⟩ (fun _ => ()) (by
      intro u _; exact ⟨[],Run.stop rfl,by simp [answers,reads]⟩)
  have mem := cover (.of true) (Set.mem_univ _)
  have pos : 0 < labels.card := Finset.card_pos.mpr ⟨(),mem⟩
  change labels.card+1 ≤ 4^0 at bound
  have small : labels.card+1 ≤ 1 := by simpa only [pow_zero] using bound
  omega

def imageProof : Registration imageArena (type_of% (@bounded_serial_output_image)) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨@bounded_serial_output_image,countBad,image_bad⟩
  sensitivity := ⟨fun i => ⟨countBad,
    fun j h => (h (Subsingleton.elim j i)).elim,rfl,image_bad⟩,fun i => nomatch i⟩
  dependence := by intro i; exact ⟨Unit,∅,{()},by simp [countActual,realize]⟩

noncomputable def terminal_prefix_free_registration : LeanInformationAudit.Contract.Registration.{0,1,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.terminal_prefix_free)
    (Realization traceSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.terminal_prefix_free
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.prefixProof
  realizationSource := none
  generated := false
  arena := .source ⟨prefixArena⟩
  objectArena := .source ⟨prefixArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source prefixArena ⟨prefixProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize traceSignature traceActual.readout traceActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","body","body","body","body","fn","arg","fn","arg"], stateBinder := 7, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def bounded_serial_output_image_registration : LeanInformationAudit.Contract.Registration.{1,1,1,0,0,0,1,0,0,0,0,0}
    (@_root_.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.bounded_serial_output_image)
    (Realization countSignature) Type Unit where
  unitName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.bounded_serial_output_image
  realizationName := `Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage.imageProof
  realizationSource := none
  generated := false
  arena := .source ⟨imageArena⟩
  objectArena := .source ⟨imageArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source imageArena ⟨imageProof⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body","body","body","body","body","body","body","body","body","body","arg","body","fn","arg","fn","arg"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.FibonacciAtomic.Observer.NativeSerialImage
