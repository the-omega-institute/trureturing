import D5.S0.Automata.FiniteKernelDFAO
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-!
# Source-occurrence audits for the finite-kernel/DFAO theorem

The helper audits observe the source sequence at its conclusion's kernel
argument, retaining every original type, base, sequence, digit and premise.
The equivalence audit observes the base at its left-hand automaticity
occurrence, retaining the original finite-alphabet telescope and both
predicates. Each actual law is definitionally the complete source statement.
The rejected families change only the selected occurrence.
-/

noncomputable section

namespace Reg.D5.S0.Automata.FiniteKernelDFAO

open _root_.D5.S0.Automata.FiniteKernelDFAO
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

abbrev sequenceSignature : Signature where
  Params := Type u
  State D := ℕ → D
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ D := ℕ → D
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev sequenceActual : Realization sequenceSignature.{u} :=
  realize sequenceSignature (fun _ _ a => a) (fun e => nomatch e)

abbrev sequenceRejected : Realization sequenceSignature.{u} :=
  realize sequenceSignature (fun _ _ a => fun _ => a 0) (fun e => nomatch e)

private theorem sequence_dependence : ObservationalDependence sequenceSignature.{u} sequenceActual := by
  intro i
  refine ⟨ULift.{u} ℕ, (fun n => ⟨n⟩), (fun _ => ⟨0⟩), ?_⟩
  intro h
  have hvalue := congrArg (fun f => (f 1).down) h
  exact Nat.one_ne_zero hvalue

private theorem sequence_sensitivity
    (law : Realization sequenceSignature.{u} → Prop)
    (hbad : ¬ law sequenceRejected) :
    Sensitivity ⟨sequenceSignature, law⟩ sequenceActual := by
  constructor
  · intro i
    refine ⟨sequenceRejected, ?_, rfl, hbad⟩
    intro j h
    exact (h (Subsingleton.elim _ _)).elim
  · intro e
    exact nomatch e

namespace Self

abbrev arena : Arena where
  signature := sequenceSignature.{u}
  Law R := ∀ {D : Type u} {q : ℕ} (a : ℕ → D),
    a ∈ kKernel q (R.readout () D a)

private theorem rejected_law : ¬ arena.{u}.Law sequenceRejected := by
  intro h
  let a : ℕ → ULift.{u} ℕ := fun n => ⟨n⟩
  obtain ⟨e, r, hr, heq⟩ := @h (ULift.{u} ℕ) 2 a
  have hvalue := congrArg (fun f => (f 1).down) heq
  change (1 : ℕ) = 0 at hvalue
  exact Nat.one_ne_zero hvalue

def family : Registration arena.{u} (type_of% (@chr_self_mem_kernel.{u})) where
  actual := sequenceActual
  bridge := Iff.rfl
  variation := ⟨@chr_self_mem_kernel.{u}, sequenceRejected, rejected_law⟩
  sensitivity := sequence_sensitivity _ rejected_law
  dependence := sequence_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@chr_self_mem_kernel.{u}) (Realization sequenceSignature.{u}) Type Unit where
  unitName := `D5.S0.Automata.FiniteKernelDFAO.chr_self_mem_kernel.__information_unit
  realizationName := `Reg.D5.S0.Automata.FiniteKernelDFAO.Self.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sequenceSignature
    (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.FiniteKernelDFAO
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Self

namespace Step

abbrev arena : Arena where
  signature := sequenceSignature.{u}
  Law R := ∀ {D : Type u} {q : ℕ} {a b : ℕ → D}
    (_hb : b ∈ kKernel q a) {j : ℕ} (_hj : j < q),
    (fun n => b (q * n + j)) ∈ kKernel q (R.readout () D a)

private theorem rejected_law : ¬ arena.{u}.Law sequenceRejected := by
  intro h
  let a : ℕ → ULift.{u} ℕ := fun n => ⟨n⟩
  have hb : a ∈ kKernel 2 a := chr_self_mem_kernel a
  obtain ⟨e, r, hr, heq⟩ := @h (ULift.{u} ℕ) 2 a a hb 0 (by decide)
  have hvalue := congrArg (fun f => (f 1).down) heq
  change (2 : ℕ) = 0 at hvalue
  omega

def family : Registration arena.{u} (type_of% (@chr_kernel_lam_mem.{u})) where
  actual := sequenceActual
  bridge := Iff.rfl
  variation := ⟨@chr_kernel_lam_mem.{u}, sequenceRejected, rejected_law⟩
  sensitivity := sequence_sensitivity _ rejected_law
  dependence := sequence_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,u+1,u,0,u,0,0}
    (@chr_kernel_lam_mem.{u}) (Realization sequenceSignature.{u}) Type Unit where
  unitName := `D5.S0.Automata.FiniteKernelDFAO.chr_kernel_lam_mem.__information_unit
  realizationName := `Reg.D5.S0.Automata.FiniteKernelDFAO.Step.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize sequenceSignature
    (fun _ _ a => a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.FiniteKernelDFAO
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Step

namespace Equivalence

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

abbrev actual : Realization signature :=
  realize signature (fun _ _ k => k) (fun e => nomatch e)

abbrev rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {B : Type} [Fintype B] (k : ℕ) (a : ℕ → B),
    IsKAutomatic (R.readout () () k) a ↔ IsKAutomaticSequence k a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmachine : IsKAutomaticSequence 2 (fun _ : ℕ => ()) := by
    refine ⟨by decide, 1, by decide, 0, (fun _ _ => 0), (fun _ => ()), ?_⟩
    intro n ds hds
    rfl
  have hbad := (h 2 (fun _ : ℕ => ())).mpr hmachine
  have hz : 2 ≤ 0 := hbad.1
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by decide⟩

def family : Registration arena (type_of% (@isKAutomatic_iff_isKAutomaticSequence)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@isKAutomatic_iff_isKAutomaticSequence, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity _ _ _ rejected_law
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@isKAutomatic_iff_isKAutomaticSequence) (Realization signature) Type Unit where
  unitName := `D5.S0.Automata.FiniteKernelDFAO.isKAutomatic_iff_isKAutomaticSequence.__information_unit
  realizationName := `Reg.D5.S0.Automata.FiniteKernelDFAO.Equivalence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ k => k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Automata.FiniteKernelDFAO
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Equivalence

end Reg.D5.S0.Automata.FiniteKernelDFAO

end
