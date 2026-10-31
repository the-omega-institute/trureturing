import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_fiber_card
set_option pp.proofs false in
#print D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_same_orbit

namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT

open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open _root_.D5.S3.Quantum.Entanglement.OccupancyWordSectors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace FiberCard

attribute [local instance] Classical.propDecidable

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ N : ℕ, Σ d : ℕ, Fin N → Fin d)
    (fun p => Fin p.2.1) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ p a => (occupation p.2.2).count a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ} (x : Fin N → Fin d) (a : Fin d),
    Fintype.card {i // x i = a} = R.readout () ⟨N, d, x⟩ a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ : Fin 1 => (0 : Fin 1)) 0
  change Fintype.card {i : Fin 1 // (0 : Fin 1) = 0} = 0 at hb
  simp at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 2, fun _ => 0⟩, 0, 1, ?_⟩
  change (occupation (fun _ : Fin 1 => (0 : Fin 2))).count 0 ≠
    (occupation (fun _ : Fin 1 => (0 : Fin 2))).count 1
  norm_num [occupation, List.ofFn_succ]

def source_registration : Registration arena (type_of% @occupation_fiber_card) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupation_fiber_card, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@occupation_fiber_card) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_fiber_card.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.FiberCard.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => (occupation p.2.2).count a)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end FiberCard

namespace SameOrbit

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature
    (Σ N : ℕ, Σ d : ℕ, Fin N → Fin d)
    (fun p => Equiv.Perm (Fin p.1)) (fun p => Fin p.1 → Fin p.2.1)

def actual : Realization signature :=
  realize signature (fun _ p σ => p.2.2 ∘ σ) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => p.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ} (x y : Fin N → Fin d), occupation x = occupation y →
    ∃ σ : Equiv.Perm (Fin N), R.readout () ⟨N, d, y⟩ σ = x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have ho : occupation (fun i : Fin 2 => i) =
      occupation (fun i : Fin 2 => Equiv.swap (0 : Fin 2) 1 i) := by decide
  obtain ⟨σ, hb⟩ := h (fun i : Fin 2 => i) (fun i => Equiv.swap (0 : Fin 2) 1 i) ho
  have he := congrFun hb 0
  change Equiv.swap (0 : Fin 2) 1 0 = 0 at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 2, fun j => j⟩, Equiv.refl _, Equiv.swap 0 1, ?_⟩
  intro h
  have he := congrFun h 0
  change (0 : Fin 2) = Equiv.swap (0 : Fin 2) 1 0 at he
  norm_num at he

def source_registration : Registration arena (type_of% @occupation_same_orbit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@occupation_same_orbit, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@occupation_same_orbit) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_same_orbit.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.SameOrbit.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p σ => p.2.2 ∘ σ) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end SameOrbit
end
end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
