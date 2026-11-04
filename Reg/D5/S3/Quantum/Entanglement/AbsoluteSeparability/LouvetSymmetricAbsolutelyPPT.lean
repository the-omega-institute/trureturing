import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the public theorems in the mirrored owner. -/

set_option linter.style.longLine false

set_option pp.proofs false in
#print D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.occupation_fiber_card

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
end
end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT

set_option pp.proofs false in
#print D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant

namespace Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
open _root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.SymmetricAbsolutePPTPermutationFloor
open _root_.D5.S3.Quantum.Entanglement.OccupancyWordSectors
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
noncomputable section
namespace SymmetricOccupationConstant

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ N : ℕ, Σ d : ℕ, Fin N → Fin d)
    (fun p => Fin p.1 → Fin p.2.1) (fun p => Multiset (Fin p.2.1))
def actual : Realization signature :=
  realize signature (fun _ _ x => occupation x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ p _ => occupation p.2.2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ} (v : (Fin N → Fin d) → ℂ)
    (_hv : IsSymmetricVector v) (x y : Fin N → Fin d)
    (_h : R.readout () ⟨N, d, y⟩ x = occupation y), v x = v y

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let v : (Fin 1 → Fin 2) → ℂ := fun x => if x 0 = 0 then 0 else 1
  have hv : IsSymmetricVector v := by
    intro σ x
    have hs : σ = Equiv.refl _ := Subsingleton.elim _ _
    subst σ
    rfl
  have hb := h v hv (fun _ => 0) (fun _ => 1) rfl
  norm_num [v] at hb

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 2, fun _ => 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change occupation (fun _ : Fin 1 => (0 : Fin 2)) ≠ occupation (fun _ : Fin 1 => 1)
  decide

def source_registration : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.symmetric_occupation_constant.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT.SymmetricOccupationConstant.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => occupation x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms source_registration
#print axioms registration

end SymmetricOccupationConstant

end
end Reg.D5.S3.Quantum.Entanglement.AbsoluteSeparability.LouvetSymmetricAbsolutelyPPT
