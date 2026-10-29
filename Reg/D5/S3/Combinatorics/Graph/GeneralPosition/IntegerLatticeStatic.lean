import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
open _root_.IntegerLatticeStatic
namespace Upper
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Finset (Fin (n + 1) → ℤ)) (fun _ => ℕ)
def observation : ∀ (_ : Unit) n, signature.State n → ℕ := fun _ _ S => S.card
def actual : Realization signature := realize signature observation (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, ∅, {fun _ => 0}, ?_⟩
  change (∅ : Finset (Fin 1 → ℤ)).card ≠ ({fun _ => 0} : Finset (Fin 1 → ℤ)).card
  simp
def rejected : Realization signature :=
  realize signature (fun _ n _ => 2 ^ (2 ^ n) + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {S : Finset (Fin (n + 1) → ℤ)},
    CoordinateGP S → R.readout () n S ≤ 2 ^ (2 ^ n)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  have hh := h (n := 0) (S := ∅) (by simp [CoordinateGP])
  change 2 ^ (2 ^ 0) + 1 ≤ 2 ^ (2 ^ 0) at hh
  norm_num at hh
def family : Registration arena (type_of% (@_root_.IntegerLatticeStatic.card_le)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.IntegerLatticeStatic.card_le, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@IntegerLatticeStatic.card_le) (Realization signature) Unit Unit where
  unitName := `IntegerLatticeStatic.card_le.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic.Upper.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end Upper
namespace Attainment
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ
    (fun n => Finset (Fin (n + 1) → ℤ)) (fun _ => ℕ)
def observation : ∀ (_ : Unit) n, signature.State n → ℕ := fun _ _ S => S.card
def actual : Realization signature := realize signature observation (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, ∅, {fun _ => 0}, ?_⟩
  change (∅ : Finset (Fin 1 → ℤ)).card ≠ ({fun _ => 0} : Finset (Fin 1 → ℤ)).card
  simp
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, ∃ S : Finset (Fin (n + 1) → ℤ),
    CoordinateGP S ∧ R.readout () n S = 2 ^ (2 ^ n) ∧ S.Nonempty ∧
    (∀ x ∈ S, ∀ j, 0 ≤ x j ∧ x j < (2 ^ (2 ^ n) : ℕ)) ∧
    ∀ j, Set.InjOn (fun x : Fin (n + 1) → ℤ => x j) (S : Set _)
private theorem rejectedLaw : ¬ arena.Law rejected := by
  intro h
  obtain ⟨S, _, hcard, _⟩ := h 0
  change 0 = 2 ^ (2 ^ 0) at hcard
  norm_num at hcard
def family : Registration arena (type_of% (@_root_.IntegerLatticeStatic.exists_attaining)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨_root_.IntegerLatticeStatic.exists_attaining, rejected, rejectedLaw⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejectedLaw
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@IntegerLatticeStatic.exists_attaining) (Realization signature) Unit Unit where
  unitName := `IntegerLatticeStatic.exists_attaining.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic.Attainment.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","arg","body","arg","fn","arg","fn","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms family
#print axioms audit
end Attainment
end Reg.D5.S3.Combinatorics.Graph.GeneralPosition.IntegerLatticeStatic
