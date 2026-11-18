import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Matrix

noncomputable section

abbrev signature (X : ℕ × ℕ → Type) : Signature :=
  Reg.Support.SingleDependentReadout.signature (ℕ × ℕ) X (fun p => X p → Prop)

def actual (X : ℕ × ℕ → Type) : Realization (signature X) :=
  realize (signature X) (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected (X : ℕ × ℕ → Type) : Realization (signature X) :=
  realize (signature X) (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem dependence (X : ℕ × ℕ → Type) (p : ℕ × ℕ)
    (x y : X p) (hxy : x ≠ y) : ObservationalDependence (signature X) (actual X) := by
  intro i
  refine ⟨p, x, y, ?_⟩
  intro he
  exact hxy (Eq.mp (congrFun he x) rfl).symm

abbrev factorOutput (p : ℕ × ℕ) := Fin p.1
abbrev coordOutput (p : ℕ × ℕ) := Fin p.2
abbrev scalarOutput (_ : ℕ × ℕ) := ℂ
abbrev flatOutput (p : ℕ × ℕ) := Fin (2 * p.1) → Fin p.2
abbrev positionOutput (p : ℕ × ℕ) := Fin (2 * p.1)
abbrev matrixOutput (p : ℕ × ℕ) := Matrix (Index p.1 p.2) (Index p.1 p.2) ℂ

private theorem factor_dependence : ObservationalDependence (signature factorOutput) (actual factorOutput) :=
  dependence _ (2, 2) 0 1 (by decide)
private theorem coord_dependence : ObservationalDependence (signature coordOutput) (actual coordOutput) :=
  dependence _ (1, 2) 0 1 (by decide)
private theorem scalar_dependence : ObservationalDependence (signature scalarOutput) (actual scalarOutput) :=
  dependence _ (1, 2) 0 1 (by norm_num)
private theorem position_dependence : ObservationalDependence (signature positionOutput) (actual positionOutput) :=
  dependence _ (1, 2) 0 1 (by decide)
private theorem flat_dependence : ObservationalDependence (signature flatOutput) (actual flatOutput) := by
  apply dependence _ (1, 2) (fun _ => 0) (fun _ => 1)
  intro h
  have hh := congrFun h 0
  exact (by decide : (0 : Fin 2) ≠ 1) hh
private theorem matrix_dependence : ObservationalDependence (signature matrixOutput) (actual matrixOutput) := by
  apply dependence _ (0, 0) 0 1
  intro h
  have hh := congrArg (fun M : Matrix (Index 0 0) (Index 0 0) ℂ =>
    M (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)) h
  norm_num at hh

namespace party_ketPos
abbrev arena : Arena where
  signature := signature factorOutput
  Law R := ∀ {r : ℕ} (k : Fin r), R.readout () (r, 0) (party (ketPos k)) k
private theorem rejected_law : ¬ arena.Law (rejected factorOutput) := by
  intro h
  exact @h 1 0
def source_registration : Registration arena (type_of% @party_ketPos) where
  actual := actual factorOutput
  bridge := Iff.rfl
  variation := ⟨@party_ketPos, rejected factorOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := factor_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.party_ketPos)
    (Realization (signature factorOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.party_ketPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.party_ketPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual factorOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end party_ketPos

namespace party_braPos
abbrev arena : Arena where
  signature := signature factorOutput
  Law R := ∀ {r : ℕ} (k : Fin r), R.readout () (r, 0) (party (braPos k)) k
private theorem rejected_law : ¬ arena.Law (rejected factorOutput) := by
  intro h
  exact @h 1 0
def source_registration : Registration arena (type_of% @party_braPos) where
  actual := actual factorOutput
  bridge := Iff.rfl
  variation := ⟨@party_braPos, rejected factorOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := factor_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.party_braPos)
    (Realization (signature factorOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.party_braPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.party_braPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual factorOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end party_braPos

namespace merge_ketPos
abbrev arena : Arena where
  signature := signature coordOutput
  Law R := ∀ {r d : ℕ} (a b : Index r d) (k : Fin r), R.readout () (r, d) (merge a b (ketPos k)) (a k)
private theorem rejected_law : ¬ arena.Law (rejected coordOutput) := by
  intro h
  exact @h 1 2 (fun _ => 0) (fun _ => 0) 0
def source_registration : Registration arena (type_of% @merge_ketPos) where
  actual := actual coordOutput
  bridge := Iff.rfl
  variation := ⟨@merge_ketPos, rejected coordOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coord_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.merge_ketPos)
    (Realization (signature coordOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_ketPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_ketPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual coordOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end merge_ketPos

namespace merge_braPos
abbrev arena : Arena where
  signature := signature coordOutput
  Law R := ∀ {r d : ℕ} (a b : Index r d) (k : Fin r), R.readout () (r, d) (merge a b (braPos k)) (b k)
private theorem rejected_law : ¬ arena.Law (rejected coordOutput) := by
  intro h
  exact @h 1 2 (fun _ => 0) (fun _ => 0) 0
def source_registration : Registration arena (type_of% @merge_braPos) where
  actual := actual coordOutput
  bridge := Iff.rfl
  variation := ⟨@merge_braPos, rejected coordOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coord_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.merge_braPos)
    (Realization (signature coordOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_braPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_braPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual coordOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end merge_braPos


namespace ketPos_party
abbrev arena : Arena where
  signature := signature positionOutput
  Law R := ∀ {r : ℕ} (p : Fin (2 * r)), p.val % 2 = 0 → R.readout () (r, 0) (ketPos (party p)) p
private theorem rejected_law : ¬ arena.Law (rejected positionOutput) := by
  intro h
  exact @h 1 0 rfl
def source_registration : Registration arena (type_of% @ketPos_party) where
  actual := actual positionOutput
  bridge := Iff.rfl
  variation := ⟨@ketPos_party, rejected positionOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := position_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.ketPos_party)
    (Realization (signature positionOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.ketPos_party.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.ketPos_party.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual positionOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end ketPos_party

namespace braPos_party
abbrev arena : Arena where
  signature := signature positionOutput
  Law R := ∀ {r : ℕ} (p : Fin (2 * r)), p.val % 2 ≠ 0 → R.readout () (r, 0) (braPos (party p)) p
private theorem rejected_law : ¬ arena.Law (rejected positionOutput) := by
  intro h
  exact @h 1 1 (by decide)
def source_registration : Registration arena (type_of% @braPos_party) where
  actual := actual positionOutput
  bridge := Iff.rfl
  variation := ⟨@braPos_party, rejected positionOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := position_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.braPos_party)
    (Realization (signature positionOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.braPos_party.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.braPos_party.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual positionOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end braPos_party

namespace merge_projections
abbrev arena : Arena where
  signature := signature flatOutput
  Law R := ∀ {r d : ℕ} (i : Fin (2 * r) → Fin d), R.readout () (r, d) (merge (fun k => i (ketPos k)) (fun k => i (braPos k))) i
private theorem rejected_law : ¬ arena.Law (rejected flatOutput) := by
  intro h
  exact @h 0 0 (fun k => Fin.elim0 k)
def source_registration : Registration arena (type_of% @merge_projections) where
  actual := actual flatOutput
  bridge := Iff.rfl
  variation := ⟨@merge_projections, rejected flatOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := flat_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.merge_projections)
    (Realization (signature flatOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_projections.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_projections.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual flatOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end merge_projections

namespace J_ketPos
abbrev arena : Arena where
  signature := signature positionOutput
  Law R := ∀ {r : ℕ} (k : Fin r), R.readout () (r, 0) (J r (ketPos k)) (braPos k)
private theorem rejected_law : ¬ arena.Law (rejected positionOutput) := by
  intro h
  exact @h 1 0
def source_registration : Registration arena (type_of% @J_ketPos) where
  actual := actual positionOutput
  bridge := Iff.rfl
  variation := ⟨@J_ketPos, rejected positionOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := position_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.J_ketPos)
    (Realization (signature positionOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.J_ketPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.J_ketPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual positionOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end J_ketPos

namespace J_braPos
abbrev arena : Arena where
  signature := signature positionOutput
  Law R := ∀ {r : ℕ} (k : Fin r), R.readout () (r, 0) (J r (braPos k)) (ketPos k)
private theorem rejected_law : ¬ arena.Law (rejected positionOutput) := by
  intro h
  exact @h 1 0
def source_registration : Registration arena (type_of% @J_braPos) where
  actual := actual positionOutput
  bridge := Iff.rfl
  variation := ⟨@J_braPos, rejected positionOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := position_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.J_braPos)
    (Realization (signature positionOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.J_braPos.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.J_braPos.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual positionOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end J_braPos


namespace merge_J
abbrev arena : Arena where
  signature := signature coordOutput
  Law R := ∀ {r d : ℕ} (a b : Index r d) (p : Fin (2 * r)), R.readout () (r, d) (merge a b (J r p)) (merge b a p)
private theorem rejected_law : ¬ arena.Law (rejected coordOutput) := by
  intro h
  exact @h 1 2 (fun _ => 0) (fun _ => 0) 0
def source_registration : Registration arena (type_of% @merge_J) where
  actual := actual coordOutput
  bridge := Iff.rfl
  variation := ⟨@merge_J, rejected coordOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := coord_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.merge_J)
    (Realization (signature coordOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_J.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.merge_J.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual coordOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end merge_J

namespace permute_output_exchange
abbrev arena : Arena where
  signature := signature matrixOutput
  Law R := ∀ {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r))) (ρ : Matrix (Index r d) (Index r d) ℂ), R.readout () (r, d) (permute (σ.trans (J r)) ρ) (permute σ ρ)ᵀ
private theorem rejected_law : ¬ arena.Law (rejected matrixOutput) := by
  intro h
  exact @h 0 0 (Equiv.refl _) 0
def source_registration : Registration arena (type_of% @permute_output_exchange) where
  actual := actual matrixOutput
  bridge := Iff.rfl
  variation := ⟨@permute_output_exchange, rejected matrixOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := matrix_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.permute_output_exchange)
    (Realization (signature matrixOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_output_exchange.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_output_exchange.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual matrixOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end permute_output_exchange

namespace permute_apply
abbrev arena : Arena where
  signature := signature scalarOutput
  Law R := ∀ {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r))) (ρ : Matrix (Index r d) (Index r d) ℂ) (a b : Index r d), R.readout () (r, d) (permute σ ρ a b) (ρ (indexPermutation σ (a, b)).1 (indexPermutation σ (a, b)).2)
private theorem rejected_law : ¬ arena.Law (rejected scalarOutput) := by
  intro h
  exact @h 0 0 (Equiv.refl _) 0 (fun k => Fin.elim0 k) (fun k => Fin.elim0 k)
def source_registration : Registration arena (type_of% @permute_apply) where
  actual := actual scalarOutput
  bridge := Iff.rfl
  variation := ⟨@permute_apply, rejected scalarOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := scalar_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.permute_apply)
    (Realization (signature scalarOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_apply.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_apply.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual scalarOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end permute_apply

namespace permute_single
abbrev arena : Arena where
  signature := signature matrixOutput
  Law R := ∀ {r d : ℕ} (σ : Equiv.Perm (Fin (2 * r))) (a b : Index r d) (z : ℂ), R.readout () (r, d) (permute σ (Matrix.single a b z)) (Matrix.single ((indexPermutation σ).symm (a,b)).1 ((indexPermutation σ).symm (a,b)).2 z)
private theorem rejected_law : ¬ arena.Law (rejected matrixOutput) := by
  intro h
  exact @h 0 0 (Equiv.refl _) (fun k => Fin.elim0 k) (fun k => Fin.elim0 k) 0
def source_registration : Registration arena (type_of% @permute_single) where
  actual := actual matrixOutput
  bridge := Iff.rfl
  variation := ⟨@permute_single, rejected matrixOutput, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law _ _ rejected_law
  dependence := matrix_dependence
def registration : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.permute_single)
    (Realization (signature matrixOutput)) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_single.unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup.permute_single.source_registration
  realizationSource := none, generated := false
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous, localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (actual matrixOutput)
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none, coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown, familyRecord := none, options := #[] }
end permute_single

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.Setup


namespace Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery

open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
open _root_.D5.S3.Quantum.Entanglement.PermutationCriteria.LabelRecovery
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ
    (fun r => Finset (Fin (2 * r))) (fun r => Finset (Fin (2 * r)) → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {r : ℕ} (S T : Finset (Fin (2 * r))),
    (∀ k, sameSide (rowLabels S k) ↔ sameSide (rowLabels T k)) →
    (∀ i j, pairDistance (rowLabels S i) (rowLabels S j) =
      pairDistance (rowLabels T i) (rowLabels T j)) →
    R.readout () r T S ∨ R.readout () r T Sᶜ ∨
      R.readout () r T (S.map (J r).toEmbedding) ∨
      R.readout () r T (S.map (J r).toEmbedding)ᶜ

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := @h 0 ∅ ∅ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  rcases hh with hh | hh | hh | hh <;> exact hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (∅ : Finset (Fin (2 * 1))), {0}, ?_⟩
  intro he
  have hbad : ({0} : Finset (Fin (2 * 1))) = ∅ :=
    Eq.mp (congrFun he ∅) rfl
  simpa using hbad

def source_registration : Registration arena (type_of% @recover_rowSets) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@recover_rowSets, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery.recover_rowSets)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "arg", "arg", "arg", "fn", "fn"]
        stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Entanglement.PermutationCriteria.RowSetRecovery
