import LeanInformationAuditInterface.Contract.Registration
import D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
import Reg.Support.SingleDependentReadout

/-! Source-bound registrations for the square's parity, context indices and observable matrices. -/

namespace Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
open _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace ZITable

/-- Observe the matrix at the table's observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9 → Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => f 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () obs = !![1,0,0,0; 0,1,0,0; 0,0,-1,0; 0,0,0,-1]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize] at hc

def source_registration : Registration arena (type_of% @ZITable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ZITable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.ZITable)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ZITable.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ZITable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end ZITable

namespace XITable

/-- Observe the matrix at the table's observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 9 → Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ f => f 4) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () obs = !![0,0,1,0; 0,0,0,1; 1,0,0,0; 0,1,0,0]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 2) h
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize] at hc

def source_registration : Registration arena (type_of% @XITable) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨XITable, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.XITable)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.XITable.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.XITable.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => f 4) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end XITable

namespace HermitianSquare

/-- Observe left multiplication by a variable matrix at each observable index. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 9)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)
    (fun _ => Matrix (Fin 4) (Fin 4) ℂ)

def actual : Realization signature :=
  realize signature (fun _ v M => M * obs v) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain Hermitian symmetry and the full square identity for every index. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ v, (obs v).IsHermitian ∧ R.readout () v (obs v) = 1

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) (h 0).2
  change (0 : ℂ) = 1 at hc
  norm_num at hc

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro h
  have hc := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℂ => M 0 0) h
  norm_num [actual, realize,
    _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.ZITable] at hc

def source_registration : Registration arena (type_of% @obs_herm_sq) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨obs_herm_sq, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Matrices.obs_herm_sq)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.HermitianSquare.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.HermitianSquare.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ v M => M * obs v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end HermitianSquare

namespace BVParity
open _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square

/-- Read the parity bit as a natural number from a varied three-bit assignment. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => Fin 3 → Bool) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ a => Bool.toNat (parity3 a)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ a : Fin 3 → Bool,
    R.readout () () a = (Bool.toNat (a 0) + Bool.toNat (a 1) + Bool.toNat (a 2)) % 2

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h (fun _ => false)
  change (1 : ℕ) = 0 at hzero
  exact Nat.one_ne_zero hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨(), (fun _ => false), (fun _ => true), by decide⟩

def source_registration : Registration arena (type_of% @bv_parity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨bv_parity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square.bv_parity)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.BVParity.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.BVParity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ a => Bool.toNat (parity3 a)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square.bv_parity
#print axioms source_registration
#print axioms registration

end BVParity

namespace ParityMiss
open _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square

/-- Read the parity of the local assignment supplied at the selected context. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 6)
    (fun _ => Fin 3 → Bool) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ a => parity3 a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ x _ => target x) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ g : Fin 9 → Bool, ∃ x : Fin 6,
    R.readout () x (fun i => g ((C x).get i)) ≠ target x

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨x, hx⟩ := h (fun _ => false)
  exact hx rfl

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨0, (fun _ => false), (fun _ => true), by decide⟩

def source_registration : Registration arena (type_of% @parity_miss) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨parity_miss, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square.parity_miss)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ParityMiss.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.ParityMiss.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ a => parity3 a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Square.parity_miss
#print axioms source_registration
#print axioms registration

end ParityMiss

namespace PMGetIdx
open _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo

/-- Read a context's observable index at a varied position. -/
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Fin 6)
    (fun _ => Fin 3) (fun _ => Fin 9)

def actual : Realization signature :=
  realize signature (fun _ s i => (Square.C s).get i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 8) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (s : Fin 6) (i : Fin 3), R.readout () s i = Square.idx s i

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hzero := h 0 0
  change (8 : Fin 9) = 0 at hzero
  exact (by decide : (8 : Fin 9) ≠ 0) hzero

theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨0, 0, 1, by decide⟩

def source_registration : Registration arena (type_of% @Product.pm_get_idx) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨Product.pm_get_idx, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product.pm_get_idx)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.PMGetIdx.unit
  realizationName :=
    `Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.PMGetIdx.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ s i => (Square.C s).get i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print _root_.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo.Product.pm_get_idx
#print axioms source_registration
#print axioms registration

end PMGetIdx

end
end Reg.D5.S3.QuantumContext.RankOfContextualityNonPowerTwo
