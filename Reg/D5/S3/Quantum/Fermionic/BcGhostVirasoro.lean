import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostVirasoro

/-! Source-family registrations for the actual locally finite ghost representation. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open private epsilon_L_vacuum epsilon_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

namespace Support
abbrev signature : Signature where
  Params := ℤ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ m v q => summand m q v) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m : ℤ) (v : Fock), Function.HasFiniteSupport (R.readout () m v)
def rejected : Realization signature := realize signature
  (fun _ _ _ _ => vacuum) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0 0
  have hv : (vacuum : Fock) ≠ 0 := by simp [vacuum, ket]
  change (Function.support (fun _ : ℤ => vacuum)).Finite at hf
  have he : Function.support (fun _ : ℤ => vacuum) = Set.univ := by ext q; simp [hv]
  rw [he] at hf
  exact Set.infinite_univ hf
private theorem actual_dependence : actual.readout () (-2) 0 ≠ actual.readout () (-2) vacuum := by
  intro h
  have hket : summand (-2) 0 vacuum = (-2 : ℂ) • ket {0,3} := by
    norm_num [summand, normal, b, c, create_vacuum, create_ket, phase, lowerCount]
  change (fun q => summand (-2) q 0) = (fun q => summand (-2) q vacuum) at h
  have he := congrArg (fun f : ℤ → Fock => f 0 {0,3}) h
  change (summand (-2) 0 0) {0,3} = (summand (-2) 0 vacuum) {0,3} at he
  rw [hket] at he
  norm_num [ket] at he

def family : Registration arena (type_of% @summand_finite) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨summand_finite, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨-2, 0, vacuum, actual_dependence⟩

def support_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@summand_finite) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.support_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.Support.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ m v q => summand m q v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostVirasoro
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Support

namespace B
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ r m => L m * b r - b r * L m) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m r : ℤ), R.readout () r m = ((m-r : ℤ) : ℂ) • b (m+r)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0}) (h (-2) 0)
  norm_num [rejected, realize, b, create_vacuum, ket] at he
private theorem actual_dependence : actual.readout () 0 0 ≠ actual.readout () 0 (-2) := by
  intro h
  change L 0 * b 0 - b 0 * L 0 = L (-2) * b 0 - b 0 * L (-2) at h
  rw [ward_b, ward_b] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {0}) h
  norm_num [b, create_vacuum, ket] at he
def family : Registration arena (type_of% @ward_b) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_b, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨0, 0, -2, actual_dependence⟩

def b_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ward_b) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.b_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.B.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r m => L m * b r - b r * L m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostVirasoro
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end B

namespace C
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ r m => L m * c r - c r * L m) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m r : ℤ), R.readout () r m = ((-2*m-r : ℤ) : ℂ) • c (m+r)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {1}) (h (1) 0)
  norm_num [rejected, realize, c, create_vacuum, ket] at he
private theorem actual_dependence : actual.readout () 0 0 ≠ actual.readout () 0 (1) := by
  intro h
  change L 0 * c 0 - c 0 * L 0 = L (1) * c 0 - c 0 * L (1) at h
  rw [ward_c, ward_c] at h
  have he := congrArg (fun A : Module.End ℂ Fock => A vacuum {1}) h
  norm_num [c, create_vacuum, ket] at he
def family : Registration arena (type_of% @ward_c) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ward_c, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨0, 0, 1, actual_dependence⟩

def c_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ward_c) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.c_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.C.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ r m => L m * c r - c r * L m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostVirasoro
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end C

namespace Virasoro
abbrev signature : Signature where
  Params := ℤ
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Module.End ℂ Fock
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ n m => L m * L n - L n * L m) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (m n : ℤ), R.readout () n m =
    ((m-n : ℤ) : ℂ) • L (m+n) +
    (if m+n = 0 then (-26/12 : ℂ) * ((m : ℂ)^3-m) else 0) •
      (1 : Module.End ℂ Fock)
def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := congrArg (fun A : Module.End ℂ Fock => epsilon (A vacuum)) (h 2 (-2))
  norm_num [rejected, realize, map_add, map_smul, epsilon_L_vacuum, epsilon_vacuum] at he
private theorem actual_dependence : actual.readout () (-2) 0 ≠ actual.readout () (-2) 2 := by
  intro h
  change L 0 * L (-2) - L (-2) * L 0 = L 2 * L (-2) - L (-2) * L 2 at h
  rw [virasoro, virasoro] at h
  have he := congrArg (fun A : Module.End ℂ Fock => epsilon (A vacuum)) h
  norm_num [map_add, map_smul, epsilon_L_vacuum, epsilon_vacuum] at he
def family : Registration arena (type_of% @virasoro) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨virasoro, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := by intro role; exact ⟨-2, 0, 2, actual_dependence⟩

def virasoro_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@virasoro) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.virasoro_auditUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro.Virasoro.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n m => L m * L n - L n * L m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℤ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostVirasoro
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Virasoro

end Reg.D5.S3.Quantum.Fermionic.BcGhostVirasoro
