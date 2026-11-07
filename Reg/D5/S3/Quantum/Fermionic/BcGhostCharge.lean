import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostCharge

/-! Source-family candidate for the original pointwise ghost-number identity. -/

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostCharge

open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostCharge
open _root_.D5.S3.Quantum.Fermionic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v => ghostNumber v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, R.readout () () v = ∑ᶠ n : ℤ, normalTerm n v

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem number_singleton : ghostNumber (ket {1}) = ket {1} := by
  have hcharge : charge ({1} : Finset ℕ) = 1 := by
    norm_num [charge, Finset.filter_singleton]
  simp only [ghostNumber, ket, Finsupp.lsum_single, LinearMap.smulRight_apply,
    LinearMap.id_apply, one_smul, hcharge, Int.cast_one]

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (ket {1})
  change (0 : Fock) = ∑ᶠ n : ℤ, normalTerm n (ket {1}) at hz
  rw [← ghost_number_normal_sum, number_singleton] at hz
  exact (by simp [ket] : ket {1} ≠ 0) hz.symm

def family : Registration arena (type_of% @ghost_number_normal_sum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨ghost_number_normal_sum, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 0, ket {1}, ?_⟩
    change ghostNumber 0 ≠ ghostNumber (ket {1})
    rw [map_zero, number_singleton]
    exact Ne.symm (by simp [ket] : ket {1} ≠ 0)

def normal_sum_audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ghost_number_normal_sum) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.normalSumUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => ghostNumber v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCharge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


namespace Degrees

abbrev arena : Arena where
  signature := _root_.Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.signature
  Law R := R.readout () () vacuum = 0 ∧
    (∀ (m : ℤ) (v : Fock), R.readout () () (BcGhostFock.b m v) -
      BcGhostFock.b m (R.readout () () v) = -BcGhostFock.b m v) ∧
    (∀ (m : ℤ) (v : Fock), R.readout () () (BcGhostFock.c m v) -
      BcGhostFock.c m (R.readout () () v) = BcGhostFock.c m v)

private theorem law_bridge : (type_of% @ghost_number_relations) ↔ arena.Law actual := by
  constructor
  · rintro ⟨hv, hb, hc⟩
    exact ⟨hv, fun m v => LinearMap.congr_fun (hb m) v,
      fun m v => LinearMap.congr_fun (hc m) v⟩
  · rintro ⟨hv, hb, hc⟩
    exact ⟨hv, fun m => LinearMap.ext (hb m), fun m => LinearMap.ext (hc m)⟩

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h.2.2 1 vacuum
  change 0 - BcGhostFock.c 1 0 = BcGhostFock.c 1 vacuum at hz
  have hn := BcGhostFock.ghost_vacuum.2.2.2.2.1
  exact hn (by simpa using hz.symm)

def family : Registration arena (type_of% @ghost_number_relations) where
  actual := actual
  bridge := law_bridge
  variation := ⟨law_bridge.mp ghost_number_relations, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 0, ket {1}, ?_⟩
    change ghostNumber 0 ≠ ghostNumber (ket {1})
    rw [map_zero, number_singleton]
    exact Ne.symm (by simp [ket] : ket {1} ≠ 0)

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@ghost_number_relations) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.degreesUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.Degrees.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ v => ghostNumber v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCharge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Degrees

namespace Capture

abbrev signature : Signature where
  Params := Finset ℤ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ K v => (∑ n ∈ K, normalTerm n) v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (v : Fock) (K : Finset ℤ), activeModes v ⊆ K →
    R.readout () K v = ghostNumber v

def rejected : Realization signature := realize signature (fun _ _ _ => 0)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hz := h (ket {1}) (activeModes (ket {1})) (fun _ hi => hi)
  change (0 : Fock) = ghostNumber (ket {1}) at hz
  rw [number_singleton] at hz
  exact (by simp [ket] : ket {1} ≠ 0) hz.symm

def family : Registration arena (type_of% @finite_normal_capture) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_normal_capture, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨activeModes (ket {1}), 0, ket {1}, ?_⟩
    change (∑ n ∈ activeModes (ket {1}), normalTerm n) 0 ≠
      (∑ n ∈ activeModes (ket {1}), normalTerm n) (ket {1})
    rw [map_zero, finite_normal_capture _ _ (fun _ h => h), number_singleton]
    exact Ne.symm (by simp [ket] : ket {1} ≠ 0)

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@finite_normal_capture) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.captureUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.Capture.family
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
    (fun _ K v => (∑ n ∈ K, normalTerm n) v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCharge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Capture

namespace LocalSupport

abbrev signature : Signature where
  Params := Unit
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Fock
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ v n => normalTerm n v) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ v : Fock, (R.readout () () v).HasFiniteSupport

def rejected : Realization signature := realize signature (fun _ _ _ _ => vacuum)
  (fun e => nomatch e)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hf := h 0
  change Set.Finite (Function.support (fun _ : ℤ => vacuum)) at hf
  have he : Function.support (fun _ : ℤ => vacuum) = Set.univ := by
    ext n
    simp [Function.mem_support, vacuum, ket]
  rw [he] at hf
  exact Set.infinite_univ hf

private theorem normal_one_singleton : normalTerm 1 (ket {1}) = ket {1} := by
  have h := finite_normal_capture (ket {1}) {1}
    (by simp [activeModes, ket, siteMode])
  simpa only [Finset.sum_singleton, number_singleton] using h

def family : Registration arena (type_of% @normal_term_finite_support) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨normal_term_finite_support, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨(), 0, ket {1}, ?_⟩
    intro he
    have h := congrFun he 1
    change normalTerm 1 0 = normalTerm 1 (ket {1}) at h
    rw [map_zero, normal_one_singleton] at h
    exact (by simp [ket] : ket {1} ≠ 0) h.symm

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@normal_term_finite_support) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.localSupportUnit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostCharge.LocalSupport.family
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
    (fun _ _ v n => normalTerm n v) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostCharge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end LocalSupport

end Reg.D5.S3.Quantum.Fermionic.BcGhostCharge
