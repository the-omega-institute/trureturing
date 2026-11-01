import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

namespace Observation
abbrev signature : Signature where
  Params := ℕ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ A w => Radius A w) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)
theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, ket {2}, ?_⟩
  intro h
  have hh : Radius 2 (ket {2}) := Eq.mp h (by simp [Radius])
  norm_num [Radius, sites, ket, Finset.range_succ] at hh
end Observation

namespace Existence
abbrev arena : Arena where
  signature := Observation.signature
  Law R := ∀ w : Fock, ∃ A : ℕ, 2 ≤ A ∧ R.readout () A w
private theorem rejected_law : ¬ arena.Law Observation.rejected := by
  intro h
  simpa using h 0
def family : Registration arena (type_of% @exists_radius) where
  actual := Observation.actual
  bridge := Iff.rfl
  variation := ⟨exists_radius, Observation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Observation.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Observation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_radius) (Realization Observation.signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Existence.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Existence.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Observation.signature Observation.actual.readout Observation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "arg", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Existence

namespace Mode
abbrev arena : Arena where
  signature := Observation.signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w) (t : ℤ),
    R.readout () (max A (max t.natAbs 2)) (b t w) ∧
      R.readout () (max A (max t.natAbs 2)) (c t w)
private theorem rejected_law : ¬ arena.Law Observation.rejected := by
  intro h
  exact (h (A := 2) (by decide) (w := 0) (by simp [Radius]) 0).1
def family : Registration arena (type_of% @mode_radius) where
  actual := Observation.actual
  bridge := Iff.rfl
  variation := ⟨mode_radius, Observation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Observation.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Observation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mode_radius) (Realization Observation.signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Mode.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Mode.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Observation.signature Observation.actual.readout Observation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mode

namespace Virasoro
abbrev arena : Arena where
  signature := Observation.signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w) (r : ℤ),
    R.readout () (A+(-r).toNat)
      (_root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L r w)
private theorem rejected_law : ¬ arena.Law Observation.rejected := by
  intro h
  exact h (A := 2) (by decide) (w := 0) (by simp [Radius]) 0
def family : Registration arena (type_of% @virasoro_radius) where
  actual := Observation.actual
  bridge := Iff.rfl
  variation := ⟨virasoro_radius, Observation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨Observation.rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := Observation.dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@virasoro_radius) (Realization Observation.signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Virasoro.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.Virasoro.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Observation.signature Observation.actual.readout Observation.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Virasoro

namespace High
abbrev signature : Signature where
  Params := ℤ
  State _ := Fock
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun role t w => if role then c t w else b t w) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ w => w) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w)
    (t : ℤ) (_ : (A : ℤ) < t), R.readout false t w = 0 ∧ R.readout true t w = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (A := 2) (by decide) (w := vacuum)
    (by simp [Radius, vacuum, ket, sites, Finset.range_succ]) 3 (by decide)).1
  simpa [rejected, realize, vacuum, ket] using he
private def replaced (role : Bool) : Realization signature := realize signature
  (fun other t w => if other = role then w else actual.readout other t w)
  (fun e => nomatch e)
private theorem replaced_law (role : Bool) : ¬ arena.Law (replaced role) := by
  intro h
  have he := h (A := 2) (by decide) (w := vacuum)
    (by simp [Radius, vacuum, ket, sites, Finset.range_succ]) 3 (by decide)
  cases role <;> simp [replaced, realize, vacuum, ket] at he

def family : Registration arena (type_of% @high_modes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨high_modes, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨replaced role, ?_, rfl, replaced_law role⟩
      intro other hne
      simp [replaced, realize, hne]
    · intro e; exact nomatch e
  dependence := by
    intro role
    cases role
    · refine ⟨-2, 0, vacuum, ?_⟩
      norm_num [actual, realize, b, create_vacuum, ket]
    · refine ⟨1, 0, vacuum, ?_⟩
      norm_num [actual, realize, c, create_vacuum, ket]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@high_modes) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.High.unit
  realizationName := `Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius.High.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Fock
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end High
end Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
