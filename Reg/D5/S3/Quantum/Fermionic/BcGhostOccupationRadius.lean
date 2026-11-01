import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

open scoped BigOperators
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Fermionic.CountableOccupationFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostFock
open _root_.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
open private L_vacuum from D5.S3.Quantum.Fermionic.BcGhostVirasoro

noncomputable section
namespace Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius

namespace Existence
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
abbrev arena : Arena where
  signature := signature
  Law R := ∀ w : Fock, ∃ A : ℕ, 2 ≤ A ∧ R.readout () A w
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  simpa using h 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨2, 0, ket {2}, ?_⟩
  intro h
  have hh : Radius 2 (ket {2}) := Eq.mp h (by simp [Radius])
  norm_num [Radius, sites, ket, Finset.range_succ] at hh
def family : Registration arena (type_of% @exists_radius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_radius, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_radius) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[1]
    readouts := #[{ path := #["body", "arg", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Existence

namespace Modes
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
theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  · refine ⟨-2, 0, vacuum, ?_⟩
    norm_num [actual, realize, b, create_vacuum, ket]
  · refine ⟨1, 0, vacuum, ?_⟩
    norm_num [actual, realize, c, create_vacuum, ket]
end Modes

namespace High
def rejected : Realization Modes.signature := realize Modes.signature
  (fun _ _ w => w) (fun e => nomatch e)
abbrev arena : Arena where
  signature := Modes.signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w)
    (t : ℤ) (_ : (A : ℤ) < t), R.readout false t w = 0 ∧ R.readout true t w = 0
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (A := 2) (by decide) (w := vacuum)
    (by simp [Radius, vacuum, ket, sites, Finset.range_succ]) 3 (by decide)).1
  simpa [rejected, realize, vacuum, ket] using he
private def replaced (role : Bool) : Realization Modes.signature := realize Modes.signature
  (fun other t w => if other = role then w else Modes.actual.readout other t w)
  (fun e => nomatch e)
private theorem replaced_law (role : Bool) : ¬ arena.Law (replaced role) := by
  intro h
  have he := h (A := 2) (by decide) (w := vacuum)
    (by simp [Radius, vacuum, ket, sites, Finset.range_succ]) 3 (by decide)
  cases role <;> simp [replaced, realize, vacuum, ket] at he
def family : Registration arena (type_of% @high_modes) where
  actual := Modes.actual
  bridge := Iff.rfl
  variation := ⟨high_modes, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨replaced role, ?_, rfl, replaced_law role⟩
      intro other hne
      simp [replaced, realize, hne]
    · intro e; exact nomatch e
  dependence := Modes.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@high_modes) (Realization Modes.signature) Unit Unit where
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
  readout := some (realize Modes.signature Modes.actual.readout Modes.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end High

namespace Mode
def rejected : Realization Modes.signature := realize Modes.signature
  (fun _ _ _ => ket {2}) (fun e => nomatch e)
abbrev arena : Arena where
  signature := Modes.signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w) (t : ℤ),
    Radius (max A (max t.natAbs 2)) (R.readout false t w) ∧
      Radius (max A (max t.natAbs 2)) (R.readout true t w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := (h (A := 2) (by decide) (w := 0) (by simp [Radius]) 0).1
  norm_num [rejected, realize, Radius, sites, ket, Finset.range_succ] at he
private def replaced (role : Bool) : Realization Modes.signature := realize Modes.signature
  (fun other t w => if other = role then ket {2} else Modes.actual.readout other t w)
  (fun e => nomatch e)
private theorem replaced_law (role : Bool) : ¬ arena.Law (replaced role) := by
  intro h
  have he := h (A := 2) (by decide) (w := 0) (by simp [Radius]) 0
  cases role <;> norm_num [replaced, realize, Radius, sites, ket, Finset.range_succ] at he
def family : Registration arena (type_of% @mode_radius) where
  actual := Modes.actual
  bridge := Iff.rfl
  variation := ⟨mode_radius, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨replaced role, ?_, rfl, replaced_law role⟩
      intro other hne
      simp [replaced, realize, hne]
    · intro e; exact nomatch e
  dependence := Modes.dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@mode_radius) (Realization Modes.signature) Unit Unit where
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
  readout := some (realize Modes.signature Modes.actual.readout Modes.actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false },
      { path := #["body", "body", "body", "body", "body", "arg", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Mode

namespace Virasoro
abbrev signature : Signature where
  Params := ℤ
  State _ := Fock
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Fock
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature
  (fun _ r w => _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L r w) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => ket {2}) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {A : ℕ} (_ : 2 ≤ A) {w : Fock} (_ : Radius A w) (r : ℤ),
    Radius (A+(-r).toNat) (R.readout () r w)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (A := 2) (by decide) (w := 0) (by simp [Radius]) 0
  norm_num [rejected, realize, Radius, sites, ket, Finset.range_succ] at he
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨-2, 0, vacuum, ?_⟩
  intro h
  change _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-2) 0 =
    _root_.D5.S3.Quantum.Fermionic.BcGhostVirasoro.L (-2) vacuum at h
  rw [map_zero] at h
  have he := congrArg (fun w : Fock => w {0,3}) h
  rw [L_vacuum] at he
  have hi : Finset.Icc ((-2 : ℤ)+2) 1 = {0,1} := by decide
  norm_num [hi, b, c, create_vacuum, create_ket, phase, lowerCount, ket] at he
def family : Registration arena (type_of% @virasoro_radius) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨virasoro_radius, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim other role)).elim
    · intro e; exact nomatch e
  dependence := dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@virasoro_radius) (Realization signature) Unit Unit where
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
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
    definition := none
    coordinates := #[4]
    readouts := #[{ path := #["body", "body", "body", "body", "body", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Virasoro

end Reg.D5.S3.Quantum.Fermionic.BcGhostOccupationRadius
