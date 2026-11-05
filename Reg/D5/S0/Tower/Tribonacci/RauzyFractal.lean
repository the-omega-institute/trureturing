import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S0.Tower.Tribonacci.RauzyFractal

/-! Registration mirrors for the seven public Rauzy-fractal results. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S0.Tower.Tribonacci.RauzyFractal

open _root_.D5.S0.Tower.Tribonacci.RauzyFractal
open _root_.D5.S0.Tower.Tribonacci.Binet
open _root_.D5.S0.Tower.Tribonacci.Values
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Set

abbrev signature : Signature where
  Params := Unit
  State := fun _ => Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ state => state) (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun anchor => nomatch anchor)

abbrev claim_nonempty : Prop := ∀ z : Complex, (rauzyFractal z).Nonempty
abbrev arena_nonempty : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_nonempty

theorem actual_law_nonempty : arena_nonempty.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_nonempty
  · intro _
    rfl

theorem rejected_law_nonempty : ¬ arena_nonempty.Law rejected := by
  intro h
  change (false = true) ↔ claim_nonempty at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_nonempty)
  cases bad

theorem source_bridge_nonempty : claim_nonempty ↔ arena_nonempty.Law actual :=
  by simpa [arena_nonempty, actual, realize] using actual_law_nonempty.symm

def familyRegistration_nonempty :
    Registration arena_nonempty claim_nonempty where
  actual := actual
  bridge := source_bridge_nonempty
  variation := ⟨actual_law_nonempty, rejected, rejected_law_nonempty⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_nonempty⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_nonempty :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_nonempty)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_nonempty.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_nonempty
  realizationSource := none
  generated := false
  arena := .source ⟨arena_nonempty⟩
  objectArena := .source ⟨arena_nonempty⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_nonempty ⟨familyRegistration_nonempty⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_compact : Prop := ∀ {z : Complex},
    z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex) →
    IsCompact (rauzyFractal z)
abbrev arena_compact : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_compact

theorem actual_law_compact : arena_compact.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_isCompact
  · intro _
    rfl

theorem rejected_law_compact : ¬ arena_compact.Law rejected := by
  intro h
  change (false = true) ↔ claim_compact at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_isCompact)
  cases bad

theorem source_bridge_compact : claim_compact ↔ arena_compact.Law actual :=
  by simpa [arena_compact, actual, realize] using actual_law_compact.symm

def familyRegistration_compact : Registration arena_compact claim_compact where
  actual := actual
  bridge := source_bridge_compact
  variation := ⟨actual_law_compact, rejected, rejected_law_compact⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_compact⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_compact :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_isCompact)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_isCompact.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_compact
  realizationSource := none
  generated := false
  arena := .source ⟨arena_compact⟩
  objectArena := .source ⟨arena_compact⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_compact ⟨familyRegistration_compact⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_subset : Prop := ∀ {z : Complex},
    z ∈ D5.S0.Tower.Tribonacci.Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (D5.S0.Tower.Tribonacci.Values.tribonacciConstant : Complex) →
    rauzyFractal z ⊆ Metric.closedBall 0 (1 - ‖z‖)⁻¹
abbrev arena_subset : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_subset

theorem actual_law_subset : arena_subset.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_subset_closedBall
  · intro _
    rfl

theorem rejected_law_subset : ¬ arena_subset.Law rejected := by
  intro h
  change (false = true) ↔ claim_subset at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_subset_closedBall)
  cases bad

theorem source_bridge_subset : claim_subset ↔ arena_subset.Law actual :=
  by simpa [arena_subset, actual, realize] using actual_law_subset.symm

def familyRegistration_subset : Registration arena_subset claim_subset where
  actual := actual
  bridge := source_bridge_subset
  variation := ⟨actual_law_subset, rejected, rejected_law_subset⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_subset⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_subset :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_subset_closedBall)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_subset_closedBall.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_subset
  realizationSource := none
  generated := false
  arena := .source ⟨arena_subset⟩
  objectArena := .source ⟨arena_subset⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_subset ⟨familyRegistration_subset⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_zero : Prop := ∀ z : Complex,
    MapsTo (zeroPrefixMap z) (rauzyFractal z) (rauzyFractal z)
abbrev arena_zero : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_zero

theorem actual_law_zero : arena_zero.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.zeroPrefixMap_mapsTo_rauzyFractal
  · intro _
    rfl

theorem rejected_law_zero : ¬ arena_zero.Law rejected := by
  intro h
  change (false = true) ↔ claim_zero at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.zeroPrefixMap_mapsTo_rauzyFractal)
  cases bad

theorem source_bridge_zero : claim_zero ↔ arena_zero.Law actual :=
  by simpa [arena_zero, actual, realize] using actual_law_zero.symm

def familyRegistration_zero : Registration arena_zero claim_zero where
  actual := actual
  bridge := source_bridge_zero
  variation := ⟨actual_law_zero, rejected, rejected_law_zero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_zero⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_zero :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.zeroPrefixMap_mapsTo_rauzyFractal)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.zeroPrefixMap_mapsTo_rauzyFractal.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_zero
  realizationSource := none
  generated := false
  arena := .source ⟨arena_zero⟩
  objectArena := .source ⟨arena_zero⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_zero ⟨familyRegistration_zero⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_oneZero : Prop := ∀ z : Complex,
    MapsTo (oneZeroPrefixMap z) (rauzyFractal z) (rauzyFractal z)
abbrev arena_oneZero : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_oneZero

theorem actual_law_oneZero : arena_oneZero.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.oneZeroPrefixMap_mapsTo_rauzyFractal
  · intro _
    rfl

theorem rejected_law_oneZero : ¬ arena_oneZero.Law rejected := by
  intro h
  change (false = true) ↔ claim_oneZero at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.oneZeroPrefixMap_mapsTo_rauzyFractal)
  cases bad

theorem source_bridge_oneZero : claim_oneZero ↔ arena_oneZero.Law actual :=
  by simpa [arena_oneZero, actual, realize] using actual_law_oneZero.symm

def familyRegistration_oneZero : Registration arena_oneZero claim_oneZero where
  actual := actual
  bridge := source_bridge_oneZero
  variation := ⟨actual_law_oneZero, rejected, rejected_law_oneZero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_oneZero⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_oneZero :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.oneZeroPrefixMap_mapsTo_rauzyFractal)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.oneZeroPrefixMap_mapsTo_rauzyFractal.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_oneZero
  realizationSource := none
  generated := false
  arena := .source ⟨arena_oneZero⟩
  objectArena := .source ⟨arena_oneZero⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_oneZero ⟨familyRegistration_oneZero⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_oneOneZero : Prop := ∀ z : Complex,
    MapsTo (oneOneZeroPrefixMap z) (rauzyFractal z) (rauzyFractal z)
abbrev arena_oneOneZero : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_oneOneZero

theorem actual_law_oneOneZero : arena_oneOneZero.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.oneOneZeroPrefixMap_mapsTo_rauzyFractal
  · intro _
    rfl

theorem rejected_law_oneOneZero : ¬ arena_oneOneZero.Law rejected := by
  intro h
  change (false = true) ↔ claim_oneOneZero at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.oneOneZeroPrefixMap_mapsTo_rauzyFractal)
  cases bad

theorem source_bridge_oneOneZero : claim_oneOneZero ↔ arena_oneOneZero.Law actual :=
  by simpa [arena_oneOneZero, actual, realize] using actual_law_oneOneZero.symm

def familyRegistration_oneOneZero : Registration arena_oneOneZero claim_oneOneZero where
  actual := actual
  bridge := source_bridge_oneOneZero
  variation := ⟨actual_law_oneOneZero, rejected, rejected_law_oneOneZero⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_oneOneZero⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_oneOneZero :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.oneOneZeroPrefixMap_mapsTo_rauzyFractal)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.oneOneZeroPrefixMap_mapsTo_rauzyFractal.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_oneOneZero
  realizationSource := none
  generated := false
  arena := .source ⟨arena_oneOneZero⟩
  objectArena := .source ⟨arena_oneOneZero⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_oneOneZero ⟨familyRegistration_oneOneZero⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev claim_prefix : Prop := ∀ z : Complex,
    zeroPrefixMap z '' rauzyFractal z ∪
        oneZeroPrefixMap z '' rauzyFractal z ∪
        oneOneZeroPrefixMap z '' rauzyFractal z ⊆ rauzyFractal z
abbrev arena_prefix : Arena where
  signature := signature
  Law R := R.readout () () true = true ↔ claim_prefix

theorem actual_law_prefix : arena_prefix.Law actual := by
  constructor
  · intro _
    exact @D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_prefix_invariant
  · intro _
    rfl

theorem rejected_law_prefix : ¬ arena_prefix.Law rejected := by
  intro h
  change (false = true) ↔ claim_prefix at h
  have bad : (false : Bool) = true := h.mpr
    (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_prefix_invariant)
  cases bad

theorem source_bridge_prefix : claim_prefix ↔ arena_prefix.Law actual :=
  by simpa [arena_prefix, actual, realize] using actual_law_prefix.symm

def familyRegistration_prefix : Registration arena_prefix claim_prefix where
  actual := actual
  bridge := source_bridge_prefix
  variation := ⟨actual_law_prefix, rejected, rejected_law_prefix⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law_prefix⟩
      intro j hji
      exact (hji (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    exact ⟨(), false, true, by simp [actual, realize]⟩

noncomputable def registration_prefix :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_prefix_invariant)
      (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.RauzyFractal.rauzyFractal_prefix_invariant.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.RauzyFractal.familyRegistration_prefix
  realizationSource := none
  generated := false
  arena := .source ⟨arena_prefix⟩
  objectArena := .source ⟨arena_prefix⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena_prefix ⟨familyRegistration_prefix⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some actual
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Tower.Tribonacci.RauzyFractal
