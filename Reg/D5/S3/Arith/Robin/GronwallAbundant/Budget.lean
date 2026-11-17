import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.GronwallAbundant.Budget
import Reg.Support.SingleDependentReadout

set_option linter.style.longLine false
noncomputable section
namespace Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Robin.GronwallAbundant
open Filter
open Filter
open scoped BigOperators Topology

namespace first_layer_add_repeatedMass
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ}, N ≠ 0 →
    R.readout () () ((∑ p ∈ N.primeFactors, Real.log p) + repeatedMass N) (Real.log N)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 1) (by decide)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.first_layer_add_repeatedMass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.first_layer_add_repeatedMass, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.first_layer_add_repeatedMass) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.first_layer_add_repeatedMass.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.first_layer_add_repeatedMass.source_registration
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
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end first_layer_add_repeatedMass

namespace missing_mass_identity
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N P : ℕ}, N ≠ 0 →
    N.primeFactors ⊆ Nat.primesLE P →
    R.readout () () (Real.log N) (Chebyshev.theta P - missingMass N P + repeatedMass N)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 1) (P := 0) (by decide) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) = 0 := Eq.mp (congrFun he 0) rfl
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_identity) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_identity, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_identity) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.missing_mass_identity.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.missing_mass_identity.source_registration
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
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end missing_mass_identity

namespace missing_mass_le_psi_error
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N P : ℕ}, N ≠ 0 →
    N.primeFactors ⊆ Nat.primesLE P → (P : ℝ) ≤ Real.log N →
    R.readout () () (missingMass N P) (Chebyshev.psi P - P + repeatedMass N)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 1) (P := 0) (by decide) (by simp) (by norm_num)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_le_psi_error) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_le_psi_error, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.missing_mass_le_psi_error) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.missing_mass_le_psi_error.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.missing_mass_le_psi_error.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end missing_mass_le_psi_error

namespace repeatedMass_le_support_budget
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {Y B : ℝ}, 0 ≤ Y → 0 ≤ B →
    (∀ p ∈ N.primeFactors, 2 ≤ N.factorization p → (p : ℝ) ≤ Y) →
    (∀ p ∈ N.primeFactors, (N.factorization p : ℝ) * Real.log p ≤ B) →
    R.readout () () (repeatedMass N) ((Y + 1) * B)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 1) (Y := 0) (B := 0) le_rfl le_rfl (by simp) (by simp)
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.repeatedMass_le_support_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.repeatedMass_le_support_budget, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.repeatedMass_le_support_budget) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.repeatedMass_le_support_budget.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.repeatedMass_le_support_budget.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end repeatedMass_le_support_budget

namespace log_tenth_eventually_le
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (c : ℝ) {ε : ℝ}, 0 < ε →
    ∀ᶠ X : ℝ in atTop,
      R.readout () () (c * (Real.log X) ^ ((1 : ℝ) / 10)) (ε * Real.log X)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, hX⟩ := (h 0 (ε := 1) zero_lt_one).exists
  exact hX
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.log_tenth_eventually_le) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.log_tenth_eventually_le, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.log_tenth_eventually_le) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.log_tenth_eventually_le.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.log_tenth_eventually_le.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end log_tenth_eventually_le

namespace rpow_eventually_le_pnt_envelope
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a r : ℝ), r < 1 →
    ∀ᶠ X : ℝ in atTop,
      R.readout () () (X ^ r)
        (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, hX⟩ := (h 0 0 zero_lt_one).exists
  exact hX
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.rpow_eventually_le_pnt_envelope) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.rpow_eventually_le_pnt_envelope, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.rpow_eventually_le_pnt_envelope) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.rpow_eventually_le_pnt_envelope.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.rpow_eventually_le_pnt_envelope.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end rpow_eventually_le_pnt_envelope

namespace uniform_psi_error_budget
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∃ a > 0, ∃ C > 0, ∀ᶠ X : ℝ in atTop,
    ∀ y : ℝ, 0 ≤ y → y ≤ X →
      R.readout () () (Chebyshev.psi y - y)
        (C * (X * Real.exp (-a * (Real.log X) ^ ((1 : ℝ) / 10))))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨a, ha, C, hC, hbudget⟩ := h
  obtain ⟨X, hX, hbad⟩ := ((eventually_ge_atTop (0 : ℝ)).and hbudget).exists
  exact hbad 0 le_rfl hX
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.uniform_psi_error_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.uniform_psi_error_budget, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.uniform_psi_error_budget) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.uniform_psi_error_budget.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.uniform_psi_error_budget.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "arg", "fn", "arg", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end uniform_psi_error_budget


namespace codeK_lower
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ X B : ℝ, R.readout () () (2 * B / Real.log X) (codeK X B : ℝ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 2 0
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_lower) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_lower, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_lower) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.codeK_lower.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.codeK_lower.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end codeK_lower

namespace codeK_upper
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X B : ℝ}, 1 < X → 0 ≤ B →
    R.readout () () (codeK X B : ℝ) (2 * B / Real.log X + 2)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (X := 2) (B := 0) (by norm_num) le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_upper) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_upper, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.codeK_upper) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.codeK_upper.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.codeK_upper.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end codeK_upper

namespace pnt_count_scale_eventually_ge_one
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ c : ℝ, ∀ᶠ X : ℝ in atTop,
    R.readout () () 1 (X / Real.log X * Real.exp (-c * (Real.log X) ^ ((1 : ℝ) / 10)))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨X, hX⟩ := (h 1).exists
  exact hX
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.pnt_count_scale_eventually_ge_one) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.pnt_count_scale_eventually_ge_one, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.pnt_count_scale_eventually_ge_one) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.pnt_count_scale_eventually_ge_one.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.pnt_count_scale_eventually_ge_one.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end pnt_count_scale_eventually_ge_one

namespace upperHoles_card_le_mass
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℝ) (fun _ => ℝ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) {X : ℝ}, 2 ≤ X →
    R.readout () () ((upperHoles N (codeL X)).card : ℝ)
      (2 * missingMass N (primeEnd N) / Real.log X)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 1 (X := 2) le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hf : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  norm_num at hf
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.upperHoles_card_le_mass) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.upperHoles_card_le_mass, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.upperHoles_card_le_mass) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.upperHoles_card_le_mass.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.upperHoles_card_le_mass.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end upperHoles_card_le_mass

namespace ga1_holes_bound
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N : ℕ} {X B : ℝ}, 2 ≤ X → missingMass N (primeEnd N) ≤ B →
    R.readout () () (upperHoles N (codeL X)).card (codeK X B)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (N := 1) (X := 2) (B := missingMass 1 (primeEnd 1)) le_rfl le_rfl
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  omega
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_holes_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_holes_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_holes_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.ga1_holes_bound.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.ga1_holes_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ga1_holes_bound

namespace ga1_count_code_bound
abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ → Prop)
def actual : Realization signature := realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {X B : ℝ}, 2 ≤ X →
    (∀ N : ℕ, IsProperGA1 N → Real.log N ≤ X → missingMass N (primeEnd N) ≤ B) →
    R.readout () () (Q1 (Real.exp X))
      (codeM X * (codeA X + 1) ^ codeL X *
        (∑ j ∈ Finset.range (codeK X B + 1), (codeM X).choose j))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  classical
  let S := Finset.range (⌊Real.exp (2 : ℝ)⌋₊ + 1)
  let B := ∑ N ∈ S, missingMass N (primeEnd N)
  have hnonneg : ∀ N : ℕ, 0 ≤ missingMass N (primeEnd N) := by
    intro N
    apply Finset.sum_nonneg
    intro q hq
    have hp := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hq).1
    exact Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hbudget : ∀ N : ℕ, IsProperGA1 N → Real.log N ≤ 2 →
      missingMass N (primeEnd N) ≤ B := by
    intro N hN hNX
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by have := hN.1.2.1; omega)
    have hreal : (N : ℝ) ≤ Real.exp 2 := (Real.log_le_iff_le_exp hNpos).mp hNX
    apply Finset.single_le_sum (fun n _ => hnonneg n)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hreal))
  exact h (X := 2) (B := B) le_rfl hbudget
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), (0 : ℕ), (1 : ℕ), ?_⟩
  intro he
  have hf : (1 : ℕ) ≤ 0 := Eq.mp (congrFun he 0) (le_refl 0)
  omega
def source_registration : Registration arena (type_of% @_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_count_code_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_count_code_bound, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence
def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.Arith.Robin.GronwallAbundant.ga1_count_code_bound) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.ga1_count_code_bound.unit
  realizationName := `Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget.ga1_count_code_bound.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x ≤ y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.GronwallAbundant.Budget
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
end ga1_count_code_bound

end Reg.D5.S3.Arith.Robin.GronwallAbundant.Budget
