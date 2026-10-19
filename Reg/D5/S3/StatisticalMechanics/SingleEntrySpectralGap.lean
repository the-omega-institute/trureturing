import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntrySpectralGap
import Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGapAuxiliary
import Reg.Support.DependentFamily

/-! # Source-bound audit of the free-mode spectral extension -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u_1
open scoped BigOperators
open Matrix

namespace Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev Parameters := Σ Sites : Type u_1, Σ _ : Sites → ℝ, Sites → ℝ

abbrev signature : Signature where
  Params := Parameters.{u_1}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u_1}).State p → (signature.{u_1}).Output role p :=
  fun _ p i => siteRate p.2.1 p.2.2 i

def actualAnchor : ∀ (_ : (signature.{u_1}).Anchor) p, (signature.{u_1}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u_1} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- The original upper-bound site-rate occurrence is observed. The complete
secular equation, both eigenvector clauses and every original premise remain. -/
abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (a b : ι → ℝ) (η θ : ℝ),
    (∀ i, 0 < a i) → (∀ i, 0 < b i) → 0 < η → 0 < θ →
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < R.readout () ⟨ι, a, b⟩ i) ∧ secular a b η θ l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        modeNegativeGenerator a b η θ *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          modeNegativeGenerator a b η θ *ᵥ y = μ • y) → l ≤ μ

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  obtain ⟨l, hl, hu, _⟩ :=
    h (ι := ULift.{u_1} Unit) (fun _ => 1) (fun _ => 1) 1 1
      (by intro i; norm_num) (by intro i; norm_num) (by norm_num) (by norm_num)
  have hh := hu (ULift.up ())
  norm_num [rejected, realize] at hh
  linarith

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro role
  let a : ULift.{u_1} (Fin 2) → ℝ := fun i => if i.down = 0 then 1 else 2
  refine ⟨⟨ULift.{u_1} (Fin 2), a, fun _ => 1⟩, ULift.up 0, ULift.up 1, ?_⟩
  norm_num [actual, actualReadout, realize, siteRate, a]

def family : Registration arena.{u_1} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@secular_root_least_mode_eigenvalue.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 4, 5]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
    stateBinder := 13
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``secular_root_least_mode_eigenvalue).type
  let path := #["body", "body", "body", "body", "body", "body", "body", "body",
    "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected spectral upper-bound occurrence is absent"
  unless e.isAppOfArity ``siteRate 4 && binders == 14 do
    throwError "The selected occurrence is not the original site-rate observation"
  unless e.getAppArgs[3]! == .bvar 0 do
    throwError "The selected site-rate observation does not use its original site binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@secular_root_least_mode_eigenvalue.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration

def analysisSource : Analysis.Source (@secular_root_least_mode_eigenvalue.{u_1}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@secular_root_least_mode_eigenvalue.{u_1}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Mode-coordinate spectrum: no probability trajectory or five-mode pushforward in this theorem" }

namespace Generator

abbrev Parameters := Σ Sites : Type u_1,
  _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Rates Sites

abbrev signature : Signature where
  Params := Parameters.{u_1}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u_1}).State p → (signature.{u_1}).Output role p :=
  fun _ p i => siteRate p.2.a p.2.b i

def actualAnchor : ∀ (_ : (signature.{u_1}).Anchor) p, (signature.{u_1}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u_1} := realize signature actualReadout actualAnchor
def rejected : Realization signature.{u_1} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u_1}
  Law R := ∀ {ι : Type u_1} [fi : Fintype ι] [de : DecidableEq ι] [ne : Nonempty ι]
    (k : _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Rates ι),
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < R.readout () ⟨ι, k⟩ i) ∧
      secular k.a k.b k.eta k.theta l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        (-_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.generator k) *ᵥ x = l • x) ∧
      ∀ μ : ℝ, 0 < μ →
        (∃ y : Option (Finset ι) → ℝ, y ≠ 0 ∧
          (-_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.generator k) *ᵥ y = μ • y) → l ≤ μ

private def unitRates : _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Rates (ULift.{u_1} Unit) where
  a := fun _ => 1
  b := fun _ => 1
  eta := 1
  theta := 1
  a_pos := by intro i; norm_num
  b_pos := by intro i; norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.{u_1}.Law rejected := by
  intro h
  obtain ⟨l, hl, hu, _⟩ := h unitRates
  have hh := hu (ULift.up ())
  norm_num [rejected, realize] at hh
  linarith

private theorem dependence : ObservationalDependence signature.{u_1} actual := by
  intro role
  let k : _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Rates (ULift.{u_1} (Fin 2)) := {
    a := fun i => if i.down = 0 then 1 else 2
    b := fun _ => 1
    eta := 1
    theta := 1
    a_pos := by intro i; split_ifs <;> norm_num
    b_pos := by intro i; norm_num
    eta_pos := by norm_num
    theta_pos := by norm_num }
  refine ⟨⟨ULift.{u_1} (Fin 2), k⟩, ULift.up 0, ULift.up 1, ?_⟩
  norm_num [actual, actualReadout, realize, siteRate, k]

def family : Registration arena.{u_1} (arena.Law actual) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@secular_root_least_generator_eigenvalue.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j h
        exact (h (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntrySpectralGap
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``secular_root_least_generator_eigenvalue).type
  let path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The full-generator upper-bound source occurrence is absent"
  unless e.isAppOfArity ``siteRate 4 && binders == 7 && e.getAppArgs[3]! == .bvar 0 do
    throwError "The full-generator source occurrence is not the original site observation"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@secular_root_least_generator_eigenvalue.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.Generator.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap.Generator.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actualReadout actualAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

def analysisSource : Analysis.Source (@secular_root_least_generator_eigenvalue.{u_1}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@secular_root_least_generator_eigenvalue.{u_1}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "Full configuration-generator spectrum: probability trajectory and five-mode observation bridge not acquired by the spectral theorem" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis
end Generator

end Reg.D5.S3.StatisticalMechanics.SingleEntrySpectralGap
