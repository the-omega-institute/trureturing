import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryReturnTail
import Reg.Support.DependentFamily

/-! # Source-bound registration of the actual return-current tail -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u_1
open scoped BigOperators
open Matrix
namespace Reg.D5.S3.StatisticalMechanics.SingleEntryReturnTail
open _root_.D5.S3.StatisticalMechanics.SingleEntrySecularRoot
open _root_.D5.S3.StatisticalMechanics.SingleEntryReturnTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
    (k : _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Rates ι)
    (p : ℝ → Option (Finset ι) → ℝ),
    _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.ForwardSolution k p →
    ∃ l : ℝ, 0 < l ∧ (∀ i, l < R.readout () ⟨ι, k⟩ i) ∧
      secular k.a k.b k.eta k.theta l = 0 ∧
      (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
        (-_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.generator k) *ᵥ x = l • x) ∧
      (∀ μ : ℝ, 0 < μ →
        (∃ x : Option (Finset ι) → ℝ, x ≠ 0 ∧
          (-_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.generator k) *ᵥ x = μ • x) → l ≤ μ) ∧
      Filter.Tendsto (fun t => Real.exp (l * t) *
        (k.theta * p t none - k.eta * p t (some ∅))) Filter.atTop
        (nhds (-k.theta / secularSlope k.a k.b k.eta l)) ∧
      0 < -k.theta / secularSlope k.a k.b k.eta l ∧
      ∀ i j : ι, i ≠ j →
        Filter.Tendsto (fun t => Real.exp (l * t) *
          _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.association p i j t)
          Filter.atTop (nhds (-k.theta * (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅)) *
            occupancy k.a k.b i * occupancy k.a k.b j /
            ((siteRate k.a k.b i + siteRate k.a k.b j - l) * secularSlope k.a k.b k.eta l))) ∧
        0 < -k.theta * (k.theta / (k.theta + k.eta * modeWeight k.a k.b ∅)) *
          occupancy k.a k.b i * occupancy k.a k.b j /
          ((siteRate k.a k.b i + siteRate k.a k.b j - l) * secularSlope k.a k.b k.eta l)

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
  obtain ⟨p, hp, _⟩ :=
    (_root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.finite_network_strict_pair unitRates).1
  obtain ⟨l, hl, hu, _⟩ := h unitRates p hp
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
  variation := ⟨@finite_network_common_slow_tail.{u_1}, rejected, rejected_law⟩
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
  owner := `D5.S3.StatisticalMechanics.SingleEntryReturnTail
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
    stateBinder := 8
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``finite_network_common_slow_tail).type
  let path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body", "arg", "fn", "arg", "body", "arg"]
  let mut binders := 0
  for step in path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The full-generator upper-bound source occurrence is absent"
  unless e.isAppOfArity ``siteRate 4 && binders == 9 && e.getAppArgs[3]! == .bvar 0 do
    throwError "The full-generator source occurrence is not the original site observation"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_network_common_slow_tail.{u_1}) (Realization signature.{u_1}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryReturnTail.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryReturnTail.family
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

def analysisSource : Analysis.Source (@finite_network_common_slow_tail.{u_1}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@finite_network_common_slow_tail.{u_1}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "The selected occurrence is the free site rate in the root bound; no five-mode occupancy pushforward has been acquired on this same occurrence" }

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis
end Reg.D5.S3.StatisticalMechanics.SingleEntryReturnTail
