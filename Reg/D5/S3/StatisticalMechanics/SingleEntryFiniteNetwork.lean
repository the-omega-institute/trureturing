import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
import Reg.Support.DependentFamily

/-! # The actual return coordinate and observable values retain the full laws -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Matrix Filter
namespace Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
universe u

abbrev signature : Signature where
  Params := Σ I : Type u, ℝ → Option (Finset I) → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p t => p.2 t none

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ p t => p.2 t none + 1) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I] (k : Rates I),
    (∃ p : ℝ → Option (Finset I) → ℝ, ForwardSolution k p ∧
      ∀ u, 0 ≤ u → (∀ x, 0 ≤ p u x) ∧ p u none + activeMass p u = 1) ∧
    ∀ (p : ℝ → Option (Finset I) → ℝ), ForwardSolution k p →
      ∀ (i j : I), i ≠ j → ∀ t, 0 < t →
      activeMass p t = 1 - R.readout () ⟨I, p⟩ t ∧
      0 < activeMass p t ∧ 0 < fiberWidth p i j t ∧ 0 < association p i j t ∧
      0 < k.theta * p t none - k.eta * p t (some ∅) ∧
      (∀ u, 0 ≤ u → HasDerivAt (association p i j)
        (-(k.a i + k.b i + k.a j + k.b j) * association p i j u +
          (k.theta * p u none - k.eta * p u (some ∅)) * joint p i j u) u) ∧
      ∃ L : Option (Finset I) → ℝ,
        (∀ x, Tendsto (fun u => p u x) atTop (nhds (L x))) ∧ generator k *ᵥ L = 0 ∧
        joint (fun _ => L) i j 0 = activeMass (fun _ => L) 0 *
          (k.a i / (k.a i + k.b i)) * (k.a j / (k.a j + k.b j))

private def unitRates : Rates (ULift.{u} (Fin 2)) where
  a := fun _ => 1
  b := fun _ => 1
  eta := 1
  theta := 1
  a_pos _ := by norm_num
  b_pos _ := by norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  obtain ⟨p, hp, _⟩ := (finite_network_strict_pair unitRates).1
  intro h
  have hij : (⟨0⟩ : ULift.{u} (Fin 2)) ≠ ⟨1⟩ := by decide
  have hg := ((finite_network_strict_pair unitRates).2 p hp ⟨0⟩ ⟨1⟩ hij 1 (by norm_num)).1
  have hb := ((h unitRates).2 p hp ⟨0⟩ ⟨1⟩ hij 1 (by norm_num)).1
  change activeMass p 1 = 1 - (p 1 none + 1) at hb
  linarith

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, fun t _ => t⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualReadout]

def family : Registration arena.{u} (type_of% @finite_network_strict_pair.{u}) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@finite_network_strict_pair.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "arg",
      "body", "body", "body", "body", "body", "body", "body",
      "fn", "arg", "arg", "arg"]
    stateBinder := 9
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``finite_network_strict_pair).type
  let mut binders := 0
  let some selected := selection.readouts[0]? | throwError "A readout selection is required"
  for step in selected.path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected original readout occurrence is absent"
  unless binders == 11 && e.getAppFn == .bvar 6 &&
      e.getAppArgs[0]? == some (.bvar 1) do
    throwError "The selected readout is not the original function at its state binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_network_strict_pair.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.family
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

def analysisSource : Analysis.Source (@finite_network_strict_pair.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@finite_network_strict_pair.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "The same finite-network trajectory has actual two-site occupancies and inhibited conformation; no finite law reader or native continuation bridge is supplied." }

namespace Dual
abbrev signature : Signature where
  Params := Σ I : Type u, Option (Finset I) → ℝ
  State p := Option (Finset p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p x => p.2 x

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p := fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} := realize signature (fun _ _ _ => 0) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (k : Rates I) (f p : Option (Finset I) → ℝ),
    (∑ x, R.readout () ⟨I, f⟩ x * (generator k *ᵥ p) x) =
      ∑ x, backward k f x * p x

private def unitRates : Rates (ULift.{u} Unit) where
  a := fun _ => 1
  b := fun _ => 1
  eta := 1
  theta := 1
  a_pos _ := by norm_num
  b_pos _ := by norm_num
  eta_pos := by norm_num
  theta_pos := by norm_num

private def f : Option (Finset (ULift.{u} Unit)) → ℝ
  | none => 0
  | some _ => 1

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hb := h unitRates f (Pi.single none 1)
  simp [rejected, realize, backward, Fintype.sum_option, f, unitRates] at hb

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, f⟩, none, some ∅, ?_⟩
  norm_num [actual, realize, actualReadout, f]

def family : Registration arena.{u} (type_of% @dual_backward.{u}) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@dual_backward.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def selection : Contract.SourceSelection where
  owner := `D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
  definition := none
  coordinates := #[0, 4]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body",
      "fn", "arg", "arg", "body", "fn", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``dual_backward).type
  let mut binders := 0
  let some selected := selection.readouts[0]? | throwError "A readout selection is required"
  for step in selected.path do
    e ← match e, step with
      | .forallE _ _ b _, "body" | .lam _ _ b _, "body" =>
        binders := binders + 1
        pure b
      | .app f _, "fn" => pure f
      | .app _ a, "arg" => pure a
      | _, _ => throwError "The selected original readout occurrence is absent"
  unless binders == 7 && e.getAppFn == .bvar 2 &&
      e.getAppArgs[0]? == some (.bvar 0) do
    throwError "The selected readout is not the original function at its state binder"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@dual_backward.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Dual.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork.Dual.family
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
end Dual

#print axioms family
#print axioms registration
#print axioms analysisSource
#print axioms analysis
end Reg.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
