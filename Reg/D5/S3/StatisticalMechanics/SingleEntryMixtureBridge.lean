import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.AuricFib
import D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
namespace Reg.D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
open _root_.D5.S3.StatisticalMechanics.SingleEntryFiniteNetwork
open _root_.D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Σ I : Type u, (ℝ → Option (Finset I) → ℝ) × Finset I
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actualReadout : ∀ role p, (signature.{u}).State p → (signature.{u}).Output role p :=
  fun _ p t => p.2.1 t (some p.2.2)

def actualAnchor : ∀ (_ : (signature.{u}).Anchor) p, (signature.{u}).State p :=
  fun e => nomatch e

def actual : Realization signature.{u} := realize signature actualReadout actualAnchor

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) actualAnchor

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I] (k : Rates I)
    (p : ℝ → Option (Finset I) → ℝ), ForwardSolution k p →
    ∀ t : ℝ, 0 < t → ∀ S T : Finset I, ¬ S ⊆ T → ¬ T ⊆ S →
      p t (some S) * p t (some T) <
        R.readout () ⟨I, p, S ∩ T⟩ t * p t (some (S ∪ T))

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
  obtain ⟨p, hp, hn⟩ := (finite_network_strict_pair unitRates).1
  intro h
  let i : ULift.{u} (Fin 2) := ULift.up 0
  let j : ULift.{u} (Fin 2) := ULift.up 1
  have hij : i ≠ j := by simp [i, j]
  have hb := h unitRates p hp 1 (by norm_num) {i} {j}
    (by simpa using hij) (by simpa using Ne.symm hij)
  have hpn := (hn 1 (by norm_num)).1
  change p 1 (some {i}) * p 1 (some {j}) < 0 * p 1 (some ({i} ∪ {j})) at hb
  rw [zero_mul] at hb
  exact (not_lt_of_ge (mul_nonneg (hpn _) (hpn _))) hb

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, (fun t _ => t), ∅⟩, 0, 1, ?_⟩
  norm_num [actual, realize, actualReadout]

def family : Registration arena.{u} (type_of% @finite_network_strict_mtp2.{u}) where
  actual := realize signature actualReadout actualAnchor
  bridge := Iff.rfl
  variation := ⟨@finite_network_strict_mtp2.{u}, rejected, rejected_law⟩
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
  owner := `D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
  definition := none
  coordinates := #[0, 4, 8, 9]
  readouts := #[{
    path := #["body", "body", "body", "body", "body", "body",
      "body", "body", "body", "body", "body", "body", "arg", "fn", "arg"]
    stateBinder := 6
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

run_cmd do
  let mut e := (← Lean.getConstInfo ``finite_network_strict_mtp2).type
  for _ in [:12] do
    match e with
    | .forallE _ _ b _ => e := b
    | _ => throwError "Expected the complete twelve-binder strict-MTP2 telescope"
  for step in #["arg", "fn", "arg"] do
    e ← match e, step with
      | .app _ a, "arg" => pure a
      | .app f _, "fn" => pure f
      | _, _ => throwError "The selected actual intersection mass is absent"
  unless e.getAppFn == .bvar 7 && e.getAppArgs.size == 2 &&
      e.getAppArgs[0]? == some (.bvar 5) do
    throwError "The selected operand is not the original two-argument trajectory"

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_network_strict_mtp2.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.SingleEntryMixtureBridge.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.SingleEntryMixtureBridge.family
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

def analysisSource : Analysis.Source (@finite_network_strict_mtp2.{u}) :=
  Analysis.Source.ofRegistration _ family .exact selection

def analysis : AuricFib.Contract.Application (@finite_network_strict_mtp2.{u}) where
  evidence := .typed {
    source := analysisSource
    plan := { task := (), initial := [], additions := [[()]] }
    acquisition := .unavailable
      "The actual sites and inhibited conformation are retained in the same forward law; a finite native reader for the continuous-time trajectory is unacquired." }

#print axioms family
#print axioms registration
#print axioms analysis
end Reg.D5.S3.StatisticalMechanics.SingleEntryMixtureBridge
