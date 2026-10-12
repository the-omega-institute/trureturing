import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail

open scoped ENNReal
open Finset MeasureTheory
open _root_.D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
open _root_.D5.S0.Computability.Coding.PrefixFreeCode
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.HistoricalDepthBudgetJointExtremum
open _root_.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
universe u

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- Observe the actual first historical law's surviving mass. -/
def actual : Realization signature :=
  realize signature (fun _ _ mass => mass.toReal) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

/-- The complete original telescope and transport inequality, with one mass readout. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {A : Type u} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    (a₀ : A) (δ : ℝ) (hδ : 0 < δ) (hd : 2 ≤ Fintype.card A)
    (hδmax : δ ≤ 1 / (Fintype.card A : ℝ))
    (q₀ q₁ : List A → A → ℝ) (hq₀ : NormalizedRows q₀) (hq₁ : NormalizedRows q₁)
    (hlo : ∀ v z, δ ≤ q₁ v z)
    (c : ℝ) (hc : 0 ≤ c) (hrow : ∀ v z, q₀ v z ≤ c * q₁ v z)
    (b : ℕ → ℕ) (F : Set (List A)) (hF : Legal b F)
    (a : ℝ) (ha : 0 ≤ a) (N : ℕ)
    (hbud : ∀ n, N < n → (b n : ℝ) ≤ a ^ n)
    (hρ : a * (1 - ((Fintype.card A : ℝ) - 1) * δ) < 1),
    R.readout () () ((trajectoryLaw q₀ hq₀) (deletedSet F)ᶜ) ≤
      c ^ N * ((trajectoryLaw q₁ hq₁) (deletedSet F)ᶜ).toReal +
      (a * (1 - ((Fintype.card A : ℝ) - 1) * δ)) *
        (c * (a * (1 - ((Fintype.card A : ℝ) - 1) * δ))) ^ N /
        (1 - a * (1 - ((Fintype.card A : ℝ) - 1) * δ))

theorem actual_law : arena.{u}.Law actual :=
  @historical_survivor_transport.{u}

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro law
  let A := ULift.{u} (Fin 2)
  letI : MeasurableSpace A := ⊤
  letI : MeasurableSingletonClass A := ⟨fun _ => trivial⟩
  let q : List A → A → ℝ := fun _ _ => 1 / 2
  have hq : NormalizedRows q := by
    constructor
    · intro v z; norm_num [q]
    · intro v; norm_num [q, A, Finset.sum_const]
  have hF : Legal (fun _ => 0) (∅ : Set (List A)) := by
    constructor
    · intro v hv; simp at hv
    · constructor
      · simp
      · intro n; simp [level]
  have hd : 2 ≤ Fintype.card A := by simp [A]
  have hmax : (1 / 2 : ℝ) ≤ 1 / (Fintype.card A : ℝ) := by norm_num [A]
  have hlo : ∀ v z, (1 / 2 : ℝ) ≤ q v z := by intro v z; exact le_rfl
  have hrow : ∀ v z, q v z ≤ (1 : ℝ) * q v z := by intro v z; simp
  have hbud : ∀ n : ℕ, 0 < n → ((0 : ℕ) : ℝ) ≤ (0 : ℝ) ^ n := by
    intro n _
    simpa only [Nat.cast_zero] using pow_nonneg (by norm_num : (0 : ℝ) ≤ 0) n
  have hrho : (0 : ℝ) * (1 - ((Fintype.card A : ℝ) - 1) * (1 / 2)) < 1 := by
    norm_num
  letI : Encodable (List A) := Encodable.ofCountable _
  let tie : ℕ → LinearOrder (List A) := fun _ =>
    LinearOrder.lift' Encodable.encode Encodable.encode_injective
  letI : IsProbabilityMeasure (trajectoryLaw q hq) :=
    ((historical_depth_budget_joint_extremum (⟨0⟩ : A) (1 / 2)
      (by norm_num) hd hmax (fun _ => 0) tie).2.1 q hq).1
  have h := law (⟨0⟩ : A) (1 / 2) (by norm_num) hd hmax q q hq hq hlo
    1 (by norm_num) hrow (fun _ => 0) ∅ hF 0 (by norm_num) 0 hbud hrho
  norm_num [rejected, realize, deletedSet] at h

theorem sensitivity : Sensitivity arena.{u} actual := by
  constructor
  · intro i
    refine ⟨rejected, ?_, rfl, rejected_law⟩
    intro j hj
    exact (hj (@Subsingleton.elim Unit _ j i)).elim
  · intro e; exact nomatch e

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def record : Registration arena.{u} (type_of% (@historical_survivor_transport.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := sensitivity
  dependence := dependence

noncomputable def transportRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@historical_survivor_transport.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail.transport,
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail.record,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨record.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ mass => mass.toReal) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg"],
      stateBinder := 0,
      functionOperand := false,
      stateOperand := some #["arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `autoImplicit, value := .bool false },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms actual_law
#print axioms rejected_law
#print axioms record
#print axioms transportRegistration

end
end Reg.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.EffectiveRationalTransportTail
