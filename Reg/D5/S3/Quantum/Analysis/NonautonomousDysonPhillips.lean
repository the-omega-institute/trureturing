import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! Full-telescope dependent-family audits of the causal estimate and evolution. -/

open scoped Nat Topology NNReal
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

private def zeroSemigroup : Contraction PUnit.{u+1} where
  operator _ := 1
  zero := rfl
  add _ _ := by ext x; rfl
  norm_le _ := ContinuousLinearMap.norm_id_le
  continuous _ := continuous_const

namespace Iterate

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E),
    ∀ {r T M C : ℝ} (hrT : r ≤ T)
    (hB : ContinuousOn B (Set.Icc r T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc r T, ‖B s‖ ≤ M)
    {v : ℝ → E} (hv : ContinuousOn v (Set.Icc r T))
    (hvC : ∀ s ∈ Set.Icc r T, ‖v s‖ ≤ C)
    (n : ℕ) {t : ℝ} (ht : t ∈ Set.Icc r T),
    R.readout () () ‖causalIterate S B r v n t‖ (C * ((M * (t - r)) ^ n / n !))

private theorem actual_law : arena.{u}.Law actual := @causal_iterate_bound.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h zeroSemigroup (fun _ => 0) (r := 0) (T := 0) (M := 0) (C := 0)
    le_rfl continuous_const.continuousOn le_rfl (fun _ _ => by simp)
    (v := fun _ => 0) continuous_const.continuousOn (fun _ _ => by simp)
    0 ⟨le_rfl, le_rfl⟩

def family : Registration arena.{u} (type_of% (@causal_iterate_bound.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@causal_iterate_bound.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.iterateUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.Iterate.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Iterate

namespace Evolution

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E),
    ∀ {T M : ℝ} (hT : 0 ≤ T)
    (hB : ContinuousOn B (Set.Icc 0 T)) (hM : 0 ≤ M)
    (hBM : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M),
    (∀ n t r, (t, r) ∈ triangle T → ∀ x : E,
      R.readout () () ‖term S B n t r x‖ (M ^ n * (t - r) ^ n / n ! * ‖x‖)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      HasSum (fun n => term S B n t r x) (evolution S B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => evolution S B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      evolution S B t r x = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (evolution S B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, evolution S B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = evolution S B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (evolution S B t s).comp (evolution S B s r) = evolution S B t r) ∧
    (∀ t r, (t, r) ∈ triangle T → ‖evolution S B t r‖ ≤ Real.exp (M * (t - r))) ∧
    (∀ n r x, term S B (n + 1) r r x = 0) ∧
    (∀ (B' : ℝ → E →L[ℂ] E) t r, (t, r) ∈ triangle T →
      Set.EqOn B B' (Set.Icc r t) → evolution S B t r = evolution S B' t r) ∧
    (∀ (Bzero : E →L[ℂ] E), Set.EqOn B (fun _ => Bzero) (Set.Icc 0 T) →
      ∀ t r, (t, r) ∈ triangle T → ∀ x : E, evolution S B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Bzero (t - r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t, r) ∈ triangle T →
      evolution S B t r = S.action (t - r))

private theorem actual_law : arena.{u}.Law actual := @nonautonomous_bounded_perturbation.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := h zeroSemigroup (fun _ => 0) (T := 0) (M := 0)
    le_rfl continuous_const.continuousOn le_rfl (fun _ _ => by simp)
  exact hp.1 0 0 0 ⟨le_rfl, le_rfl, le_rfl⟩ 0

def family : Registration arena.{u} (type_of% (@nonautonomous_bounded_perturbation.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (show j = i from @Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
    intro he
    have hb : (1 : ℝ) ≤ 0 := Eq.mp (congrFun he 0) le_rfl
    norm_num at hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@nonautonomous_bounded_perturbation.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.evolutionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.Evolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Evolution
end Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
