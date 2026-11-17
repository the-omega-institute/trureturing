import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
import Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

open scoped Nat Topology NNReal
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis
open _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips

namespace StrongIterate

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E),
    ∀ {r H M C : ℝ} (_hrH : r ≤ H)
    (_hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc r H)) (_hM : 0 ≤ M)
    (_hBM : ∀ s ∈ Set.Icc r H, ‖B s‖ ≤ M)
    {v : ℝ → E} (_hv : ContinuousOn v (Set.Icc r H))
    (_hvC : ∀ s ∈ Set.Icc r H, ‖v s‖ ≤ C)
    (n : ℕ) {t : ℝ} (_ht : t ∈ Set.Icc r H),
    R.readout () () ‖causalIterate S B r v n t‖ (C * ((M * (t - r)) ^ n / n !))

private theorem actual_law : arena.{u}.Law actual := @fixedWstrong.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h zeroSemigroup (fun _ => 0) (r := 0) (H := 0) (M := 0) (C := 0)
    le_rfl (fun _ => continuous_const.continuousOn) le_rfl (fun _ _ => by simp)
    (v := fun _ => 0) continuous_const.continuousOn (fun _ _ => by simp)
    0 ⟨le_rfl, le_rfl⟩

def family : Registration arena.{u} (type_of% (@fixedWstrong.{u})) where
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
    (@fixedWstrong.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips.strongIterateUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips.StrongIterate.family
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
    owner := `D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end StrongIterate

namespace StrongEvolution

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B : ℝ → E →L[ℂ] E),
    ∀ {T : ℝ} (_hT : 0 ≤ T)
    (_hB : ∀ z : E, ContinuousOn (fun s => B s z) (Set.Icc 0 T)),
    (∃ M : ℝ, 0 ≤ M ∧ ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) ∧
    ∀ M : ℝ, 0 ≤ M → (∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ M) →
    (∀ n t r, (t, r) ∈ triangle T → ∀ x : E,
      R.readout () () ‖term S B n t r x‖ (M ^ n * (t - r) ^ n / n ! * ‖x‖)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      HasSum (fun n => term S B n t r x) (strongEvolution S B t r x)) ∧
    (∀ x : E, ContinuousOn (fun p : ℝ × ℝ => strongEvolution S B p.1 p.2 x) (triangle T)) ∧
    (∀ t r, (t, r) ∈ triangle T → ∀ x : E,
      strongEvolution S B t r x = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (strongEvolution S B s r x))) ∧
    (∀ r ∈ Set.Icc 0 T, strongEvolution S B r r = 1) ∧
    (∀ r ∈ Set.Icc 0 T, ∀ (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc r T) →
      (∀ t ∈ Set.Icc r T, X t = S.action (t - r) x +
        ∫ s in r..t, S.action (t - s) (B s (X s))) →
      ∀ t ∈ Set.Icc r T, X t = strongEvolution S B t r x) ∧
    (∀ r s t, 0 ≤ r → r ≤ s → s ≤ t → t ≤ T →
      (strongEvolution S B t s).comp (strongEvolution S B s r) = strongEvolution S B t r) ∧
    (∀ t r, (t, r) ∈ triangle T → ‖strongEvolution S B t r‖ ≤ Real.exp (M * (t - r))) ∧
    (∀ n r x, term S B (n + 1) r r x = 0) ∧
    (∀ (B' : ℝ → E →L[ℂ] E) t r, (t, r) ∈ triangle T →
      Set.EqOn B B' (Set.Icc r t) → strongEvolution S B t r = strongEvolution S B' t r) ∧
    (∀ (Bzero : E →L[ℂ] E), Set.EqOn B (fun _ => Bzero) (Set.Icc 0 T) →
      ∀ t r, (t, r) ∈ triangle T → ∀ x : E, strongEvolution S B t r x =
        DysonPhillipsPerturbation.dysonSum S.action Bzero (t - r) x) ∧
    (Set.EqOn B (fun _ => 0) (Set.Icc 0 T) → ∀ t r, (t, r) ∈ triangle T →
      strongEvolution S B t r = S.action (t - r))

private theorem actual_law : arena.{u}.Law actual := @fullstrongconstruction.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := h zeroSemigroup (fun _ => 0) (T := 0)
    le_rfl (fun _ => continuous_const.continuousOn)
  exact (hp.2 0 le_rfl (fun _ _ => by simp)).1 0 0 0 ⟨le_rfl, le_rfl, le_rfl⟩ 0

def family : Registration arena.{u} (type_of% (@fullstrongconstruction.{u})) where
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
    (@fullstrongconstruction.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips.strongEvolutionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips.StrongEvolution.family
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
    owner := `D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end StrongEvolution
end Reg.D5.S3.Quantum.Analysis.StrongNonautonomousDysonPhillips
