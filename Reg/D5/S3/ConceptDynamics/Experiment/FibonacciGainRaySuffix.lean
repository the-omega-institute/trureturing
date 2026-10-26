import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix
import Reg.Support.DependentFamily

/-! Source-bound whole-family audit of the short-sensitive-suffix implication. -/

namespace Reg.D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix

open _root_.D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

abbrev Parameters := Σ d : ℕ, Σ N : ℕ, Matrix (Fin (d + 1)) (Fin N) ℝ

abbrev signature : Signature where
  Params := Parameters
  State p := Fin p.2.1 → ℝ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.1 + 1) → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The same fixed matrix is used in the collinearity premise and the conclusion. -/
def actual : Realization signature :=
  realize signature (fun _ p z => p.2.2 *ᵥ z) (fun e => nomatch e)

/-- Intervene only on the collinearity-premise observation. -/
def rejected_premise : Realization signature :=
  realize signature (fun role p z => if role = 0 then 0 else p.2.2 *ᵥ z)
    (fun e => nomatch e)

/-- Intervene only on the observation asserted to vanish. -/
def rejected_conclusion : Realization signature :=
  realize signature (fun role p z => if role = 1 then (fun _ => 1) else p.2.2 *ᵥ z)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d N : ℕ) (_hd : 1 ≤ d) (_hN : 1 ≤ N)
    (w : List Bool) (_hw : w.length = N - 1)
    (C : Matrix (Fin (d + 1)) (Fin N) ℝ)
    (_regime : false ∉ w ∨ ∃ n : ℕ, ∃ p q : List Bool,
      w = p ++ false :: q ∧ false ∉ p ∧ n = p.length + 1 ∧ N - n < d + 1),
    (∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin (d + 1) → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, R.readout 0 ⟨d, N, C⟩ (reads w θ β δ) = s • β) →
    ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin (d + 1) → ℝ, β ≠ 0 → ∀ δ : ℝ,
      R.readout 1 ⟨d, N, C⟩ (reads w θ β δ) = 0

private theorem rejected_premise_law : ¬ arena.Law rejected_premise := by
  intro h
  have hc : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin 2 → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, rejected_premise.readout 0 ⟨1, 1, fun _ _ => 1⟩
        (reads [] θ β δ) = s • β := by
    intros
    exact ⟨0, by simp [rejected_premise, realize]⟩
  have he := h 1 1 (by omega) (by omega) [] rfl (fun _ _ => 1)
    (Or.inl (by simp)) hc (1/2) (by norm_num) (by norm_num) ![1,0]
    (by intro hz; have hh := congrFun hz 0; norm_num at hh) 0
  have hh := congrFun he 0
  change (∑ i : Fin 1, (1 : ℝ) * reads [] (1/2) (![1,0] : Fin 2 → ℝ) 0 i) = 0 at hh
  norm_num [reads, gain, source,
    _root_.D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings.observe,
    _root_.D5.S3.ConceptDynamics.Experiment.SelfCalibratingRulings.matrix,
    _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
    Matrix.mulVec, dotProduct, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_two, Pi.zero_apply] at hh

private theorem rejected_conclusion_law : ¬ arena.Law rejected_conclusion := by
  intro h
  have hc : ∀ θ : ℝ, 0 < θ → θ < 1 → ∀ β : Fin 2 → ℝ, β ≠ 0 → ∀ δ : ℝ,
      ∃ s : ℝ, rejected_conclusion.readout 0 ⟨1, 1, 0⟩ (reads [] θ β δ) = s • β := by
    intros
    exact ⟨0, by simp [rejected_conclusion, realize]⟩
  have he := h 1 1 (by omega) (by omega) [] rfl 0
    (Or.inl (by simp)) hc (1/2) (by norm_num) (by norm_num) ![1,0]
    (by intro hz; have hh := congrFun hz 0; norm_num at hh) 0
  have hh := congrFun he 0
  change (1 : ℝ) = 0 at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1, 1, fun _ _ => 1⟩, 0, (fun _ => 1), ?_⟩
  intro he
  have hh := congrFun he 0
  change (∑ i : Fin 1, (1 : ℝ) * (0 : Fin 1 → ℝ) i) = ∑ _i : Fin 1, (1 : ℝ) * 1 at hh
  norm_num at hh

def source_registration : Registration arena (type_of% (@short_suffix_annihilates)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@short_suffix_annihilates, rejected_premise, rejected_premise_law⟩
  sensitivity := by
    constructor
    · intro role
      fin_cases role
      · refine ⟨rejected_premise, ?_, rfl, rejected_premise_law⟩
        intro j hj
        fin_cases j
        · exact (hj rfl).elim
        · rfl
      · refine ⟨rejected_conclusion, ?_, rfl, rejected_conclusion_law⟩
        intro j hj
        fin_cases j
        · rfl
        · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@short_suffix_annihilates) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix.unit
  realizationName :=
    `Reg.D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p z => p.2.2 *ᵥ z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix
    definition := none
    coordinates := #[0, 1, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "domain",
        "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.Experiment.FibonacciGainRaySuffix
