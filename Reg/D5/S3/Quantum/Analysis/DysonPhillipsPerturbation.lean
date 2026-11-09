import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
import Reg.Support.DependentFamily

/-! Full-source dependent-family audit of the Dyson–Phillips theorem. -/

open scoped Nat Topology
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.DysonPhillipsPerturbation

/-- The observation is the real norm comparison in the factorial estimate. -/
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

/-- Every original Banach fiber and every clause is retained. Interventions
replace just the comparison in the all-index term estimate. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : ℝ → E →L[ℂ] E) (B : E →L[ℂ] E)
    (h0 : ∀ t, t ≤ 0 → S t = 1)
    (hadd : ∀ s t, 0 ≤ s → 0 ≤ t → S (s + t) = S s * S t)
    (hnorm : ∀ t, ‖S t‖ ≤ 1)
    (hcont : ∀ x, Continuous fun t => S t x),
    (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → ∀ x : E,
      R.readout () () ‖dysonTerm S B n t x‖ ((‖B‖ * t) ^ n / n ! * ‖x‖)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ x : E, Summable fun n => dysonTerm S B n t x) ∧
    ∃ U : ℝ → E →L[ℂ] E,
      (∀ t, t ≤ 0 → U t = 1) ∧
      (∀ x, Continuous fun t => U t x) ∧
      (∀ t, 0 ≤ t → ∀ x, U t x = S t x +
        ∫ r in (0 : ℝ)..t, S (t - r) (B (U r x))) ∧
      (∀ V : ℝ → E →L[ℂ] E,
        ((∀ t, t ≤ 0 → V t = 1) ∧
         (∀ x, Continuous fun t => V t x) ∧
         (∀ t, 0 ≤ t → ∀ x, V t x = S t x +
           ∫ r in (0 : ℝ)..t, S (t - r) (B (V r x)))) → V = U) ∧
      (∀ t x, U t x = ∑' n, dysonTerm S B n (max t 0) x) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → U (s + t) = (U s).comp (U t)) ∧
      (∀ t, ‖U t‖ ≤ Real.exp (‖B‖ * max t 0)) ∧
      (∀ (T : ℝ) (X : ℝ → E) (x : E), ContinuousOn X (Set.Icc 0 T) →
        (∀ t ∈ Set.Icc (0 : ℝ) T, X t = S t x +
          ∫ r in (0 : ℝ)..t, S (t - r) (B (X r))) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, X t = U t x)

private theorem actual_law : arena.{u}.Law actual := @bounded_perturbation.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hzero : ∀ t : ℝ, ‖(fun _ : ℝ => (1 : PUnit.{u+1} →L[ℂ] PUnit.{u+1})) t‖ ≤ 1 :=
    fun _ => ContinuousLinearMap.norm_id_le
  have hc : ∀ x : PUnit.{u+1}, Continuous fun _ : ℝ =>
      (1 : PUnit.{u+1} →L[ℂ] PUnit.{u+1}) x := fun _ => continuous_const
  have hp := h (fun _ => (1 : PUnit.{u+1} →L[ℂ] PUnit.{u+1})) 0
    (fun _ _ => rfl) (fun _ _ _ _ => by simp) hzero hc
  exact hp.1 0 0 le_rfl 0

def family : Registration arena.{u} (type_of% (@bounded_perturbation.{u})) where
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
    (@bounded_perturbation.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.DysonPhillipsPerturbation.perturbationUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.DysonPhillipsPerturbation.family
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
    owner := `D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.DysonPhillipsPerturbation
