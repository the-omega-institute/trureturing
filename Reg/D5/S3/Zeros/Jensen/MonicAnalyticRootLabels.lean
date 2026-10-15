import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Zeros.Jensen.MonicAnalyticRootLabels
import Reg.Support.DependentFamily
import Mathlib.Analysis.Convex.Contractible

open _root_.D5.S3.Zeros.Jensen.MonicAnalyticRootLabels
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Polynomial Set Topology

noncomputable section
open scoped Classical
namespace Reg.D5.S3.Zeros.Jensen.MonicAnalyticRootLabels

namespace Covering
abbrev Inputs := Σ _ : ℂ → Polynomial ℂ, Set ℂ
abbrev ZeroGraph (p : Inputs) := {e : p.2 × ℂ // (p.1 e.1).eval e.2 = 0}
abbrev signature : Signature where
  Params := Inputs
  State p := ZeroGraph p → p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f => decide (IsCoveringMap f)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    (hΩ : IsOpen Ω) (hm : ∀ t ∈ Ω, (P t).Monic)
    (hd : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (hs : ∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 → (P t).derivative.eval z ≠ 0),
    R.readout () ⟨P, Ω⟩ (fun e => e.1.1) = true

private theorem positive : arena.Law actual := by
  intro P Ω q hΩ hm hd ha hs
  exact decide_eq_true (monic_analytic_simple_root_projection_isCovering P Ω q hΩ hm hd ha hs)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  have hh := h (fun _ => (X : Polynomial ℂ)) univ 1 isOpen_univ
    (fun _ _ => monic_X) (fun _ _ => by simp)
    (fun _ _ _ _ => analyticAt_const) (fun _ _ _ _ => by simp)
  change false = true at hh
  exact Bool.false_ne_true hh

abbrev complexInputs : Inputs := ⟨fun _ => X, univ⟩
abbrev zeroBase : (Set.univ : Set ℂ) := ⟨0, mem_univ _⟩

private theorem constant_not_covering :
    ¬ IsCoveringMap (fun _ : ZeroGraph complexInputs => zeroBase) := by
  intro h
  have hrange : (fun _ : ZeroGraph complexInputs => zeroBase) '' univ = {zeroBase} := by
    apply Set.Nonempty.image_const
    exact ⟨⟨(zeroBase, 0), by simp [complexInputs]⟩, mem_univ _⟩
  have hopen : IsOpen ({zeroBase} : Set (Set.univ : Set ℂ)) := by
    rw [← hrange]
    exact h.isOpenMap _ isOpen_univ
  have hzero : IsOpen ({(0 : ℂ)} : Set ℂ) := by
    have hi := isOpen_univ.isOpenMap_subtype_val _ hopen
    simpa only [Set.image_singleton] using hi
  exact not_isOpen_singleton (0 : ℂ) hzero

private theorem projection_covering :
    IsCoveringMap (fun e : ZeroGraph complexInputs => e.1.1) := by
  exact monic_analytic_simple_root_projection_isCovering (fun _ => X) univ 1 isOpen_univ
    (fun _ _ => monic_X) (fun _ _ => by simp)
    (fun _ _ _ _ => analyticAt_const) (fun _ _ _ _ => by simp)

def evidence : Registration arena
    (type_of% (@monic_analytic_simple_root_projection_isCovering)) where
  actual := actual
  bridge := by
    constructor
    · intro h P Ω q hΩ hm hd ha hs
      exact decide_eq_true (h P Ω q hΩ hm hd ha hs)
    · intro h P Ω q hΩ hm hd ha hs
      exact of_decide_eq_true (h P Ω q hΩ hm hd ha hs)
  variation := ⟨positive, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨complexInputs, (fun e => e.1.1), (fun _ => zeroBase), ?_⟩
    change decide (IsCoveringMap (fun e : ZeroGraph complexInputs => e.1.1)) ≠
      decide (IsCoveringMap (fun _ : ZeroGraph complexInputs => zeroBase))
    rw [decide_eq_true projection_covering, decide_eq_false constant_not_covering]
    decide

-- Whole proposition reification at its actual map operand: Boolean output is data,
-- retaining the original predicate instead of weakening it to properness.
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monic_analytic_simple_root_projection_isCovering)
    (type_of% (realize signature (fun _ _ f => decide (IsCoveringMap f))
      (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Zeros.Jensen.MonicAnalyticRootLabels.monic_analytic_simple_root_projection_isCovering.audit
  realizationName := `Reg.D5.S3.Zeros.Jensen.MonicAnalyticRootLabels.Covering.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f => decide (IsCoveringMap f))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.MonicAnalyticRootLabels
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms audit
end Covering

namespace Labels
abbrev signature : Signature where
  Params := ℕ
  State q := Fin q → ℂ → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Fin q → ℂ → ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => fun _ _ => 0) (fun e => nomatch e)

-- The unchanged first and third clauses retain the same b, P and Ω. Only the
-- actual b-function occurrence inside exhaustion is selected for intervention.
def arena : Arena where
  signature := signature
  Law R := ∀ (P : ℂ → Polynomial ℂ) (Ω : Set ℂ) (q : ℕ)
    [SimplyConnectedSpace Ω]
    (hΩ : IsOpen Ω) (hm : ∀ t ∈ Ω, (P t).Monic)
    (hd : ∀ t ∈ Ω, (P t).natDegree = q)
    (ha : ∀ i ≤ q, ∀ t ∈ Ω, AnalyticAt ℂ (fun v => (P v).coeff i) t)
    (hs : ∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 → (P t).derivative.eval z ≠ 0)
    (t₀ : Ω),
    ∃ b : Fin q → ℂ → ℂ,
      (∀ i, ∀ t ∈ Ω, AnalyticAt ℂ (b i) t) ∧
      (∀ t ∈ Ω, ∀ z : ℂ, (P t).eval z = 0 ↔ ∃! i, (R.readout () q b) i t = z) ∧
      (∀ i, ∀ c : ℂ → ℂ,
        (∀ t ∈ Ω, AnalyticAt ℂ c t) →
        (∀ t ∈ Ω, (P t).eval (c t) = 0) → c t₀ = b i t₀ →
        ∀ t ∈ Ω, c t = b i t)

private theorem negative : ¬ arena.Law rejected := by
  intro h
  letI : ContractibleSpace (Set.univ : Set ℂ) :=
    (convex_univ : Convex ℝ (Set.univ : Set ℂ)).contractibleSpace Set.univ_nonempty
  obtain ⟨b, hb, hexhaust, hunique⟩ := h (fun _ => X - C (1 : ℂ)) univ 1 isOpen_univ
    (fun _ _ => monic_X_sub_C 1) (fun _ _ => natDegree_X_sub_C 1)
    (fun _ _ _ _ => analyticAt_const) (fun _ _ _ _ => by simp)
    ⟨0, mem_univ _⟩
  obtain ⟨i, hi, _⟩ := (hexhaust 0 (mem_univ _) 1).mp (by simp)
  change (0 : ℂ) = 1 at hi
  exact zero_ne_one hi

def evidence : Registration arena
    (type_of% (@monic_analytic_simple_roots_have_global_labels)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨monic_analytic_simple_roots_have_global_labels, rejected, negative⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, negative⟩
      intro j hj
      exact (hj (@Subsingleton.elim Unit _ j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(1 : ℕ), (fun _ _ => (0 : ℂ)), (fun _ _ => (1 : ℂ)), ?_⟩
    intro he
    have h := congrArg (fun b : Fin 1 → ℂ → ℂ => b 0 0) he
    change (0 : ℂ) = 1 at h
    exact zero_ne_one h

-- Selector path requires confirmation against raw compiled Expr; its logical
-- route is: conclusion Exists b; And second; And first (exhaustion); Iff right;
-- ExistsUnique i; Eq left; b-function head. No P/Ω/proof discarded from Law.
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@monic_analytic_simple_roots_have_global_labels)
    (type_of% (realize signature (fun _ _ b => b) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Zeros.Jensen.MonicAnalyticRootLabels.monic_analytic_simple_roots_have_global_labels.audit
  realizationName := `Reg.D5.S3.Zeros.Jensen.MonicAnalyticRootLabels.Labels.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Zeros.Jensen.MonicAnalyticRootLabels
    definition := none
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg", "body", "body", "body", "arg", "arg", "body",
        "fn", "arg", "fn", "fn"]
      stateBinder := 10
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms evidence
#print axioms audit
end Labels
end Reg.D5.S3.Zeros.Jensen.MonicAnalyticRootLabels
