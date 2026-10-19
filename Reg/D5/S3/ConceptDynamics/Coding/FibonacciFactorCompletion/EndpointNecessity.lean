import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.ExactOriginal57
noncomputable section
open EndpointNecessity FixedSources CanonicalGeometry TailGeometry

abbrev observationSignature : Signature.{0,0,0,0,0} where
  Params := Unit
  State := fun _ => ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ b => b) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{0,0,0,0,0} observationSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev sourceArena : Arena.{0,0,0,0,0} where
  signature := observationSignature
  Law r := ∀ (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U V : Bool → List Label) (W : Bool → List Color)
    (L : ℕ) (hL : 0 < L)
    (hUlen : ∀ i, (U i).length = L) (hVlen : ∀ i, (V i).length = L)
    (hWlen : ∀ i, (W i).length = L)
    (hU : ∀ i, LegalWord s1 s1 (U i)) (hV : ∀ i, LegalWord s2 s2 (V i))
    (ξ η : ℕ → Label) (x y : ℕ → ℝ) (path1 path2 : ℕ → Guard)
    (b : ℝ) (hb : 0 ≤ b)
    (feasible : ∀ zs : List Bool,
      ClosedOriginalTailExtension b (P ++ choiceBlocks U zs) (h ++ choiceBlocks W zs) ξ x path1 ∧
      ClosedOriginalTailExtension b (Q ++ choiceBlocks V zs) (h ++ choiceBlocks W zs) η y path2) ,
    familyEndpointBudget P Q h U V W L ≤ r.readout () () b ∧
      familyEndpointBudget P Q h U V W L ∈ coefficientField

theorem constant_blocks {α : Type} (v : α) (zs : List Bool) :
    choiceBlocks (fun _ => [v]) zs = List.replicate zs.length v := by
  induction zs with
  | nil => rfl
  | cons i zs ih => simp [choiceBlocks, ih, List.replicate_succ]

theorem rejected_law : ¬ sourceArena.Law rejected := by
  intro h
  let b : ℝ := |cut 0| + |cut 1| + 1
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have supported : InSupport .G0 0 := by
    refine ⟨by norm_num, ?_⟩
    change (0 : ℝ) ≤ phi
    linarith [tail_arithmetic.2.2.2.2.2]
  have closed : ClosedExpanded b (0 : Color) 0 := by
    refine ⟨supported, ?_, ?_⟩
    · change cut 0 - b ≤ 0
      dsimp [b]
      linarith [le_abs_self (cut 0), abs_nonneg (cut 1)]
    · change 0 ≤ cut 1 + b
      dsimp [b]
      linarith [neg_abs_le (cut 1), abs_nonneg (cut 0)]
  have extension (zs : List Bool) : ClosedOriginalTailExtension b
      ([] ++ choiceBlocks (fun _ => [Label.L0]) zs)
      ([] ++ choiceBlocks (fun _ => [(0 : Color)]) zs)
      (fun _ => .L0) (fun _ => 0) (fun _ => .G0) := by
    refine ⟨(fun _ => .L0), (fun _ => 0), (fun _ => .G0), rfl,
      (fun _ => rfl), (fun _ => supported), ?_, ?_, ?_, ?_⟩
    · intro p
      simp [branch, shift]
    · intro p hp
      simp only [List.nil_append, constant_blocks] at hp ⊢
      simp
    · intro p
      exact ⟨rfl, rfl, rfl⟩
    · intro p hp
      simpa only [List.nil_append, constant_blocks, List.getElem_replicate] using closed
  have nonnegative := (family_endpoint_certificates .G0 .G0 [] [] [] rfl rfl
    (fun _ => [.L0]) (fun _ => [.L0]) (fun _ => [(0 : Color)]) 1 (by decide)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)).1
  have impossible := (h .G0 .G0 [] [] [] rfl rfl
    (fun _ => [.L0]) (fun _ => [.L0]) (fun _ => [(0 : Color)]) 1 (by decide)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => .L0) (fun _ => .L0) (fun _ => 0) (fun _ => 0)
    (fun _ => .G0) (fun _ => .G0) b hb (fun zs => ⟨extension zs, extension zs⟩)).1
  change familyEndpointBudget _ _ _ _ _ _ _ ≤ (-1 : ℝ) at impossible
  linarith

def evidence : Registration sourceArena (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.original_fixed_tail_endpoint_budget) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.original_fixed_tail_endpoint_budget, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def original_fixed_tail_endpoint_budget_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.original_fixed_tail_endpoint_budget)
      (type_of% (realize.{0,0,0,0,0} observationSignature
        (fun _ _ b => b) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.ExactOriginal57.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.ExactOriginal57.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena⟩
  objectArena := .source ⟨sourceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{0,0,0,0,0} observationSignature
    (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 23
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms original_fixed_tail_endpoint_budget_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.EndpointNecessity.ExactOriginal57
