import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
import Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! Source-bound full-telescope audits for strong L1 evolution stability. -/

open scoped Nat Topology
open MeasureTheory Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
open LeanInformationAudit
noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability

abbrev scalarSignature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization scalarSignature :=
  realize scalarSignature (fun _ _ a b => a < b) (fun e => nomatch e)
def rejected : Realization scalarSignature :=
  realize scalarSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence scalarSignature actual := by
  intro i
  refine ⟨(), (0 : ℝ), (1 : ℝ), ?_⟩
  intro he
  have hb : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) zero_lt_one
  exact (lt_irrefl _ hb)

namespace CompactEvaluation

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ {α : Type v} [MeasurableSpace α]
    {μ : Measure α} (D : ℕ → α → E →L[ℂ] E)
    (hD : ∀ n x, AEStronglyMeasurable (fun s => D n s x) μ)
    {c : α → ℝ} (hc : Integrable c μ) (hcn : 0 ≤ᵐ[μ] c)
    (hDc : ∀ n, ∀ᵐ s ∂μ, ‖D n s‖ ≤ c s)
    (hlim : ∀ x, Tendsto (fun n => ∫ s, ‖D n s x‖ ∂μ) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact K),
    (∀ n (v : α → E), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → Integrable (fun s => D n s (v s)) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      R.readout () () (∫ s, ‖D n s (v s)‖ ∂μ) ε

private theorem actual_law : arena.Law actual := @uniform_integral_evaluation

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1}) (α := PUnit.{v+1}) (μ := 0)
    (fun _ _ => 0) (fun _ _ => aestronglyMeasurable_const)
    (c := fun _ => 0) (by simp) (Eventually.of_forall fun _ => le_rfl)
    (fun _ => Eventually.of_forall fun _ => by simp)
    (fun _ => by simpa using (tendsto_const_nhds (x := (0 : ℝ))))
    (K := Set.univ) isCompact_univ
  obtain ⟨n, hn⟩ := (hz.2 1 zero_lt_one).exists
  exact hn (fun _ => 0) aestronglyMeasurable_const (by simp)

def family : Registration arena (type_of% (@uniform_integral_evaluation)) where
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
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_integral_evaluation) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.uniform_integral_evaluationUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.CompactEvaluation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end CompactEvaluation

namespace Terms

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)) (m : ℕ) (x : E),
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      R.readout () () ‖term S (Bseq n) m t r x - term S B m t r x‖ ε

private theorem actual_law : arena.Law actual := @uniform_term_convergence

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1})
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (T := 0) le_rfl (fun _ _ => 0) (fun _ => 0)
    (fun _ _ => aestronglyMeasurable_const) (fun _ => aestronglyMeasurable_const)
    (fun _ => 0) (by simp) (fun _ _ => le_rfl)
    (fun _ _ _ => by simp) (fun _ _ => by simp)
    (fun _ => by simpa using (tendsto_const_nhds (x := (0 : ℝ)))) 0 0 1 zero_lt_one
  obtain ⟨n, hn⟩ := hz.exists
  exact hn 0 0 le_rfl le_rfl le_rfl

def family : Registration arena (type_of% (@uniform_term_convergence)) where
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
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_term_convergence) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.uniform_term_convergenceUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.Terms.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Terms

namespace Evolution

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (g : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ g s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)),
    ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      R.readout () () ‖measurableEvolution S (Bseq n) t r x - measurableEvolution S B t r x‖ ε

private theorem actual_law : arena.Law actual := @measurable_evolution_stability

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1})
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (T := 0) le_rfl (fun _ _ => 0) (fun _ => 0)
    (fun _ _ => aestronglyMeasurable_const) (fun _ => aestronglyMeasurable_const)
    (fun _ => 0) (by simp) (fun _ _ => le_rfl)
    (fun _ _ _ => by simp) (fun _ _ => by simp)
    (fun _ => by simpa using (tendsto_const_nhds (x := (0 : ℝ)))) 0 1 zero_lt_one
  obtain ⟨N, hN⟩ := hz
  exact hN N le_rfl 0 0 le_rfl le_rfl le_rfl

def family : Registration arena (type_of% (@measurable_evolution_stability)) where
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
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@measurable_evolution_stability) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.measurable_evolution_stabilityUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability.Evolution.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize scalarSignature (fun _ _ a b => a < b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℝ
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
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

end Reg.D5.S3.Quantum.Analysis.NonautonomousEvolutionStability
