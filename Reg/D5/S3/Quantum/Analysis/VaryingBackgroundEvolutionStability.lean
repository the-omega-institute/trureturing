import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
import Reg.D5.S3.Quantum.Analysis.SeparateMassEvolutionStability
import Reg.Support.DependentFamily

/-! Full original telescopes for the varying-background integral, term and evolution assertions. -/

open scoped Nat Topology
open MeasureTheory Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
open _root_.Reg.D5.S3.Quantum.Analysis.SeparateMassEvolutionStability
open LeanInformationAudit
noncomputable section
universe u v
namespace Reg.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability

namespace Background

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E],
    ∀ {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (Sseq : ℕ → Contraction E) (S : Contraction E) (T : ℝ)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (B : α → E →L[ℂ] E)
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x) μ)
    (g : α → ℝ) (hg : Integrable g μ) (hgn : 0 ≤ᵐ[μ] g)
    (hBg : ∀ᵐ s ∂μ, ‖B s‖ ≤ g s) {K : Set E} (hK : IsCompact K),
    (∀ n (v : α → E) (h : α → ℝ), AEStronglyMeasurable v μ →
      (∀ᵐ s ∂μ, v s ∈ K) → AEStronglyMeasurable h μ →
      Integrable (fun s => (Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))) μ) ∧
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (v : α → E) (h : α → ℝ),
      AEStronglyMeasurable v μ → (∀ᵐ s ∂μ, v s ∈ K) →
      AEStronglyMeasurable h μ → (∀ᵐ s ∂μ, h s ∈ Set.Icc 0 T) →
      R.readout () () (∫ s, ‖(Sseq n).action (h s) (B s (v s)) -
        S.action (h s) (B s (v s))‖ ∂μ) ε

private theorem actual_law : arena.Law actual := @uniform_integral_background_action

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1}) (α := PUnit.{v+1}) (μ := 0)
    (fun _ => _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup)
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup 0
    (by
      intro x ε hε
      refine ⟨0, ?_⟩
      intro n hn t ht htT
      simpa using hε)
    (fun _ => 0) (fun _ => aestronglyMeasurable_const)
    (fun _ => 0) (by simp) (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => by simp) (K := Set.univ) isCompact_univ
  obtain ⟨n, hn⟩ := (hz.2 1 zero_lt_one).exists
  exact hn (fun _ => 0) (fun _ => 0) aestronglyMeasurable_const (by simp)
    aestronglyMeasurable_const (Eventually.of_forall fun _ => ⟨le_rfl,le_rfl⟩)

def family : Registration arena (type_of% (@uniform_integral_background_action)) where
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
    have hb : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) zero_lt_one
    exact lt_irrefl _ hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_integral_background_action) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.uniform_integral_background_actionUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.Background.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Background

namespace Terms

def arena : Arena where
  signature := scalarSignature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (Sseq : ℕ → Contraction E) (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (gn : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hgn : ∀ n, IntegrableOn (gn n) (Set.Icc 0 T))
    (hg : IntegrableOn g (Set.Icc 0 T))
    (hgnn : ∀ n, ∀ s ∈ Set.Icc 0 T, 0 ≤ gn n s)
    (hgpos : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ gn n s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (C : ℝ) (hC : 0 ≤ C)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)),
    ∀ (m : ℕ) (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      R.readout () () ‖term (Sseq n) (Bseq n) m t r x - term S B m t r x‖ ε

private theorem actual_law : arena.Law actual := @uniform_term_convergence_of_mass

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1})
    (fun _ => _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup)
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (T := 0) le_rfl
    (by
      intro x ε hε
      refine ⟨0, ?_⟩
      intro n hn t ht htT
      simpa using hε)
    (fun _ _ => 0) (fun _ => 0)
    (fun _ _ => aestronglyMeasurable_const) (fun _ => aestronglyMeasurable_const)
    (fun _ _ => 0) (fun _ => 0) (fun _ => by simp) (by simp)
    (fun _ _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ _ => by simp) (fun _ _ => by simp) 0 le_rfl
    (fun _ => by simp) (by simp)
    (fun _ => by simpa using (tendsto_const_nhds (x := (0 : ℝ)))) 0 0 1 zero_lt_one
  obtain ⟨N,hN⟩ := hz
  exact hN N le_rfl 0 0 le_rfl le_rfl le_rfl

def family : Registration arena (type_of% (@uniform_term_convergence_of_mass)) where
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
    have hb : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) zero_lt_one
    exact lt_irrefl _ hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@uniform_term_convergence_of_mass) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.uniform_term_convergence_of_massUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.Terms.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
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
    ∀ (Sseq : ℕ → Contraction E) (S : Contraction E) {T : ℝ} (hT : 0 ≤ T)
    (hSlim : ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
      ∀ h : ℝ, 0 ≤ h → h ≤ T → ‖(Sseq n).action h x - S.action h x‖ < ε)
    (Bseq : ℕ → ℝ → E →L[ℂ] E) (B : ℝ → E →L[ℂ] E)
    (hseq : ∀ n x, AEStronglyMeasurable (fun s => Bseq n s x)
      (volume.restrict (Set.Icc 0 T)))
    (hB : ∀ x, AEStronglyMeasurable (fun s => B s x)
      (volume.restrict (Set.Icc 0 T)))
    (gn : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hgn : ∀ n, IntegrableOn (gn n) (Set.Icc 0 T))
    (hg : IntegrableOn g (Set.Icc 0 T))
    (hgnn : ∀ n, ∀ s ∈ Set.Icc 0 T, 0 ≤ gn n s)
    (hgpos : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s)
    (hseqg : ∀ n, ∀ s ∈ Set.Icc 0 T, ‖Bseq n s‖ ≤ gn n s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s)
    (C : ℝ) (hC : 0 ≤ C)
    (hseqmass : ∀ n, (∫ s in (0 : ℝ)..T, gn n s) ≤ C)
    (hBmass : (∫ s in (0 : ℝ)..T, g s) ≤ C)
    (hlim : ∀ x, Tendsto (fun n => ∫ s in (0 : ℝ)..T, ‖(Bseq n s - B s) x‖)
      atTop (𝓝 0)),
    ∀ (x : E) (ε : ℝ), 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ r t : ℝ,
      0 ≤ r → r ≤ t → t ≤ T →
      R.readout () () ‖measurableEvolution (Sseq n) (Bseq n) t r x - measurableEvolution S B t r x‖ ε

private theorem actual_law : arena.Law actual := @measurable_evolution_stability_of_mass

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h (E := PUnit.{u+1})
    (fun _ => _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup)
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (T := 0) le_rfl
    (by
      intro x ε hε
      refine ⟨0, ?_⟩
      intro n hn t ht htT
      simpa using hε)
    (fun _ _ => 0) (fun _ => 0)
    (fun _ _ => aestronglyMeasurable_const) (fun _ => aestronglyMeasurable_const)
    (fun _ _ => 0) (fun _ => 0) (fun _ => by simp) (by simp)
    (fun _ _ _ => le_rfl) (fun _ _ => le_rfl)
    (fun _ _ _ => by simp) (fun _ _ => by simp) 0 le_rfl
    (fun _ => by simp) (by simp)
    (fun _ => by simpa using (tendsto_const_nhds (x := (0 : ℝ)))) 0 1 zero_lt_one
  obtain ⟨N,hN⟩ := hz
  exact hN N le_rfl 0 0 le_rfl le_rfl le_rfl

def family : Registration arena (type_of% (@measurable_evolution_stability_of_mass)) where
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
    have hb : (1 : ℝ) < 1 := Eq.mp (congrFun he 1) zero_lt_one
    exact lt_irrefl _ hb

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@measurable_evolution_stability_of_mass) (Realization scalarSignature) Type Unit where
  unitName := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.measurable_evolution_stability_of_massUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability.Evolution.family
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
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
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

#print axioms uniform_integral_background_action
#print axioms uniform_term_convergence_of_mass
#print axioms measurable_evolution_stability_of_mass

end Reg.D5.S3.Quantum.Analysis.VaryingBackgroundEvolutionStability
