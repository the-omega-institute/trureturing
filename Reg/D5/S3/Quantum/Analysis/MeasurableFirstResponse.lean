import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.MeasurableFirstResponse
import Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! Full-telescope audit with the actual vector-response bound as its observation. -/

open scoped Topology
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableFirstResponse
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.MeasurableFirstResponse

abbrev signature := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.signature
abbrev actual := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.actual
abbrev rejected := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.rejected

def arena : Arena where
  signature := signature
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (hH : ∀ x : E, AEStronglyMeasurable (fun s => H s x) (volume.restrict (Set.Icc 0 T)))
    (g h : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (hh : IntegrableOn h (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hhn : ∀ s ∈ Set.Icc 0 T, 0 ≤ h s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (hHh : ∀ s ∈ Set.Icc 0 T, ‖H s‖ ≤ h s),
    (∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T → ∀ x : E,
      IntervalIntegrable
        (fun s => measurableEvolution S B t s (H s (measurableEvolution S B s r x))) volume r t ∧
      R.readout () () ‖response S B H t r x‖
        (Real.exp (∫ s in r..t, g s) * (∫ s in r..t, h s) * ‖x‖) ∧
      ‖measurableEvolution S (B+H) t r x - measurableEvolution S B t r x -
        response S B H t r x‖ ≤ Real.exp (∫ s in r..t, g s) *
        (Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s) * ‖x‖ ∧
      Real.exp (∫ s in r..t, g s) * (Real.exp (∫ s in r..t, h s) - 1 - ∫ s in r..t, h s) * ‖x‖ ≤
        (1 / 2 : ℝ) * Real.exp ((∫ s in r..t, g s) + ∫ s in r..t, h s) *
        (∫ s in r..t, h s)^2 * ‖x‖) ∧
    (∀ (x : E) (η : ℝ), 0 < η → ∃ δ : ℝ, 0 < δ ∧
      ∀ ε : ℝ, 0 < |ε| → |ε| < δ → ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ T →
      ‖ε⁻¹ • (measurableEvolution S (B + ε • H) t r x - measurableEvolution S B t r x) -
        response S B H t r x‖ < η)

private theorem actual_law : arena.{u}.Law actual := @uniform_signed_response.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := h
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (fun _ => 0) (fun _ => 0) (T := 0) le_rfl
    (fun _ => by simp) (fun _ => by simp)
    (fun _ => 0) (fun _ => 0)
    (integrableOn_const measure_Icc_lt_top.ne) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => by simp) (fun _ _ => by simp)
  exact (hp.1 0 0 le_rfl le_rfl le_rfl 0).2.1

def family : Registration arena.{u} (type_of% (@uniform_signed_response.{u})) where
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
    (@uniform_signed_response.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableFirstResponse.uniform_signed_responseUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableFirstResponse.family
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
    owner := `D5.S3.Quantum.Analysis.MeasurableFirstResponse
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.MeasurableFirstResponse
