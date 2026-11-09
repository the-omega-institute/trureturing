import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
import Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
import Reg.Support.DependentFamily

/-! The original telescope with a dependent vector-equality observation. -/

open scoped Topology
open MeasureTheory
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableNonautonomousDysonPhillips
open _root_.D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
open LeanInformationAudit

noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel

abbrev signature := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.equalitySignature.{u}
abbrev actual := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.equalityActual.{u}
abbrev rejected := _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.equalityRejected.{u}

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E],
    ∀ (S : Contraction E) (B H : ℝ → E →L[ℂ] E)
    {T : ℝ} (hT : 0 ≤ T)
    (hB : ∀ x : E, AEStronglyMeasurable (fun s => B s x) (volume.restrict (Set.Icc 0 T)))
    (hH : ∀ x : E, AEStronglyMeasurable (fun s => H s x) (volume.restrict (Set.Icc 0 T)))
    (g h : ℝ → ℝ) (hg : IntegrableOn g (Set.Icc 0 T)) (hh : IntegrableOn h (Set.Icc 0 T))
    (hgn : ∀ s ∈ Set.Icc 0 T, 0 ≤ g s) (hhn : ∀ s ∈ Set.Icc 0 T, 0 ≤ h s)
    (hBg : ∀ s ∈ Set.Icc 0 T, ‖B s‖ ≤ g s) (hHh : ∀ s ∈ Set.Icc 0 T, ‖H s‖ ≤ h s)
    {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T) (x : E),
    IntervalIntegrable
      (fun s => measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x))) volume r t ∧
    IntervalIntegrable
      (fun s => measurableEvolution S (B+H) t s (H s (measurableEvolution S B s r x))) volume r t ∧
    R.readout () E (measurableEvolution S (B+H) t r x - measurableEvolution S B t r x)
      (∫ s in r..t, measurableEvolution S B t s (H s (measurableEvolution S (B+H) s r x))) ∧
    (measurableEvolution S (B+H) t r x - measurableEvolution S B t r x =
      ∫ s in r..t, measurableEvolution S (B+H) t s (H s (measurableEvolution S B s r x)))

private theorem actual_law : arena.{u}.Law actual := @relative_duhamel.{u}

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hp := h
    _root_.Reg.D5.S3.Quantum.Analysis.NonautonomousDysonPhillips.zeroSemigroup
    (fun _ => 0) (fun _ => 0) (T := 0) le_rfl
    (fun _ => by simp) (fun _ => by simp)
    (fun _ => 0) (fun _ => 0)
    (integrableOn_const measure_Icc_lt_top.ne) (integrableOn_const measure_Icc_lt_top.ne)
    (fun _ _ => le_rfl) (fun _ _ => le_rfl) (fun _ _ => by simp) (fun _ _ => by simp)
    (r := 0) (t := 0) le_rfl le_rfl le_rfl 0
  exact hp.2.2.1

def family : Registration arena.{u} (type_of% (@relative_duhamel.{u})) where
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
    refine ⟨ULift.{u} ℂ, (0 : ULift.{u} ℂ), (1 : ULift.{u} ℂ), ?_⟩
    intro he
    have hb : (1 : ULift.{u} ℂ) = 0 := Eq.mp (congrFun he 0) rfl
    exact one_ne_zero (congrArg ULift.down hb)

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@relative_duhamel.{u}) (Realization signature.{u}) (Type (u+1)) Unit where
  unitName := `D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel.relative_duhamelUnit
  realizationName := `Reg.D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ F x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Type u)
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "arg", "arg", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Analysis.MeasurableRelativeDuhamel
