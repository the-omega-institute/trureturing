import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema
import Reg.Support.DependentFamily

namespace Reg.D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema

open _root_.D5.S1.Words.AdmissibleWords.AdmissibleCount
open _root_.D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit MeasureTheory Set
open scoped ENNReal

set_option autoImplicit false
noncomputable section

private abbrev signature : Signature where
  Params := Σ n : ℕ, Fin n × Fin n
  State q := Fin q.1 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

private def actual : Realization signature :=
  realize signature (fun _ q p => ENNReal.ofReal
    (if q.2.1.val % 2 = q.2.2.val % 2 then min (p q.2.1) (p q.2.2)
      else max 0 (p q.2.1 + p q.2.2 - 1))) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} {p : Fin n → ℝ},
    (∀ i, 0 ≤ p i ∧ p i ≤ 1) →
    (∀ i j, i.val + 1 = j.val → p i + p j ≤ 1) →
    ∃ w : ℝ → Fin n → Bool, (∀ u, Adm n (w u)) ∧
      (∀ u ∉ Ioo (0 : ℝ) 1, ∀ i, w u i = false) ∧
      (∀ i, MeasurableSet {u | w u i = true} ∧
        volume {u | w u i = true} = ENNReal.ofReal (p i)) ∧
      ∀ i j, volume {u | w u i = true ∧ w u j = true} =
        R.readout () ⟨n, i, j⟩ p

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, _, _, marginal, pair⟩ := h (n := 1) (p := fun _ => 0) (by simp) (by simp)
  have hzero := (marginal 0).2
  have hone := pair 0 0
  simp only [and_self] at hone
  change volume {u | w u 0 = true} = 1 at hone
  rw [hone, ENNReal.ofReal_zero] at hzero
  exact one_ne_zero hzero

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨⟨1, 0, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change ENNReal.ofReal (min 0 0) ≠ ENNReal.ofReal (min 1 1)
  norm_num

def proofRecord : Registration arena (type_of% @threshold_pair_extrema) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@threshold_pair_extrema, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@threshold_pair_extrema) (Realization signature) Unit Unit where
  unitName :=
    `D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema.threshold_pair_extrema.audit
  realizationName :=
    `Reg.D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema.proofRecord
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨proofRecord⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema
    definition := none
    coordinates := #[0, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "arg", "arg", "body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S1.Words.AdmissibleWords.FIBThresholdPairExtrema
