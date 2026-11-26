import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators ComplexOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum

abbrev signature : Signature where
  Params := Unit
  State _ := Benchmark
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ β => exactError β) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law obs := ∀ β : Benchmark,
    ∃ H : M₂, H.PosSemidef ∧ (DD β.a β.b-H).PosSemidef ∧
      2*(1-capped β.w (quad H) (quad (DD β.a β.b-H))) = obs.readout () () β ∧
      ∀ X : M₂, X.PosSemidef → (DD β.a β.b-X).PosSemidef →
        exactError β ≤ 2*(1-capped β.w (quad X) (quad (DD β.a β.b-X)))

theorem actual_law : arena.Law actual := by
  intro β
  exact result β

def matchingBench : Benchmark := ⟨4/5,3/5,9/25,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩
def mismatchBench : Benchmark := ⟨4/5,3/5,144/625,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨H,hH,hC,hError,_⟩ := h matchingBench
  change 2*(1-capped matchingBench.w (quad H) (quad (DD matchingBench.a matchingBench.b-H))) = -1 at hError
  unfold capped at hError
  linarith [
    min_le_left matchingBench.w (quad H),
    min_le_left (1-matchingBench.w) (quad (DD matchingBench.a matchingBench.b-H))]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), matchingBench, mismatchBench, ?_⟩
  change exactError matchingBench ≠ exactError mismatchBench
  have h₀ : exactError matchingBench = 0 := by
    norm_num [exactError,errorFormula,matchingBench]
  have h₁ : 0 < exactError mismatchBench := by
    norm_num [exactError,errorFormula,mismatchBench,max_def]
  rw [h₀]
  exact h₁.ne

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum.result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      cases role; cases other; exact (hne rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum.result) (Realization signature) Benchmark Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum.optimalErrorUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ β => exactError β) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","arg","body","arg","arg","fn","arg","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
