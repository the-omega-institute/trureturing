import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact
import Reg.Support.DependentFamily

open _root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact
open _root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryEffectOptimum
open _root_.D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open _root_.D5.S3.Quantum.Foundation.FiniteStateChannel
open _root_.D5.S3.Quantum.Foundation.FiniteDiamondDistance
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder

noncomputable section
namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact

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
  Law obs := ∀ {A : Type} [Fintype A] [DecidableEq A] (t : A) (β : Benchmark),
    ∃ (ρ : DensityState (Bit × Bit)) (L R : QuantumChannel Bit Bit) (Q T : QuantumChannel A (Bit × Bit)),
      CStarMatrix.ofMatrix.symm ρ.val = wresource β.a β.b ∧
      (∀ X, rawEntry Q X = X.trace • tensorRawAction L R (CStarMatrix.ofMatrix.symm ρ.val)) ∧
      (∀ X, rawEntry T X = X.trace • Matrix.diagonal (fun p => (binaryTarget β.w p : ℂ))) ∧
      diamondDistance Q T = obs.readout () () β ∧
      ∀ (E : QuantumChannel A (Bit × Bit)) (U V : QuantumChannel Bit Bit),
        rawEntry E (Matrix.single t t 1) = tensorRawAction U V (CStarMatrix.ofMatrix.symm ρ.val) →
        exactError β ≤ diamondDistance E T

theorem actual_law : arena.Law actual := by
  intro A _ _ t β
  exact _root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact.result t β

def matchingBench : Benchmark := ⟨4/5,3/5,9/25,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩
def mismatchBench : Benchmark := ⟨4/5,3/5,144/625,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ρ,L,R,Q,T,hρ,hQ,hT,hError,_⟩ := h () matchingBench
  change diamondDistance Q T = -1 at hError
  have h0 : 0 ≤ diamondDistance Q T := by
    unfold diamondDistance
    apply le_csSup
    · refine ⟨2, ?_⟩
      rintro x (hx | hx)
      · simp [Set.mem_singleton_iff.mp hx]
      · obtain ⟨m, tau, rfl⟩ := hx
        have he := D5.S3.Quantum.Foundation.FiniteTraceDistance.traceDistance_le_one
          (referenceState Q tau) (referenceState T tau)
        change referenceError Q T tau / 2 ≤ 1 at he
        linarith
    · exact Or.inl (Set.mem_singleton 0)
  linarith

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

def family : Registration arena (type_of% (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact.result)) where
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
    (@_root_.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact.result) (Realization signature) Benchmark Unit where
  unitName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact.optimalErrorUnit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact.family
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
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","arg","body","arg","body","arg","body","arg","body","arg","body","arg","arg","arg","fn","arg","arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.WeightedBinaryReplacementExact
