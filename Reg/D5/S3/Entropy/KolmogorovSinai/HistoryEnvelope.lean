import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Entropy.KolmogorovSinai.HistoryEnvelope
import Reg.Support.DependentFamily

open MeasureTheory Function Filter Topology
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Entropy.KolmogorovSinai
open D5.S3.Entropy.ConditionalEntropy D5.S3.Entropy.MaxEntropy
open D5.S3.Divergence.ChainRule LeanInformationAudit

noncomputable section
universe u v
namespace Reg.D5.S3.Entropy.KolmogorovSinai.HistoryEnvelope

abbrev signature : Signature where
  Params := Σ I : Type u, Fintype I × ℕ
  State p := ((Fin p.2.2 → p.1) × p.1) → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p w => @conditionalEntropy (Fin p.2.2 → p.1) p.1
    (by letI := p.2.1; exact inferInstance) p.2.1 w) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {X : Type v} {I : Type u} [MeasurableSpace X] [StandardBorelSpace X]
    [fi : Fintype I] {mu : Measure X} [IsProbabilityMeasure mu]
    {T : X → X} (hT : MeasurePreserving T mu mu) (P : MeasurePartition mu I) (n : ℕ),
    ksEntropyPartition hT P ≤ R.readout () ⟨I, fi, n⟩
      (fun x => mu.real ((ksJoin hT P n).cells x.1 ∩ (T^[n]) ⁻¹' P.cells x.2))

theorem actual_law : arena.{u,v}.Law actual := by
  intro X I _ _ _ mu _ T hT P n
  exact ksEntropyPartition_le_history_conditionalEntropy hT P n

theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let X := ULift.{v} Unit
  let I := ULift.{u} Unit
  let mu : Measure X := Measure.dirac ⟨()⟩
  let hT : MeasurePreserving (id : X → X) mu mu := MeasurePreserving.id mu
  let P : MeasurePartition mu I := {
    cells := fun _ => Set.univ
    measurable := fun _ => MeasurableSet.univ
    aedisjoint := by intro i j hij; exact (hij (Subsingleton.elim _ _)).elim
    cover := Set.eq_univ_iff_forall.mpr (fun x =>
      Set.mem_iUnion.mpr ⟨⟨()⟩, Set.mem_univ x⟩) }
  have hn : 0 ≤ ksEntropyPartition hT P := by
    refine ge_of_tendsto (tendsto_ksEntropySeq hT P) ?_
    exact Eventually.of_forall fun n =>
      div_nonneg (ksEntropySeq_nonneg hT P n) (Nat.cast_nonneg n)
  have hb := h hT P 0
  change ksEntropyPartition hT P ≤ -1 at hb
  linarith

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let I := ULift.{u} (Fin 2)
  let p : signature.Params := ⟨I, inferInstance, 0⟩
  refine ⟨p, (fun _ => 0), (fun _ => 1 / 2), ?_⟩
  change conditionalEntropy (fun _ : (Fin 0 → I) × I => (0 : ℝ)) ≠
    conditionalEntropy (fun _ : (Fin 0 → I) × I => (1 / 2 : ℝ))
  have hh : conditionalEntropy (fun _ : (Fin 0 → I) × I => (1 / 2 : ℝ)) = Real.log 2 := by
    norm_num [conditionalEntropy, marginal, conditional, shannonEntropy,
      Fintype.sum_prod_type, I, Fin.sum_univ_two,
      Real.negMulLog, Real.log_div]
    <;> ring
  rw [hh]
  simp only [conditionalEntropy, marginal, Finset.sum_const_zero, conditional,
    zero_div, shannonEntropy, Real.negMulLog_zero, zero_mul]
  exact ne_of_lt (Real.log_pos (by norm_num))

def family : Registration arena.{u,v} (arena.Law actual) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      cases i; cases j
      exact (hji rfl).elim
    · intro e; exact nomatch e
  dependence := dependence

#print axioms family
#print axioms _root_.D5.S3.Entropy.KolmogorovSinai.ksEntropyPartition_le_history_conditionalEntropy

end Reg.D5.S3.Entropy.KolmogorovSinai.HistoryEnvelope
