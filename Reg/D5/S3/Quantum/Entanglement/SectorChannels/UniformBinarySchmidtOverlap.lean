import D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

set_option autoImplicit false

open D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap
open D5.S3.Quantum.Entanglement.SectorChannels.UniformSchmidtOverlap.RTOverlap
open D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap

namespace Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section

private def deterministic (i : Fin 2) : LocalColumns (Fin 1) (Fin 2) (Fin 1) where
  entry := fun _ j _ => if j = i then 1 else 0
  gram := by
    intro a b
    have h : a = b := Subsingleton.elim a b
    fin_cases i <;> simp [h]

private def experiment (i j : Fin 2) : CapExperiment :=
  ⟨1, 2, 1, 1, fun _ => 1, deterministic i, deterministic j⟩

private theorem matching_readout : measuredCap 1 (experiment 0 0) = 1/2 := by
  unfold measuredCap
  simp only [Nat.cast_one]
  change (∑ i : Fin 2, min (1/((1:ℝ)+1))
    ((lnorm (bornVector (deterministic 0) (deterministic 0)
      (fun _ => (Real.sqrt 1 : ℂ)) i i)) ^ 2)) = 1/2
  norm_num [deterministic, lnorm, lsquare, bornVector, Fin.sum_univ_two, norm_one]
  all_goals norm_num [Complex.sq_norm, Complex.normSq_apply]

private theorem differing_readout : measuredCap 1 (experiment 0 1) = 0 := by
  unfold measuredCap
  simp only [Nat.cast_one]
  change (∑ i : Fin 2, min (1/((1:ℝ)+1))
    ((lnorm (bornVector (deterministic 0) (deterministic 1)
      (fun _ => (Real.sqrt 1 : ℂ)) i i)) ^ 2)) = 0
  norm_num [deterministic, lnorm, lsquare, bornVector, Fin.sum_univ_two, norm_one]

private theorem constant_zero_invalid : ¬ BinaryCapLaw (fun _ => 0) := by
  intro h
  obtain ⟨u, _, _, hR, _, _, X, _, hX, hpos, _, he⟩ := h
  have hS : 0 < RTCriticalOverlap.spectralScore 2 X.spectrum := by
    have : Nonempty (Fin X.rank) := ⟨⟨0, by omega⟩⟩
    exact Finset.sum_pos
      (fun i _ => lt_min (hpos i) (Real.sqrt_pos_of_pos (div_pos (hpos i) (by norm_num))))
      Finset.univ_nonempty
  have hp := mul_pos (lt_trans (show (0:ℝ)<1084871396888/1000000000000 by norm_num) hR) hS
  exact (ne_of_gt hp) he.symm


abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => CapExperiment)
    (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ => measuredCap 1) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    let observed := R.readout () ()
    BinaryCapLaw observed

private theorem rejected_law : ¬ arena.Law rejected := constant_zero_invalid

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  have h : i = () := Subsingleton.elim _ _
  subst i
  refine ⟨(), experiment 0 0, experiment 0 1, ?_⟩
  change measuredCap 1 (experiment 0 0) ≠ measuredCap 1 (experiment 0 1)
  rw [matching_readout, differing_readout]
  norm_num

def family : Registration arena (type_of% @actual_binary_maximum) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_binary_maximum, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@actual_binary_maximum) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap.actual_binary_maximum.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => measuredCap 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.SectorChannels.UniformBinarySchmidtOverlap
