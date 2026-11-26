import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators Classical
noncomputable section

private theorem q_three : (2:ℝ)^((3:ℝ)-1)=4 := by
  rw [show (3:ℝ)-1=((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem q_five : (2:ℝ)^((5:ℝ)-1)=16 := by
  rw [show (5:ℝ)-1=((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  norm_num

private theorem observed_three : fullPairObserved 3=1/4 := by
  have h := physical_full_pair_readout 3 (by norm_num) (by rw [q_three]; norm_num)
  change fullPairObserved 3=((2:ℝ)^((3:ℝ)-1))⁻¹ at h
  rw [q_three] at h
  simpa [one_div] using h

private theorem observed_five : fullPairObserved 5=1/16 := by
  have h := physical_full_pair_readout 5 (by norm_num) (by rw [q_five]; norm_num)
  change fullPairObserved 5=((2:ℝ)^((5:ℝ)-1))⁻¹ at h
  rw [q_five] at h
  simpa [one_div] using h

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => fullPairObserved K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℝ, 0<K → (2:ℝ)^(K-1)≠2 →
    let observed := R.readout () () K
    observed = ((2:ℝ)^(K-1))⁻¹

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h 3 (by norm_num) (by rw [q_three]; norm_num)
  change (0:ℝ)=((2:ℝ)^((3:ℝ)-1))⁻¹ at hh
  rw [q_three] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),3,5,?_⟩
  intro h
  change fullPairObserved 3=fullPairObserved 5 at h
  rw [observed_three,observed_five] at h
  norm_num at h

def source_registration : Registration arena (type_of% @physical_full_pair_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_full_pair_readout,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_full_pair_readout) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh.physical_full_pair_readout.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => fullPairObserved K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalRibbonBoundaryWalsh
