import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators Classical
noncomputable section

private def factor (K : ℝ) : ℝ :=
  let x := (2:ℝ)^(1-K)
  ((1-x)^3*(1+3*x)-3*x^3*(1-x))/256

private theorem factor_two : factor 2=1/2048 := by
  unfold factor
  dsimp only
  rw [show (1:ℝ)-2 = -1 by norm_num, Real.rpow_neg_one]
  norm_num

private theorem factor_three : factor 3=45/16384 := by
  unfold factor
  dsimp only
  rw [show (1:ℝ)-3 = -(2:ℝ) by norm_num, Real.rpow_neg (by norm_num)]
  norm_num [←Nat.cast_ofNat (R:=ℝ), Real.rpow_natCast]

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
  realize signature (fun _ _ K => fourObserved K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℝ, 0<K →
    let observed := R.readout () () K
    let x := (2:ℝ)^(1-K)
    observed = ((1-x)^3*(1+3*x)-3*x^3*(1-x))/256

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 3 (by norm_num)
  change (0:ℝ)=factor 3 at he
  rw [factor_three] at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,3,?_⟩
  intro he
  change fourObserved 2=fourObserved 3 at he
  have h2 : fourObserved 2=factor 2 := physical_four_readout 2 (by norm_num)
  have h3 : fourObserved 3=factor 3 := physical_four_readout 3 (by norm_num)
  rw [h2,h3,factor_two,factor_three] at he
  norm_num at he

def source_registration : Registration arena (type_of% @physical_four_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_four_readout,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_four_readout) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication.physical_four_readout.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => fourObserved K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalCodeCircuitReplication
