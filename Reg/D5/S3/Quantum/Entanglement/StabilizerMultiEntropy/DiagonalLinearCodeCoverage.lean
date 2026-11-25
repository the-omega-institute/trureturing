import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators Classical
noncomputable section

private def factor (K : ℝ) : ℝ :=
  (∏ j : Fin 3, (1-(2:ℝ)^j.val/(2:ℝ)^(K-1))) / walshNorm (Site 3)

private theorem cardinal_sites : Fintype.card (Site 3)=7 := by decide

private theorem factor_two : factor 2=0 := by
  unfold factor
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (1:ℝ)-(2:ℝ)^j/(2:ℝ)^((2:ℝ)-1))]
  norm_num [Real.rpow_one,Finset.prod_range_succ,walshNorm,cardinal_sites]

private theorem factor_four : factor 4=21/8192 := by
  unfold factor
  rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => (1:ℝ)-(2:ℝ)^j/(2:ℝ)^((4:ℝ)-1))]
  norm_num [←Nat.cast_ofNat (R:=ℝ),Real.rpow_natCast,Finset.prod_range_succ,walshNorm,cardinal_sites]

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
  realize signature (fun _ _ K => fanoObserved K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ K : ℝ, 0<K →
    let observed := R.readout () () K
    observed = (∏ j : Fin 3, (1-(2:ℝ)^j.val/(2:ℝ)^(K-1))) / walshNorm (Site 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 4 (by norm_num)
  change (0:ℝ)=factor 4 at he
  rw [factor_four] at he
  norm_num at he

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,4,?_⟩
  intro he
  change fanoObserved 2=fanoObserved 4 at he
  have h2 : fanoObserved 2=factor 2 := physical_fano_readout 2 (by norm_num)
  have h4 : fanoObserved 4=factor 4 := physical_fano_readout 4 (by norm_num)
  rw [h2,h4,factor_two,factor_four] at he
  norm_num at he

def source_registration : Registration arena (type_of% @physical_fano_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_fano_readout,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_fano_readout) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage.physical_fano_readout.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => fanoObserved K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
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
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.DiagonalLinearCodeCoverage
