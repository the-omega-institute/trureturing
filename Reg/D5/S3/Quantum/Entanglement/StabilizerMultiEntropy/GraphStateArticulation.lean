import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix Finset
open scoped BigOperators Classical
noncomputable section

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := MomentTable
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => momentTable K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℝ), 1 < K →
    let observed := R.readout () () K
    ∀ (I J : Type) [Fintype I] [Fintype J]
      (A : Matrix (Unit ⊕ I) (Unit ⊕ I) (ZMod 2)) (B : Matrix (Unit ⊕ J) (Unit ⊕ J) (ZMod 2)),
    (∀ i j, A i j=A j i) → (∀ i j, B i j=B j i) →
    (∀ i, A i i=0) → (∀ i, B i i=0) →
    ∀ (root : Prop) (s : I → Prop) (t : J → Prop),
    let x := (2:ℝ)^(1-K)
    let h := observe observed (A.submatrix Sum.inr Sum.inr) (univ.filter s)
    let j := observe observed (B.submatrix Sum.inr Sum.inr) (univ.filter t)
    let g := observe observed A (selectRoot root s)
    let k := observe observed B (selectRoot root t)
    observe observed (wedge A B) (selectRoot root (Sum.elim s t)) =
      x*h*j + ((g-x*h)*(k-x*j))/(1-x)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have e := h 2 (by norm_num) Empty Empty
    (0 : Matrix (Unit ⊕ Empty) (Unit ⊕ Empty) (ZMod 2))
    (0 : Matrix (Unit ⊕ Empty) (Unit ⊕ Empty) (ZMod 2))
    (by simp) (by simp) (by simp) (by simp) False (fun _ => False) (fun _ => False)
  change (2:ℝ) = (2:ℝ)^(1-(2:ℝ))*2*2 +
    ((2-(2:ℝ)^(1-(2:ℝ))*2)*(2-(2:ℝ)^(1-(2:ℝ))*2))/(1-(2:ℝ)^(1-(2:ℝ))) at e
  norm_num [Real.rpow_neg_one] at e

private def total (g : MomentTable) : ℝ :=
  ∑ U : Finset (Fin 4), (-1:ℝ)^U.card * g 4 (Characteristic.projectiveGraph 1) U

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,3,?_⟩
  intro he
  have e : total (momentTable 2) = total (momentTable 3) := congrArg total he
  have h2 : total (momentTable 2) = 0 := by
    have h := (compact_projective_walsh 2 (by norm_num)).1 1
    change total (momentTable 2) = _ at h
    exact h.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])
  have h3 : total (momentTable 3) = 3/4 := by
    have h := (compact_projective_walsh 3 (by norm_num)).1 1
    change total (momentTable 3) = _ at h
    exact h.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])
  rw [h2,h3] at e
  norm_num at e

def source_registration : Registration arena (type_of% @physical_articulation_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_articulation_readout,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_articulation_readout) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation.physical_articulation_readout.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => momentTable K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
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
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateArticulation
