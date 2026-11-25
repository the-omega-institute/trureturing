import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.CompactProjectiveGraphWalsh
import D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification

namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification.Witness
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Matrix Finset
open scoped BigOperators Classical Matrix
open D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateConcentratableEntanglement
noncomputable section

def path4 : Matrix (Fin 4) (Fin 4) F :=
  fun i j => if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0

theorem path_symm (i j : Fin 4) : path4 i j=path4 j i := by simp [path4,or_comm]
theorem path_diag (i : Fin 4) : path4 i i=0 := by simp [path4]

private theorem step_edge {i j : Fin 4} (h : i.val+1=j.val) : adj path4 i j := by
  simp [adj,path4,h]

theorem path_connected : cutConnected path4 := by
  intro U hU hD
  by_contra! no
  have same {i j : Fin 4} (h : i.val+1=j.val) : i∈U ↔ j∈U := by
    constructor
    · intro hi
      by_contra! hj
      have hj' : j∈complement U := by simp [complement,hj]
      have he := step_edge h
      exact no i hi j hj' (by unfold adj at *; rw [path_symm]; exact he)
    · intro hj
      by_contra! hi
      have hi' : i∈complement U := by simp [complement,hi]
      exact no j hj i hi' (step_edge h)
  have b01 := same (i:=0) (j:=1) (by decide)
  have b12 := same (i:=1) (j:=2) (by decide)
  have b23 := same (i:=2) (j:=3) (by decide)
  have eq0 (i : Fin 4) : i∈U ↔ (0:Fin 4)∈U := by
    fin_cases i
    · rfl
    · exact b01.symm
    · exact (b01.trans b12).symm
    · exact ((b01.trans b12).trans b23).symm
  obtain ⟨i,hi⟩ := hU
  obtain ⟨j,hj⟩ := hD
  exact (by simpa [complement] using hj : j∉U) ((eq0 j).2 ((eq0 i).1 hi))

theorem path_neighbors (i : Fin 4) : ∃ j, adj path4 i j := by
  fin_cases i
  · exact ⟨1,step_edge (by decide)⟩
  · exact ⟨2,step_edge (by decide)⟩
  · exact ⟨3,step_edge (by decide)⟩
  · refine ⟨2,?_⟩
    unfold adj
    rw [path_symm]
    exact step_edge (by decide)

theorem path_not_flat : ¬Star (adj path4) ∧ ¬Clique (adj path4) := by
  have nonleaf1 (c : Fin 4) : ¬ Leaf (adj path4) 1 c := by
    intro h
    have h0 : adj path4 1 0 := by unfold adj; rw [path_symm]; exact step_edge (by decide)
    have h2 : adj path4 1 2 := step_edge (by decide)
    exact (by decide : (0:Fin 4)≠2) ((h.2 0 h0).trans (h.2 2 h2).symm)
  have nonleaf2 (c : Fin 4) : ¬ Leaf (adj path4) 2 c := by
    intro h
    have h1 : adj path4 2 1 := by unfold adj; rw [path_symm]; exact step_edge (by decide)
    have h3 : adj path4 2 3 := step_edge (by decide)
    exact (by decide : (1:Fin 4)≠3) ((h.2 1 h1).trans (h.2 3 h3).symm)
  constructor
  · rintro ⟨c,hc⟩
    by_cases h : (1:Fin 4)=c
    · subst c
      exact nonleaf2 1 (hc 2 (by decide))
    · exact nonleaf1 c (hc 1 h)
  · intro h
    have he := h 0 2 (by decide)
    exact he (by decide)

theorem path_cannot_approach :
    ¬ (∀ ε : ℝ, 0<ε → ∃ K : ℝ, 1<K ∧ K<1+ε ∧ hitLaw (graphTraceMoment path4 K)) := by
  intro h
  have he := (near_actual_orders_iff path4 path_symm path_diag path_neighbors path_connected).1 h
  exact he.elim path_not_flat.1 path_not_flat.2

theorem order_for_three_quarters :
    ∃ K : ℝ, 1<K ∧ (2:ℝ)^(1-K)=3/4 := by
  let l := Real.log (3/4:ℝ) / Real.log 2
  have h2 : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h : l<0 := div_neg_of_neg_of_pos (Real.log_neg (by norm_num) (by norm_num)) h2
  refine ⟨1-l,by linarith,?_⟩
  rw [show 1-(1-l)=l by ring,Real.rpow_def_of_pos (by norm_num)]
  unfold l
  rw [mul_comm,div_mul_cancel₀ _ h2.ne',Real.exp_log (by norm_num)]

theorem four_gap (C : Finset (Fin 4)) :
    (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(3/4:ℝ))<2 := by
  have hs : C.card + Cᶜ.card = 4 := by simp
  have hr : (C.card : ℝ)+(Cᶜ.card : ℝ)=4 := by exact_mod_cast hs
  have hp : ((C.card : ℝ)+(Cᶜ.card : ℝ))^2=16 := by rw [hr]; norm_num
  nlinarith [sq_nonneg ((C.card : ℝ)-(Cᶜ.card : ℝ))]

end
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification.Witness

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
open _root_.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderWalsh
open Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification.Witness
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
  Output _ _ := SmallMomentTable
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ K => smallMomentTable K) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (K : ℝ), 1 < K →
    let observed := R.readout () () K
    ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
      (∀ i j, A i j=A j i) → (∀ i, A i i=0) → (∀ i, ∃ j, adj A i j) →
      cutConnected A → (¬Star (adj A) ∧ ¬Clique (adj A)) →
      ∃ C : Finset (Fin n),
        (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(2:ℝ)^(1-K))<2 →
        ∃ T, Even T.card ∧ (T∩C).Nonempty ∧ (T∩Cᶜ).Nonempty ∧
          inverse (observed n A) T<0

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨K,hK,hThree⟩ := order_for_three_quarters
  obtain ⟨C,hC⟩ := h K hK 4 path4 path_symm path_diag path_neighbors path_connected path_not_flat
  have hg : (C.card : ℝ)*(Cᶜ.card : ℝ)*(1-(2:ℝ)^(1-K))<2 := by rw [hThree]; exact four_gap C
  obtain ⟨T,_,_,_,ht⟩ := hC hg
  change inverse (fun _ : Finset (Fin 4) => 0) T<0 at ht
  simp [inverse] at ht

private def total (g : SmallMomentTable) : ℝ :=
  ∑ U : Finset (Fin 4), (-1:ℝ)^U.card * g 4 (Characteristic.projectiveGraph 1) U

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  cases role
  refine ⟨(),2,3,?_⟩
  intro he
  have e : total (smallMomentTable 2) = total (smallMomentTable 3) := congrArg total he
  have h2 : total (smallMomentTable 2) = 0 := by
    have h := (compact_projective_walsh 2 (by norm_num)).1 1
    change total (smallMomentTable 2) = _ at h
    exact h.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])
  have h3 : total (smallMomentTable 3) = 3/4 := by
    have h := (compact_projective_walsh 3 (by norm_num)).1 1
    change total (smallMomentTable 3) = _ at h
    exact h.trans (by norm_num [Fin.prod_univ_succ, ← Nat.cast_ofNat (R := ℝ), Real.rpow_natCast])
  rw [h2,h3] at e
  norm_num at e

def source_registration : Registration arena (type_of% @physical_gap_readout) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨physical_gap_readout,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,
    rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence


def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@physical_gap_readout) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification.physical_gap_readout.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ K => smallMomentTable K) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
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
end Reg.D5.S3.Quantum.Entanglement.StabilizerMultiEntropy.GraphStateSmallOrderClassification
