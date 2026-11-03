import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.NearSquareLatticeRigidity
import Reg.Support.DependentFamily

/-! Exact determinant readout for the consumed two-generator index identity. -/

namespace Reg.D5.S3.FiniteGroups.NearSquareLatticeRigidity

open _root_.D5.S3.FiniteGroups.NearSquareLatticeRigidity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev determinantSignature : Signature where
  Params := Plane
  State _ := Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def determinantActual : Realization determinantSignature := realize determinantSignature
  (fun _ u v => (u 0 * v 1 - u 1 * v 0).natAbs) (fun e => nomatch e)

def determinantRejected : Realization determinantSignature := realize determinantSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

abbrev determinantArena : Arena where
  signature := determinantSignature
  Law R := ∀ (u v : Plane) (_ : u 0 * v 1 - u 1 * v 0 ≠ 0),
    (Submodule.span ℤ (Set.range ![u, v])).toAddSubgroup.index =
      R.readout () u v

private theorem determinantRejected_law : ¬ determinantArena.Law determinantRejected := by
  intro h
  have hh := h ![1,0] ![0,1] (by norm_num)
  rw [span_pair_index _ _ (by norm_num)] at hh
  norm_num [determinantRejected, realize] at hh

def determinantSource : Registration determinantArena (type_of% (@span_pair_index)) where
  actual := determinantActual
  bridge := Iff.rfl
  variation := ⟨span_pair_index, determinantRejected, determinantRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨determinantRejected, ?_, rfl, determinantRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨![1,0], ![0,1], ![0,2], ?_⟩
    norm_num [determinantActual, realize]

def determinantRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@span_pair_index) (Realization determinantSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.NearSquareLatticeRigidity.span_pair_index.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.NearSquareLatticeRigidity.determinantSource
  realizationSource := none
  generated := false
  arena := .source ⟨determinantArena⟩
  objectArena := .source ⟨determinantArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source determinantArena ⟨determinantSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize determinantSignature
    (fun _ u v => (u 0 * v 1 - u 1 * v 0).natAbs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.NearSquareLatticeRigidity
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev coveringSignature : Signature where
  Params := Σ _ : ℤ, ℤ
  State _ := Submodule ℤ Plane
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def coveringActual : Realization coveringSignature := realize coveringSignature
  (fun _ _ L => L.toAddSubgroup.index) (fun e => nomatch e)

def coveringRejected : Realization coveringSignature := realize coveringSignature
  (fun _ _ _ => 3) (fun e => nomatch e)

abbrev coveringArena : Arena where
  signature := coveringSignature
  Law R := ∀ {n δ : ℤ} (L : Submodule ℤ Plane)
    (_ : 2 ≤ n) (_ : 0 ≤ δ) (_ : δ < n)
    (_ : (R.readout () ⟨n,δ⟩ L : ℤ) = n ^ 2 - δ)
    (_ : RectangleCovers L n n),
    ∃ a b ε : ℤ, 0 ≤ a ∧ a < n ∧ 0 ≤ b ∧ b < n ∧
      (ε = 1 ∨ ε = -1) ∧ a * b = δ ∧
      L = Submodule.span ℤ (Set.range ![![n, -ε*b], ![-a, ε*n]])

private def badLattice : Submodule ℤ Plane :=
  Submodule.span ℤ (Set.range ![![(3 : ℤ),0], ![(0 : ℤ),1]])

private theorem coveringRejected_law : ¬ coveringArena.Law coveringRejected := by
  intro h
  have hgood : RectangleCovers (⊤ : Submodule ℤ Plane) 2 2 := by
    intro z
    exact ⟨0,0,by norm_num,by norm_num,by norm_num,by norm_num,Submodule.mem_top⟩
  obtain ⟨a,b,ε,_,_,_,_,hε,hab,he⟩ := h (n := 2) (δ := 1) ⊤
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [coveringRejected, realize]) hgood
  have hdet : (2*(ε*2)-(-ε*b)*(-a)).natAbs = 3 := by
    rcases hε with rfl | rfl
    · have hh : 2*((1 : ℤ)*2)-(-(1 : ℤ)*b)*(-a) = 3 := by nlinarith
      rw [hh]
      norm_num
    · have hh : 2*((-1 : ℤ)*2)-(-(-1 : ℤ)*b)*(-a) = -3 := by nlinarith
      rw [hh]
      norm_num
  have hd : 2*(ε*2)-(-ε*b)*(-a) ≠ 0 := by
    intro hz
    rw [hz] at hdet
    norm_num at hdet
  have hi := span_pair_index ![2,-ε*b] ![-a,ε*2] hd
  rw [← he] at hi
  change (⊤ : AddSubgroup Plane).index = _ at hi
  rw [AddSubgroup.index_top] at hi
  change 1 = (2*(ε*2)-(-ε*b)*(-a)).natAbs at hi
  rw [hdet] at hi
  norm_num at hi

def coveringSource : Registration coveringArena (type_of% (@near_square_rigidity)) where
  actual := coveringActual
  bridge := Iff.rfl
  variation := ⟨near_square_rigidity, coveringRejected, coveringRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coveringRejected, ?_, rfl, coveringRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, ⊤, badLattice, ?_⟩
    have hi : badLattice.toAddSubgroup.index = 3 := by
      rw [badLattice, span_pair_index _ _ (by norm_num)]
      norm_num
    have ht : (⊤ : Submodule ℤ Plane).toAddSubgroup.index = 1 := AddSubgroup.index_top
    norm_num [coveringActual, realize, ht, hi]

def coveringRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@near_square_rigidity) (Realization coveringSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.NearSquareLatticeRigidity.near_square_rigidity.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.NearSquareLatticeRigidity.coveringSource
  realizationSource := none
  generated := false
  arena := .source ⟨coveringArena⟩
  objectArena := .source ⟨coveringArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coveringArena ⟨coveringSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coveringSignature
    (fun _ _ L => L.toAddSubgroup.index) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.NearSquareLatticeRigidity
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body","body","body","domain","fn","arg","arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.FiniteGroups.NearSquareLatticeRigidity
