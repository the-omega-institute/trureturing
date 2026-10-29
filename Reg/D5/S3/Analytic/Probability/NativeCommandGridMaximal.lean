import Reg.D5.S3.Analytic.Probability.NativeCommandPathTightness
import D5.S3.Analytic.Probability.NativeCommandGridMaximal

/-! A dependent realization of the entire uniform normal-grid estimate. -/
noncomputable section
open Set MeasureTheory LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.Analytic.Probability.NativeCommandLifetime
open _root_.D5.S3.Analytic.Probability.NativeCommandGridMaximal
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Probability.NativeCommandGridMaximal

private theorem grid_zero (B : Model) (n k : ℕ) :
    gridFourthExpectation B n k 0 = 0 := by
  simp [gridFourthExpectation,gridFourthMaximum]

private theorem witness_grid_positive :
    0 < gridFourthExpectation NativeCommandLifetime.witnessModel 1 0 1 := by
  let B := NativeCommandLifetime.witnessModel
  have h0 (w : Fin (1^3) → SignPair) : 0 ≤ gridFourthMaximum B 1 w 0 1 := by
    unfold gridFourthMaximum
    exact (by positivity : 0 ≤ ‖command B 1 w (((0+0:ℕ):ℝ)*mesh 1)-
      command B 1 w (((0:ℕ):ℝ)*mesh 1)‖^4).trans
        (Finset.le_sup' (fun j => ‖command B 1 w (((0+j:ℕ):ℝ)*mesh 1)-
          command B 1 w (((0:ℕ):ℝ)*mesh 1)‖^4)
          (Finset.mem_range.mpr (by norm_num : 0 < 1+1)))
  let w : Fin (1^3) → SignPair := fun _ => (true,true)
  have hz : command B 1 w 0 = 0 :=
    trajectory_zero B (mesh 1) (by norm_num [mesh]) _ _
      (by norm_num [Alive,sourceMap,B,NativeCommandLifetime.witnessModel])
  have hbound : ‖command B 1 w 1-command B 1 w 0‖^4 ≤ gridFourthMaximum B 1 w 0 1 := by
    have h := Finset.le_sup' (fun j => ‖command B 1 w (((0+j:ℕ):ℝ)*mesh 1)-
      command B 1 w (((0:ℕ):ℝ)*mesh 1)‖^4)
      (Finset.mem_range.mpr (by norm_num : 1 < 1+1))
    simpa only [gridFourthMaximum,mesh,Nat.zero_add,Nat.cast_one,Nat.cast_zero,
      one_pow,div_one,mul_one,zero_mul] using h
  have hpos : 0 < ‖command B 1 w 1-command B 1 w 0‖^4 := by
    apply pow_pos
    apply norm_pos_iff.mpr
    intro he
    have hh := congrFun he 0
    rw [hz] at hh
    have hv := NativeCommandPathTightness.witness_endpoint
    change command B 1 w 1 0 = _ at hv
    simp [hv] at hh
  have hsum : 0 < ∑ v : Fin (1^3) → SignPair, gridFourthMaximum B 1 v 0 1 :=
    Finset.sum_pos' (fun v _ => h0 v) ⟨w,Finset.mem_univ w,hpos.trans_le hbound⟩
  exact mul_pos (by norm_num) hsum

@[reducible] def signature : Signature where
  Params := Σ _ : Model, Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => gridFourthExpectation p.1 p.2.1 p.2.2 m) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law X := ∀ B : Model, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → ∀ k m : ℕ,
    k+m ≤ n^3 → (m:ℝ)*mesh n ≤ 2 →
      X.readout () ⟨B,n,k⟩ m ≤ C*((m:ℝ)*mesh n)^2

private theorem rejected_law : ¬arena.Law rejected := by
  intro hh
  obtain ⟨C,_hC,hall⟩ := hh NativeCommandLifetime.witnessModel
  have h := hall 1 (by norm_num) 0 0 (by norm_num) (by norm_num [mesh])
  have he : rejected.readout () ⟨NativeCommandLifetime.witnessModel,1,0⟩ 0 = 1 := by
    rfl
  rw [he] at h
  norm_num at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨NativeCommandLifetime.witnessModel,1,0⟩,0,1,?_⟩
  change gridFourthExpectation NativeCommandLifetime.witnessModel 1 0 0 ≠
    gridFourthExpectation NativeCommandLifetime.witnessModel 1 0 1
  rw [grid_zero]
  exact ne_of_lt witness_grid_positive

def family : Registration arena (type_of% (@actual_grid_maximal_estimate)) where
  actual := realize signature
    (fun _ p m => gridFourthExpectation p.1 p.2.1 p.2.2 m) Empty.elim
  bridge := Iff.rfl
  variation := ⟨actual_grid_maximal_estimate,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_grid_maximal_estimate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Probability.NativeCommandGridMaximal.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.NativeCommandGridMaximal.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p m => gridFourthExpectation p.1 p.2.1 p.2.2 m) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.NativeCommandGridMaximal
    definition := none
    coordinates := #[0,2,4]
    readouts := #[{
      path := #["body","arg","body","arg",
        "body","body","body","body","body","body","fn","arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Analytic.Probability.NativeCommandGridMaximal
