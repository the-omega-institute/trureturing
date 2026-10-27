import Reg.D5.S3.Analytic.Probability.NativeCommandLifetime
import D5.S3.Analytic.Probability.NativeCommandPathTightness

noncomputable section
open Set MeasureTheory LeanInformationAudit
open scoped BigOperators
open _root_.D5.S3.Analytic.Probability.NativeCommandLifetime
open _root_.D5.S3.Analytic.Probability.NativeCommandPathTightness
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
attribute [local instance] Classical.propDecidable
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Analytic.Probability.NativeCommandPathTightness

private theorem command_one (B : Model) (w : Fin (1^3) → SignPair)
    (t : ℝ) (ht : t ≤ 1) :
    command B 1 w t = cutChord 1
      (if Alive B (next B 1 0 (w 0)) then 1 else hitFraction B 0 (increment B 1 0 (w 0)))
      0 (increment B 1 0 (w 0)) t := by
  have he : List.ofFn w = [w 0] := by simp [List.ofFn_succ]
  simp only [command,he,trajectory,mesh]
  norm_num only [Nat.cast_one,one_pow,div_one]
  by_cases ha : Alive B (next B 1 0 (w 0))
  · simp [ha,ht,cutChord,cutParameter]
  · simp [ha,cutChord,cutParameter]

private theorem command_one_continuous (B : Model) (w : Fin (1^3) → SignPair) :
    ContinuousOn (command B 1 w) (Icc 0 1) := by
  let cap := if Alive B (next B 1 0 (w 0)) then 1 else hitFraction B 0 (increment B 1 0 (w 0))
  have hc : Continuous (cutChord 1 cap (0 : Triple) (increment B 1 0 (w 0))) := by
    unfold cutChord chord cutParameter
    fun_prop
  exact hc.continuousOn.congr (fun t ht => command_one B w t ht.2)

private theorem block_one_bdd (B : Model) (w : Fin (1^3) → SignPair) :
    BddAbove {x : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      x = ‖command B 1 w t-command B 1 w s‖^4} := by
  have hc := command_one_continuous B w
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ‖command B 1 w p.2-command B 1 w p.1‖^4) ((Icc (0:ℝ) 1) ×ˢ (Icc (0:ℝ) 1)) :=
    ((hc.comp continuous_snd.continuousOn (fun _ hp => hp.2)).sub
      (hc.comp continuous_fst.continuousOn (fun _ hp => hp.1))).norm.pow 4
  have hK := ((isCompact_Icc : IsCompact (Icc (0:ℝ) 1)).prod isCompact_Icc).image_of_continuousOn hcont
  apply hK.bddAbove.mono
  rintro x ⟨s,hs,t,ht,rfl⟩
  exact ⟨(s,t),⟨hs,ht⟩,rfl⟩


private theorem witness_increment :
    increment NativeCommandLifetime.witnessModel 1 0 (true,true) 0 = Real.sqrt 2 := by
  simp [increment,drift,sigma,
    _root_.D5.S3.Observer.Hankel.PositiveGramianBalancing.gramianRoot,
    NativeCommandLifetime.witnessModel, Matrix.one_apply]
  rfl


private theorem block_zero (B : Model) (n : ℕ) :
    blockFourthExpectation B n 1 0 0 = 0 := by
  simp [blockFourthExpectation,blockFourthOscillation]

private theorem witness_endpoint :
    command NativeCommandLifetime.witnessModel 1 (fun _ => (true,true)) 1 0 = 1/16 := by
  let B := NativeCommandLifetime.witnessModel
  have hs : (1/16:ℝ) < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg (2:ℝ)]
  have hv : increment B 1 0 (true,true) 0 = Real.sqrt 2 := by
    simpa [B] using witness_increment
  have ha : ¬Alive B (next B 1 0 (true,true)) := by
    intro h
    have hu := h.2
    simp only [sourceMap,next,chord,Matrix.cons_val_zero,Pi.zero_apply,zero_add,one_mul] at hu
    change (1/8:ℝ)+increment B 1 0 (true,true) 0 < 3/16 at hu
    rw [hv] at hu
    linarith
  have hcap : hitFraction B 0 (increment B 1 0 (true,true)) = (1/16:ℝ)/Real.sqrt 2 := by
    rw [hitFraction,hv,ite_eq_left (by linarith : 0 < Real.sqrt 2)]
    norm_num [sourceMap,B,NativeCommandLifetime.witnessModel]
    exact (div_le_one (by linarith : 0 < Real.sqrt 2)).mpr (by linarith)
  rw [command_one B (fun _ => (true,true)) 1 le_rfl]
  simp only [ha,ite_false,cutChord,cutParameter,div_one,chord,
    Matrix.cons_val_zero,Pi.zero_apply,zero_add,hcap]
  rw [max_eq_left (by norm_num : (0:ℝ) ≤ 1)]
  rw [min_eq_right ((div_le_one (by linarith : 0 < Real.sqrt 2)).mpr (by linarith)),hv]
  exact div_mul_cancel₀ _ (by linarith : Real.sqrt 2 ≠ 0)

private theorem witness_block_positive :
    0 < blockFourthExpectation NativeCommandLifetime.witnessModel 1 1 0 1 := by
  let B := NativeCommandLifetime.witnessModel
  have h0 (w : Fin (1^3) → SignPair) : 0 ≤ blockFourthOscillation B 1 w 1 0 1 := by
    apply le_csSup (by simpa [blockFourthOscillation] using block_one_bdd B w)
    exact ⟨0,by norm_num,0,by norm_num,by simp⟩
  let w : Fin (1^3) → SignPair := fun _ => (true,true)
  have hbound : ‖command B 1 w 1-command B 1 w 0‖^4 ≤ blockFourthOscillation B 1 w 1 0 1 := by
    apply le_csSup (by simpa [blockFourthOscillation] using block_one_bdd B w)
    exact ⟨0,by norm_num,1,by norm_num,rfl⟩
  have hz : command B 1 w 0 = 0 := by
    exact trajectory_zero B (mesh 1) (by norm_num [mesh]) _ _ (by norm_num [Alive,sourceMap,B,NativeCommandLifetime.witnessModel])
  have hpos : 0 < ‖command B 1 w 1-command B 1 w 0‖^4 := by
    apply pow_pos
    apply norm_pos_iff.mpr
    intro he
    have hh := congrFun he 0
    rw [hz] at hh
    have hv := witness_endpoint
    change command B 1 w 1 0 = _ at hv
    simp [hv] at hh
  have hsum : 0 < ∑ w : Fin (1^3) → SignPair, blockFourthOscillation B 1 w 1 0 1 :=
    Finset.sum_pos' (fun w _ => h0 w) ⟨w,Finset.mem_univ w,hpos.trans_le hbound⟩
  exact mul_pos (by norm_num) hsum


@[reducible] def signature : Signature where
  Params := Σ _ : Model, Σ _ : ℝ, Σ _ : ℕ, ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p h => blockFourthExpectation p.1 p.2.2.1 p.2.1 p.2.2.2 h) Empty.elim

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law X := ∀ B : Model, ∃ C : ℝ, 0 ≤ C ∧
    ∀ R : ℝ, 0 < R → ∀ n : ℕ, R+1 < n →
      ∀ a h : ℝ, 0 ≤ a → a ≤ R → 0 < h → h ≤ mesh n →
        X.readout () ⟨B,R,n,a⟩ h ≤ C*h^2 ∧
        ∀ (w : Fin (n^3) → SignPair) (t : ℝ), 0 ≤ t →
          commandArea B n w t = command B n w t 2

private theorem rejected_law : ¬arena.Law rejected := by
  intro hh
  obtain ⟨C,hC,hall⟩ := hh NativeCommandLifetime.witnessModel
  let h : ℝ := 1/(9*(C+1))
  have hd : 0 < 9*(C+1) := by positivity
  have hp : 0 < h := by dsimp [h]; positivity
  have he : h*(9*(C+1)) = 1 := by dsimp [h]; field_simp
  have hsmall : h ≤ mesh 3 := by norm_num [mesh]; nlinarith
  have hCh : C*h < 1 := by nlinarith
  have hh1 : h ≤ 1 := by norm_num [mesh] at hsmall; linarith
  have hpow : C*h^2 < 1 := by
    have hm := mul_le_mul_of_nonneg_left hh1 (mul_nonneg hC hp.le)
    nlinarith
  have hb := (hall 1 (by norm_num) 3 (by norm_num) 0 h
    (by norm_num) (by norm_num) hp hsmall).1
  change 1 ≤ C*h^2 at hb
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨⟨NativeCommandLifetime.witnessModel,1,1,0⟩,0,1,?_⟩
  change blockFourthExpectation NativeCommandLifetime.witnessModel 1 1 0 0 ≠
    blockFourthExpectation NativeCommandLifetime.witnessModel 1 1 0 1
  rw [block_zero]
  exact ne_of_lt witness_block_positive

def family : Registration arena (type_of% (@actual_short_block_estimate)) where
  actual := realize signature
    (fun _ p h => blockFourthExpectation p.1 p.2.2.1 p.2.1 p.2.2.2 h) Empty.elim
  bridge := Iff.rfl
  variation := ⟨actual_short_block_estimate,rejected,rejected_law⟩
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
    (@actual_short_block_estimate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Analytic.Probability.NativeCommandPathTightness.unit
  realizationName := `Reg.D5.S3.Analytic.Probability.NativeCommandPathTightness.family
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
    (fun _ p h => blockFourthExpectation p.1 p.2.2.1 p.2.1 p.2.2.2 h) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Analytic.Probability.NativeCommandPathTightness
    definition := none
    coordinates := #[0,2,4,6]
    readouts := #[{
      path := #["body","arg","body","arg",
        "body","body","body","body","body","body","body","body","body","body",
        "fn","arg","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Analytic.Probability.NativeCommandPathTightness
