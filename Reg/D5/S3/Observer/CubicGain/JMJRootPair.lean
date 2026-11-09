import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.JMJRootPair
import Reg.D5.S3.Observer.CubicGain.JMJPairLosing
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
noncomputable section
open scoped Matrix Classical
namespace Reg.D5.S3.Observer.CubicGain.JMJRootPair
open _root_.D5.S3.Observer.Linear.GainRay
open _root_.D5.S3.Observer.CubicGain.MixedTripleExclusion
open _root_.D5.S3.Observer.CubicGain.JMJRootPair
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

private theorem ha : 0 < (1/5:ℝ) ∧ (1/5:ℝ) < 2/5 := by norm_num
private def WL : World3 := lowerWorld (1/5) ha
private def WU : World3 := upperWorld (1/5) ha
private theorem witness : WL ≠ WU ∧
    readings WL [true, false, true, true] = ![0, 24, 48, 36, 144/5] ∧
    readings WU [true, false, true, true] = ![0, 24, 48, 36, 144/5] ∧
    Losing 3 {WL, WU} [true, false, true, true] := by
  have h := canonical_pair_losing (1/5) ha
  norm_num only [show (36:ℝ)*(1/5+4/5)=36 by norm_num] at h
  exact h

abbrev signature : Signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => Finset World3) (fun _ => Bool)

namespace Construction
def actual : Realization signature := realize signature
  (fun _ _ T => decide (Losing 3 T [true, false, true, true])) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) (ha : 0 < a ∧ a < 2/5),
    lowerWorld a ha ≠ upperWorld a ha ∧
    readings (lowerWorld a ha) [true, false, true, true] = ![0, 24, 48, 36*(a+4/5), 144/5] ∧
    readings (upperWorld a ha) [true, false, true, true] = ![0, 24, 48, 36*(a+4/5), 144/5] ∧
    R.readout () () {lowerWorld a ha, upperWorld a ha} = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := (h (1/5) ha).2.2.2
  simp [rejected, realize] at hh

def family : Registration arena (type_of% @canonical_pair_losing) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using canonical_pair_losing,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ∅, {WL, WU}, ?_⟩
    have he : ¬ Losing 3 (∅ : Finset World3) [true, false, true, true] := by
      intro h
      have hg := h.1
      norm_num at hg
    simp [actual, realize, he, witness.2.2.2]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonical_pair_losing) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.JMJRootPair.canonical_pair_losing.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.JMJRootPair.Construction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => decide (Losing 3 T [true, false, true, true])) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.JMJRootPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Construction

namespace Classification
def actual : Realization signature := realize signature
  (fun _ _ T => decide (Losing 3 T [true, false, true, true])) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (z v : ℝ) (W Z : World3) (_hne : W ≠ Z)
    (_hW : readings W [true, false, true, true] = ![0, 24, 48, z, v])
    (_hZ : readings Z [true, false, true, true] = ![0, 24, 48, z, v]),
    R.readout () () {W, Z} = true ↔
      ∃ hz : 144/5 < z ∧ z < 216/5, v=144/5 ∧ {W, Z}=canonicalPair z hz
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hr := (jmjj_pair_losing_iff 36 (144/5) WL WU witness.1 witness.2.1 witness.2.2.1).1 witness.2.2.2
  have hh := (h 36 (144/5) WL WU witness.1 witness.2.1 witness.2.2.1).2 hr
  simp [rejected, realize] at hh

def family : Registration arena (type_of% @jmjj_pair_losing_iff) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using jmjj_pair_losing_iff,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ∅, {WL, WU}, ?_⟩
    have he : ¬ Losing 3 (∅ : Finset World3) [true, false, true, true] := by
      intro h
      have hg := h.1
      norm_num at hg
    simp [actual, realize, he, witness.2.2.2]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@jmjj_pair_losing_iff) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.JMJRootPair.jmjj_pair_losing_iff.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.JMJRootPair.Classification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => decide (Losing 3 T [true, false, true, true])) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.JMJRootPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Classification


private def mLeft : World3 := Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld
  1 1 (by norm_num) (by norm_num) ![576/7, 56, -260/7, 36/7]
  (by intro h; have hh := congrFun h 0; norm_num at hh) (-576/7)
private def mRight : World3 := Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld
  2 1 (by norm_num) (by norm_num) ![400/3, 512/9, -38, 46/9]
  (by intro h; have hh := congrFun h 0; norm_num at hh) (-400/3)
private theorem m_ne : mLeft ≠ mRight := by
  intro h
  have hh := congrArg (fun W : World3 => W.source 0 0) h
  norm_num [mLeft, mRight, Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld, sourceChart] at hh
private theorem m_history :
    readings mLeft [true, false, true, false] = ![0, 24, 48, 0, 0] ∧
    readings mRight [true, false, true, false] = ![0, 24, 48, 0, 0] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [mLeft, mRight, Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld,
      sourceChart, readings, readAt, gain, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ,
      acquisition, Raw,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.word,
      _root_.D5.S3.Arith.FibonacciAtomic.SelfCalibratingRawWords.atomic,
      _root_.D5.S3.Arith.FibonacciAtomic.GraftAffineClosure.matrixM,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

private def zeroWorld (b : Bool) : World3 := Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld
  (if b then 1 else 2) 1 (by cases b <;> norm_num) (by norm_num) ![-210, 107, -18, 1]
  (by intro h; have hh := congrFun h 0; norm_num at hh) 0
private theorem zero_ne : zeroWorld true ≠ zeroWorld false := by
  intro h
  have hh := congrArg (fun W : World3 => W.source 0 0) h
  norm_num [zeroWorld, Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld, sourceChart] at hh
private theorem zero_read (b : Bool) (u : List Bool) (n : ℕ)
    (hn : n=5 ∨ n=6 ∨ n=7) : readAt (zeroWorld b) u n=0 := by
  rcases hn with rfl | rfl | rfl <;>
    norm_num [readAt, zeroWorld, Reg.D5.S3.Observer.CubicGain.MixedTripleExclusion.legalWorld,
      gain, Polynomial.ofFn_eq_sum_monomial, Fin.sum_univ_succ]
private def zeroPair : Finset World3 := {zeroWorld true, zeroWorld false}
private theorem zero_slice (v : List Bool) (E : Bool) (hv : 4 ≤ v.length ∧ v.length ≤ 6) :
    responseSlice zeroPair v E 0=zeroPair := by
  apply Finset.filter_eq_self.2
  intro W hW
  simp only [zeroPair, Finset.mem_insert, Finset.mem_singleton] at hW
  rcases hW with rfl | rfl
  · apply zero_read
    omega
  · apply zero_read
    omega
private theorem zero_losing : Losing 3 zeroPair [true, false, true, false] := by
  have hc : 2 ≤ zeroPair.card := by simp [zeroPair, zero_ne]
  refine ⟨hc, fun E => ⟨0, ?_⟩⟩
  rw [zero_slice _ E (by simp)]
  refine ⟨hc, fun F => ⟨0, ?_⟩⟩
  rw [zero_slice _ F (by simp)]
  refine ⟨hc, fun G => ⟨0, ?_⟩⟩
  rw [zero_slice _ G (by simp)]
  exact hc

namespace Exclusion
def actual : Realization signature := realize signature
  (fun _ _ T => decide (Losing 3 T [true, false, true, false])) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => true) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (z v : ℝ) (W Z : World3) (_hne : W ≠ Z)
    (_hW : readings W [true, false, true, false] = ![0, 24, 48, z, v])
    (_hZ : readings Z [true, false, true, false] = ![0, 24, 48, z, v]),
    ¬ R.readout () () {W, Z} = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h 0 0 mLeft mRight m_ne m_history.1 m_history.2 rfl

def family : Registration arena (type_of% @jmjm_pair_not_losing) where
  actual := actual
  bridge := by simp only [arena, actual, realize, decide_eq_true_eq]
  variation := ⟨by simpa only [arena, actual, realize, decide_eq_true_eq] using jmjm_pair_not_losing,
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), ∅, zeroPair, ?_⟩
    have he : ¬ Losing 3 (∅ : Finset World3) [true, false, true, false] := by
      intro h
      have hg := h.1
      norm_num at hg
    simp [actual, realize, he, zero_losing]

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@jmjm_pair_not_losing) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.JMJRootPair.jmjm_pair_not_losing.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.JMJRootPair.Exclusion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ T => decide (Losing 3 T [true, false, true, false])) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.JMJRootPair
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family
#print axioms registration
end Exclusion

end Reg.D5.S3.Observer.CubicGain.JMJRootPair
