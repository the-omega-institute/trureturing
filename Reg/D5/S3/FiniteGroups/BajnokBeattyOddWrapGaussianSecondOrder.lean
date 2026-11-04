import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
import Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import Reg.Support.DependentFamily

/-! Registration for the full original-count second-order envelope.
The native count family, whole-role interventions, original integer domain
and every band endpoint are retained, including composite odd p.
Source-occurrence binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 .
sourceSelection and familyRecord remain none; continuation is unknown.
-/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

abbrev gaussianSecondOrderArena : Arena where
  signature := gaussianUpperSignature
  Law R := ∀ (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
      (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t),
    let pp : gaussianUpperSignature.Params := ⟨p,hp5,hpo⟩
    let tt : gaussianUpperSignature.State pp := ⟨t,ht2,htp,hband⟩
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    |2*(R.readout 0 pp tt : ℝ)/(R.readout 1 pp tt : ℝ) -
        (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(p : ℝ)^2| ≤
      1/(5*(p : ℝ)^4)

private theorem gaussianSecondOrder_actual_law :
    gaussianSecondOrderArena.Law gaussianUpperActual := by
  exact actual_gaussian_second_order_envelope

private theorem gaussianSecondOrder_rejected_law (i : Fin 2) :
    ¬ gaussianSecondOrderArena.Law (gaussianUpperRejected i) := by
  intro h
  have hh := h 5 5 (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
  let s : ℝ := 4*(5 : ℝ)^2/((5 : ℝ)*(6*(5 : ℝ)-1)+1)
  have hs0 : 0 < s := by norm_num [s]
  have hs1 : s < 1 := by norm_num [s]
  have hs3 : s^3 ≤ 1 := by
    simpa using pow_le_pow_left₀ hs0.le hs1.le 3
  have he1 : Real.exp s < 11/4 :=
    (Real.exp_lt_exp.mpr hs1).trans
      (Real.exp_one_lt_d9.trans (by norm_num))
  have he2 : Real.exp (-9*s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hH : (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s)) ≤ 55/192 := by
    calc
      _ ≤ (s^3/48)*(5*Real.exp s) := by
        exact mul_le_mul_of_nonneg_left
          (by linarith only [Real.exp_pos (-9*s)]) (by positivity)
      _ ≤ (1/48)*(5*Real.exp s) := by
        exact mul_le_mul_of_nonneg_right
          (by linarith only [hs3]) (by positivity)
      _ ≤ 55/192 := by linarith only [he1]
  have hrhs : Real.exp s+Real.exp (-9*s)+
      (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(5 : ℝ)^2+
      1/(5*(5 : ℝ)^4) < 4 := by
    calc
      _ ≤ (11/4 : ℝ)+1+(55/192)/(5 : ℝ)^2+1/(5*(5 : ℝ)^4) :=
        add_le_add
          (add_le_add (add_le_add he1.le he2.le)
            (div_le_div_of_nonneg_right hH (by norm_num))) le_rfl
      _ < 4 := by norm_num
  have hc := actual_odd_wrap_counts 5 5 (by norm_num) (by decide) (by norm_num)
  have h19 : 2 ≤ (original_return_pair 5 5).1 := by
    have hcount : (original_return_pair 5 5).1 =
        2*(Nat.choose 145 75+Nat.choose 145 95) := by
      calc
        _ = 2*(Nat.choose (5*(6*5-1) : ℤ).toNat (5*((6*5-1)+1)/2 : ℤ).toNat+Nat.choose (5*(6*5-1) : ℤ).toNat (5*((6*5-1)+9)/2 : ℤ).toNat) := hc.1
        _ = _ := by rw [show (5*(6*5-1) : ℤ).toNat = 145 by norm_num,
          show (5*((6*5-1)+1)/2 : ℤ).toNat = 75 by norm_num,
          show (5*((6*5-1)+9)/2 : ℤ).toNat = 95 by norm_num]
    have hp : 0 < Nat.choose 145 75 := Nat.choose_pos (by decide)
    omega
  have h33 : 0 < (original_return_pair 5 5).2 := by
    have hcount : (original_return_pair 5 5).2 = 4*Nat.choose 145 80 := by
      calc
        _ = 4*Nat.choose (5*(6*5-1) : ℤ).toNat (5*((6*5-1)+3)/2 : ℤ).toNat := hc.2
        _ = _ := by rw [show (5*(6*5-1) : ℤ).toNat = 145 by norm_num,
          show (5*((6*5-1)+3)/2 : ℤ).toNat = 80 by norm_num]
    have hp : 0 < Nat.choose 145 80 := Nat.choose_pos (by decide)
    omega
  have h19R : (2 : ℝ) ≤ ((original_return_pair 5 5).1 : ℝ) := by exact_mod_cast h19
  have h33R : (0 : ℝ) < ((original_return_pair 5 5).2 : ℝ) := by exact_mod_cast h33
  fin_cases i
  · have hh' : |2*(2*((original_return_pair 5 5).2 : ℝ))/
        ((original_return_pair 5 5).2 : ℝ) -
        (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(5 : ℝ)^2| ≤
        1/(5*(5 : ℝ)^4) := by
      simpa [gaussianUpperRejected, gaussianUpperActual, realize, s] using hh
    have hratio : 2*(2*((original_return_pair 5 5).2 : ℝ))/
        ((original_return_pair 5 5).2 : ℝ) = 4 := by
      field_simp [h33R.ne'] <;> ring
    rw [hratio] at hh'
    have hu := (abs_le.mp hh').2
    linarith only [hu,hrhs]
  · have hh' : |2*((original_return_pair 5 5).1 : ℝ) -
        (Real.exp s+Real.exp (-9*s)) -
        (s^3/48)*(5*Real.exp s-405*Real.exp (-9*s))/(5 : ℝ)^2| ≤
        1/(5*(5 : ℝ)^4) := by
      simpa [gaussianUpperRejected, gaussianUpperActual, realize, s] using hh
    have hu := (abs_le.mp hh').2
    linarith only [hu,hrhs,h19R]

noncomputable def gaussianSecondOrderSource : Registration gaussianSecondOrderArena
    (type_of% actual_gaussian_second_order_envelope) where
  actual := gaussianUpperActual
  bridge := Iff.rfl
  variation := ⟨gaussianSecondOrder_actual_law,
    gaussianUpperRejected 0, gaussianSecondOrder_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gaussianUpperRejected i, ?_, rfl, gaussianSecondOrder_rejected_law i⟩
      intro j hj
      funext p t
      simp [gaussianUpperRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := gaussianUpperSource.dependence

noncomputable def gaussianSecondOrderRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_gaussian_second_order_envelope)
      (Realization gaussianUpperSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder.actual_gaussian_second_order_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder.gaussianSecondOrderSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianSecondOrderArena⟩
  objectArena := .source ⟨gaussianSecondOrderArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianSecondOrderArena ⟨gaussianSecondOrderSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some gaussianUpperActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianSecondOrder
