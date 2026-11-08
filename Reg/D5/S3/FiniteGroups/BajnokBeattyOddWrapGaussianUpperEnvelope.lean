import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! UNCOMPILED upper-only fragment, to be appended to the existing mirrored
Envelope Reg after the lower delivery. The full upper theorem telescope is
retained. Dependence uses the two admissible states p=25,t=24/25.
Binding to the original readout occurrences remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 . -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

theorem choose_grow_diagonal (n k m : ℕ) (hk : k ≤ n) (hm : 0 < m) :
    Nat.choose n k < Nat.choose (n+2*m) (k+m) := by
  have step (a b : ℕ) (hba : b ≤ a) :
      a.choose b < (a+2).choose (b+1) := by
    have hle : a.choose b ≤ (a+1).choose b := by
      simpa only [Nat.succ_eq_add_one] using Nat.choose_le_succ a b
    have hpos : 0 < (a+1).choose (b+1) := Nat.choose_pos (by omega)
    calc
      a.choose b ≤ (a+1).choose b := hle
      _ < (a+1).choose b+(a+1).choose (b+1) := by omega
      _ = (a+2).choose (b+1) := by
        simpa only [Nat.add_assoc] using (Nat.choose_succ_succ' (a+1) b).symm
  have weak (r : ℕ) : n.choose k ≤ (n+2*r).choose (k+r) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have hh := ih.trans (step (n+2*r) (k+r) (by omega)).le
      simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc] using hh
  cases m with
  | zero => omega
  | succ r =>
    have hh := (weak r).trans_lt (step (n+2*r) (k+r) (by omega))
    simpa only [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc] using hh

abbrev gaussianUpperSignature : Signature where
  Params := {p : ℤ // 5 ≤ p ∧ Odd p}
  State p := {t : ℤ // 2 ≤ t ∧ t ≤ p.1 ∧ 24*p.1 ≤ 25*t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def gaussianUpperActual : Realization gaussianUpperSignature :=
  realize gaussianUpperSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e)

noncomputable def gaussianUpperRejected (i : Fin 2) :
    Realization gaussianUpperSignature :=
  realize gaussianUpperSignature
    (fun j p t => if j = i then
      (if i = 0 then 2*(original_return_pair p.1 t.1).2 else 1)
      else gaussianUpperActual.readout j p t)
    (fun e => nomatch e)

abbrev gaussianUpperArena : Arena where
  signature := gaussianUpperSignature
  Law R := ∀ (p t : ℤ) (hp5 : 5 ≤ p) (hpo : Odd p)
      (ht2 : 2 ≤ t) (htp : t ≤ p) (hband : 24*p ≤ 25*t),
    let pp : gaussianUpperSignature.Params := ⟨p,hp5,hpo⟩
    let tt : gaussianUpperSignature.State pp := ⟨t,ht2,htp,hband⟩
    let s : ℝ := 4*(p : ℝ)^2/((p : ℝ)*(6*(t : ℝ)-1)+1)
    2*(R.readout 0 pp tt : ℝ)/(R.readout 1 pp tt : ℝ) <
      Real.exp s+Real.exp (-9*s)+1/(10*(p : ℝ)^2)

private theorem gaussianUpper_actual_law :
    gaussianUpperArena.Law gaussianUpperActual := by
  exact actual_gaussian_upper_envelope

private theorem gaussianUpper_rejected_law (i : Fin 2) :
    ¬ gaussianUpperArena.Law (gaussianUpperRejected i) := by
  intro h
  have hh := h 5 5 (by norm_num) (by decide) (by norm_num) (by norm_num) (by norm_num)
  let s : ℝ := 4*(5 : ℝ)^2/((5 : ℝ)*(6*(5 : ℝ)-1)+1)
  have hs0 : 0 < s := by norm_num [s]
  have hs1 : s < 1 := by norm_num [s]
  have he1 : Real.exp s < 11/4 :=
    (Real.exp_lt_exp.mpr hs1).trans
      (Real.exp_one_lt_d9.trans (by norm_num))
  have he2 : Real.exp (-9*s) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hrhs : Real.exp s+Real.exp (-9*s)+1/(10*(5 : ℝ)^2) < 4 := by
    calc
      Real.exp s+Real.exp (-9*s)+1/(10*(5 : ℝ)^2) <
          (11/4 : ℝ)+1+1/(10*(5 : ℝ)^2) :=
        by simpa only [add_comm] using
          (add_lt_add_right (add_lt_add he1 he2) (1/(10*(5 : ℝ)^2)))
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
  · have hh' : 2*(2*((original_return_pair 5 5).2 : ℝ))/
        ((original_return_pair 5 5).2 : ℝ) <
        Real.exp s+Real.exp (-9*s)+1/(10*(5 : ℝ)^2) := by
      simpa [gaussianUpperRejected, gaussianUpperActual, realize, s] using hh
    have hratio : 2*(2*((original_return_pair 5 5).2 : ℝ))/
        ((original_return_pair 5 5).2 : ℝ) = 4 := by
      field_simp [h33R.ne'] <;> ring
    rw [hratio] at hh'
    linarith only [hh',hrhs]
  · have hh' : 2*((original_return_pair 5 5).1 : ℝ) <
        Real.exp s+Real.exp (-9*s)+1/(10*(5 : ℝ)^2) := by
      simpa [gaussianUpperRejected, gaussianUpperActual, realize, s] using hh
    linarith only [hh',hrhs,h19R]

private theorem gaussianUpper_actual_dependence :
    ObservationalDependence gaussianUpperSignature gaussianUpperActual := by
  intro i
  let p : gaussianUpperSignature.Params := ⟨25,by decide⟩
  refine ⟨p, ⟨24,by decide⟩, ⟨25,by decide⟩, ?_⟩
  have h24 := actual_odd_wrap_counts 25 24 (by norm_num) (by decide) (by norm_num)
  have h25 := actual_odd_wrap_counts 25 25 (by norm_num) (by decide) (by norm_num)
  have hA : Nat.choose 3575 1800 < Nat.choose 3725 1875 :=
    choose_grow_diagonal 3575 1800 75 (by decide) (by decide)
  have hB : Nat.choose 3575 1825 < Nat.choose 3725 1900 :=
    choose_grow_diagonal 3575 1825 75 (by decide) (by decide)
  have hD : Nat.choose 3575 1900 < Nat.choose 3725 1975 :=
    choose_grow_diagonal 3575 1900 75 (by decide) (by decide)
  fin_cases i
  · change returns19 25 24 3575 ≠ returns19 25 25 3725
    have hc24 : returns19 25 24 3575 =
        2*(Nat.choose 3575 1800+Nat.choose 3575 1900) := by
      calc
        _ = 2*(Nat.choose (25*(6*24-1) : ℤ).toNat (25*((6*24-1)+1)/2 : ℤ).toNat+Nat.choose (25*(6*24-1) : ℤ).toNat (25*((6*24-1)+9)/2 : ℤ).toNat) := h24.1
        _ = _ := by rw [show (25*(6*24-1) : ℤ).toNat = 3575 by norm_num,
          show (25*((6*24-1)+1)/2 : ℤ).toNat = 1800 by norm_num,
          show (25*((6*24-1)+9)/2 : ℤ).toNat = 1900 by norm_num]
    have hc25 : returns19 25 25 3725 =
        2*(Nat.choose 3725 1875+Nat.choose 3725 1975) := by
      calc
        _ = 2*(Nat.choose (25*(6*25-1) : ℤ).toNat (25*((6*25-1)+1)/2 : ℤ).toNat+Nat.choose (25*(6*25-1) : ℤ).toNat (25*((6*25-1)+9)/2 : ℤ).toNat) := h25.1
        _ = _ := by rw [show (25*(6*25-1) : ℤ).toNat = 3725 by norm_num,
          show (25*((6*25-1)+1)/2 : ℤ).toNat = 1875 by norm_num,
          show (25*((6*25-1)+9)/2 : ℤ).toNat = 1975 by norm_num]
    rw [hc24,hc25]
    omega
  · change returns33 25 24 3575 ≠ returns33 25 25 3725
    have hc24 : returns33 25 24 3575 = 4*Nat.choose 3575 1825 := by
      calc
        _ = 4*Nat.choose (25*(6*24-1) : ℤ).toNat (25*((6*24-1)+3)/2 : ℤ).toNat := h24.2
        _ = _ := by rw [show (25*(6*24-1) : ℤ).toNat = 3575 by norm_num,
          show (25*((6*24-1)+3)/2 : ℤ).toNat = 1825 by norm_num]
    have hc25 : returns33 25 25 3725 = 4*Nat.choose 3725 1900 := by
      calc
        _ = 4*Nat.choose (25*(6*25-1) : ℤ).toNat (25*((6*25-1)+3)/2 : ℤ).toNat := h25.2
        _ = _ := by rw [show (25*(6*25-1) : ℤ).toNat = 3725 by norm_num,
          show (25*((6*25-1)+3)/2 : ℤ).toNat = 1900 by norm_num]
    rw [hc24,hc25]
    omega

noncomputable def gaussianUpperSource : Registration gaussianUpperArena
    (type_of% actual_gaussian_upper_envelope) where
  actual := gaussianUpperActual
  bridge := Iff.rfl
  variation := ⟨gaussianUpper_actual_law,
    gaussianUpperRejected 0, gaussianUpper_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨gaussianUpperRejected i, ?_, rfl, gaussianUpper_rejected_law i⟩
      intro j hj
      funext p t
      simp [gaussianUpperRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := gaussianUpper_actual_dependence

noncomputable def gaussianUpperRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@actual_gaussian_upper_envelope)
      (Realization gaussianUpperSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope.actual_gaussian_upper_envelope.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope.gaussianUpperSource
  realizationSource := none
  generated := false
  arena := .source ⟨gaussianUpperArena⟩
  objectArena := .source ⟨gaussianUpperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gaussianUpperArena ⟨gaussianUpperSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gaussianUpperSignature
    (fun i p t => if i = 0 then (original_return_pair p.1 t.1).1
      else (original_return_pair p.1 t.1).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianUpperEnvelope
