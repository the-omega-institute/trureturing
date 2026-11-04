import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample
import Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
import Reg.Support.DependentFamily

/-! Full-domain registration attempt for the exact counterexample.
Both roles retain the complete original quotient counts at p=57425 and all
natural t>=2. Before, at, after and the centered-ceiling evaluation remain
in the Law. Dependence uses t=2/3 and symbolic binomial diagonal growth.
Binding remains unfinished under
https://github.com/the-omega-institute/trureturing/issues/25856 . -/

namespace Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample

open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapGaussianRoot
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapSingleCrossing
open _root_.D5.S3.FiniteGroups.BajnokBeattyOddWrapReturnCounts
open _root_.Reg.D5.S3.FiniteGroups.BajnokBeattyFirstReturnDefect
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Classical

private theorem choose_grow_diagonal (n k m : ℕ) (hk : k ≤ n) (hm : 0 < m) :
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

abbrev centeredCounterSignature : Signature where
  Params := Unit
  State _ := {t : ℕ // 2 ≤ t}
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def centeredCounterActual : Realization centeredCounterSignature :=
  realize centeredCounterSignature
    (fun i _ t => if i = 0 then (original_return_pair 57425 t.1).1
      else (original_return_pair 57425 t.1).2)
    (fun e => nomatch e)

noncomputable def centeredCounterRejected (i : Fin 2) :
    Realization centeredCounterSignature :=
  realize centeredCounterSignature
    (fun j p t => if j = i then 0 else centeredCounterActual.readout j p t)
    (fun e => nomatch e)

abbrev centeredCounterArena : Arena where
  signature := centeredCounterSignature
  Law R := 2 < (55310 : ℕ) ∧
    (∀ (t : ℕ) (ht2 : 2 ≤ t), t < 55310 →
      R.readout 1 () ⟨t,ht2⟩ < R.readout 0 () ⟨t,ht2⟩) ∧
    R.readout 0 () ⟨55310,by decide⟩ ≤ R.readout 1 () ⟨55310,by decide⟩ ∧
    (∀ (t : ℕ) (ht : 55310 < t),
      R.readout 0 () ⟨t,by omega⟩ < R.readout 1 () ⟨t,by omega⟩) ∧
    Int.ceil (alpha*57425+(1/6 : ℝ)) = 55311

private theorem centeredCounter_actual_law :
    centeredCounterArena.Law centeredCounterActual := by
  exact original_centered_ceiling_counterexample

private theorem centeredCounter_rejected_law (i : Fin 2) :
    ¬ centeredCounterArena.Law (centeredCounterRejected i) := by
  intro h
  fin_cases i
  · have hh := h.2.1 2 (by decide) (by decide)
    simpa [centeredCounterRejected, centeredCounterActual, realize] using hh
  · have hh := h.2.2.2.1 55311 (by decide)
    simpa [centeredCounterRejected, centeredCounterActual, realize] using hh

private theorem centeredCounter_actual_dependence :
    ObservationalDependence centeredCounterSignature centeredCounterActual := by
  intro i
  refine ⟨(), ⟨2,by decide⟩, ⟨3,by decide⟩, ?_⟩
  have h2 := actual_odd_wrap_counts 57425 2 (by norm_num)
    (by exact ⟨28712,by norm_num⟩) (by norm_num)
  have h3 := actual_odd_wrap_counts 57425 3 (by norm_num)
    (by exact ⟨28712,by norm_num⟩) (by norm_num)
  have hA : Nat.choose 631675 344550 < Nat.choose 976225 516825 :=
    choose_grow_diagonal 631675 344550 172275 (by decide) (by decide)
  have hB : Nat.choose 631675 401975 < Nat.choose 976225 574250 :=
    choose_grow_diagonal 631675 401975 172275 (by decide) (by decide)
  have hD : Nat.choose 631675 574250 < Nat.choose 976225 746525 :=
    choose_grow_diagonal 631675 574250 172275 (by decide) (by decide)
  fin_cases i
  · change returns19 57425 2 631675 ≠ returns19 57425 3 976225
    have hc2 : returns19 57425 2 631675 =
        2*(Nat.choose 631675 344550+Nat.choose 631675 574250) := by
      calc
        _ = 2*(Nat.choose (57425*(6*2-1) : ℤ).toNat
              (57425*((6*2-1)+1)/2 : ℤ).toNat +
            Nat.choose (57425*(6*2-1) : ℤ).toNat
              (57425*((6*2-1)+9)/2 : ℤ).toNat) := h2.1
        _ = _ := by rw [
          show (57425*(6*2-1) : ℤ).toNat = 631675 by norm_num,
          show (57425*((6*2-1)+1)/2 : ℤ).toNat = 344550 by norm_num,
          show (57425*((6*2-1)+9)/2 : ℤ).toNat = 574250 by norm_num]
    have hc3 : returns19 57425 3 976225 =
        2*(Nat.choose 976225 516825+Nat.choose 976225 746525) := by
      calc
        _ = 2*(Nat.choose (57425*(6*3-1) : ℤ).toNat
              (57425*((6*3-1)+1)/2 : ℤ).toNat +
            Nat.choose (57425*(6*3-1) : ℤ).toNat
              (57425*((6*3-1)+9)/2 : ℤ).toNat) := h3.1
        _ = _ := by rw [
          show (57425*(6*3-1) : ℤ).toNat = 976225 by norm_num,
          show (57425*((6*3-1)+1)/2 : ℤ).toNat = 516825 by norm_num,
          show (57425*((6*3-1)+9)/2 : ℤ).toNat = 746525 by norm_num]
    rw [hc2,hc3]
    omega
  · change returns33 57425 2 631675 ≠ returns33 57425 3 976225
    have hc2 : returns33 57425 2 631675 = 4*Nat.choose 631675 401975 := by
      calc
        _ = 4*Nat.choose (57425*(6*2-1) : ℤ).toNat
            (57425*((6*2-1)+3)/2 : ℤ).toNat := h2.2
        _ = _ := by rw [
          show (57425*(6*2-1) : ℤ).toNat = 631675 by norm_num,
          show (57425*((6*2-1)+3)/2 : ℤ).toNat = 401975 by norm_num]
    have hc3 : returns33 57425 3 976225 = 4*Nat.choose 976225 574250 := by
      calc
        _ = 4*Nat.choose (57425*(6*3-1) : ℤ).toNat
            (57425*((6*3-1)+3)/2 : ℤ).toNat := h3.2
        _ = _ := by rw [
          show (57425*(6*3-1) : ℤ).toNat = 976225 by norm_num,
          show (57425*((6*3-1)+3)/2 : ℤ).toNat = 574250 by norm_num]
    rw [hc2,hc3]
    omega

noncomputable def centeredCounterSource : Registration centeredCounterArena
    (type_of% original_centered_ceiling_counterexample) where
  actual := centeredCounterActual
  bridge := Iff.rfl
  variation := ⟨centeredCounter_actual_law,
    centeredCounterRejected 0, centeredCounter_rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨centeredCounterRejected i, ?_, rfl, centeredCounter_rejected_law i⟩
      intro j hj
      funext p t
      simp [centeredCounterRejected, realize, hj]
    · intro e
      exact nomatch e
  dependence := centeredCounter_actual_dependence

noncomputable def centeredCounterRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0} (@original_centered_ceiling_counterexample)
      (Realization centeredCounterSignature) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample.original_centered_ceiling_counterexample.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample.centeredCounterSource
  realizationSource := none
  generated := false
  arena := .source ⟨centeredCounterArena⟩
  objectArena := .source ⟨centeredCounterArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source centeredCounterArena ⟨centeredCounterSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize centeredCounterSignature
    (fun i _ t => if i = 0 then (original_return_pair 57425 t.1).1
      else (original_return_pair 57425 t.1).2)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.BajnokBeattyOddWrapCenteredCeilingCounterexample
