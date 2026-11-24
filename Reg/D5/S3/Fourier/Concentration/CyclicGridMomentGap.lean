import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CyclicGridMomentGap
import Mathlib.Tactic.FinCases

/-! Dependence of the first-moment deficit on the separation of the available phases. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicGridMomentGap
open _root_.Reg.Support

noncomputable section

universe u

abbrev phaseSignature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ _ x => x ^ 2 / 684) (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev phaseArena : Arena where
  signature := phaseSignature
  Law V := ∀ {J : Type u} [Fintype J] (z : J → ℂ) (w : J → ℝ)
      (_ : ∀ j, ‖z j‖ = 1) (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j)
      {δ : ℝ} (_ : 0 < δ)
      (_ : ∀ j k, 0 < w j → 0 < w k → δ ≤ |(z j * star (z k)).re|),
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let deficit := V.readout () () δ
    ‖b‖ ≤ δ / 3 → ‖∑ j, (w j : ℂ) * z j‖ ^ 2 ≤ (1 + ‖b‖) / 2 - deficit

private def triangle (j : Fin 3) : ℂ :=
  if j = 0 then 1 else ⟨-1 / 2, if j = 1 then Real.sqrt 3 / 2 else -Real.sqrt 3 / 2⟩

private theorem triangle_norm (j : Fin 3) : ‖triangle j‖ = 1 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsq : ‖triangle j‖ ^ 2 = 1 := by
    fin_cases j <;> norm_num [triangle, Complex.sq_norm, Complex.normSq_apply] <;> nlinarith
  nlinarith [norm_nonneg (triangle j)]

private theorem triangle_separation (j k : Fin 3) :
    (1 / 2 : ℝ) ≤ |(triangle j * star (triangle k)).re| := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  fin_cases j <;> fin_cases k <;>
    simp only [triangle, Fin.isValue, Fin.zero_eta, reduceCtorEq, ite_true, ite_false,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im] <;>
    first | norm_num | apply le_abs_self.trans' <;> nlinarith
  all_goals
    rw [le_abs]
    first | left; nlinarith | right; nlinarith

private theorem phase_rejected_law : ¬ phaseArena.{u}.Law phaseRejected := by
  intro law
  let z (j : ULift.{u} (Fin 3)) := triangle j.down
  let w (_ : ULift.{u} (Fin 3)) : ℝ := 1 / 3
  have hsum {A : Type} [AddCommMonoid A] (f : ULift.{u} (Fin 3) → A) :
      ∑ j, f j = f ⟨0⟩ + f ⟨1⟩ + f ⟨2⟩ := by
    let e : Fin 3 ≃ ULift.{u} (Fin 3) := Equiv.ulift.symm
    rw [← e.sum_comp f, Fin.sum_univ_three]
    rfl
  have hmass : ∑ j, w j = 1 := by rw [hsum]; norm_num [w]
  have hpos (j : ULift.{u} (Fin 3)) : 0 ≤ w j := by norm_num [w]
  have hb : ∑ j, (w j : ℂ) * z j ^ 2 = 0 := by
    have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    rw [hsum]
    apply Complex.ext <;>
      norm_num [z, w, triangle, pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re,
        Complex.add_im, Complex.div_re, Complex.div_im] <;> nlinarith
  have h := law z w (fun j => triangle_norm j.down) hmass hpos
    (δ := 1 / 2) (by norm_num) (fun j k _ _ => triangle_separation j.down k.down)
  dsimp only at h
  rw [hb, norm_zero] at h
  have impossible := h (by norm_num)
  change _ ≤ (1 + 0) / 2 - 1 at impossible
  nlinarith [sq_nonneg ‖∑ j, (w j : ℂ) * z j‖]

private theorem phase_dependence : ObservationalDependence phaseSignature phaseActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℝ) ^ 2 / 684 ≠ 1 ^ 2 / 684
  norm_num

def phaseEvidence : Registration phaseArena.{u} (type_of% @first_moment_gap_of_small_second.{u}) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨@first_moment_gap_of_small_second.{u}, phaseRejected, phase_rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity phaseArena.Law phaseActual phaseRejected phase_rejected_law
  dependence := phase_dependence

abbrev gridSignature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def gridActual : Realization gridSignature :=
  realize gridSignature (fun _ _ x => Real.sin x) (fun e => nomatch e)

def gridRejected : Realization gridSignature :=
  realize gridSignature (fun _ _ _ => 32) (fun e => nomatch e)

abbrev gridArena : Arena where
  signature := gridSignature
  Law V := ∀ (q : ℕ) [NeZero q] (_ : ¬ 4 ∣ q) (w : ZMod q → ℝ)
      (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j),
    let δ := V.readout () () ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
    let b := ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q)
    ‖b‖ ≤ δ / 3 →
      ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)‖ ^ 2 ≤ (1 + ‖b‖) / 2 - δ ^ 2 / 684

private theorem grid_rejected_law : ¬ gridArena.Law gridRejected := by
  intro law
  let w (_ : ZMod 3) : ℝ := 1 / 3
  have hb : ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod 3) = 0 := by
    rw [ZMod.dft_apply]
    have harg (j : ZMod 3) : -(j * 2) = (-2) * j := by ring
    simp_rw [w, smul_eq_mul, harg, ← sum_mul]
    have hz : ∑ i : ZMod 3, ZMod.stdAddChar ((-2 : ZMod 3) * i) = 0 := by
      simpa only [AddChar.mulShift_apply] using
        AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 3
          (by decide : (-2 : ZMod 3) ≠ 0))
    rw [hz, zero_mul]
  have h := law 3 (by decide) w (by simp [w, ZMod.card]) (fun _ => by norm_num [w])
  dsimp only at h
  rw [hb, norm_zero] at h
  have impossible := h (by norm_num [gridRejected, realize])
  change _ ≤ (1 + 0) / 2 - (32 : ℝ) ^ 2 / 684 at impossible
  nlinarith [sq_nonneg ‖ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 3)‖]

private theorem grid_dependence : ObservationalDependence gridSignature gridActual := by
  intro i
  cases i
  refine ⟨(), 0, Real.pi / 2, ?_⟩
  change Real.sin 0 ≠ Real.sin (Real.pi / 2)
  norm_num

def gridEvidence : Registration gridArena (type_of% @cyclic_grid_fourier_gap) where
  actual := gridActual
  bridge := Iff.rfl
  variation := ⟨@cyclic_grid_fourier_gap, gridRejected, grid_rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity gridArena.Law gridActual gridRejected grid_rejected_law
  dependence := grid_dependence

def phaseRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@first_moment_gap_of_small_second.{u}) (Realization phaseSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap.phaseUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap.phaseEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨phaseArena.{u}⟩
  objectArena := .source ⟨phaseArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source phaseArena.{u} ⟨phaseEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize phaseSignature (fun _ _ x => x ^ 2 / 684) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicGridMomentGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def gridRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclic_grid_fourier_gap) (Realization gridSignature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap.gridUnit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap.gridEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨gridArena⟩
  objectArena := .source ⟨gridArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source gridArena ⟨gridEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize gridSignature (fun _ _ x => Real.sin x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicGridMomentGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap
