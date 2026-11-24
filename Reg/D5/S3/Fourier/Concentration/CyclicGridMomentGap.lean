import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CyclicGridMomentGap

/-! Readout dependence in the pairwise separation and cyclic projection bounds. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicGridMomentGap
open _root_.Reg.Support

noncomputable section

universe u

abbrev phaseSignature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def phaseActual : Realization phaseSignature :=
  realize phaseSignature (fun _ _ x => max x 0) (fun e => nomatch e)

def phaseRejected : Realization phaseSignature :=
  realize phaseSignature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev phaseArena : Arena where
  signature := phaseSignature
  Law V := ∀ {J : Type u} [Fintype J] (z : J → ℂ) (w : J → ℝ)
      (_ : ∀ j, ‖z j‖ = 1) (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j)
      (δ : ℝ) (_ : ∀ j k, 0 < w j → 0 < w k → δ ≤ |(z j * star (z k)).re|),
    let m := ∑ j, (w j : ℂ) * z j
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let c := ‖m‖ ^ 2
    let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
    let s := c * (1 - c)
    let d := V.readout () () (δ - |2 * c - 1|)
    0 < d → c * d ^ 2 ≤ 4 * (1 + 4 / s + c * d ^ 2 / s ^ 2) * D

private theorem phase_rejected_law : ¬ phaseArena.{u}.Law phaseRejected := by
  intro law
  let z (j : ULift.{u} (Fin 2)) : ℂ := if j.down = 0 then 1 else Complex.I
  let w (_ : ULift.{u} (Fin 2)) : ℝ := 1 / 2
  have hsum {A : Type} [AddCommMonoid A] (f : ULift.{u} (Fin 2) → A) :
      ∑ j, f j = f ⟨0⟩ + f ⟨1⟩ := by
    let e : Fin 2 ≃ ULift.{u} (Fin 2) := Equiv.ulift.symm
    rw [← e.sum_comp f, Fin.sum_univ_two]
    rfl
  have hz (j : ULift.{u} (Fin 2)) : ‖z j‖ = 1 := by
    unfold z
    split <;> simp
  have hw : ∑ j, w j = 1 := by rw [hsum]; norm_num [w]
  have hpos (j : ULift.{u} (Fin 2)) : 0 ≤ w j := by norm_num [w]
  have h := law z w hz hw hpos 0 (fun _ _ _ _ => abs_nonneg _)
  have hm : (∑ j, (w j : ℂ) * z j) = (1 + Complex.I) / 2 := by
    rw [hsum]
    norm_num [w, z]
    ring
  have hb : (∑ j, (w j : ℂ) * z j ^ 2) = 0 := by
    rw [hsum]
    norm_num [w, z, Complex.I_sq]
  have hc : ‖(1 + Complex.I) / 2‖ ^ 2 = 1 / 2 := by
    rw [Complex.sq_norm, Complex.normSq_div, Complex.normSq_apply]
    norm_num [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  dsimp only at h
  rw [hm, hb, hc] at h
  norm_num [phaseRejected, realize] at h

private theorem phase_dependence : ObservationalDependence phaseSignature phaseActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change max (0 : ℝ) 0 ≠ max 1 0
  norm_num

def phaseEvidence :
    Registration phaseArena.{u} (type_of% @phase_separation_variance_bound.{u}) where
  actual := phaseActual
  bridge := Iff.rfl
  variation := ⟨@phase_separation_variance_bound.{u}, phaseRejected, phase_rejected_law⟩
  sensitivity :=
    SingleDependentReadout.sensitivity phaseArena.Law phaseActual phaseRejected phase_rejected_law
  dependence := phase_dependence

abbrev gridSignature := SingleDependentReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def gridActual : Realization gridSignature :=
  realize gridSignature (fun _ _ x => x.re) (fun e => nomatch e)

def gridRejected : Realization gridSignature :=
  realize gridSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev gridArena : Arena where
  signature := gridSignature
  Law V := ∀ (q : ℕ) [NeZero q] (_ : ¬ 4 ∣ q) (w : ZMod q → ℝ)
      (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j),
    let δ := Real.sin ((if Even q then (2 : ℝ) else 1) * Real.pi / (2 * q))
    let m := ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod q)
    let b := ZMod.dft (fun j => (w j : ℂ)) (2 : ZMod q)
    let c := ‖m‖ ^ 2
    let projection := V.readout () () (star m ^ 2 * b)
    let D := c / 2 - c ^ 2 + projection / 2
    let s := c * (1 - c)
    let d := max (δ - |2 * c - 1|) 0
    0 < d → c * d ^ 2 ≤ 4 * (1 + 4 / s + c * d ^ 2 / s ^ 2) * D

private theorem grid_rejected_law : ¬ gridArena.Law gridRejected := by
  intro law
  let w (j : ZMod 3) : ℝ := 1 / 8 + if j = 0 then 5 / 8 else 0
  have hw : ∑ j, w j = 1 := by
    simp [w, sum_add_distrib, ZMod.card]
    norm_num
  have hp (j : ZMod 3) : 0 ≤ w j := by
    dsimp [w]
    split <;> norm_num
  have hm : ZMod.dft (fun j => (w j : ℂ)) (1 : ZMod 3) = 5 / 8 := by
    rw [ZMod.dft_apply]
    have hz : ∑ j : ZMod 3, ZMod.stdAddChar (-j) = 0 := by
      simpa only [AddChar.mulShift_apply, neg_one_mul] using
        AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 3
          (by decide : (-1 : ZMod 3) ≠ 0))
    simp only [mul_one, smul_eq_mul, w, Complex.ofReal_add, mul_add, sum_add_distrib, ← sum_mul, hz,
      zero_mul, zero_add]
    simp [apply_ite Complex.ofReal, mul_ite]
  have hc : ‖(5 / 8 : ℂ)‖ ^ 2 = 25 / 64 := by norm_num [norm_div]
  have h := law 3 (by decide) w hw hp
  dsimp only at h
  rw [hm, hc] at h
  norm_num [show ¬Even (3 : ℕ) by decide, gridRejected, realize, max_def] at h

private theorem grid_dependence : ObservationalDependence gridSignature gridActual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change (0 : ℂ).re ≠ (1 : ℂ).re
  norm_num

def gridEvidence : Registration gridArena (type_of% @cyclic_grid_fourier_gap) where
  actual := gridActual
  bridge := Iff.rfl
  variation := ⟨@cyclic_grid_fourier_gap, gridRejected, grid_rejected_law⟩
  sensitivity :=
    SingleDependentReadout.sensitivity gridArena.Law gridActual gridRejected grid_rejected_law
  dependence := grid_dependence

def phaseRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@phase_separation_variance_bound.{u}) (Realization phaseSignature) Unit Unit where
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
  readout := some (realize phaseSignature (fun _ _ x => max x 0) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicGridMomentGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "value", "fn"]
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
  readout := some (realize gridSignature (fun _ _ x => x.re) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicGridMomentGap
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicGridMomentGap
