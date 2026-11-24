import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Fourier.Concentration.CyclicMomentStability

/-! Dependence of the phase error on the imaginary height of the two comparison points. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicMomentStability

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicMomentStability
open _root_.Reg.Support

noncomputable section

universe u

abbrev signature := SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e)

def rejected : Realization signature := realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {J : Type u} [Fintype J]
      (z : J → ℂ) (w : J → ℝ) (_ : ∀ j, ‖z j‖ = 1)
      (_ : ∑ j, w j = 1) (_ : ∀ j, 0 ≤ w j),
    let m := ∑ j, (w j : ℂ) * z j
    let b := ∑ j, (w j : ℂ) * z j ^ 2
    let c := ‖m‖ ^ 2
    let X (j : J) := star m * z j
    let t := V.readout () () (c * (1 - c))
    let η (j : J) : ℝ := if 0 ≤ (X j).im then 1 else -1
    let D := c / 2 - c ^ 2 + (star m ^ 2 * b).re / 2
    0 < c → c < 1 →
      (∑ j, w j * ‖X j - (c : ℂ) - (↑(η j * t) : ℂ) * Complex.I‖ ^ 2) ≤
        (1 + 4 / t ^ 2) * D ∧ (∑ j, w j * η j) ^ 2 ≤ 4 * D / t ^ 4

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let z (j : ULift.{u} (Fin 2)) : ℂ := if j.down = 0 then 1 else Complex.I
  let w (_ : ULift.{u} (Fin 2)) : ℝ := 1 / 2
  have hsum {A : Type} [AddCommMonoid A] (f : ULift.{u} (Fin 2) → A) :
      ∑ j, f j = f ⟨0⟩ + f ⟨1⟩ := by
    let e : Fin 2 ≃ ULift.{u} (Fin 2) := Equiv.ulift.symm
    calc
      _ = ∑ j : Fin 2, f (e j) := (e.sum_comp f).symm
      _ = _ := Fin.sum_univ_two (fun j => f (e j))
  have hz (j : ULift.{u} (Fin 2)) : ‖z j‖ = 1 := by unfold z; split <;> simp
  have hw : ∑ j, w j = 1 := by rw [hsum]; norm_num [w]
  have hpos (j : ULift.{u} (Fin 2)) : 0 ≤ w j := by norm_num [w]
  have h := law z w hz hw hpos
  dsimp only at h
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
  rw [hm, hb, hc] at h
  have hbad := (h (by norm_num) (by norm_num)).1
  rw [hsum] at hbad
  simp only [rejected, realize, zero_mul, Complex.ofReal_zero, sub_zero,
    mul_zero] at hbad
  simp only [w, z, ite_eq_left rfl, star_div₀, star_add,
    star_one, Complex.star_def, Complex.conj_I, map_ofNat, Complex.sq_norm] at hbad
  norm_num [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im] at hbad

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  refine ⟨(), 0, 1, ?_⟩
  change Real.sqrt 0 ≠ Real.sqrt 1
  norm_num

def evidence : Registration arena.{u} (type_of% @first_two_moment_stability.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@first_two_moment_stability.{u}, rejected, rejected_law⟩
  sensitivity := SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@first_two_moment_stability.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.CyclicMomentStability.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicMomentStability.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => Real.sqrt x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicMomentStability
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "value", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicMomentStability
