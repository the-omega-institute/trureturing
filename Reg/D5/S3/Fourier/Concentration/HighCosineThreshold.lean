import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.Fourier.Concentration.HighCosineThreshold

/-! Dependence of feasible descent below the high-threshold interval on squared mass. -/

namespace Reg.D5.S3.Fourier.Concentration.HighCosineThreshold

open Finset
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.HighCosineThreshold
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ x => x ^ 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ {q : ℕ} (_ : 4 ≤ q),
    let c := cyclicReadout q
    let u := cyclicUpper q
    let l := cyclicLower q
    let square := V.readout () ()
    tailMoment u l < criticalThreshold c u l ∧ criticalThreshold c u l < 1 ∧
      (∀ a, criticalThreshold c u l ≤ a → a ≤ 1 → IsCertified c u l a) ∧
      ∀ a, tailMoment u l ≤ a → a < criticalThreshold c u l →
        let v := weights c u l ((1 - a) / (1 - tailMoment u l))
        ∃ w : Fin q → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧
          a < (∑ i, w i * c i) ∧ a < (∑ i, w i * (2 * (c i) ^ 2 - 1)) ∧
          (∑ i, square (w i)) < (∑ i, square (v i))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨hlt, _, _, hdescent⟩ := law (q := 4) (by decide)
  obtain ⟨a, hba, hac⟩ := exists_between hlt
  obtain ⟨w, _, _, _, _, hw⟩ := hdescent a hba.le hac
  simp [rejected, realize] at hw

def evidence : Registration arena (type_of% @cyclic_high_threshold_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_high_threshold_certificate, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℝ) ^ 2 ≠ (1 : ℝ) ^ 2
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_high_threshold_certificate) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.HighCosineThreshold.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.HighCosineThreshold.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.HighCosineThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Fold

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ q n => Real.cos (2 * Real.pi * (n : ℝ) / q)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V :=
    let sample := fun (q n : ℕ) => V.readout () () q n
    ∀ {q : ℕ} (k : Fin q), k.val ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ n ≤ q / 2 ∧
      cyclicReadout q k = sample q n ∧ (n = k.val ∨ n = q - k.val)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  obtain ⟨n, _, _, he, _⟩ := law (⟨1, by decide⟩ : Fin 4) (by decide)
  change Real.cos (2 * Real.pi * (↑(1 : ℕ) : ℝ) / (↑(4 : ℕ) : ℝ)) = 2 at he
  norm_num only [Nat.cast_ofNat] at he
  linarith only [he, Real.cos_le_one (2 * Real.pi * (1 : ℝ) / 4)]

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 4, 8, ?_⟩
  intro he
  have h := congrFun he 2
  change Real.cos (2 * Real.pi * (↑(2 : ℕ) : ℝ) / (↑(4 : ℕ) : ℝ)) =
    Real.cos (2 * Real.pi * (↑(2 : ℕ) : ℝ) / (↑(8 : ℕ) : ℝ)) at h
  norm_num only [Nat.cast_ofNat] at h
  rw [show 2 * Real.pi * 2 / 4 = Real.pi by ring,
    show 2 * Real.pi * 2 / 8 = Real.pi / 2 by ring, Real.cos_pi, Real.cos_pi_div_two] at h
  norm_num at h

def evidence : Registration arena (type_of% @cyclic_fold) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cyclic_fold, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
      (@cyclic_fold) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.Concentration.HighCosineThreshold.Fold.unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.HighCosineThreshold.Fold.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.HighCosineThreshold
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Fold

end

end Reg.D5.S3.Fourier.Concentration.HighCosineThreshold
