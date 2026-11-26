import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV.ThreeBlockGram
open _root_.RefinedBMV.FourCopyGap (gapDefect)
open LeanInformationAudit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x < y) (fun anchor => nomatch anchor)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun anchor => nomatch anchor)

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq (1 / 2 : ℝ)
  norm_num [actual, realize] at h

abbrev conditioningArena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) (_hp : 0 < p) (x : Fin 3 → ℝ) (i j : Fin 3)
      (_hi : 0 < x i) (_hj : 0 < x j) (_hij : x i ≠ x j),
    R.readout () () ((g (spectralDefect p x) i j)^2)
      (2 * f (spectralDefect p x) i j * f (spectralDefect p x) j i)

private theorem conditioning_rejected : ¬ conditioningArena.Law rejected := by
  intro h
  exact h 1 (by decide) ![1, 2, 1] 0 1
    (by norm_num) (by norm_num) (by norm_num)

def conditioningFamily : Registration conditioningArena
    (type_of% @spectralDefect_binary_conditioning) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectralDefect_binary_conditioning, rejected, conditioning_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    conditioningArena.Law actual rejected conditioning_rejected
  dependence := dependence

def conditioningRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectralDefect_binary_conditioning) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.ThreeBlockGram.spectralDefect_binary_conditioning.__information_unit
  realizationName := ``conditioningFamily
  realizationSource := none
  generated := false
  arena := .source ⟨conditioningArena⟩
  objectArena := .source ⟨conditioningArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source conditioningArena ⟨conditioningFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev sharpnessArena : Arena where
  signature := signature
  Law R := ∀ {c : ℝ} (_hc : c < 2), ∃ (p : ℕ) (r : ℝ),
    0 < p ∧ 0 < r ∧ r < 1 ∧ R.readout () ()
      (c * gapDefect p r r r 1 * gapDefect p 1 1 1 r) ((gapDefect p r r 1 1)^2)

private theorem sharpness_rejected : ¬ sharpnessArena.Law rejected := by
  intro h
  obtain ⟨p, r, hp, hr, hr₁, impossible⟩ := h (c := 0) (by norm_num)
  exact impossible

def sharpnessFamily : Registration sharpnessArena
    (type_of% @gapDefect_binary_conditioning_sharp) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@gapDefect_binary_conditioning_sharp, rejected, sharpness_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    sharpnessArena.Law actual rejected sharpness_rejected
  dependence := dependence

def sharpnessRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@gapDefect_binary_conditioning_sharp) (Realization signature) Unit Unit where
  unitName := `RefinedBMV.ThreeBlockGram.gapDefect_binary_conditioning_sharp.__information_unit
  realizationName := ``sharpnessFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sharpnessArena⟩
  objectArena := .source ⟨sharpnessArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sharpnessArena ⟨sharpnessFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Analysis.RefinedBMV.BinaryGramConditioning
