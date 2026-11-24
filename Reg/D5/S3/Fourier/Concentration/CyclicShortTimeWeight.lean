import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Concentration.CyclicShortTimeWeight
import Reg.Support.UniverseSingleReadout

/-! Dependence of the deficit estimate on the signed real Fourier values. -/

namespace Reg.D5.S3.Fourier.Concentration.CyclicShortTimeWeight

open Finset
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.Concentration.CyclicShortTimeWeight
open _root_.Reg.Support

noncomputable section

abbrev signature := UniverseSingleReadout.signature Unit (fun _ => ℂ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z.re) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ (q : ℕ) [NeZero q] (F : ZMod q → ℝ)
    (_ : ∀ r, 0 ≤ F r) (a : ℝ) (R J : Finset ℤ)
    (_ : Set.InjOn (fun r : ℤ => (r : ZMod q)) (R : Set ℤ))
    (_ : ∀ r ∈ R, a ≤ F (r : ZMod q))
    (_ : ∀ r ∈ R, ∀ k ∈ J, 2 * |(r : ℝ) * (k : ℝ)| ≤ (q : ℝ)),
    let realPart := V.readout () ()
    (∑ k ∈ J, realPart (ZMod.dft (fun x => (F x : ℂ)) (k : ZMod q))) +
      (8 * a / (q : ℝ) ^ 2) * (∑ r ∈ R, (r : ℝ) ^ 2) * (∑ k ∈ J, (k : ℝ) ^ 2) ≤
        (J.card : ℝ) * ∑ x, F x

private theorem rejected_law : ¬ arena.Law rejected := by
  intro ha
  have h0 := ha 1 (fun _ => 0) (by simp) 0 ∅ {0}
    (by simp [Set.InjOn]) (by simp) (by simp)
  norm_num [rejected, realize] at h0

def family : Registration arena (type_of% @low_fourier_weight_deficit) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@low_fourier_weight_deficit, rejected, rejected_law⟩
  sensitivity := UniverseSingleReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (0 : ℂ).re ≠ (1 : ℂ).re
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@low_fourier_weight_deficit) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Fourier.Concentration.CyclicShortTimeWeight.low_fourier_weight_deficit.__information_unit
  realizationName := `Reg.D5.S3.Fourier.Concentration.CyclicShortTimeWeight.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Concentration.CyclicShortTimeWeight
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.Concentration.CyclicShortTimeWeight
