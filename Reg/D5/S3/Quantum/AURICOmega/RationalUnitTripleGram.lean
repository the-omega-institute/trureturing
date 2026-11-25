import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalUnitTripleGram

/-! The squared third inner product in the five-coordinate Gram criterion. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalUnitTripleGram

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalUnitTripleGram (rationalFiveCoordinateUnitTriple)
open LeanInformationAudit Matrix

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def actual : Realization signature :=
  realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ c => c ^ 2 + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (a b c : ℚ) (_ : 0 ≤ 1 - a ^ 2) (_ : 0 ≤ 1 - b ^ 2),
    (∃ u v w : Fin 5 → ℚ, u ⬝ᵥ u = 1 ∧ v ⬝ᵥ v = 1 ∧ w ⬝ᵥ w = 1 ∧
      u ⬝ᵥ v = a ∧ u ⬝ᵥ w = b ∧ v ⬝ᵥ w = c) ↔
    (∃ i j k : ℚ, 1 + 2 * a * b * c - a ^ 2 - b ^ 2 - R.readout () () c =
      i ^ 2 + j ^ 2 + k ^ 2)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have original := (rationalFiveCoordinateUnitTriple 1 1 1 (by norm_num) (by norm_num)).mpr
    ⟨0, 0, 0, by norm_num⟩
  obtain ⟨i, j, k, hij⟩ := (h 1 1 1 (by norm_num) (by norm_num)).mp original
  change 1 + 2 * 1 * 1 * 1 - 1 ^ 2 - 1 ^ 2 - ((1 : ℚ) ^ 2 + 1) =
    i ^ 2 + j ^ 2 + k ^ 2 at hij
  norm_num at hij
  nlinarith [sq_nonneg i, sq_nonneg j, sq_nonneg k]

def family : Registration arena (type_of% @rationalFiveCoordinateUnitTriple) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rationalFiveCoordinateUnitTriple, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 0, 1, by change (0 : ℚ) ^ 2 ≠ 1 ^ 2; norm_num⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rationalFiveCoordinateUnitTriple) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalUnitTripleGram.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalUnitTripleGram.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => c ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalUnitTripleGram
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body",
        "arg", "body", "fun", "arg", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalUnitTripleGram
