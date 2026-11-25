import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.AURICOmega.RationalGramCospectral

/-! The seven-coordinate minimum in the conic family's first realizability threshold. -/

namespace Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.AURICOmega.RationalGramCospectral
open LeanInformationAudit

set_option autoImplicit false

noncomputable section

private abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

private def actual : Realization signature :=
  realize signature (fun _ _ n => n) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ n => n + 1) (fun e => nomatch e)

private abbrev arena : Arena where
  signature := signature
  Law R := ∀ (u v : ℚ), 5 * u ^ 2 + 7 * v ^ 2 = 3 → ∀ n : ℕ,
    let t := (5 * u ^ 2 - 1) / 4
    ((pairedEdges t).charpoly = (triangleBlock t).charpoly ∧
      (pairedEdges t).charpoly =
        (Polynomial.X - Polynomial.C (1 + 4 * t)) * (Polynomial.X - 1) *
          (Polynomial.X - Polynomial.C (1 - 2 * t)) ^ 2) ∧
      (RealizableIn (pairedEdges t) n ↔ 7 ≤ R.readout () () n) ∧
      (RealizableIn (triangleBlock t) n ↔ 6 ≤ n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₆ : 7 ≤ rejected.readout () () 6 := by decide
  have trueLaw := thresholds_on_conic (1 / 2) (1 / 2) (by norm_num) 6
  have badLaw := h (1 / 2) (1 / 2) (by norm_num) 6
  have impossible := trueLaw.2.1.mp (badLaw.2.1.mpr h₆)
  omega

def family : Registration arena (type_of% @thresholds_on_conic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@thresholds_on_conic, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 6, 7, by
    change (6 : ℕ) ≠ 7
    decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@thresholds_on_conic) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalGramCospectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body",
        "arg", "fn", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral
