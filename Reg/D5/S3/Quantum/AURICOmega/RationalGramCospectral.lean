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
  Law R :=
    ((∃ P : Matrix (Fin 4) (Fin 4) ℚ, P.det ≠ 0 ∧
        ∀ t : ℚ, pairedEdges t * P = P * triangleBlock t) ∧
    ∀ t : ℚ, (pairedEdges t).charpoly = (triangleBlock t).charpoly ∧
      (pairedEdges t).charpoly =
        (Polynomial.X - Polynomial.C (1 + 4 * t)) * (Polynomial.X - 1) *
          (Polynomial.X - Polynomial.C (1 - 2 * t)) ^ 2) ∧
    ∀ (u v : ℚ), 5 * u ^ 2 + 7 * v ^ 2 = 3 → ∀ n : ℕ,
      let t := (5 * u ^ 2 - 1) / 4
      (RealizableIn (pairedEdges t) n ↔ 7 ≤ R.readout () () n) ∧
      (RealizableIn (triangleBlock t) n ↔ 6 ≤ n)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h₆ : 7 ≤ rejected.readout () () 6 := by decide
  have trueLaw := spectrum_and_thresholds.2 (1 / 2) (1 / 2) (by norm_num) 6
  have badLaw := h.2 (1 / 2) (1 / 2) (by norm_num) 6
  have impossible := trueLaw.1.mp (badLaw.1.mpr h₆)
  omega

def family : Registration arena (type_of% @spectrum_and_thresholds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectrum_and_thresholds, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := fun _ => ⟨(), 6, 7, by
    change (6 : ℕ) ≠ 7
    decide⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@spectrum_and_thresholds) (Realization signature) Unit Unit where
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
      path := #["arg", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private abbrev fiveSevenArena : Arena where
  signature := signature
  Law R := ∀ (u v : ℚ), u ≠ 0 → 5 * u ^ 2 + 4 * v ^ 2 = 9 → ∀ n : ℕ,
    let t := (5 * u ^ 2 / 3 - 1) / 4
    (RealizableIn (pairedEdges t) n ↔ 5 ≤ n) ∧
      (RealizableIn (triangleBlock t) n ↔ 7 ≤ R.readout () () n)

private theorem five_seven_rejected_law : ¬ fiveSevenArena.Law rejected := by
  intro h
  have acceptsSix : 7 ≤ rejected.readout () () 6 := by decide
  have trueLaw := five_seven_on_conic 1 1 (by norm_num) (by norm_num) 6
  have badLaw := h 1 1 (by norm_num) (by norm_num) 6
  have impossible := trueLaw.2.mp (badLaw.2.mpr acceptsSix)
  omega

def fiveSevenFamily : Registration fiveSevenArena (type_of% @five_seven_on_conic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@five_seven_on_conic, rejected, five_seven_rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity
      fiveSevenArena.Law actual rejected five_seven_rejected_law
  dependence := fun _ => ⟨(), 6, 7, by
    change (6 : ℕ) ≠ 7
    decide⟩

def fiveSevenAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@five_seven_on_conic) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.fiveSevenUnit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.fiveSevenFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fiveSevenArena⟩
  objectArena := .source ⟨fiveSevenArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fiveSevenArena ⟨fiveSevenFamily⟩
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
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral
