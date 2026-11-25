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

private abbrev sevenFiveArena : Arena where
  signature := signature
  Law R := ∀ (u v : ℚ), u ^ 2 + 14 * v ^ 2 = 15 → ∀ n : ℕ,
    let t := (u ^ 2 / 5 - 1) / 4
    (RealizableIn (pairedEdges t) n ↔ 7 ≤ R.readout () () n) ∧
      (RealizableIn (triangleBlock t) n ↔ 5 ≤ n)

private theorem seven_five_rejected_law : ¬ sevenFiveArena.Law rejected := by
  intro h
  have acceptsSix : 7 ≤ rejected.readout () () 6 := by decide
  have trueLaw := seven_five_on_conic 1 1 (by norm_num) 6
  have badLaw := h 1 1 (by norm_num) 6
  have impossible := trueLaw.1.mp (badLaw.1.mpr acceptsSix)
  omega

def sevenFiveFamily : Registration sevenFiveArena (type_of% @seven_five_on_conic) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@seven_five_on_conic, rejected, seven_five_rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity
      sevenFiveArena.Law actual rejected seven_five_rejected_law
  dependence := fun _ => ⟨(), 6, 7, by
    change (6 : ℕ) ≠ 7
    decide⟩

def sevenFiveAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@seven_five_on_conic) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.sevenFiveUnit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.sevenFiveFamily
  realizationSource := none
  generated := false
  arena := .source ⟨sevenFiveArena⟩
  objectArena := .source ⟨sevenFiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sevenFiveArena ⟨sevenFiveFamily⟩
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
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


private abbrev fourCoordinateSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℚ) (fun _ => ℚ)

private def fourCoordinateActual : Realization fourCoordinateSignature :=
  realize fourCoordinateSignature (fun _ _ t => t) (fun e => nomatch e)

private def fourCoordinateRejected : Realization fourCoordinateSignature :=
  realize fourCoordinateSignature (fun _ _ t => t + 1 / 6) (fun e => nomatch e)

private abbrev fourCoordinateArena : Arena where
  signature := fourCoordinateSignature
  Law R := ∀ t : ℚ,
    (RealizableIn (pairedEdges (R.readout () () t)) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2) ∧
    (RealizableIn (triangleBlock t) 4 ↔
      t = 1/2 ∨ ∃ s x y : ℚ, 1 + 4*t = s^2 ∧ 2*(1-2*t) = x^2+y^2)

private theorem four_coordinate_rejected_law : ¬ fourCoordinateArena.Law fourCoordinateRejected := by
  intro h
  have candidate := (h 0).1.mpr (Or.inr ⟨1, 1, 1, by norm_num, by norm_num⟩)
  change RealizableIn (pairedEdges (0 + 1/6)) 4 at candidate
  rw [zero_add] at candidate
  have known := (five_seven_on_conic 1 1 (by norm_num) (by norm_num) 4).1
  norm_num at known
  exact known candidate

def fourCoordinateFamily : Registration fourCoordinateArena (type_of% @four_coordinate_criterion) where
  actual := fourCoordinateActual
  bridge := Iff.rfl
  variation := ⟨@four_coordinate_criterion, fourCoordinateRejected, four_coordinate_rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity fourCoordinateArena.Law
      fourCoordinateActual fourCoordinateRejected four_coordinate_rejected_law
  dependence := fun _ => ⟨(), 0, 1, by
    change (0 : ℚ) ≠ 1
    norm_num⟩

def fourCoordinateAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@four_coordinate_criterion) (Realization fourCoordinateSignature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.fourCoordinateUnit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral.fourCoordinateFamily
  realizationSource := none
  generated := false
  arena := .source ⟨fourCoordinateArena⟩
  objectArena := .source ⟨fourCoordinateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fourCoordinateArena ⟨fourCoordinateFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fourCoordinateSignature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.RationalGramCospectral
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.AURICOmega.RationalGramCospectral
