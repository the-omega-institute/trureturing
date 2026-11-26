import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature
  (Σ _ : Matrix (Fin 8) (Fin 8) ℤ, Fin 8) (fun _ => Fin 8) (fun _ => ℤ)
def readout : Realization signature := realize signature
  (fun _ x y => x.1 y x.2) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ x y => x.1 y x.2 + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (d : ℕ) (t : Matrix (Fin 8) (Fin 8) ℤ),
    (∀ i j : Fin 8, (∑ r : Row,
      if bondDefects between (representatives i) r = d ∧ boundary r = j
      then (1 : ℤ) else 0) = t i j) → ∀ (p : Row) (j : Fin 8),
    (∑ r : Row, if bondDefects between p r = d ∧ boundary r = j
      then (1 : ℤ) else 0) = r.readout () ⟨t, j⟩ (boundary p)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have rep : ∀ i : Fin 8, boundary (representatives i) = i := by decide +kernel
  have hr (i j : Fin 8) : (∑ r : Row,
      if bondDefects between (representatives i) r = 0 ∧ boundary r = j
      then (1 : ℤ) else 0) = T i j := by
    simpa only [rep] using counts (representatives i) j
  have hb := h 0 T hr (representatives 0) 0
  have ha := counts (representatives 0) 0
  change _ = T (boundary (representatives 0)) 0 + 1 at hb
  linarith

def family : Registration arena (type_of% @lift_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨lift_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨T, 0⟩, 0, 6, ?_⟩
    change T 0 0 ≠ T 6 0
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@lift_counts) (Realization signature) Type Unit where
  unitName := `Reg.ADiagonalSymmetry.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x y => x.1 y x.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
    definition := none
    coordinates := #[1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.DiagonalSymmetry
