import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] a

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ),
    (r.readout () () (n + 5) : ℤ) = 15 * r.readout () () (n + 4) -
      270 * r.readout () () (n + 2) + 324 * r.readout () () (n + 1)

private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_distinct : a 1 ≠ a 2 := by
  have h1 := counting_bridge 1 (by omega)
  have h2 := counting_bridge 2 (by omega)
  generalize hx : a 1 = x at h1 ⊢
  generalize hy : a 2 = y at h2 ⊢
  have t1 : dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData.initial
      (_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate.W ⟨1, by decide⟩) = (2304 : ℤ) := by decide +kernel
  have t2 : dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData.initial
      (_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate.W ⟨2, by decide⟩) = (31104 : ℤ) := by decide +kernel
  rw [_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate.powers ⟨1, by decide⟩, t1] at h1
  rw [_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate.powers ⟨2, by decide⟩, t2] at h2
  omega

def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 1, 2, count_distinct⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203980Strip.Recurrence.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Recurrence

namespace Bridge
abbrev signature : Signature := Recurrence.signature
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, 1 ≤ m →
    dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData.initial
      ((_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData.T ^ m).mulVec _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData.terminal) =
        6 * (r.readout () () m : ℤ)
private theorem rejected_at (h : arena.Law rejected) (m : ℕ) (hm : 1 ≤ m) : False := by
  have hb := h m hm
  have ha := counting_bridge m hm
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 1 (by decide)

def family : Registration arena (type_of% @counting_bridge) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 1, 2, Recurrence.count_distinct⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203980Strip.Bridge.auditUnit
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
  readout := some (realize signature (fun _ _ n => a n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bridge
end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980Strip
