import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
noncomputable section
set_option backward.isDefEq.respectTransparency false
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
attribute [local irreducible] a
private theorem count_distinct : a 2 ≠ a 3 := by
  have h1 := counting_bridge 1
  have h2 := counting_bridge 2
  generalize hx : a 2 = x at h1 ⊢
  generalize hy : a 3 = y at h2 ⊢
  have t1 : dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData.initial (_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate.W ⟨1, by decide⟩) = (16128 : ℤ) := by decide +kernel
  have t2 : dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData.initial (_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate.W ⟨2, by decide⟩) = (648000 : ℤ) := by decide +kernel
  rw [_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate.powers ⟨1, by decide⟩, t1] at h1
  rw [_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate.powers ⟨2, by decide⟩, t2] at h2
  omega

namespace Recurrence
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ _ n => a n) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, (r.readout () () (n + 14) : ℤ) = 45 * r.readout () () (n + 13) - 675 * r.readout () () (n + 12) + 2565 * r.readout () () (n + 11) + 25272 * r.readout () () (n + 10) - 211410 * r.readout () () (n + 9) + 3805380 * r.readout () () (n + 7) - 8188128 * r.readout () () (n + 6) - 14959080 * r.readout () () (n + 5) + 70858800 * r.readout () () (n + 4) - 85030560 * r.readout () () (n + 3) + 34012224 * r.readout () () (n + 2)
private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
def family : Registration arena (type_of% @result) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, count_distinct⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229682Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
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
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ _ n => a n) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ m : ℕ, dotProduct initial ((T ^ m).mulVec terminal) = 6 * (r.readout () () (m + 1) : ℤ)
private theorem rejected_at (h : arena.Law rejected) (m : ℕ) : False := by
  have hb := h m
  have ha := counting_bridge m
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
def family : Registration arena (type_of% @counting_bridge) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨counting_bridge, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    exact ⟨(), 2, 3, count_distinct⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229682Strip.Bridge.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bridge

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682Strip
