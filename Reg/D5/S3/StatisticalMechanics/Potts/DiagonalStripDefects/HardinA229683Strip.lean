import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Init.Core
import Init.Data.Int.Basic
import Init.Data.Sum.Basic
import Init.Prelude
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (forward_eq)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects
open LeanInformationAudit
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] a
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false

namespace Recurrence
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def readout : Realization signature := realize signature (fun _ _ n => a n) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (n : ℕ),
    (r.readout () () (n + 21) : ℤ) = 75 * r.readout () () (n + 20) - 2010 * r.readout () () (n + 19) + 19486 * r.readout () () (n + 18) + 60075 * r.readout () () (n + 17) - 2206575 * r.readout () () (n + 16) + 7404210 * r.readout () () (n + 15) + 70536825 * r.readout () () (n + 14) - 435322350 * r.readout () () (n + 13) - 601275555 * r.readout () () (n + 12) + 8082823950 * r.readout () () (n + 11) - 6257717775 * r.readout () () (n + 10) - 54520532190 * r.readout () () (n + 9) + 92909172825 * r.readout () () (n + 8) + 132368667075 * r.readout () () (n + 7) - 366499782594 * r.readout () () (n + 6) + 470715894135 * r.readout () () (n + 4) - 282429536481 * r.readout () () (n + 3)

private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_distinct : a 2 ≠ a 3 := by
  let t := HardinA229683StripData.T
  let v := HardinA229683StripData.initial
  let e := HardinA229683StripData.terminal
  let table := HardinA229683StripCertificate.W
  have terminal_sum (w : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) → ℤ) :
      dotProduct w e = ∑ j : Fin 15, (w ∘ Sum.inr) j := by
    simp only [e, HardinA229683StripData.terminal, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.one_apply, mul_zero, mul_one,
      Finset.sum_const_zero, zero_add, Function.comp_apply]
  have evaluate (i : Fin 21) :
      dotProduct v ((t ^ i.val).mulVec e) = ∑ j : Fin 15, table i j :=
    (Matrix.dotProduct_mulVec _ _ _).trans
      ((congrArg (fun w => dotProduct w e) (forward_eq t v i.val).symm).trans
        ((terminal_sum _).trans
          (congrArg (fun w : Fin 15 → ℤ => ∑ j, w j)
            (HardinA229683StripCertificate.forward_two i))))
  have different : (∑ j : Fin 15, table 1 j) ≠ ∑ j : Fin 15, table 2 j := by
    decide +kernel
  intro equal
  exact different ((evaluate 1).symm.trans
    ((counting_bridge 1 le_rfl).trans
      ((congrArg (fun k : ℕ => (6 : ℤ) * (k : ℤ)) equal).trans
        ((counting_bridge 2 (by decide)).symm.trans (evaluate 2)))))

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
  unitName := `Reg.AHardinA229683Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
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
    dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData.initial
      ((_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData.T ^ m).mulVec _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData.terminal) =
        6 * (r.readout () () (m + 1) : ℤ)
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
    exact ⟨(), 2, 3, Recurrence.count_distinct⟩
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counting_bridge) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683Strip.Bridge.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
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
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683Strip
