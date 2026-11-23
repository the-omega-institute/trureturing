import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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
namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
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
    (r.readout () () (n + 14) : ℤ) = 50 * r.readout () () (n + 13) - 715 * r.readout () () (n + 12) + 324 * r.readout () () (n + 11) + 50175 * r.readout () () (n + 10) - 180630 * r.readout () () (n + 9) - 940491 * r.readout () () (n + 8) + 4556250 * r.readout () () (n + 7) + 2329155 * r.readout () () (n + 6) - 27398736 * r.readout () () (n + 5) + 13286025 * r.readout () () (n + 4) + 47829690 * r.readout () () (n + 3) - 43046721 * r.readout () () (n + 2)

private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_distinct : a 2 ≠ a 3 := by
  let t := HardinA229508StripData.T
  let v := HardinA229508StripData.initial
  let e := HardinA229508StripData.terminal
  let table := HardinA229508StripCertificate.W
  have terminal_sum (w : (Fin 15 ⊕ Fin 15) → ℤ) :
      dotProduct w e = ∑ j : Fin 15, (w ∘ Sum.inr) j := by
    simp only [e, HardinA229508StripData.terminal, dotProduct, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, Pi.one_apply, mul_zero, mul_one,
      Finset.sum_const_zero, zero_add, Function.comp_apply]
  have evaluate (i : Fin 21) :
      dotProduct v ((t ^ i.val).mulVec e) = ∑ j : Fin 15, table i j :=
    (Matrix.dotProduct_mulVec _ _ _).trans
      ((congrArg (fun w => dotProduct w e) (forward_eq t v i.val).symm).trans
        ((terminal_sum _).trans
          (congrArg (fun w : Fin 15 → ℤ => ∑ j, w j)
            (HardinA229508StripCertificate.forward_one i))))
  have different : (∑ j : Fin 15, table 1 j) ≠ ∑ j : Fin 15, table 2 j := by
    decide +kernel
  intro equal
  exact different ((evaluate 1).symm.trans
    ((counting_bridge 1).trans
      ((congrArg (fun k : ℕ => (6 : ℤ) * (k : ℤ)) equal).trans
        ((counting_bridge 2).symm.trans (evaluate 2)))))

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
  unitName := `Reg.AHardinA229508Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
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
  Law r := ∀ m : ℕ,
    dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData.initial
      ((_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData.T ^ m).mulVec _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData.terminal) =
        6 * (r.readout () () (m + 1) : ℤ)
private theorem rejected_at (h : arena.Law rejected) (m : ℕ) : False := by
  have hb := h m
  have ha := counting_bridge m
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 1

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
  unitName := `Reg.AHardinA229508Strip.Bridge.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
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
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508Strip
