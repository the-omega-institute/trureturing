import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Init.Data.Int.Basic
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder

/-! Readout registrations for exact defective-strip counts and finite transfer data. -/
namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (forward_eq)
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
    (r.readout () () (n + 7) : ℤ) = 25 * r.readout () () (n + 6) - 45 * r.readout () () (n + 5) - 963 * r.readout () () (n + 4) + 2025 * r.readout () () (n + 3) + 3645 * r.readout () () (n + 2) - 6561 * r.readout () () (n + 1)

private theorem rejected_at (h : arena.Law rejected) (n : ℕ) : False := by
  have hb := h n
  have ha := result n
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith
private theorem rejected_law : ¬ arena.Law rejected := fun h => rejected_at h 0
private theorem count_distinct : a 1 ≠ a 2 := by
  let t := HardinA203981StripData.T
  let v := HardinA203981StripData.initial
  let e : Fin 15 → ℤ := 1
  have evaluate (i : Fin 21) :
      dotProduct v ((t ^ i.val).mulVec e) =
        dotProduct (HardinA203981StripCertificate.W i) e :=
    (Matrix.dotProduct_mulVec _ _ _).trans
      (congrArg (fun w => dotProduct w e)
        ((forward_eq t v i.val).symm.trans (HardinA203981StripCertificate.forward_table i)))
  have different : dotProduct (HardinA203981StripCertificate.W 1) e ≠
      dotProduct (HardinA203981StripCertificate.W 2) e := by
    decide +kernel
  intro equal
  exact different ((evaluate 1).symm.trans
    ((show dotProduct v ((t ^ 1).mulVec e) = 6 * (a 1 : ℤ) from by
      simpa only [Nat.one_ne_zero, if_false, add_zero] using counting_bridge 1).trans
      ((congrArg (fun k : ℕ => (6 : ℤ) * (k : ℤ)) equal).trans
        ((show dotProduct v ((t ^ 2).mulVec e) = 6 * (a 2 : ℤ) from by
          simpa only [show (2 : ℕ) ≠ 0 by decide, if_false, add_zero] using counting_bridge 2).symm.trans (evaluate 2)))))

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
  unitName := `Reg.AHardinA203981Strip.Recurrence.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
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
    dotProduct _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData.initial
      ((_root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData.T ^ m).mulVec (1 : Fin 15 → ℤ)) +
        (if m = 0 then 3 else 0) = 6 * (r.readout () () m : ℤ)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 1
  have ha := counting_bridge 1
  simp only [rejected, realize, Nat.cast_add, Nat.cast_one] at hb
  linarith

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
  unitName := `Reg.AHardinA203981Strip.Bridge.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
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
namespace Scale

open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (defects literalCount)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

attribute [local irreducible] literalCount

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => ℕ) (fun _ => ℕ)

def readout : Realization signature := realize signature
  (fun _ d m => literalCount (q := 3) ∅ (betw 6) d (m + 1)) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ d m => literalCount (q := 3) ∅ (betw 6) d (m + 1) + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (m d : ℕ),
    r.readout () d m + (if d = m * 10 then 3 else 0) =
      6 * (Finset.univ.filter fun f : Fin (m + 1) × Fin 6 → Fin 3 =>
        defects ∅ (betw 6) (List.ofFn fun i j => f (i, j)) = d ∧
        (@Canonical (Fin (m + 1) × Fin 6)
          (LinearOrder.lift' finProdFinEquiv finProdFinEquiv.injective).toLT 3 f)).card

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hx := h 1 0
  change literalCount (q := 3) ∅ (betw 6) 0 (1 + 1) + 1 +
    (if (0 : ℕ) = 1 * 10 then 3 else 0) = _ at hx
  have ha := scale_count 1 0
  omega

private theorem literal_ne_of_count_ne (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (different : a m ≠ a n) :
    literalCount (q := 3) ∅ (betw 6) 0 (m + 1) ≠
      literalCount (q := 3) ∅ (betw 6) 0 (n + 1) := by
  have scale (k : ℕ) (hk : 1 ≤ k) :
      literalCount (q := 3) ∅ (betw 6) 0 (k + 1) = 6 * a k := by
    unfold a
    simpa only [if_neg (show (0 : ℕ) ≠ k * 10 by omega), add_zero] using scale_count k 0
  intro equal
  exact different (Nat.eq_of_mul_eq_mul_left (by decide)
    ((scale m hm).symm.trans (equal.trans (scale n hn))))

def family : Registration arena (type_of% @scale_count) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨scale_count, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    exact ⟨0, 1, 2, literal_ne_of_count_ne 1 2 le_rfl (by decide)
      Recurrence.count_distinct⟩

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0}
    (@scale_count) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981Strip.Scale.auditUnit
  realizationName := ``family
  realizationSource := none
  generated := false
  arena := Contract.ArenaRef.source.{0, 0, 0, 0, 0, 0, 0, 0, 0} ⟨arena⟩
  objectArena := Contract.ArenaRef.source.{0, 0, 0, 0, 0, 0, 0, 0, 0} ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := Contract.Implementation.source.{0, 0, 0, 0, 0, 0, 0, 0, 0} arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
  (fun _ d m => literalCount (q := 3) ∅ (betw 6) d (m + 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Scale

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981Strip
