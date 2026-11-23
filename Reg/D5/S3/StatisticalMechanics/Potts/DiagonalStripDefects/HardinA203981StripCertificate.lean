import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Init.Data.Fin.Lemmas
import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Notation.Pi.Defs

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Counts
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 3 6) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T (boundary x) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => T (boundary x) y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row 3 6) (j : Fin 15),
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 0 ∧ boundary r = j then (1 : ℤ) else 0) = r.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0 : Row 3 6) 0
  have ha := counts (0 : Row 3 6) 0
  change _ = T (boundary (0 : Row 3 6)) 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0 : Row 3 6), 0, 1, ?_⟩
    change T 0 0 ≠ T 0 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981StripCertificate.Counts.auditUnit
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
  readout := some (realize signature (fun _ x y => T (boundary x) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Counts

namespace Initial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ y => initial y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ y => initial y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ j : Fin 15,
    (∑ r : Row 3 6, if boundary r = j then (1 : ℤ) else 0) = r.readout () () j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  have ha := initial_counts 0
  change _ = initial 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @initial_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨initial_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change initial 0 ≠ initial 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@initial_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981StripCertificate.Initial.auditUnit
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
  readout := some (realize signature (fun _ _ y => initial y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Initial

namespace Powers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 21) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => W x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => W x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (i : Fin 21), forward T initial i.val = fun j => r.readout () i j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (forward_table 0) 0
  change _ = W 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @forward_table) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_table, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change W 1 0 ≠ W 1 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_table) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981StripCertificate.Powers.auditUnit
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
  readout := some (realize signature (fun _ x y => W x y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Powers

namespace Polynomial

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Fin 15 → ℤ)

def readout : Realization signature := realize signature
  (fun _ _ n => forward T initial n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n j => forward T initial n j + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () (1 + 6) = ∑ j : Fin 6, coeff j • r.readout () () (1 + j.val)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h 0
  have ha := congrFun finite_certificate 0
  simp only [rejected, realize, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply,
    smul_eq_mul, coeff, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.reduceAdd, add_zero] at hb ha
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change forward T initial 0 ≠ forward T initial 1
    rw [show forward T initial 0 = W 0 from forward_table 0,
      show forward T initial 1 = W 1 from forward_table 1]
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203981StripCertificate.Polynomial.auditUnit
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
  readout := some (realize signature
  (fun _ _ n => forward T initial n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Polynomial

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
