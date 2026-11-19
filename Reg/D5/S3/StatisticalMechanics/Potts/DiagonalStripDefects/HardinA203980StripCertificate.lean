import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Counts
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 8) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T (boundary x) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => (fun _ x y => T (boundary x) y) () x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row) (j : Fin 8),
    (∑ r : Row, if bondDefects between p r = 0 ∧ boundary r = j then (1 : ℤ) else 0) = r.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0, 0, 0] 0
  have ha := counts ![0, 0, 0, 0, 0] 0
  change _ = T (boundary ![0, 0, 0, 0, 0]) 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 0, 0, 0, 0], 0, 6, ?_⟩
    change T 0 0 ≠ T 0 6
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203980StripCertificate.Counts.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 8) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ _ y => initial y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => (fun _ _ y => initial y) () x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ j : Fin 8,
    (∑ r : Row, if boundary r = j then (1 : ℤ) else 0) = r.readout () () j
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
  unitName := `Reg.AHardinA203980StripCertificate.Initial.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 14) (fun _ => Fin 8) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => W x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => (fun _ x y => W x y) () x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (i : Fin 14), (T ^ i.val).mulVec terminal = fun j => r.readout () i j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (powers 0) 0
  change _ = W 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @powers) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨powers, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change W 1 0 ≠ W 1 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203980StripCertificate.Powers.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Fin 8 → ℤ)
def readout : Realization signature := realize signature
  (fun _ _ x => (T ^ x).mulVec terminal) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ x j => (T ^ x).mulVec terminal j + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () 5 = ∑ k : Fin 4,
    (![324, -270, 0, 15] k : ℤ) • r.readout () () (1 + k.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h 0
  have ha := congrFun finite_certificate 0
  simp only [rejected, realize, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply, smul_eq_mul,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.reduceAdd] at hb ha
  change (T ^ 5).mulVec terminal 0 + 1 =
    324 * ((T ^ 1).mulVec terminal 0 + 1) +
    (-270 * ((T ^ 2).mulVec terminal 0 + 1) +
    (0 * ((T ^ 3).mulVec terminal 0 + 1) +
    (15 * ((T ^ 4).mulVec terminal 0 + 1) + 0))) at hb
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
    change (T ^ 0).mulVec terminal ≠ (T ^ 1).mulVec terminal
    have hzero : (T ^ 0).mulVec terminal = W 0 := powers ⟨0, by decide⟩
    have hone : (T ^ 1).mulVec terminal = W 1 := powers ⟨1, by decide⟩
    rw [hzero, hone]
    intro he
    have hh := congrFun he 0
    norm_num [W] at hh
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA203980StripCertificate.Polynomial.auditUnit
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
  readout := some (realize signature (fun _ _ x => (T ^ x).mulVec terminal) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Polynomial

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripCertificate
