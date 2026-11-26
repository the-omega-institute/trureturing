import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203980StripData (Row boundary between)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (bondDefects)

namespace Cost
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Row (fun _ => Fin 8) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => costTwo (boundary x) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ x y => costTwo (boundary x) y) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row) (j : Fin 8),
    (∑ r : Row, if bondDefects between p r = 2 ∧ boundary r = j then (1 : ℤ) else 0) = r.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0, 0, 0] 0
  have ha := two_counts ![0, 0, 0, 0, 0] 0
  change _ = costTwo 0 0 at ha
  change _ = costTwo 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @two_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨two_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 0, 0, 0, 0], 0, 1, ?_⟩
    change costTwo 0 0 ≠ costTwo 0 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@two_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229682StripCertificate.Cost.auditUnit
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
  readout := some (realize signature (fun _ x y => costTwo (boundary x) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
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

end Cost

namespace Transitions
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row, Fin 3) (fun _ => Fin 24) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T (cl x.1 x.2.val) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ x y => T (cl x.1 x.2.val) y) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row) (d : Fin 3) (j : Fin 24),
    (∑ r : Row, if bondDefects between p r ≤ d.val ∧ cl r (d.val - bondDefects between p r) = j
      then (1 : ℤ) else 0) = r.readout () ⟨p, d⟩ j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0, 0, 0] 2 0
  have ha := transition_counts ![0, 0, 0, 0, 0] 2 0
  change _ = T 0 0 at ha
  change _ = T 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨![0, 0, 0, 0, 0], 2⟩, 0, 6, ?_⟩
    change T 0 0 ≠ T 0 6
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229682StripCertificate.Transitions.auditUnit
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
  readout := some (realize signature (fun _ x y => T (cl x.1 x.2.val) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Transitions

namespace Powers
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Fin 14) (fun _ => Fin 24) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => W x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ x y => W x y) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ i : Fin 14, (T ^ i.val).mulVec terminal = fun j => r.readout () i j
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
  unitName := `Reg.AHardinA229682StripCertificate.Powers.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
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
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Fin 24 → ℤ)
def readout : Realization signature := realize signature (fun _ _ x => (T ^ x).mulVec terminal) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ x j => (T ^ x).mulVec terminal j + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () 13 = ∑ k : Fin 12,
    (![34012224, -85030560, 70858800, -14959080, -8188128, 3805380, 0, -211410, 25272, 2565, -675, 45] k : ℤ) • r.readout () () (1 + k.val)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h 0
  have ha := congrFun finite_certificate 0
  simp only [rejected, realize, Finset.sum_apply, Pi.smul_apply, Pi.add_apply, Pi.zero_apply,
    smul_eq_mul, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_one, Nat.reduceAdd] at hb ha
  change (T ^ 13).mulVec terminal 0 + 1 = (34012224) * ((T ^ 1).mulVec terminal 0 + 1) + ((-85030560) * ((T ^ 2).mulVec terminal 0 + 1) + ((70858800) * ((T ^ 3).mulVec terminal 0 + 1) + ((-14959080) * ((T ^ 4).mulVec terminal 0 + 1) + ((-8188128) * ((T ^ 5).mulVec terminal 0 + 1) + ((3805380) * ((T ^ 6).mulVec terminal 0 + 1) + ((0) * ((T ^ 7).mulVec terminal 0 + 1) + ((-211410) * ((T ^ 8).mulVec terminal 0 + 1) + ((25272) * ((T ^ 9).mulVec terminal 0 + 1) + ((2565) * ((T ^ 10).mulVec terminal 0 + 1) + ((-675) * ((T ^ 11).mulVec terminal 0 + 1) + ((45) * ((T ^ 12).mulVec terminal 0 + 1) + (0)))))))))))) at hb
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
    have hz : (T ^ 0).mulVec terminal = W 0 := powers ⟨0, by decide⟩
    have ho : (T ^ 1).mulVec terminal = W 1 := powers ⟨1, by decide⟩
    rw [hz, ho]
    intro he
    have hh := congrFun he 0
    change (0 : ℤ) = 56 at hh
    omega
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229682StripCertificate.Polynomial.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
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
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229682StripCertificate
