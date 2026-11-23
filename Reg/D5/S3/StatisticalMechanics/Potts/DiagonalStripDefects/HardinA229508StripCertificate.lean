import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData
import D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer
import D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Init.Core
import Init.Data.Int.Order
import Init.Prelude
import Init.Tactics
import Mathlib.Order.Defs.PartialOrder

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate

open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA203981StripData (boundary)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.DefectTransfer (Row bondDefects forward)
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefects.HardinA229637RowColumn (betw)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false

namespace Counts
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Row 3 6) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => costOne (boundary x) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => costOne (boundary x) y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row 3 6) (j : Fin 15),
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 1 ∧ boundary r = j then (1 : ℤ) else 0) = r.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0 : Row 3 6) 0
  have ha := one_counts (0 : Row 3 6) 0
  change _ = costOne (boundary (0 : Row 3 6)) 0 + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @one_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨one_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0 : Row 3 6), 0, 3, ?_⟩
    change costOne 0 0 ≠ costOne 0 3
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@one_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229508StripCertificate.Counts.auditUnit
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
  readout := some (realize signature (fun _ x y => costOne (boundary x) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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

namespace Transitions
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row 3 6, Fin 2) (fun _ => (Fin 15 ⊕ Fin 15)) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T (cl x.1 x.2.val) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ x y => T (cl x.1 x.2.val) y) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row 3 6) (d : Fin 2) (j : (Fin 15 ⊕ Fin 15)),
    (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ d.val ∧ cl r (d.val - bondDefects (betw 6) p r) = j
      then (1 : ℤ) else 0) = r.readout () ⟨p, d⟩ j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (0 : Row 3 6) 1 (Sum.inl 0)
  have ha := transition_counts (0 : Row 3 6) 1 (Sum.inl 0)
  change _ = T (Sum.inl 0) (Sum.inl 0) at ha
  change _ = T (Sum.inl 0) (Sum.inl 0) + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨(0 : Row 3 6), 1⟩, (Sum.inl 0), (Sum.inl 1), ?_⟩
    change T (Sum.inl 0) (Sum.inl 0) ≠ T (Sum.inl 0) (Sum.inl 1)
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229508StripCertificate.Transitions.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 21) (fun _ => Fin 15) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => W x y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => W x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (i : Fin 21), forward T initial i.val ∘ Sum.inr = fun j => r.readout () i j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (forward_one 0) 0
  change _ = W 0 0 + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @forward_one) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_one, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change W 1 0 ≠ W 1 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_one) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229508StripCertificate.Powers.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => (Fin 15 ⊕ Fin 15) → ℤ)

def readout : Realization signature := realize signature
  (fun _ _ n => forward T initial n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n j => if n = 1 + 12 then forward T initial n j + 1 else forward T initial n j)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () (1 + 12) = ∑ j : Fin 12, coeff j • r.readout () () (1 + j.val)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (fun j => if (1 + 12 : ℕ) = 1 + 12 then forward T initial (1 + 12) j + 1
    else forward T initial (1 + 12) j) =
    ∑ k : Fin 12, coeff k • (fun j =>
      if 1 + k.val = 1 + 12 then forward T initial (1 + k.val) j + 1
      else forward T initial (1 + k.val) j) at h
  have hbefore (k : Fin 12) : 1 + k.val ≠ 1 + 12 :=
    Nat.ne_of_lt (Nat.add_lt_add_left k.isLt 1)
  simp only [if_pos rfl, if_neg (hbefore _)] at h
  have hb := congrFun h (Sum.inr 0)
  have ha := congrFun finite_certificate (Sum.inr 0)
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.trans hb.symm)

def family : Registration arena (type_of% @finite_certificate) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h (Sum.inr 0)
    have h₀ := congrFun (forward_one 0) 0
    have h₁ := congrFun (forward_one 1) 0
    exact (by decide +kernel : W 0 0 ≠ W 1 0) (h₀.symm.trans (he.trans h₁))

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229508StripCertificate.Polynomial.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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

namespace Inherited

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => Fin 15 → ℤ)

def readout : Realization signature := realize signature
  (fun _ _ n => forward HardinA203981StripData.T HardinA203981StripData.initial n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n j => forward HardinA203981StripData.T HardinA203981StripData.initial n j + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, forward T initial n ∘ Sum.inl = r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) 0
  have ha := congrFun (forward_zeroth 0) 0
  change _ = forward HardinA203981StripData.T HardinA203981StripData.initial 0 0 + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)

def family : Registration arena (type_of% @forward_zeroth) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_zeroth, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h 0
    have h₀ := congrFun (HardinA203981StripCertificate.forward_table 0) 0
    have h₁ := congrFun (HardinA203981StripCertificate.forward_table 1) 0
    exact (by decide +kernel : HardinA203981StripCertificate.W 0 0 ≠
      HardinA203981StripCertificate.W 1 0) (h₀.symm.trans (he.trans h₁))

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_zeroth) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229508StripCertificate.Inherited.auditUnit
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
  (fun _ _ n => forward HardinA203981StripData.T HardinA203981StripData.initial n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
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

end Inherited

end
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
