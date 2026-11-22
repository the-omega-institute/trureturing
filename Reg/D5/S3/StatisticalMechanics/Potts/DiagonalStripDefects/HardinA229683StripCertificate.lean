import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripCertificate
import D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229508StripData
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

namespace Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate

open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
open _root_.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripData
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
def readout : Realization signature := realize signature (fun _ x y => costTwo (boundary x) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ x y => costTwo (boundary x) y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row 3 6) (j : Fin 15),
    (∑ r : Row 3 6, if bondDefects (betw 6) p r = 2 ∧ boundary r = j then (1 : ℤ) else 0) = r.readout () p j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0, 0, 0, 0] 0
  have ha := two_counts ![0, 0, 0, 0, 0, 0] 0
  change _ = costTwo (boundary ![0, 0, 0, 0, 0, 0]) 0 + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @two_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨two_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨![0, 0, 0, 0, 0, 0], 0, 1, ?_⟩
    change costTwo 0 0 ≠ costTwo 0 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@two_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683StripCertificate.Counts.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
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
abbrev signature : Signature := _root_.Reg.Support.SingleDependentReadout.signature (Σ _ : Row 3 6, Fin 3) (fun _ => ((Fin 15 ⊕ Fin 15) ⊕ Fin 15)) (fun _ => ℤ)
def readout : Realization signature := realize signature (fun _ x y => T (cl x.1 x.2.val) y) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun i x y => (fun _ x y => T (cl x.1 x.2.val) y) i x y + 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : Row 3 6) (d : Fin 3) (j : ((Fin 15 ⊕ Fin 15) ⊕ Fin 15)),
    (∑ r : Row 3 6, if bondDefects (betw 6) p r ≤ d.val ∧ cl r (d.val - bondDefects (betw 6) p r) = j
      then (1 : ℤ) else 0) = r.readout () ⟨p, d⟩ j
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h ![0, 0, 0, 0, 0, 0] 2 (Sum.inl (Sum.inl 0))
  have ha := transition_counts ![0, 0, 0, 0, 0, 0] 2 (Sum.inl (Sum.inl 0))
  change _ = T (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inl 0)) at ha
  change _ = T (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inl 0)) + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @transition_counts) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨transition_counts, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨⟨![0, 0, 0, 0, 0, 0], 2⟩, (Sum.inl (Sum.inl 0)), (Sum.inl (Sum.inl 1)), ?_⟩
    change T (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inl 0)) ≠ T (Sum.inl (Sum.inl 0)) (Sum.inl (Sum.inl 1))
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@transition_counts) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683StripCertificate.Transitions.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
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
  have ha := congrFun (forward_two 0) 0
  change _ = W 0 0 + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)
def family : Registration arena (type_of% @forward_two) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_two, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    change W 1 0 ≠ W 1 1
    decide +kernel
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_two) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683StripCertificate.Powers.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ((Fin 15 ⊕ Fin 15) ⊕ Fin 15) → ℤ)

def readout : Realization signature := realize signature
  (fun _ _ n => forward T initial n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n j => if n = 2 + 18 then forward T initial n j + 1 else forward T initial n j)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := r.readout () () (2 + 18) = ∑ j : Fin 18, coeff j • r.readout () () (2 + j.val)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  change (fun j => if (2 + 18 : ℕ) = 2 + 18 then forward T initial (2 + 18) j + 1
    else forward T initial (2 + 18) j) =
    ∑ k : Fin 18, coeff k • (fun j =>
      if 2 + k.val = 2 + 18 then forward T initial (2 + k.val) j + 1
      else forward T initial (2 + k.val) j) at h
  have hbefore (k : Fin 18) : 2 + k.val ≠ 2 + 18 :=
    Nat.ne_of_lt (Nat.add_lt_add_left k.isLt 2)
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
    have h₀ := congrFun (forward_two 0) 0
    have h₁ := congrFun (forward_two 1) 0
    exact (by decide +kernel : W 0 0 ≠ W 1 0) (h₀.symm.trans (he.trans h₁))

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683StripCertificate.Polynomial.auditUnit
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
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => (Fin 15 ⊕ Fin 15) → ℤ)

def readout : Realization signature := realize signature
  (fun _ _ n => forward HardinA229508StripData.T HardinA229508StripData.initial n) (fun e => nomatch e)

def rejected : Realization signature := realize signature
  (fun _ _ n j => forward HardinA229508StripData.T HardinA229508StripData.initial n j + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ n : ℕ, forward T initial n ∘ Sum.inl = r.readout () () n

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) (Sum.inr 0)
  have ha := congrFun (forward_inherited 0) (Sum.inr 0)
  change _ = forward HardinA229508StripData.T HardinA229508StripData.initial 0 (Sum.inr 0) + 1 at hb
  exact (ne_of_lt (Int.lt_add_one_iff.mpr le_rfl)) (ha.symm.trans hb)

def family : Registration arena (type_of% @forward_inherited) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨forward_inherited, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro h
    have he := congrFun h (Sum.inr 0)
    have h₀ := congrFun (HardinA229508StripCertificate.forward_one 0) 0
    have h₁ := congrFun (HardinA229508StripCertificate.forward_one 1) 0
    exact (by decide +kernel : HardinA229508StripCertificate.W 0 0 ≠
      HardinA229508StripCertificate.W 1 0) (h₀.symm.trans (he.trans h₁))

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@forward_inherited) (Realization signature) Type Unit where
  unitName := `Reg.AHardinA229683StripCertificate.Inherited.auditUnit
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
  (fun _ _ n => forward HardinA229508StripData.T HardinA229508StripData.initial n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
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
end Reg.D5.S3.StatisticalMechanics.Potts.DiagonalStripDefects.HardinA229683StripCertificate
