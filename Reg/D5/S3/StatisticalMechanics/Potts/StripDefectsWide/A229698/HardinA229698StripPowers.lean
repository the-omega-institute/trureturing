import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripTables
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 28) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => V k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => V k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 28,
    (T ^ k.val).mulVec terminal =
      Sum.elim (A.readout () () k) ((HardinA229590StripData.T ^ k.val).mulVec HardinA229590StripData.terminal)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) (Sum.inl 0)
  have ha := congrFun (powers_table 0) (Sum.inl 0)
  change _ = V 0 0 at ha
  change _ = V 0 0 + 1 at hb
  linarith
def family : Registration arena (type_of% @powers_table) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨powers_table, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    intro he
    have hh := congrFun he 0
    change V 0 0 = V 1 0 at hh
    have hn : V 0 0 ≠ V 1 0 := by decide +kernel
    exact hn hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers_table) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripPowers.auditUnit
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
  readout := some (realize signature (fun _ _ k => V k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace Polynomial
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 21) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ _ j => (coefficients j : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A :=
    (T ^ (6+21)).mulVec terminal =
      ∑ j : Fin 21, A.readout () () j • (T ^ (6+j.val)).mulVec terminal
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h (Sum.inl 0)
  simp only [rejected, realize, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hb
  rw [show 6+21 = (27 : Fin 28).val from rfl,
    _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers.powers_table] at hb
  change V 27 0 = 0 at hb
  exact (by decide +kernel : V 27 0 ≠ 0) hb
def family : Registration arena (type_of% @power_polynomial) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨power_polynomial, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (-512 : ℤ) ≠ 9216
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@power_polynomial) (Realization signature) Type Unit where
  unitName := `Reg.A229698HardinA229698StripPowersPolynomial.auditUnit
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
  readout := some (realize signature (fun _ _ j => (coefficients j : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Polynomial
end
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229698.HardinA229698StripPowers
