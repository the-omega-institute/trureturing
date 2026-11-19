import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers

/-! Dependent observations of the exact five-row defect counts. -/

namespace Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233260Literal (Q)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators
noncomputable section
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripData
open _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 19) (fun _ => Fin 41 → ℤ)
def readout : Realization signature := realize signature (fun _ _ k => U k) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ k => U k + Pi.single 0 1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A := ∀ k : Fin 19,
    (T ^ k.val).mulVec terminal =
      Sum.elim (A.readout () () k) ((Q ^ k.val).mulVec (1 : Fin 41 → ℤ))
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun (h 0) (Sum.inl 0)
  have ha := congrFun (powers_table 0) (Sum.inl 0)
  change _ = U 0 0 at ha
  change _ = U 0 0 + 1 at hb
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
    change U 0 0 = U 1 0 at hh
    have hn : U 0 0 ≠ U 1 0 := by decide +kernel
    exact hn hh

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@powers_table) (Realization signature) Type Unit where
  unitName := `Reg.A229590HardinA229590StripPowers.auditUnit
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
  readout := some (realize signature (fun _ _ k => U k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
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
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Fin 14) (fun _ => ℤ)
def readout : Realization signature :=
  realize signature (fun _ _ j => (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ)) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => (0 : ℤ)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law A :=
    (T ^ (4+14)).mulVec terminal =
      ∑ j : Fin 14, A.readout () () j • (T ^ (4+j.val)).mulVec terminal
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := congrFun h (Sum.inl 0)
  simp only [rejected, realize, zero_smul, Finset.sum_const_zero, Pi.zero_apply] at hb
  rw [show 4+14 = (18 : Fin 19).val from rfl,
    _root_.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers.powers_table] at hb
  change U 18 0 = 0 at hb
  exact (by decide +kernel : U 18 0 ≠ 0) hb
def family : Registration arena (type_of% @power_polynomial) where
  actual := readout
  bridge := Iff.rfl
  variation := ⟨power_polynomial, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law readout rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (-64 : ℤ) ≠ 768
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@power_polynomial) (Realization signature) Type Unit where
  unitName := `Reg.A229590HardinA229590StripPowersPolynomial.auditUnit
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
  readout := some (realize signature (fun _ _ j => (![-64,768,-3648,8336,-7472,-5464,18879,-14888,-816,9016,-6494,2200,-384,32] j : ℤ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
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
end Reg.D5.S3.StatisticalMechanics.Potts.StripDefectsWide.A229590.HardinA229590StripPowers
