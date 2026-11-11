import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration
import Lean.Elab.Tactic.Omega

/-! Four-slot registration of the literal five-column recurrence. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

attribute [local instance 2000] Pi.instFintype
attribute [local instance 2000]
  _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.widthInstDecidableGood
attribute [local irreducible] a

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ,
    (R.readout () () (n + 8) : ℤ) =
      480 * (R.readout () () (n + 7) : ℤ) - 60416 * (R.readout () () (n + 6) : ℤ) +
      1966080 * (R.readout () () (n + 5) : ℤ) +
      22020096 * (R.readout () () (n + 4) : ℤ) -
      1845493760 * (R.readout () () (n + 3) : ℤ) +
      22548578304 * (R.readout () () (n + 2) : ℤ) -
      68719476736 * (R.readout () () (n + 1) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h 0
  change (1 : ℤ) = 480 * 1 - 60416 * 1 + 1966080 * 1 + 22020096 * 1 -
    1845493760 * 1 + 22548578304 * 1 - 68719476736 * 1 at hb
  omega

def family : Registration arena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change a 0 ≠ a 1
    have hz : a 0 = 0 := by
      unfold a
      decide +kernel
    have hp : 0 < a 1 := by
      unfold a
      apply Finset.card_pos.mpr
      refine ⟨fun ij => ![0, 1, 0, 1, 0] ij.2, ?_⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by decide +kernel⟩
    omega

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.A233171.auditUnit
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
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

#print axioms audit

end

end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233171DiagonalStrip
