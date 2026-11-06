import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

attribute [local irreducible] a

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 5 ≤ n →
      (R.readout () () n : ℤ) =
        2 * (a (n - 1) : ℤ) + 7 * (a (n - 2) : ℤ) -
          2 * (a (n - 3) : ℤ) - 3 * (a (n - 4) : ℤ)) ∧
    (1 - 2 * X - 7 * X ^ 2 + 2 * X ^ 3 + 3 * X ^ 4) *
        (PowerSeries.mk fun n => (a n : ℤ)) = X * (1 - X) * (3 + 2 * X)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible (n : ℕ) (hn : 5 ≤ n) : False := by
    have hb := h.1 n hn
    have ha := result.1 n hn
    change ((a n + 1 : ℕ) : ℤ) = _ at hb
    have he : ((a n + 1 : ℕ) : ℤ) = (a n : ℤ) := hb.trans ha.symm
    exact Nat.succ_ne_self (a n) (Int.ofNat.inj he)
  exact impossible 5 (by decide)

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
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@result) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "arg", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

namespace FiniteCertificate

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Row) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ _ r => v 4 r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ r => v 4 r + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r : Row,
    R.readout () () r = 2 * v 3 r + 7 * v 2 r - 2 * v 1 r - 3 * v 0 r

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => false)
  have ha := finite_certificate (fun _ => false)
  change v 4 (fun _ => false) + 1 = _ at hb
  have hz : (1 : ℤ) = 0 := add_left_cancel
    (show v 4 (fun _ => false) + 1 = v 4 (fun _ => false) + 0 by
      simpa only [add_zero] using hb.trans ha.symm)
  exact Int.one_ne_zero hz

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ => false), (fun _ => true), ?_⟩
    change v 4 (fun _ => false) ≠ v 4 (fun _ => true)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings.FiniteCertificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings.FiniteCertificate.family
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
    (fun _ _ r => v 4 r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA228502Kings
