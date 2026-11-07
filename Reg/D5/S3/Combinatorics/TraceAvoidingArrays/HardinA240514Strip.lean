import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
import D5.S3.ConceptDynamics.InformationEscape.DependentFamily
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 21 ≤ n →
    (R.readout () () n : ℤ) =
      4 * (a (n - 1) : ℤ) - 3 * (a (n - 2) : ℤ) - 2 * (a (n - 3) : ℤ) + 2 * (a (n - 4) : ℤ) + 2 *
        (a (n - 5) : ℤ) - 7 * (a (n - 6) : ℤ) - 8 * (a (n - 7) : ℤ) + 15 * (a (n - 8) : ℤ) + 4 *
        (a (n - 9) : ℤ) - 8 * (a (n - 10) : ℤ) - 4 * (a (n - 11) : ℤ) + 15 * (a (n - 12) : ℤ) + 8
        * (a (n - 13) : ℤ) - 7 * (a (n - 14) : ℤ) - 2 * (a (n - 15) : ℤ) + 2 * (a (n - 16) : ℤ) +
        2 * (a (n - 17) : ℤ) - 3 * (a (n - 18) : ℤ) - 4 * (a (n - 19) : ℤ) - (a (n - 20) : ℤ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible (n : ℕ) (hn : 21 ≤ n) : False := by
    have hb := h n hn
    have ha := result n hn
    change ((a n + 1 : ℕ) : ℤ) = _ at hb
    rw [Nat.cast_add, Nat.cast_one] at hb
    have incompatible (x y : ℤ) (hx : x = y) (hy : x + 1 = y) : False := by omega
    exact incompatible _ _ ha hb
  exact impossible 21 (by decide)

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
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
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
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 3 → Bool)
    (fun _ => Fin 3 → Bool) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ r s => v 0 r s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ r s => v 0 r s + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r s : Fin 3 → Bool,
    v 20 r s =
      4 * v 19 r s - 3 * v 18 r s - 2 * v 17 r s + 2 * v 16 r s + 2 * v 15 r s - 7 * v 14 r s
        - 8 * v 13 r s + 15 * v 12 r s + 4 * v 11 r s - 8 * v 10 r s - 4 * v 9 r s + 15 * v 8 r s
        + 8 * v 7 r s - 7 * v 6 r s - 2 * v 5 r s + 2 * v 4 r s + 2 * v 3 r s - 3 * v 2 r s
        - 4 * v 1 r s - R.readout () r s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have impossible (r s : Fin 3 → Bool) : False := by
    have hb := h r s
    have ha := finite_certificate r s
    change v 20 r s = _ at hb
    have incompatible (x y z : ℤ) (hx : x = y - z) (hy : x = y - (z + 1)) :
        False := by omega
    exact incompatible _ _ _ ha hb
  exact impossible (fun _ => false) (fun _ => false)

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => false), (fun _ => false), (![false, true, false]), ?_⟩
    change v 0 (fun _ => false) (fun _ => false) ≠
      v 0 (fun _ => false) (![false, true, false])
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip.FiniteCertificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip.FiniteCertificate.family
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
    (fun _ r s => v 0 r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240514Strip
