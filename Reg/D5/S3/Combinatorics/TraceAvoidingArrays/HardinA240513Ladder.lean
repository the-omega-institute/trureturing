import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit PowerSeries

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ n => a n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ n => a n + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R :=
    (∀ n : ℕ, 6 ≤ n →
      (R.readout () () n : ℤ) =
        2 * (a (n - 1) : ℤ) + (a (n - 2) : ℤ) - (a (n - 3) : ℤ) -
          2 * (a (n - 4) : ℤ) + (a (n - 5) : ℤ)) ∧
    (1 - X) * (1 - X - 2 * X ^ 2 - X ^ 3 + X ^ 4) *
        (PowerSeries.mk fun n => (a n : ℤ)) =
      X * (2 - X) * (1 - X ^ 2 - 2 * X ^ 3)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h.1 6 (by decide)
  have ha := result.1 6 (by decide)
  change ((a 6 + 1 : ℕ) : ℤ) = _ at hb
  push_cast at hb
  linarith

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
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder.family
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
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
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

/-- Refer to the original continuation vector without copying its definition. -/
elab "ladderPrivate% " n:ident : term => do
  let scopePrefix := Lean.Name.num
    `_private.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder 0
  let sourceName := scopePrefix ++
    (`D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder ++ n.getId)
  Lean.Meta.mkConstWithFreshMVarLevels sourceName

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (Fin 2 → Bool)
    (fun _ => Fin 2 → Bool) (fun _ => ℤ)

def actual : Realization signature :=
  realize signature (fun _ r s => (ladderPrivate% v) 5 r s) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ r s => (ladderPrivate% v) 5 r s + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ r s : Fin 2 → Bool,
    R.readout () r s =
      2 * (ladderPrivate% v) 4 r s + (ladderPrivate% v) 3 r s -
        (ladderPrivate% v) 2 r s - 2 * (ladderPrivate% v) 1 r s +
          (ladderPrivate% v) 0 r s

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hb := h (fun _ => false) (fun _ => false)
  have ha := finite_certificate (fun _ => false) (fun _ => false)
  change (ladderPrivate% v) 5 (fun _ => false) (fun _ => false) + 1 = _ at hb
  linarith

def family : Registration arena (type_of% @finite_certificate) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨finite_certificate, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(fun _ => false), (fun _ => false), (fun _ => true), ?_⟩
    change (ladderPrivate% v) 5 (fun _ => false) (fun _ => false) ≠
      (ladderPrivate% v) 5 (fun _ => false) (fun _ => true)
    decide +kernel

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@finite_certificate) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder.FiniteCertificate.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder.FiniteCertificate.family
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
    (fun _ r s => (ladderPrivate% v) 5 r s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms audit

end FiniteCertificate

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA240513Ladder
