import D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The complete scanner-fibre identity as a dependent-family readout law. -/

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip (Seen good finish)
open _root_.D5.S3.Observer.Separation.BooleanRankThreeK4 (beta)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped BigOperators

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature (ℕ × Seen)
    (fun p => Seen → (Fin p.1 → Fin 3) → ℤ) (fun _ => ℤ)

def actual : Realization signature := by
  classical
  exact realize signature (fun _ p H => ∑ c : Fin p.1 → Fin 6,
    if good p.2 c then H (finish p.2 c) (fun j => beta (c j)) else 0) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p H => actual.readout () p H + 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (k : ℕ) (s : Seen) (H : Seen → (Fin k → Fin 3) → ℤ),
    R.readout () (k, s) H = ∑ q : Fin k → Fin 3, rowWeight s q * H (rowFinish s q) q

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h0 := h 0 (false, false) (fun _ _ => 0)
  simp [rejected, actual, realize] at h0

def family : Registration arena (type_of% @scanner_fibres) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨scanner_fibres, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(0, (false, false)), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
    simp [actual, realize, good]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@scanner_fibres) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.auditUnit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (by
    classical
    exact realize signature (fun _ p H => ∑ c : Fin p.1 → Fin 6,
      if good p.2 c then H (finish p.2 c) (fun j => beta (c j)) else 0)
        (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233255LiteralBridge
