import Mathlib.Tactic.NormNum
import D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-bound exact-order targets for the certificate soundness theorems. -/
noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel

private def two : PrimeValue := ⟨2, .two⟩

namespace Append
abbrev signature := Reg.Support.SingleDependentReadout.signature
  (Σ _ : ℕ, Σ _ : ℕ, ℕ) (fun _ => List Row) (fun _ => Bool)
def actual : Realization signature :=
  realize signature (fun _ p xs => checkBlock p.1 (p.2.1 + p.2.2) xs)
    (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ {start n m : ℕ} {xs ys : List Row},
    checkBlock start n xs = true → checkBlock (start + 2 * n) m ys = true →
      R.readout () ⟨start, n, m⟩ (xs ++ ys) = true
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hh := h (start := 3) (n := 1) (m := 0) (xs := [.p two [two]]) (ys := [])
    (by decide) (by decide)
  change false = true at hh
  cases hh
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨3, 1, 0⟩, [.p two [two]], [], ?_⟩
  change checkBlock 3 1 [.p two [two]] ≠ checkBlock 3 1 []
  decide
def family : Registration arena (type_of% @checkBlock_append) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@checkBlock_append, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@checkBlock_append) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.checkBlock_append.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel.Append.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p xs => checkBlock p.1 (p.2.1 + p.2.2) xs) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Append

#print axioms Append.family
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.Kernel
