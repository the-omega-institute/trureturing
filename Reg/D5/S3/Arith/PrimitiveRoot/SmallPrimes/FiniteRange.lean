import D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The finite theorem's source readout is the exact target exponent p−1. -/
noncomputable section
open _root_.D5.S3.Arith.PrimitiveRoot.SmallPrimes
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange

abbrev signature := Reg.Support.SingleDependentReadout.signature Unit
  (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ p => p - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ p, 3 ≤ p → p < 3483482 → p.Prime →
    ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hlt, ho⟩ := h 3 (by decide) (by decide) (by decide)
  have hq2 : q = 2 := by have := hq.two_le; omega
  subst q
  have hh : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  have he : orderOf (2 : ZMod 3) = 0 := ho
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 1, 2, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% @small_prime_primitiveRoot) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@small_prime_primitiveRoot, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@small_prime_primitiveRoot) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.small_prime_primitiveRoot.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
end Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRange
