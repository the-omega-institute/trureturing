import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.UnitaryProductBridge
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Divisors.UnitaryProductBridge

open _root_.D5.S3.Arith.Divisors.UnitaryProductBridge
open _root_.D5.S3.Arith.EulerFormDivisorSum
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change unitarySum 1 ≠ unitarySum 2
  decide

private theorem support_one :
    ∀ p, Nat.Prime p → p ≤ 1 / (∏ q ∈ (1 : ℕ).primeFactors, q) → p ∣ (1 : ℕ) := by
  intro p hp hle
  simp at hle
  have := hp.two_le
  omega

private theorem primes_le_one : Nat.primesLE 1 = ∅ := by
  ext p
  simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false]
  intro ⟨hle, hp⟩
  have := hp.two_le
  omega

private theorem squarefree_sum_one : squarefreeSum 1 = 1 := by
  simp [squarefreeSum, Finset.filter_singleton]

def productArena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), N ≠ 0 →
    R.readout () () N = ∏ p ∈ N.primeFactors, (p ^ N.factorization p + 1)

private theorem product_rejected : ¬ productArena.Law rejected := by
  intro h
  have hz := h 1 (by decide)
  change 0 = ∏ p ∈ (1 : ℕ).primeFactors, (p ^ (1 : ℕ).factorization p + 1) at hz
  simp at hz

def productSource : Registration productArena
    (∀ (N : ℕ), N ≠ 0 →
    unitarySum N = ∏ p ∈ N.primeFactors, (p ^ N.factorization p + 1)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unitarySum_eq_product, rejected, product_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    productArena.Law actual rejected product_rejected
  dependence := actual_dependence

def supportArena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹)) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (R.readout () () N : ℚ) / N + (squarefreeSum N : ℚ) / N

private theorem support_rejected : ¬ supportArena.Law rejected := by
  intro h
  have hz := h 1 (by decide) support_one
  change (let m := 1 / (∏ q ∈ (1 : ℕ).primeFactors, q); (fun m : ℕ => (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹)) +
    (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m) m ≤
    (0 : ℚ) / (1 : ℕ) + (squarefreeSum 1 : ℚ) / (1 : ℕ)) at hz
  have hq : 1 / (∏ q ∈ (1 : ℕ).primeFactors, q) = 1 := by simp
  simp only [hq, squarefree_sum_one] at hz
  norm_num [primes_le_one] at hz

def supportSource : Registration supportArena
    (∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹)) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mandatory_support_lower, rejected, support_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    supportArena.Law actual rejected support_rejected
  dependence := actual_dependence

def mandatoryArena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (R.readout () () N : ℚ) / N + (squarefreeSum N : ℚ) / N

private theorem mandatory_rejected : ¬ mandatoryArena.Law rejected := by
  intro h
  have hz := h 1 (by decide) support_one
  change (let m := 1 / (∏ q ∈ (1 : ℕ).primeFactors, q); (fun m : ℕ => (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
    (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m) m ≤
    (0 : ℚ) / (1 : ℕ) + (squarefreeSum 1 : ℚ) / (1 : ℕ)) at hz
  have hq : 1 / (∏ q ∈ (1 : ℕ).primeFactors, q) = 1 := by simp
  simp only [hq, squarefree_sum_one] at hz
  norm_num [primes_le_one] at hz

def mandatorySource : Registration mandatoryArena
    (∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    let m := N / (∏ q ∈ N.primeFactors, q)
    (∏ p ∈ Nat.primesLE m, (1 + 1 / (p : ℚ) ^ (m.factorization p + 1))) +
      (∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) / m ≤
      (unitarySum N : ℚ) / N + (squarefreeSum N : ℚ) / N) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨mandatory_product_lower, rejected, mandatory_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    mandatoryArena.Law actual rejected mandatory_rejected
  dependence := actual_dependence

def twiceArena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    2 * N ≤ R.readout () () N + squarefreeSum N

private theorem twice_rejected : ¬ twiceArena.Law rejected := by
  intro h
  have hz := h 1 (by decide) support_one
  change 2 * 1 ≤ 0 + squarefreeSum 1 at hz
  rw [squarefree_sum_one] at hz
  omega

def twiceSource : Registration twiceArena
    (∀ (N : ℕ), N ≠ 0 →
    (∀ p, Nat.Prime p → p ≤ N / (∏ q ∈ N.primeFactors, q) → p ∣ N) →
    2 * N ≤ unitarySum N + squarefreeSum N) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨unitary_squarefree_ge_twice_of_support, rejected, twice_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    twiceArena.Law actual rejected twice_rejected
  dependence := actual_dependence

def productRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.unitarySum_eq_product) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.UnitaryProductBridge.unitarySum_eq_product.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.UnitaryProductBridge.productSource
  realizationSource := none
  generated := false
  arena := .source ⟨productArena⟩
  objectArena := .source ⟨productArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena ⟨productSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.UnitaryProductBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def supportRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.mandatory_support_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.UnitaryProductBridge.mandatory_support_lower.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.UnitaryProductBridge.supportSource
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.UnitaryProductBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def mandatoryRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.mandatory_product_lower) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.UnitaryProductBridge.mandatory_product_lower.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.UnitaryProductBridge.mandatorySource
  realizationSource := none
  generated := false
  arena := .source ⟨mandatoryArena⟩
  objectArena := .source ⟨mandatoryArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source mandatoryArena ⟨mandatorySource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.UnitaryProductBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def twiceRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.unitary_squarefree_ge_twice_of_support) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.UnitaryProductBridge.unitary_squarefree_ge_twice_of_support.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.UnitaryProductBridge.twiceSource
  realizationSource := none
  generated := false
  arena := .source ⟨twiceArena⟩
  objectArena := .source ⟨twiceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source twiceArena ⟨twiceSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ N => unitarySum N) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.UnitaryProductBridge
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
noncomputable section
namespace PrimePowerUnitary

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ (fun _ => Finset ℕ) (fun _ => ℕ)

def actual : Realization signature :=
  realize signature (fun _ N F => ∏ p ∈ F, p ^ N.factorization p)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ), N ≠ 0 → ∀ (F : Finset ℕ), F ⊆ N.primeFactors →
    R.readout () N F ∈ N.divisors.filter (fun d => Nat.Coprime d (N / d))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have bad := h 1 (by decide) ∅ (by simp)
  change 0 ∈ (1 : ℕ).divisors.filter (fun d => Nat.Coprime d (1 / d)) at bad
  norm_num at bad

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.prime_power_product_unitary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@prime_power_product_unitary, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    refine ⟨2, ∅, {2}, ?_⟩
    change (∏ p ∈ (∅ : Finset ℕ), p ^ (2 : ℕ).factorization p) ≠
      ∏ p ∈ ({2} : Finset ℕ), p ^ (2 : ℕ).factorization p
    simp only [Finset.prod_empty, Finset.prod_singleton,
      Nat.prime_two.factorization, Finsupp.single_eq_same, pow_one]
    norm_num

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.UnitaryProductBridge.prime_power_product_unitary)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Divisors.UnitaryProductBridge.prime_power_product_unitary.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.UnitaryProductBridge.PrimePowerUnitary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.UnitaryProductBridge
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimePowerUnitary
end

end Reg.D5.S3.Arith.Divisors.UnitaryProductBridge
