import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.PrimeReciprocalProduct
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Arith.Divisors.PrimeReciprocalProduct

open _root_.D5.S3.Arith.Divisors.PrimeReciprocalProduct
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

noncomputable section

abbrev natSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℚ)

abbrev finsetSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => Finset ℕ) (fun _ => ℚ)

private theorem primes_le_one : Nat.primesLE 1 = ∅ := by
  ext p
  simp only [Nat.mem_primesLE, Finset.notMem_empty, iff_false]
  intro ⟨hle, hp⟩
  have := hp.two_le
  omega

def harmonicActual : Realization natSignature :=
  realize natSignature (fun _ _ m => harmonic m) (fun e => nomatch e)

def harmonicRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 10) (fun e => nomatch e)

def harmonicArena : Arena where
  signature := natSignature
  Law R := ∀ (m : ℕ), 0 < m →
    (R.readout () () m) < 2 * ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)

private theorem harmonic_rejected : ¬ harmonicArena.Law harmonicRejected := by
  intro h
  have hz := h 1 (by decide)
  change (10 : ℚ) < 2 * ∏ p ∈ Nat.primesLE 1, (1 + (p : ℚ)⁻¹) at hz
  norm_num [primes_le_one] at hz

private theorem harmonic_dependence : ObservationalDependence natSignature harmonicActual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  change harmonic 1 ≠ harmonic 2
  norm_num [harmonic]

def harmonicSource : Registration harmonicArena
    (∀ (m : ℕ), 0 < m →
    harmonic m < 2 * ∏ p ∈ Nat.primesLE m, (1 + (p : ℚ)⁻¹)) where
  actual := harmonicActual
  bridge := Iff.rfl
  variation := ⟨harmonic_lt_twice_prime_product, harmonicRejected, harmonic_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    harmonicArena.Law harmonicActual harmonicRejected harmonic_rejected
  dependence := harmonic_dependence

def supportActual : Realization finsetSignature :=
  realize finsetSignature (fun _ _ F => (∏ p ∈ F, (1 + (p : ℚ)⁻¹))) (fun e => nomatch e)

def supportRejected : Realization finsetSignature :=
  realize finsetSignature (fun _ _ _ => 10) (fun e => nomatch e)

def supportArena : Arena where
  signature := finsetSignature
  Law R := ∀ (F : Finset ℕ), F.Nonempty → (∀ p ∈ F, Nat.Prime p) →
    (R.readout () () F) ^ 2 ≤ (9 / 4 : ℚ) * F.card

private theorem support_rejected : ¬ supportArena.Law supportRejected := by
  intro h
  have hz := h {2} (by simp) (by simpa using (show Nat.Prime 2 by decide))
  change (10 : ℚ) ^ 2 ≤ (9 / 4 : ℚ) * ({2} : Finset ℕ).card at hz
  norm_num at hz

private theorem support_dependence : ObservationalDependence finsetSignature supportActual := by
  intro i
  refine ⟨(), {2}, {3}, ?_⟩
  change (∏ p ∈ ({2} : Finset ℕ), (1 + (p : ℚ)⁻¹)) ≠
    ∏ p ∈ ({3} : Finset ℕ), (1 + (p : ℚ)⁻¹)
  norm_num

def supportSource : Registration supportArena
    (∀ (F : Finset ℕ), F.Nonempty → (∀ p ∈ F, Nat.Prime p) →
    (∏ p ∈ F, (1 + (p : ℚ)⁻¹)) ^ 2 ≤ (9 / 4 : ℚ) * F.card) where
  actual := supportActual
  bridge := Iff.rfl
  variation := ⟨prime_support_product_sq_le, supportRejected, support_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    supportArena.Law supportActual supportRejected support_rejected
  dependence := support_dependence

def missingActual : Realization natSignature :=
  realize natSignature (fun _ _ m => (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹))) (fun e => nomatch e)

def missingRejected : Realization natSignature :=
  realize natSignature (fun _ _ _ => 0) (fun e => nomatch e)

def missingArena : Arena where
  signature := natSignature
  Law R := ∀ (m : ℕ), 1000 ≤ m →
    2 ≤ (R.readout () () m)

private theorem missing_rejected : ¬ missingArena.Law missingRejected := by
  intro h
  have hz := h 1000 (by decide)
  change (2 : ℚ) ≤ 0 at hz
  norm_num at hz

private theorem missing_dependence : ObservationalDependence natSignature missingActual := by
  intro i
  refine ⟨(), 1, 3, ?_⟩
  change (∏ p ∈ Nat.primesLE 1 \ (1 : ℕ).primeFactors, (1 + (p : ℚ)⁻¹)) ≠
    ∏ p ∈ Nat.primesLE 3 \ (3 : ℕ).primeFactors, (1 + (p : ℚ)⁻¹)
  have hp : Nat.primesLE 3 = {2, 3} := by decide
  have hf : (3 : ℕ).primeFactors = {3} := by simp [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
  have hs : ({2, 3} : Finset ℕ) \ {3} = {2} := by decide
  rw [primes_le_one, hp, hf, hs, Finset.empty_sdiff]
  norm_num

def missingSource : Registration missingArena
    (∀ (m : ℕ), 1000 ≤ m →
    2 ≤ (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹))) where
  actual := missingActual
  bridge := Iff.rfl
  variation := ⟨missing_support_product_ge_two, missingRejected, missing_rejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    missingArena.Law missingActual missingRejected missing_rejected
  dependence := missing_dependence

def harmonicRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.PrimeReciprocalProduct.harmonic_lt_twice_prime_product) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.PrimeReciprocalProduct.harmonic_lt_twice_prime_product.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.PrimeReciprocalProduct.harmonicSource
  realizationSource := none
  generated := false
  arena := .source ⟨harmonicArena⟩
  objectArena := .source ⟨harmonicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source harmonicArena ⟨harmonicSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ m => harmonic m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.PrimeReciprocalProduct
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
    (@_root_.D5.S3.Arith.Divisors.PrimeReciprocalProduct.prime_support_product_sq_le) (Realization finsetSignature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.PrimeReciprocalProduct.prime_support_product_sq_le.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.PrimeReciprocalProduct.supportSource
  realizationSource := none
  generated := false
  arena := .source ⟨supportArena⟩
  objectArena := .source ⟨supportArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source supportArena ⟨supportSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize finsetSignature (fun _ _ F => (∏ p ∈ F, (1 + (p : ℚ)⁻¹))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.PrimeReciprocalProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def missingRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Divisors.PrimeReciprocalProduct.missing_support_product_ge_two) (Realization natSignature) Unit Unit where
  unitName := `D5.S3.Arith.Divisors.PrimeReciprocalProduct.missing_support_product_ge_two.audit
  realizationName := `Reg.D5.S3.Arith.Divisors.PrimeReciprocalProduct.missingSource
  realizationSource := none
  generated := false
  arena := .source ⟨missingArena⟩
  objectArena := .source ⟨missingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source missingArena ⟨missingSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize natSignature (fun _ _ m => (∏ p ∈ Nat.primesLE m \ m.primeFactors, (1 + (p : ℚ)⁻¹))) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.PrimeReciprocalProduct
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Arith.Divisors.PrimeReciprocalProduct
