import D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-faithful readouts for the linear principal-term sieve. -/
noncomputable section
open scoped BigOperators
open _root_.D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
open _root_.D5.S3.Arith.PrimitiveRoot.CharacterSieve
open _root_.D5.S3.Arith.PrimitiveRoot.CharacterExpansion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)

namespace Covering
def actual : Realization signature :=
  realize signature (fun _ _ x => x) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (x : ℕ) (_hx : 5000000 ≤ x),
    ∃ (e : ℕ) (T : Finset ℕ), e ≠ 0 ∧
      (∀ q : ℕ, q.Prime → q ∣ R.readout () () x - 1 → q ∣ e ∨ q ∈ T) ∧
      0 < delta (sievePrimes (R.readout () () x) e T) ∧
      errorCoefficient (Nat.gcd e (R.readout () () x - 1))
        (sievePrimes (R.readout () () x) e T) *
        ((165458 / 111375 : ℝ) * Real.sqrt (R.readout () () x) *
          Real.log (R.readout () () x)) <
      delta (sievePrimes (R.readout () () x) e T) *
        ((23 / 50 : ℝ) * R.readout () () x)
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨e, T, he, hc, hd, hm⟩ := h 5000000 le_rfl
  norm_num [rejected, realize] at hm
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩
def family : Registration arena (type_of% covering_linear) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨covering_linear, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence
def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    covering_linear (Realization signature) Type Unit where
  unitName :=
    `D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional.covering_linear.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional.Covering.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "arg",
        "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Covering

namespace PrimeRoot
def actual : Realization signature :=
  realize signature (fun _ _ p => p - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (_hp : 5000000 ≤ p)
    (_hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤
        (165458 / 111375 : ℝ) * Real.sqrt p * Real.log p)
    (_hmain : (23 / 50 : ℝ) * p ≤ (smoothedCharacterSum p 1).re),
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤
        (165458 / 111375 : ℝ) * Real.sqrt p * Real.log p)
    (hmain : (23 / 50 : ℝ) * p ≤ (smoothedCharacterSum p 1).re) :
    ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hlt, ho⟩ := h p hp hM hmain
  have hz : (q : ZMod p) ≠ 0 := by
    intro hz
    exact Nat.not_dvd_of_pos_of_lt hq.pos hlt
      ((CharP.cast_eq_zero_iff (ZMod p) p q).mp hz)
  have hd := ZMod.orderOf_dvd_card_sub_one hz
  have hn := Nat.pos_of_dvd_of_pos hd (show 0 < p - 1 by omega)
  have he : orderOf (q : ZMod p) = 0 := by simpa [rejected, realize] using ho
  omega
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 1, 2, by norm_num [actual, realize]⟩
def family (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hM : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ q ∈ (p - 1).primeFactors, q →
      |(smoothedCharacterSum p χ).re| ≤
        (165458 / 111375 : ℝ) * Real.sqrt p * Real.log p)
    (hmain : (23 / 50 : ℝ) * p ≤ (smoothedCharacterSum p 1).re) :
    Registration arena (type_of% @exists_prime_primitiveRoot) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_prime_primitiveRoot, rejected, rejected_law p hp hM hmain⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    (rejected_law p hp hM hmain)
  dependence := dependence
end PrimeRoot
end Reg.D5.S3.Arith.PrimitiveRoot.SieveThresholdUnconditional
