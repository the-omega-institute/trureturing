import D5.S3.Arith.PrimitiveRoot.Erdos985
import Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRangeExtended
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! Source-faithful order targets for the conditional prime primitive-root conclusion. -/
noncomputable section
open scoped BigOperators
open _root_.D5.S3.Arith.PrimitiveRoot.Erdos985
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
namespace Reg.D5.S3.Arith.PrimitiveRoot.Erdos985

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ)
def actual : Realization signature :=
  realize signature (fun _ _ p => p - 1) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)
private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 1, 2, by norm_num [actual, realize]⟩

namespace Large
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (_hp : 5000000 ≤ p)
    (_hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) ,
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hlt, ho⟩ := h p hp hL
  have hz : (q : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ q := (CharP.cast_eq_zero_iff (ZMod p) p q).mp hz
    exact Nat.not_dvd_of_pos_of_lt hq.pos hlt hd
  have hd := ZMod.orderOf_dvd_card_sub_one hz
  have hp1 := (Fact.out : p.Prime).one_lt
  have hn := Nat.pos_of_dvd_of_pos hd (show 0 < p - 1 by omega)
  have he : orderOf (q : ZMod p) = 0 := by simpa [rejected, realize] using ho
  omega
def family (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Registration arena (type_of% @erdos985_large_prime) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@erdos985_large_prime, rejected, rejected_law p hp hL⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    (rejected_law p hp hL)
  dependence := dependence
def audit (p : ℕ) [Fact p.Prime] (hp : 5000000 ≤ p)
    (hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      erdos985_large_prime (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.Erdos985.erdos985_large_prime.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.Erdos985.Large.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family p hp hL⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.Erdos985
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
end Large

namespace All
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (_hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0)
    ,
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0)
    : ¬ arena.Law rejected := by
  intro h
  obtain ⟨q, hq, hlt, ho⟩ := h hL 3 (by decide) (by decide)
  have hq2 : q = 2 := by have := hq.two_le; omega
  subst q
  have hh : orderOf (2 : ZMod 3) = 2 :=
    orderOf_eq_prime (by decide) (by decide)
  change orderOf (2 : ZMod 3) = 0 at ho
  omega
def family
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0)
    : Registration arena (type_of% @erdos985_of_finiteHeight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@erdos985_of_finiteHeight, rejected, rejected_law hL⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    (rejected_law hL)
  dependence := dependence
def audit
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      erdos985_of_finiteHeight (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.Erdos985.erdos985_of_finiteHeight.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.Erdos985.All.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family hL⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.Erdos985
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
def compatibilityAudit
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      erdos985_of_GRH (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.Erdos985.erdos985_of_GRH.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.Erdos985.All.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family hL⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.Erdos985
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
def compatibilityAudit
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      erdos985_of_GRH (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.Erdos985.erdos985_of_GRH.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.Erdos985.All.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family hL⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.Erdos985
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
def compatibilityAudit
    (hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (p - 1).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0) :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      erdos985_of_GRH (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.PrimitiveRoot.Erdos985.erdos985_of_GRH.__information_unit
  realizationName := `Reg.D5.S3.Arith.PrimitiveRoot.Erdos985.All.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena ⟨family hL⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p - 1) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.PrimitiveRoot.Erdos985
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end All

#print axioms erdos985_large_prime
#print axioms erdos985_of_finiteHeight
end Reg.D5.S3.Arith.PrimitiveRoot.Erdos985
