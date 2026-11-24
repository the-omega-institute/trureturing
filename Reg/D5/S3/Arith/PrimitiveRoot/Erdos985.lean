import D5.S3.Arith.PrimitiveRoot.Erdos985
import Reg.D5.S3.Arith.PrimitiveRoot.SmallPrimes.FiniteRangeExtended
import Reg.Support.SingleDependentReadout
import LeanInformationAuditInterface.Contract.Registration

/-! The same order readout controls both the character family and the primitive-root target. -/
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

private theorem nonprincipal_not_order_dvd_one {p : ℕ}
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) (ho : orderOf χ ∣ 1) : False := by
  exact hχ (orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho))

private theorem prime_residue_order_ne_zero {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hlt : q < p) : orderOf (q : ZMod p) ≠ 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hz : (q : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ q := (CharP.cast_eq_zero_iff (ZMod p) p q).mp hz
    exact Nat.not_dvd_of_pos_of_lt hq.pos hlt hd
  have hd := ZMod.orderOf_dvd_card_sub_one hz
  exact Nat.ne_of_gt (Nat.pos_of_dvd_of_pos hd (Nat.sub_pos_of_lt hp.one_lt))

namespace Large
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : ℕ) [Fact p.Prime] (_hp : 5000000 ≤ p)
    (_hL : ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (R.readout () () p).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0),
    ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hp : Nat.Prime 5000011 := by norm_num
  letI : Fact (Nat.Prime 5000011) := ⟨hp⟩
  have hL : ∀ χ : DirichletCharacter ℂ 5000011, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (rejected.readout () () 5000011).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt 5000011 →
        χ.LFunction s ≠ 0 := by
    intro χ hχ ho
    have ho1 : orderOf χ ∣ 1 := by simpa [rejected, realize] using ho
    exact (nonprincipal_not_order_dvd_one χ hχ ho1).elim
  obtain ⟨q, hq, hlt, ho⟩ := h 5000011 (by norm_num) hL
  have hz := prime_residue_order_ne_zero hp hq hlt
  exact hz (by simpa [rejected, realize] using ho)
def family : Registration arena (type_of% @erdos985_large_prime) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@erdos985_large_prime, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence
end Large

namespace All
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (_hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (R.readout () () p).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0),
    ∀ p : ℕ, p.Prime → p ≠ 2 →
      ∃ q : ℕ, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = R.readout () () p
private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hL : ∀ (p : ℕ) (hp : p.Prime),
      letI : NeZero p := ⟨hp.ne_zero⟩;
      5000000 ≤ p → ∀ χ : DirichletCharacter ℂ p, χ ≠ 1 →
      orderOf χ ∣ ∏ r ∈ (rejected.readout () () p).primeFactors, r →
      ∀ s : ℂ, 1 / 2 < s.re → |s.im| ≤ 4 * Real.sqrt p → χ.LFunction s ≠ 0 := by
    intro p hp
    letI : NeZero p := ⟨hp.ne_zero⟩
    intro _ χ hχ ho
    have ho1 : orderOf χ ∣ 1 := by simpa [rejected, realize] using ho
    exact (nonprincipal_not_order_dvd_one χ hχ ho1).elim
  obtain ⟨q, hq, hlt, ho⟩ := h hL 3 (by decide) (by decide)
  have hz := prime_residue_order_ne_zero Nat.prime_three hq hlt
  exact hz (by simpa [rejected, realize] using ho)
def family : Registration arena (type_of% @erdos985_of_finiteHeight) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@erdos985_of_finiteHeight, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence
def compatibilityFamily : Registration arena (type_of% @erdos985_of_GRH) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@erdos985_of_GRH, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence
end All

#print axioms Large.family
#print axioms All.family
#print axioms All.compatibilityFamily
#print axioms erdos985_large_prime
#print axioms erdos985_of_GRH
#print axioms erdos985_of_finiteHeight
end Reg.D5.S3.Arith.PrimitiveRoot.Erdos985
