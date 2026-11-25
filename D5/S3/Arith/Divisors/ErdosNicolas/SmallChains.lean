/- GID: D5/S3/Arith/Divisors/ErdosNicolas/SmallChains
   generality: I
   mirror-B: none(waiver:proof-helper-in-main-import-closure)
   mirror-E: none(waiver:unbounded-combinatorial-proof)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Arith/Divisors/ErdosNicolas/Main.erdos_nicolas; premises=D5/S3/Arith/Divisors/ErdosNicolas/SmallChains.small_chain_test
   digest: Four finite short-chain comparisons and their divisor-average consequence. -/

import D5.S3.Arith.Divisors.ErdosNicolas.ChainBound
import D5.S3.Arith.Divisors.ErdosNicolas.Residual
import D5.S3.Arith.Divisors.ErdosNicolas.Cutoffs

/-! Exact pair and triple tables for the four remaining small-prime reductions. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.ErdosNicolas

open Finset

/-- Exponent reduced by the four small-modulus chain tables. -/
def smallChainExponent (p : ℕ) : ℕ := if p = 5 then 4 else if p = 7 then 3 else 2

/-- Tent lengths in the four small-modulus chain tables. -/
def smallChainLength (p : ℕ) : ℕ :=
  if p = 5 then 10 else if p = 7 then 7 else if p = 11 then 22 else 13

/-- Maximum of the two-term and three-term averages in each small-modulus table. -/
def smallChainResidual (p : ℕ) : ℚ :=
  if p = 5 then 5939 / 7560 else if p = 7 then 53 / 105 else
  if p = 11 then 64123 / 90090 else 2081 / 3432

private def shortProfile (p L r : ℕ) : ℚ :=
  w L r + w L (p - r) + if p < L then w L (p + r) + w L (2 * p - r) else 0

private theorem shortProfile_eq {p L r : ℕ} (hL : L = p ∨ L = 2 * p)
    (hr : 0 < r) (hrp : r < p) : shortProfile p L r = f p L r := by
  rcases hL with rfl | rfl
  · simp only [shortProfile, lt_self_iff_false, ite_false, add_zero]
    exact ((f_eq_two_terms hrp.le).2 (Or.inr (by omega))).symm
  · have hp : p < 2 * p := by omega
    simp only [shortProfile, hp, ite_true]
    rw [f_eq_four_terms hrp.le]
    ring

private def ShortChainTable (p L : ℕ) (c : ℚ) : Prop :=
  ∀ r q : Fin p, 0 < r.val → 1 < q.val → q.val < p - 1 →
    shortProfile p L r.val + shortProfile p L (r.val * q.val % p) ≤ 2 * c ∧
    shortProfile p L r.val + shortProfile p L (r.val * q.val % p) +
      shortProfile p L (r.val * q.val ^ 2 % p) ≤ 3 * c

private def chainDenominator (p : ℕ) : ℕ :=
  if p = 5 then 7560 else if p = 7 then 420 else
  if p = 11 then 232792560 else 360360

private def chainNumerator (p : ℕ) : ℕ :=
  if p = 5 then 5939 else if p = 7 then 212 else
  if p = 11 then 165693832 else 218505

private def scaledProfile (p r : ℕ) : ℕ :=
  if p = 5 then [756, 7014, 3789, 3789, 7014].getD r 0 else
  if p = 7 then [0, 310, 114, 65, 65, 114, 310].getD r 0 else
  if p = 11 then
    [10581480, 223067676, 108319988, 72087990, 56417764, 50111607,
      50111607, 56417764, 72087990, 108319988, 223067676].getD r 0 else
    [0, 307230, 129780, 72996, 46970, 33957, 28380, 28380,
      33957, 46970, 72996, 129780, 307230].getD r 0

private theorem scaledProfile_eq {p r : ℕ}
    (hp : p ∈ ({5, 7, 11, 13} : Finset ℕ)) (hrp : r < p) :
    shortProfile p (smallChainLength p) r =
      (scaledProfile p r : ℚ) / chainDenominator p := by
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl <;> interval_cases r <;>
    norm_num [shortProfile, smallChainLength, w, scaledProfile, chainDenominator,
      List.getD]

private def ShortIntegerTable (p : ℕ) : Prop :=
  ∀ r q : Fin p, 0 < r.val → 1 < q.val → q.val < p - 1 →
    scaledProfile p r.val + scaledProfile p (r.val * q.val % p) ≤
        2 * chainNumerator p ∧
      scaledProfile p r.val + scaledProfile p (r.val * q.val % p) +
          scaledProfile p (r.val * q.val ^ 2 % p) ≤ 3 * chainNumerator p

private theorem short_table_five : ShortIntegerTable 5 := by
  unfold ShortIntegerTable
  decide

private theorem short_table_seven : ShortIntegerTable 7 := by
  unfold ShortIntegerTable
  decide

private theorem short_table_eleven : ShortIntegerTable 11 := by
  unfold ShortIntegerTable
  decide

private theorem short_table_thirteen : ShortIntegerTable 13 := by
  unfold ShortIntegerTable
  decide

private theorem small_chain_integer_table {p : ℕ}
    (hp : p ∈ ({5, 7, 11, 13} : Finset ℕ)) : ShortIntegerTable p := by
  simp only [mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact short_table_five
  · exact short_table_seven
  · exact short_table_eleven
  · exact short_table_thirteen

private theorem small_chain_table {p : ℕ} (hp : p ∈ ({5, 7, 11, 13} : Finset ℕ)) :
    ShortChainTable p (smallChainLength p) (smallChainResidual p) := by
  have hden : (0 : ℚ) < chainDenominator p := by
    unfold chainDenominator
    split_ifs <;> norm_num
  have hpn : 0 < p := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hc : smallChainResidual p =
      (chainNumerator p : ℚ) / chainDenominator p := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      norm_num [smallChainResidual, chainNumerator, chainDenominator]
  intro r q hr hq hqtop
  have ht := small_chain_integer_table hp r q hr hq hqtop
  rw [scaledProfile_eq hp r.isLt, scaledProfile_eq hp (Nat.mod_lt _ hpn),
    scaledProfile_eq hp (Nat.mod_lt _ hpn), hc]
  constructor
  · have h : (scaledProfile p r.val : ℚ) +
        scaledProfile p (r.val * q.val % p) ≤ 2 * chainNumerator p := by
      exact_mod_cast ht.1
    convert div_le_div_of_nonneg_right h hden.le using 1 <;> ring
  · have h : (scaledProfile p r.val : ℚ) +
        scaledProfile p (r.val * q.val % p) + scaledProfile p (r.val * q.val ^ 2 % p) ≤
          3 * chainNumerator p := by exact_mod_cast ht.2
    convert div_le_div_of_nonneg_right h hden.le using 1 <;> ring

/-- All four small-prime rational tests propagate to every larger exponent. -/
theorem small_chain_test {p a : ℕ} (hp : p ∈ ({5, 7, 11, 13} : Finset ℕ))
    (ha : smallChainExponent p ≤ a) :
    KernelTest a p (smallChainLength p) 1 1 (smallChainResidual p) := by
  have hbase : KernelTest (smallChainExponent p) p (smallChainLength p)
      1 1 (smallChainResidual p) := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;>
      norm_num [smallChainExponent, smallChainLength, smallChainResidual,
        KernelTest, criterionGap]
  have he : 0 < smallChainExponent p := by
    unfold smallChainExponent
    split_ifs <;> norm_num
  have hL : (0 : ℚ) < smallChainLength p := by
    unfold smallChainLength
    split_ifs <;> norm_num
  have hF : 0 ≤ (1 : ℚ) + smallChainResidual p - 1 := by
    unfold smallChainResidual
    split_ifs <;> norm_num
  have hpn : 0 < p := by
    simp only [mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> norm_num
  have hpq : (0 : ℚ) < p := by exact_mod_cast hpn
  exact kernelTest_exponent_mono he ha hF hbase

/-- The finite pair/triple tables control every divisor of a `p`-free integer. -/
theorem small_chain_average {p q m : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hps : p ∈ ({5, 7, 11, 13} : Finset ℕ)) (hqm : q ∣ m) (hpm : ¬p ∣ m)
    (hq₁ : q % p ≠ 1) (hqMinus : q % p ≠ p - 1) :
    (∑ d ∈ m.divisors, f p (smallChainLength p) (d % p)) ≤
      smallChainResidual p * (m.divisors.card : ℚ) := by
  have hqr : 0 < q % p := by
    apply Nat.pos_of_ne_zero
    intro hz
    exact hpm ((Nat.dvd_of_mod_eq_zero hz).trans hqm)
  have hqhi : q % p < p := Nat.mod_lt _ hp.pos
  have hqlo : 1 < q % p := by omega
  have hqtop : q % p < p - 1 := by omega
  have hL : smallChainLength p = p ∨ smallChainLength p = 2 * p := by
    simp only [mem_insert, mem_singleton] at hps
    rcases hps with rfl | rfl | rfl | rfl <;> norm_num [smallChainLength]
  have ht := small_chain_table hps
  have hbound (r : ℕ) (hr : ¬p ∣ r) :
      f p (smallChainLength p) (r % p) +
          f p (smallChainLength p) ((q * r) % p) ≤ 2 * smallChainResidual p ∧
      f p (smallChainLength p) (r % p) +
          f p (smallChainLength p) ((q * r) % p) +
          f p (smallChainLength p) ((q ^ 2 * r) % p) ≤ 3 * smallChainResidual p := by
    have hrlo : 0 < r % p := by
      apply Nat.pos_of_ne_zero
      exact fun hz => hr (Nat.dvd_of_mod_eq_zero hz)
    have hrhi : r % p < p := Nat.mod_lt _ hp.pos
    have hpq : ¬p ∣ q := fun h => hpm (h.trans hqm)
    have hr₂ : ¬p ∣ q * r := hp.not_dvd_mul hpq hr
    have hr₃ : ¬p ∣ q ^ 2 * r :=
      hp.not_dvd_mul (fun h => hpq (hp.dvd_of_dvd_pow h)) hr
    have hr₂lo : 0 < (q * r) % p := Nat.pos_of_ne_zero
      (fun hz => hr₂ (Nat.dvd_of_mod_eq_zero hz))
    have hr₃lo : 0 < (q ^ 2 * r) % p := Nat.pos_of_ne_zero
      (fun hz => hr₃ (Nat.dvd_of_mod_eq_zero hz))
    have he₂ : r % p * (q % p) % p = (q * r) % p := by
      rw [← Nat.mul_mod, Nat.mul_comm]
    have he₃ : r % p * (q % p) ^ 2 % p = (q ^ 2 * r) % p := by
      simp only [Nat.mul_mod, Nat.pow_mod, Nat.mod_mod, Nat.mul_comm]
    have hh := ht ⟨r % p, hrhi⟩ ⟨q % p, hqhi⟩ hrlo hqlo hqtop
    change shortProfile p (smallChainLength p) (r % p) +
        shortProfile p (smallChainLength p) (r % p * (q % p) % p) ≤ _ ∧
      shortProfile p (smallChainLength p) (r % p) +
          shortProfile p (smallChainLength p) (r % p * (q % p) % p) +
          shortProfile p (smallChainLength p) (r % p * (q % p) ^ 2 % p) ≤ _ at hh
    rw [he₂, he₃, shortProfile_eq hL hrlo hrhi,
      shortProfile_eq hL hr₂lo (Nat.mod_lt _ hp.pos),
      shortProfile_eq hL hr₃lo (Nat.mod_lt _ hp.pos)] at hh
    exact hh
  exact divisor_chain_average_coprime (fun _ => Or.inr hq) hqm (fun _ => hpm)
    (fun r => f p (smallChainLength p) (r % p)) (smallChainResidual p)
    (fun r _ hr => (hbound r hr).1) (fun r _ hr => (hbound r hr).2)

#print axioms small_chain_test
#print axioms small_chain_average

end D5.S3.Arith.ErdosNicolas
