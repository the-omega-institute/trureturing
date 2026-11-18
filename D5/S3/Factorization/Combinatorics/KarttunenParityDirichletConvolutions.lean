/- GID: D5/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/KarttunenParityDirichletConvolutions
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The two A369255 Dirichlet convolutions. -/

/- result
   proof_shape: content
   The proof counts coprime factor pairs by assigning their prime-power blocks
   and uses a finite-product induction to bound the common convolution.
   escape_witness: none
   admission_basis: open-problem-resolution (#21450; Proved)
   Direct frozen dependencies:
   D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.h
     sha256:1421c21143dc90e96653fb7f4bbf3e3dd41e3d3626e393b91908f03247
   D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.h.eq_1
     sha256:4d0795298500ab5dc1aac3f64f91645ce9a1ba76bb0e79afd1b73d5507792be0
   D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution.tau
     sha256:ee2f119ab0adf9a923c366e785dbac778b2cccb9fb5af312c19e9c49949cfc97
   D5/S3/Arith/SchulteLiouvilleCubeMobius.liftPow
     sha256:ff34cf45d3c056ce026578c609469b4c33d6a44d4825da0c39110a61ee1a998c
   D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.FactorTuple
     sha256:46959b2558bafc37e27c14c0aec7ec9365786c36d646e26f8d0844b37a5830b9
   D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.PrimeAllocation
     sha256:7af74a7f3debca6ded95fadb804fabf1d4a2aebd781206dea2f59e40a13345bf
   D5/S3/Factorization/Combinatorics/StrictDivisorChainCount.factorTupleEquivAllocation
     sha256:df27988fb88ad34aabb8b152d09b53ed7937b5a50200075caca7e5095a131b1a
   The claim inlines the A140773 divisor sum, and hfun_literal identifies it with
   the frozen A140773 definition used in the proof.
   Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21636
-/

import D5.S3.Factorization.Combinatorics.StrictDivisorChainCount
import D5.S3.Arith.SchulteLiouvilleCubeMobius
import D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
import Mathlib.Algebra.BigOperators.Fin

set_option maxRecDepth 2048
open scoped BigOperators ArithmeticFunction.zeta
namespace D5.S3.Factorization.Combinatorics.KarttunenParityDirichletConvolutions
open D5.S3.Arith D5.S3.Arith.Divisors

noncomputable section
/-- A038548: positive divisors at most the real square root of n. -/
def g (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => d * d ≤ n)).card

/-- A007875: unordered coprime positive factor pairs, including (1,1). -/
def A (n : ℕ) : ℕ :=
  (n.divisorsAntidiagonal.filter (fun rs => rs.1 ≤ rs.2 ∧ rs.1.Coprime rs.2)).card

/-- A219009: coefficients of zeta(4s)/zeta(s), as its published Möbius sum.
For positive n, every d with d^4 dividing n is a positive divisor of n. -/
def B (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, if d ^ 4 ∣ n then ArithmeticFunction.moebius (n / d ^ 4) else 0

/-- A355837: the published multiplicative prime-power prescription; the empty product is 1. -/
noncomputable def C (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors,
    (2 : ℤ) * ((n.factorization p % 2 : ℕ) : ℤ) *
      (-1 : ℤ) ^ ((n.factorization p + 1) / 2)

/-- Both unnumbered convolution conjectures in the A369255 formula block. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((((∑ m ∈ n.divisors, g m) % 2 : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, (A d : ℤ) * B (n / d)) ∧
    ((((∑ m ∈ n.divisors, g m) % 2 : ℕ) : ℤ) =
      ∑ d ∈ n.divisors, ((∑ m ∈ d.divisors, g m : ℕ) : ℤ) * C (n / d))

private theorem pair_count (s : Finset (ℕ × ℕ))
    (hs : ∀ x, x.swap ∈ s ↔ x ∈ s) :
    2 * (s.filter (fun x => x.1 ≤ x.2)).card =
      s.card + (s.filter (fun x => x.1 = x.2)).card := by
  classical
  have hswap : (s.filter (fun x => x.1 < x.2)).card =
      (s.filter (fun x => x.2 < x.1)).card := by
    apply Finset.card_bij (fun x _ => x.swap)
    · intro x hx
      simpa only [Finset.mem_filter, Prod.fst_swap, Prod.snd_swap, hs] using hx
    · intro x _ y _ h
      exact Prod.swap_injective h
    · intro x hx
      exact ⟨x.swap, by simpa only [Finset.mem_filter, Prod.fst_swap, Prod.snd_swap, hs] using hx,
        Prod.swap_swap x⟩
  have hpart := Finset.card_filter_add_card_filter_not (s := s) (fun x => x.1 ≤ x.2)
  have hle := Finset.card_filter_add_card_filter_not
    (s := s.filter (fun x => x.1 ≤ x.2)) (fun x => x.1 = x.2)
  have h1 : ((s.filter (fun x => x.1 ≤ x.2)).filter (fun x => x.1 = x.2)) =
      s.filter (fun x => x.1 = x.2) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx,hle⟩,he⟩
      exact ⟨hx,he⟩
    · rintro ⟨hx,he⟩
      exact ⟨⟨hx,Nat.le_of_eq he⟩,he⟩
  have h2 : ((s.filter (fun x => x.1 ≤ x.2)).filter (fun x => ¬ x.1 = x.2)) =
      s.filter (fun x => x.1 < x.2) := by
    apply Finset.ext
    intro x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hx,hle⟩,hne⟩
      exact ⟨hx,lt_of_le_of_ne hle hne⟩
    · rintro ⟨hx,hlt⟩
      exact ⟨⟨hx,hlt.le⟩,hlt.ne⟩
  simp only [not_le] at hpart
  rw [h1, h2] at hle
  omega

private theorem g_pair (n : ℕ) : g n =
    (n.divisorsAntidiagonal.filter (fun x => x.1 ≤ x.2)).card := by
  classical
  unfold g
  apply Finset.card_bij (fun d _ => (d, n / d))
  · intro d hd
    obtain ⟨hd, hsq⟩ := Finset.mem_filter.mp hd
    have hp := Nat.pos_of_mem_divisors hd
    apply Finset.mem_filter.mpr
    exact ⟨Nat.mem_divisorsAntidiagonal.mpr
      ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), Nat.ne_zero_of_mem_divisors hd⟩,
      (Nat.le_div_iff_mul_le hp).mpr (by simpa [mul_comm] using hsq)⟩
  · intro d _ e _ h
    exact congrArg Prod.fst h
  · rintro ⟨r, s⟩ hx
    obtain ⟨hx, hrs⟩ := Finset.mem_filter.mp hx
    obtain ⟨hprod, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    have hr : 0 < r := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx)
    refine ⟨r, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, ?_⟩, ?_⟩
    · exact ⟨s, hprod.symm⟩
    · nlinarith
    · simp only [Prod.mk.injEq, true_and]
      rw [← hprod, Nat.mul_div_right _ hr]

private theorem liftPow_apply_pow (k : ℕ) (hk : k ≠ 0)
    (f : ArithmeticFunction ℤ) (m : ℕ) :
    SchulteLiouvilleCubeMobius.liftPow k f (m ^ k) = f m := by
  simp [SchulteLiouvilleCubeMobius.liftPow, Nat.floorRoot_pow_self hk]

private theorem liftPow_apply_nonpow (k : ℕ) (f : ArithmeticFunction ℤ) (n : ℕ)
    (hn : ¬ ∃ m, m ^ k = n) : SchulteLiouvilleCubeMobius.liftPow k f n = 0 := by
  simp [SchulteLiouvilleCubeMobius.liftPow,
    show (Nat.floorRoot k n) ^ k ≠ n from fun h => hn ⟨_, h⟩]

private theorem diagonal_count (n : ℕ) (hn : n ≠ 0) :
    ((n.divisorsAntidiagonal.filter (fun x => x.1 = x.2)).card : ℤ) = (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) n := by
  classical
  by_cases h : IsSquare n
  · obtain ⟨a, ha⟩ := h
    have hf : n.divisorsAntidiagonal.filter (fun x => x.1 = x.2) = {(a,a)} := by
      ext x
      obtain ⟨r,s⟩ := x
      simp only [Finset.mem_filter, Nat.mem_divisorsAntidiagonal, Finset.mem_singleton,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨he, _⟩, rfl⟩
        have : r = a := by nlinarith
        exact ⟨this, this⟩
      · rintro ⟨rfl,rfl⟩
        exact ⟨⟨ha.symm, hn⟩, rfl⟩
    rw [hf]
    rw [show n = a ^ 2 by simpa only [pow_two] using ha,
      liftPow_apply_pow 2 (by decide)]
    have ha0 : a ≠ 0 := fun h => hn (by simp [ha, h])
    simp [ArithmeticFunction.natCoe_apply, ha0]
  · have hf : n.divisorsAntidiagonal.filter (fun x => x.1 = x.2) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
      apply h
      exact ⟨x.1, by rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, he]⟩
    rw [hf, liftPow_apply_nonpow _ _ n (fun ⟨a, ha⟩ => h ⟨a, by simpa [pow_two] using ha.symm⟩)]
    simp

private theorem two_g (n : ℕ) (hn : n ≠ 0) :
    2 * (g n : ℤ) = (n.divisors.card : ℤ) + (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) n := by
  have h := pair_count n.divisorsAntidiagonal (fun _ => Nat.swap_mem_divisorsAntidiagonal)
  rw [← g_pair] at h
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    simpa only [Finset.card_map] using
      (congrArg Finset.card (Nat.map_div_right_divisors (n := n))).symm
  rw [hc] at h
  have hz := congrArg (fun z : ℕ => (z : ℤ)) h
  push_cast at hz
  rw [diagonal_count n hn] at hz
  exact hz

private theorem two_A (n : ℕ) :
    2 * (A n : ℤ) =
      ((n.divisorsAntidiagonal.filter (fun x => x.1.Coprime x.2)).card : ℤ) +
      (if n = 1 then 1 else 0) := by
  classical
  let s := n.divisorsAntidiagonal.filter (fun x => x.1.Coprime x.2)
  have hs : ∀ x, x.swap ∈ s ↔ x ∈ s := by
    intro x
    simp only [s, Finset.mem_filter, Nat.swap_mem_divisorsAntidiagonal,
      Prod.fst_swap, Prod.snd_swap, Nat.coprime_comm]
  have hpair := pair_count s hs
  have hle : s.filter (fun x => x.1 ≤ x.2) =
      n.divisorsAntidiagonal.filter (fun x => x.1 ≤ x.2 ∧ x.1.Coprime x.2) := by
    ext x
    simp only [s, Finset.mem_filter]
    constructor
    · rintro ⟨⟨h1,h2⟩,h3⟩; exact ⟨h1,h3,h2⟩
    · rintro ⟨h1,h2,h3⟩; exact ⟨⟨h1,h3⟩,h2⟩
  have hdiag : ((s.filter (fun x => x.1 = x.2)).card : ℤ) =
      (if n = 1 then 1 else 0) := by
    by_cases hn : n = 1
    · subst n
      norm_num [s, Finset.filter_singleton]
    · have hempty : s.filter (fun x => x.1 = x.2) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨⟨hx,hc⟩, he⟩ := (by simpa only [s, Finset.mem_filter] using hx)
        have h1 : x.1 = 1 := by
          rw [← he] at hc
          simpa only [Nat.coprime_self] using hc
        apply hn
        rw [← (Nat.mem_divisorsAntidiagonal.mp hx).1, ← he, h1]
      simp [hempty, hn]
  rw [hle] at hpair
  have hz := congrArg (fun z : ℕ => (z : ℤ)) hpair
  push_cast at hz
  rw [hdiag] at hz
  exact hz

private def hfun : ArithmeticFunction ℤ :=
  ⟨OeisA252505FourthPowerFreeConvolution.h,
    by simp [OeisA252505FourthPowerFreeConvolution.h]⟩

private theorem g_eq_ceil (n : ℕ) :
    (g n : ℤ) = (⌈(OeisA252505FourthPowerFreeConvolution.tau n : ℚ) / 2⌉₊ : ℤ) := by
  by_cases hn : n = 0
  · subst n
    simp [g, OeisA252505FourthPowerFreeConvolution.tau]
  have hg := two_g n hn
  have hb : (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) n = 0 ∨
      (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) n = 1 := by
    by_cases he : ∃ m : ℕ, m ^ 2 = n
    · obtain ⟨m, rfl⟩ := he
      right
      rw [liftPow_apply_pow 2 (by decide)]
      simp [ArithmeticFunction.natCoe_apply, ne_zero_pow (by decide : 2 ≠ 0) hn]
    · exact Or.inl (liftPow_apply_nonpow 2 _ _ he)
  rw [Int.natCast_ceil_eq_ceil (by positivity)]
  have hm := Rat.ceil_natCast_div_natCast (OeisA252505FourthPowerFreeConvolution.tau n) 2
  norm_num only [Nat.cast_ofNat] at hm
  rw [hm]
  change (g n : ℤ) = -(-(n.divisors.card : ℤ) / 2)
  rcases hb with h | h <;> omega

private theorem hfun_literal (n : ℕ) :
    hfun n = ((∑ d ∈ n.divisors, g d : ℕ) : ℤ) := by
  change OeisA252505FourthPowerFreeConvolution.h n = _
  rw [OeisA252505FourthPowerFreeConvolution.h, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun d _ => (g_eq_ceil d).symm)

private theorem tau_value (n : ℕ) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2) n = n.divisors.card := by
  rw [pow_two, ArithmeticFunction.coe_zeta_mul_apply]
  simp only [ArithmeticFunction.natCoe_apply]
  simp only [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  apply Finset.sum_congr rfl
  intro d hd
  rw [ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne', Nat.cast_one]

private theorem two_hfun : (2 : ℤ) • hfun =
    (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3 +
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  simp only [two_smul, ArithmeticFunction.add_apply]
  rw [← two_mul,
    show (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 3 =
      (ArithmeticFunction.zeta : ArithmeticFunction ℤ) *
        (ArithmeticFunction.zeta : ArithmeticFunction ℤ) ^ 2 by ring,
    ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_apply]
  rw [hfun_literal, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [tau_value]
  exact two_g d (Nat.pos_of_mem_divisors hd).ne'

attribute [local instance] Classical.propDecidable

/-- Multiplicative function with a uniform local exponent prescription. -/
private def E (f : ℕ → ℤ) : ArithmeticFunction ℤ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (fun _ k => f k), by simp⟩

private theorem E_isMultiplicative (f : ℕ → ℤ) : (E f).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp [E]
  · intro m n hm hn hmn
    simp only [E, ArithmeticFunction.coe_mk, ite_eq_right hm, ite_eq_right hn,
      ite_eq_right (mul_ne_zero hm hn), Nat.factorization_mul_of_coprime hmn]
    exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors _

private theorem E_prime_pow (f : ℕ → ℤ) (hf : f 0 = 1)
    (p e : ℕ) (hp : p.Prime) : E f (p ^ e) = f e := by
  simp [E, hp.ne_zero, hp.factorization_pow,
    Finsupp.prod_single_index, hf]

private theorem E_apply (f : ℕ → ℤ) (n : ℕ) (hn : n ≠ 0) :
    E f n = ∏ p ∈ n.primeFactors, f (n.factorization p) := by
  simpa only [E, ArithmeticFunction.coe_mk, ite_eq_right hn] using
    (Nat.prod_factorization_eq_prod_primeFactors (n := n) (fun _ k => f k))

private theorem liftPow_isMultiplicative (k : ℕ) (hk : k ≠ 0) (f : ArithmeticFunction ℤ)
    (hf : f.IsMultiplicative) : (SchulteLiouvilleCubeMobius.liftPow k f).IsMultiplicative := by
  refine ⟨?_, ?_⟩
  · simpa using (liftPow_apply_pow k hk f 1).trans hf.1
  intro a b hab
  by_cases ha : ∃ r, r ^ k = a
  · obtain ⟨r, rfl⟩ := ha
    by_cases hb : ∃ s, s ^ k = b
    · obtain ⟨s, rfl⟩ := hb
      rw [← mul_pow, liftPow_apply_pow k hk, liftPow_apply_pow k hk,
        liftPow_apply_pow k hk]
      exact hf.2 ((Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk) _ _).mp
        ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hk) _ _).mp hab))
    · rw [liftPow_apply_nonpow k f b hb, mul_zero]
      apply liftPow_apply_nonpow
      rintro ⟨s, hs⟩
      obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow
        (show IsUnit (gcd b (r ^ k)) from by
          change IsUnit (Nat.gcd b (r ^ k))
          rw [hab.symm.gcd_eq_one]
          exact isUnit_one)
        (show b * r ^ k = s ^ k from (mul_comm ..).trans hs.symm)
      exact hb ⟨t, ht.symm⟩
  · rw [liftPow_apply_nonpow k f a ha, zero_mul]
    apply liftPow_apply_nonpow
    rintro ⟨s, hs⟩
    obtain ⟨t, ht⟩ := exists_eq_pow_of_mul_eq_pow
      (show IsUnit (gcd a b) from by
        change IsUnit (Nat.gcd a b)
        rw [hab.gcd_eq_one]
        exact isUnit_one) hs.symm
    exact ha ⟨t, ht.symm⟩

private theorem liftPow_prime_pow (k : ℕ) (hk : k ≠ 0) (f : ArithmeticFunction ℤ)
    (p e : ℕ) (hp : p.Prime) :
    SchulteLiouvilleCubeMobius.liftPow k f (p ^ e) = if k ∣ e then f (p ^ (e / k)) else 0 := by
  by_cases he : k ∣ e
  · rw [ite_eq_left he]
    have hpow : p ^ e = (p ^ (e / k)) ^ k := by
      rw [← pow_mul, Nat.div_mul_cancel he]
    rw [hpow, liftPow_apply_pow k hk]
  · rw [ite_eq_right he]
    apply liftPow_apply_nonpow
    rintro ⟨m, hm⟩
    have hmdvd : m ∣ p ^ e := hm ▸ dvd_pow_self m hk
    obtain ⟨i, hi, hmi⟩ := (Nat.dvd_prime_pow hp).mp hmdvd
    have hie : i * k = e := Nat.pow_right_injective hp.one_lt (by
      change p ^ (i * k) = p ^ e
      rw [pow_mul, ← hmi, hm])
    exact he (hie ▸ dvd_mul_left k i)

private theorem Q_isMultiplicative (k : ℕ) (hk : k ≠ 0) : ((SchulteLiouvilleCubeMobius.liftPow k ArithmeticFunction.zeta)).IsMultiplicative :=
  liftPow_isMultiplicative k hk _ ArithmeticFunction.isMultiplicative_zeta.natCast
private theorem M2_isMultiplicative : (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius).IsMultiplicative :=
  liftPow_isMultiplicative 2 (by decide) _ ArithmeticFunction.isMultiplicative_moebius
private theorem W_isMultiplicative : (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius).IsMultiplicative :=
  ArithmeticFunction.isMultiplicative_moebius.pmul ArithmeticFunction.isMultiplicative_moebius

private theorem Q_prime_pow (k : ℕ) (hk : k ≠ 0) (p e : ℕ) (hp : p.Prime) :
    (SchulteLiouvilleCubeMobius.liftPow k ArithmeticFunction.zeta) (p ^ e) = if k ∣ e then 1 else 0 := by
  rw [liftPow_prime_pow k hk _ p e hp]
  simp [ArithmeticFunction.natCoe_apply, hp.ne_zero]

private theorem M2_prime_pow (p e : ℕ) (hp : p.Prime) :
    (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) (p ^ e) = if e = 0 then 1 else if e = 2 then -1 else 0 := by
  rw [liftPow_prime_pow 2 (by decide) _ p e hp]
  by_cases he : e = 0
  · subst e
    simp
  by_cases h2 : e = 2
  · subst e
    simp [ArithmeticFunction.moebius_apply_prime hp]
  by_cases hd : 2 ∣ e
  · have h0 : e / 2 ≠ 0 := by omega
    have h1 : e / 2 ≠ 1 := by omega
    simp [hd, he, h2, ArithmeticFunction.moebius_apply_prime_pow hp h0, h1]
  · simp [hd, he, h2]

private theorem convolution_prime_pow (f g : ArithmeticFunction ℤ) (p e : ℕ) (hp : p.Prime) :
    (f * g) (p ^ e) = ∑ i ∈ Finset.range (e + 1), f (p ^ i) * g (p ^ (e - i)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => f a * g b), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro i hi
  have hie : i ≤ e := by simpa using Finset.mem_range.mp hi
  have hdiv : p ^ e / p ^ i = p ^ (e - i) := Nat.pow_div hie hp.pos
  rw [hdiv]

private theorem Q_value (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) :
    (SchulteLiouvilleCubeMobius.liftPow k ArithmeticFunction.zeta) n = if ∃ d : ℕ, d ^ k = n then 1 else 0 := by
  classical
  by_cases h : ∃ d : ℕ, d ^ k = n
  · obtain ⟨d, hd⟩ := h
    rw [ite_eq_left ⟨d, hd⟩, ← hd, liftPow_apply_pow k hk]
    simp [ArithmeticFunction.natCoe_apply, ne_zero_pow hk (show d ^ k ≠ 0 from hd.symm ▸ hn)]
  · rw [ite_eq_right h, liftPow_apply_nonpow _ _ _ h]

private theorem convolution_Q (f : ArithmeticFunction ℤ) (k n : ℕ) (hk : 0 < k)
    (hn : n ≠ 0) :
    (f * (SchulteLiouvilleCubeMobius.liftPow k ArithmeticFunction.zeta)) n = ∑ d ∈ n.divisors, if d ^ k ∣ n then f (n / d ^ k) else 0 := by
  classical
  calc
    _ = ∑ t ∈ n.divisors, if ∃ d : ℕ, d ^ k = t then f (n / t) else 0 := by
      rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => f a * (SchulteLiouvilleCubeMobius.liftPow k ArithmeticFunction.zeta) b)]
      apply Finset.sum_congr rfl
      intro t ht
      rw [Q_value k t hk.ne' (Nat.pos_of_mem_divisors ht).ne']
      split <;> simp
    _ = ∑ t ∈ n.divisors.filter (fun t => ∃ d : ℕ, d ^ k = t), f (n / t) := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ n.divisors.filter (fun d => d ^ k ∣ n), f (n / d ^ k) := by
      symm
      apply Finset.sum_bij (fun d _ => d ^ k)
      · intro d hd
        obtain ⟨hd,hpow⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hpow,hn⟩, ⟨d,rfl⟩⟩
      · intro d hd e he h
        exact Nat.pow_left_injective hk.ne' h
      · intro t ht
        obtain ⟨ht,⟨d,rfl⟩⟩ := Finset.mem_filter.mp ht
        have hpow := Nat.dvd_of_mem_divisors ht
        have hdn : d ∣ n := (dvd_pow_self d hk.ne').trans hpow
        exact ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdn,hn⟩, hpow⟩, rfl⟩
      · intro d hd; rfl
    _ = _ := by rw [Finset.sum_filter]

private theorem M2_prime_pow_delta (p e : ℕ) (hp : p.Prime) :
    (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) (p ^ e) = (if e = 0 then 1 else 0) - (if e = 2 then 1 else 0) := by
  rw [M2_prime_pow p e hp]
  by_cases h0 : e = 0 <;> by_cases h2 : e = 2 <;> simp_all

private theorem Q_two_mul_M2 : (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) = 1 := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((Q_isMultiplicative 2 (by decide)).mul M2_isMultiplicative) _
    ArithmeticFunction.isMultiplicative_one).mpr
  intro p e hp
  rw [mul_comm, convolution_prime_pow _ _ p e hp]
  simp_rw [Q_prime_pow 2 (by decide) _ _ hp, M2_prime_pow_delta _ _ hp, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ]
  rw [ArithmeticFunction.one_apply]
  by_cases he : e = 0
  · subst e; simp
  · have hpow : p ^ e ≠ 1 := by
      have : 1 < p ^ e := Nat.one_lt_pow he hp.one_lt
      omega
    rw [ite_eq_right hpow]
    by_cases h2 : 2 < e + 1
    · simp only [ite_eq_left h2]
      by_cases hd : 2 ∣ e
      · have hd' : 2 ∣ e - 2 := by omega
        simp [hd, hd']
      · have hd' : ¬2 ∣ e - 2 := by omega
        simp [hd, hd']
    · have : e = 1 := by omega
      subst e; simp

private def D2 : ArithmeticFunction ℤ := E (fun e => (if e = 0 then 1 else 0) + (if e = 2 then 1 else 0))
private def cphi (e : ℕ) : ℤ :=
  if e = 0 then 1 else 2 * (e % 2 : ℕ) * (-1 : ℤ) ^ ((e + 1) / 2)
private def cf : ArithmeticFunction ℤ := E cphi

private theorem D2_isMultiplicative : D2.IsMultiplicative := E_isMultiplicative _
private theorem cf_isMultiplicative : cf.IsMultiplicative := E_isMultiplicative _

private theorem D2_prime_pow (p e : ℕ) (hp : p.Prime) :
    D2 (p ^ e) = (if e = 0 then 1 else 0) + (if e = 2 then 1 else 0) :=
  E_prime_pow _ (by norm_num) p e hp
private theorem cf_prime_pow (p e : ℕ) (hp : p.Prime) : cf (p ^ e) = cphi e :=
  E_prime_pow _ (by simp [cphi]) p e hp

private theorem cphi_rec (e : ℕ) (he : 3 ≤ e) : cphi e + cphi (e - 2) = 0 := by
  have h0 : e ≠ 0 := Nat.ne_zero_of_lt he
  have h2 : e - 2 ≠ 0 := Nat.sub_ne_zero_iff_lt.mpr he
  simp only [cphi, ite_eq_right h0, ite_eq_right h2]
  have hmod : (e - 2) % 2 = e % 2 := by omega
  have hdiv : (e + 1) / 2 = (e - 2 + 1) / 2 + 1 := by omega
  rw [hmod, hdiv, pow_succ]
  ring

private theorem Q_four_mul_D2 : (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) * D2 = (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((Q_isMultiplicative 4 (by decide)).mul D2_isMultiplicative) _ (Q_isMultiplicative 2 (by decide))).mpr
  intro p e hp
  rw [mul_comm, convolution_prime_pow _ _ p e hp]
  simp_rw [D2_prime_pow _ _ hp, Q_prime_pow 4 (by decide) _ _ hp, Q_prime_pow 2 (by decide) _ _ hp, add_mul,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, Nat.sub_zero]
  by_cases h : 2 < e + 1
  · simp only [ite_eq_left h]
    split_ifs <;> omega
  · have : e = 0 ∨ e = 1 := by omega
    rcases this with rfl | rfl <;> norm_num

private theorem moebius_prime_pow_delta (p e : ℕ) (hp : p.Prime) :
    ArithmeticFunction.moebius (p ^ e) =
      (if e = 0 then 1 else 0) - (if e = 1 then 1 else 0) := by
  by_cases h : e = 0
  · subst e; simp
  · rw [ArithmeticFunction.moebius_apply_prime_pow hp h]
    by_cases h1 : e = 1 <;> simp [h,h1]

private theorem mu_squared_prime_pow (p e : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.moebius * ArithmeticFunction.moebius) (p ^ e) =
      (if e = 0 then 1 else 0) - (if e = 1 then 2 else 0) +
      (if e = 2 then 1 else 0) := by
  rw [convolution_prime_pow _ _ p e hp]
  simp_rw [moebius_prime_pow_delta p _ hp, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, Nat.sub_zero]
  by_cases h : 1 < e + 1
  · simp only [ite_eq_left h]
    by_cases h0 : e = 0 <;> by_cases h1 : e = 1 <;> by_cases h2 : e = 2 <;>
      simp_all <;> omega
  · have : e = 0 := by omega
    subst e; norm_num

private theorem cf_mul_D2 : cf * D2 = ArithmeticFunction.moebius * ArithmeticFunction.moebius := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (cf_isMultiplicative.mul D2_isMultiplicative) _
    (ArithmeticFunction.isMultiplicative_moebius.mul ArithmeticFunction.isMultiplicative_moebius)).mpr
  intro p e hp
  rw [mul_comm cf D2, convolution_prime_pow _ _ p e hp]
  simp_rw [D2_prime_pow _ _ hp, cf_prime_pow _ _ hp, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, Nat.sub_zero]
  rw [mu_squared_prime_pow p e hp]
  by_cases h : 3 ≤ e
  · have hne0 : e ≠ 0 := by omega
    have hne1 : e ≠ 1 := by omega
    have hne2 : e ≠ 2 := Ne.symm (Nat.ne_of_lt h)
    simp only [ite_eq_left (show 2 < e + 1 by omega), ite_eq_right hne0, ite_eq_right hne1, ite_eq_right hne2,
      zero_sub, neg_zero, zero_add]
    exact cphi_rec e h
  · have : e = 0 ∨ e = 1 ∨ e = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [cphi]

private theorem cf_factorization : cf =
    ArithmeticFunction.moebius * ArithmeticFunction.moebius * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by
  calc
    cf = cf * (((SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) * D2) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius)) := by rw [Q_four_mul_D2, Q_two_mul_M2, mul_one]
    _ = (cf * D2) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by ring
    _ = _ := by rw [cf_mul_D2]

private theorem W_prime_pow_delta (p e : ℕ) (hp : p.Prime) :
    (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) (p ^ e) = (if e = 0 then 1 else 0) + (if e = 1 then 1 else 0) := by
  rw [ArithmeticFunction.pmul_apply, moebius_prime_pow_delta p e hp]
  by_cases h0 : e = 0 <;> by_cases h1 : e = 1 <;> simp_all

private theorem zeta_mul_M2 :
    (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) = (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (ArithmeticFunction.isMultiplicative_zeta.natCast.mul M2_isMultiplicative) _
    W_isMultiplicative).mpr
  intro p e hp
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [M2_prime_pow_delta p _ hp]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ]
  rw [W_prime_pow_delta p e hp]
  by_cases h : 2 < e + 1
  · have h0 : e ≠ 0 := by omega
    have h1 : e ≠ 1 := by omega
    simp [h,h0,h1]
  · have he : e = 0 ∨ e = 1 := by omega
    rcases he with rfl | rfl <;> norm_num

private theorem Q_four_mul_W : (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) = E (fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((Q_isMultiplicative 4 (by decide)).mul W_isMultiplicative) _ (E_isMultiplicative _)).mpr
  intro p e hp
  rw [mul_comm, convolution_prime_pow _ _ p e hp]
  simp_rw [W_prime_pow_delta _ _ hp, Q_prime_pow 4 (by decide) _ _ hp, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, Nat.sub_zero]
  rw [E_prime_pow _ (by norm_num) p e hp]
  by_cases h : 1 < e + 1
  · simp only [ite_eq_left h]
    split_ifs <;> omega
  · have : e = 0 := by omega
    subst e; norm_num

private theorem Q_four_mul_mu : (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) * ArithmeticFunction.moebius = E (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) := by
  apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    ((Q_isMultiplicative 4 (by decide)).mul ArithmeticFunction.isMultiplicative_moebius) _ (E_isMultiplicative _)).mpr
  intro p e hp
  rw [mul_comm, convolution_prime_pow _ _ p e hp]
  simp_rw [moebius_prime_pow_delta _ _ hp, Q_prime_pow 4 (by decide) _ _ hp, sub_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ, Nat.sub_zero]
  rw [E_prime_pow _ (by norm_num) p e hp]
  by_cases h : 1 < e + 1
  · simp only [ite_eq_left h]
    split_ifs <;> omega
  · have : e = 0 := by omega
    subst e; norm_num

private theorem signed_product_range {ι : Type*} (s : Finset ι) (e : ι → ℕ) :
    ((∏ i ∈ s, (fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e i)) = 0 ∧ (∏ i ∈ s, (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e i)) = 0) ∨
    ((∏ i ∈ s, (fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e i)) = 1 ∧ (∏ i ∈ s, (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e i)) = 1) ∨
    ((∏ i ∈ s, (fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e i)) = 1 ∧ (∏ i ∈ s, (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e i)) = -1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hloc : ((fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e a) = 0 ∧ (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e a) = 0) ∨
        ((fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e a) = 1 ∧ (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e a) = 1) ∨
        ((fun e : ℕ => if e % 4 ≤ 1 then (1 : ℤ) else 0) (e a) = 1 ∧ (fun e : ℕ => if e % 4 = 0 then (1 : ℤ) else if e % 4 = 1 then -1 else 0) (e a) = -1) := by
      by_cases h0 : e a % 4 = 0 <;> by_cases h1 : e a % 4 = 1 <;>
        by_cases h2 : e a % 4 < 2 <;> simp_all <;> omega
    rcases hloc with ⟨hr,hz⟩ | ⟨hr,hz⟩ | ⟨hr,hz⟩ <;>
      rcases ih with ⟨hr',hz'⟩ | ⟨hr',hz'⟩ | ⟨hr',hz'⟩ <;>
      simp only [hr, hz, hr', hz', mul_zero, zero_mul, one_mul, mul_one, neg_mul, neg_neg, true_and, true_or, or_true]

private theorem common_sum_range (n : ℕ) (hn : n ≠ 0) :
    (((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)) n = 0 ∨
      (((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)) n = 2 := by
  rw [add_mul, ArithmeticFunction.add_apply, mul_comm (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius), mul_comm ArithmeticFunction.moebius,
    Q_four_mul_W, Q_four_mul_mu, E_apply _ n hn, E_apply _ n hn]
  rcases signed_product_range n.primeFactors n.factorization with ⟨hr,hz⟩ | ⟨hr,hz⟩ | ⟨hr,hz⟩ <;>
    rw [hr, hz] <;> decide

private theorem ordered_coprime_count (n : ℕ) (hn : n ≠ 0) :
    (n.divisorsAntidiagonal.filter (fun x => x.1.Coprime x.2)).card =
      2 ^ n.primeFactors.card := by
  classical
  let I := n.primeFactors
  let CP := {x : ℕ × ℕ // x ∈ n.divisorsAntidiagonal.filter (fun x => x.1.Coprime x.2)}
  let eqv := StrictDivisorChainCount.factorTupleEquivAllocation n hn (Fin 2)
  let alloc : (I → Bool) → StrictDivisorChainCount.PrimeAllocation n (Fin 2) := fun b p =>
    if b p then ⟨![n.factorization p,0], by simp [Fin.sum_univ_two]⟩
      else ⟨![0,n.factorization p], by simp [Fin.sum_univ_two]⟩
  let tuple (b : I → Bool) := eqv.symm (alloc b)
  have hfac (b : I → Bool) (p : I) (i : Fin 2) :
      ((tuple b).val i).factorization p = (alloc b p).val i := by
    have h := eqv.apply_symm_apply (alloc b)
    exact congrArg (fun a => (a p).val i) h
  have hprod (b : I → Bool) : (tuple b).val 0 * (tuple b).val 1 = n := by
    simpa [Fin.prod_univ_two] using (tuple b).prop.2
  have hcop (b : I → Bool) : ((tuple b).val 0).Coprime ((tuple b).val 1) := by
    by_contra h
    obtain ⟨p,hp,hp0,hp1⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hpn : p ∈ I := Nat.mem_primeFactors.mpr
      ⟨hp, hprod b ▸ hp0.trans (dvd_mul_right _ _), hn⟩
    have h0 := hp.factorization_pos_of_dvd ((tuple b).prop.1 0).ne' hp0
    have h1 := hp.factorization_pos_of_dvd ((tuple b).prop.1 1).ne' hp1
    rw [hfac b ⟨p,hpn⟩ 0] at h0
    rw [hfac b ⟨p,hpn⟩ 1] at h1
    cases hb : b ⟨p,hpn⟩ <;> simp [alloc,hb] at h0 h1
  let encode : (I → Bool) → CP := fun b =>
    ⟨((tuple b).val 0,(tuple b).val 1),
      Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod b,hn⟩,hcop b⟩⟩
  let decode : CP → I → Bool := fun x p => decide (p.val ∣ x.val.1)
  have hleft (b : I → Bool) : decode (encode b) = b := by
    funext p
    have hep : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors p.prop).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors p.prop)
    have hf := hfac b p 0
    have hr0 := ((tuple b).prop.1 0).ne'
    cases hb : b p
    · have hf0 : ((tuple b).val 0).factorization p = 0 := by simpa [alloc,hb] using hf
      have hnot : ¬p.val ∣ (tuple b).val 0 := by
        intro h
        have := (Nat.prime_of_mem_primeFactors p.prop).factorization_pos_of_dvd hr0 h
        omega
      simp [decode,encode,hnot]
    · have hfp : ((tuple b).val 0).factorization p ≠ 0 := by
        rw [hf]
        simpa [alloc,hb] using hep.ne'
      have hdiv := Nat.dvd_of_factorization_pos hfp
      simp [decode,encode,hdiv]
  have hright (x : CP) : encode (decode x) = x := by
    have hx := Finset.mem_filter.mp x.prop
    have hp := Nat.mem_divisorsAntidiagonal.mp hx.1
    have hr : 0 < x.val.1 := Nat.pos_of_mem_divisors (Nat.fst_mem_divisors_of_mem_antidiagonal hx.1)
    have hs : 0 < x.val.2 := Nat.pos_of_mem_divisors (Nat.snd_mem_divisors_of_mem_antidiagonal hx.1)
    let tx : StrictDivisorChainCount.FactorTuple n (Fin 2) := ⟨![x.val.1,x.val.2], by
      constructor
      · intro i; fin_cases i <;> simp [hr,hs]
      · simpa [Fin.prod_univ_two] using hp.1⟩
    have halloc : alloc (decode x) = eqv tx := by
      funext p
      apply Subtype.ext
      funext i
      have heq : x.val.1.factorization p + x.val.2.factorization p = n.factorization p := by
        rw [← Finsupp.add_apply, ← Nat.factorization_mul hr.ne' hs.ne', hp.1]
      by_cases hd : p.val ∣ x.val.1
      · have hnot : ¬p.val ∣ x.val.2 := by
          intro hd'
          exact (Nat.prime_of_mem_primeFactors p.prop).ne_one
            (Nat.eq_one_of_dvd_coprimes hx.2 hd hd')
        have hz : x.val.2.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hnot
        have hfirst : x.val.1.factorization p = n.factorization p := by omega
        change (alloc (decode x) p).val i = (tx.val i).factorization p
        fin_cases i <;> simp [alloc,decode,hd,hfirst,hz,tx]
      · have hz : x.val.1.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hd
        have hsecond : x.val.2.factorization p = n.factorization p := by omega
        change (alloc (decode x) p).val i = (tx.val i).factorization p
        fin_cases i <;> simp [alloc,decode,hd,hsecond,hz,tx]
    have ht : tuple (decode x) = tx := (Equiv.symm_apply_eq eqv).mpr halloc
    apply Subtype.ext
    change ((tuple (decode x)).val 0,(tuple (decode x)).val 1) = x.val
    rw [ht]
    rfl
  let : Fintype CP := inferInstanceAs (Fintype ↥(n.divisorsAntidiagonal.filter (fun x => x.1.Coprime x.2)))
  let e : (I → Bool) ≃ CP := ⟨encode,decode,hleft,hright⟩
  have he := Fintype.card_congr e
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_coe, CP, I] using he.symm

private theorem C_one : C 1 = 1 := by simp [C]

private theorem C_even (n : ℕ) (hn : 1 < n) : (2 : ℤ) ∣ C n := by
  classical
  obtain ⟨p,hp⟩ := Nat.nonempty_primeFactors.mpr hn
  unfold C
  apply dvd_trans _ (Finset.dvd_prod_of_mem _ hp)
  exact dvd_mul_of_dvd_left (dvd_mul_right 2 _) _

private theorem convolution_C_mod_two (f : ℕ → ℤ) (n : ℕ) (hn : n ≠ 0) :
    (∑ d ∈ n.divisors, f d * C (n / d)) % 2 = f n % 2 := by
  classical
  rw [Finset.sum_int_mod]
  have hs : ∑ d ∈ n.divisors, (f d * C (n / d)) % 2 = f n % 2 := by
    calc
      _ = ∑ d ∈ n.divisors, if d = n then f n % 2 else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        by_cases hdn : d = n
        · subst d
          rw [Nat.div_self (Nat.pos_of_ne_zero hn), C_one, mul_one, ite_eq_left rfl]
        · rw [ite_eq_right hdn]
          have hq : 1 < n / d := by
            have hpos := Nat.pos_of_mem_divisors hd
            have hnle : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd)
            have hqp : 0 < n / d := Nat.div_pos hnle hpos
            have hne : n / d ≠ 1 := by
              intro h
              exact hdn (Nat.eq_of_dvd_of_div_eq_one (Nat.dvd_of_mem_divisors hd) h)
            omega
          have h2 := C_even (n / d) hq
          exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_right h2 (f d))
      _ = f n % 2 := by simp [Nat.mem_divisors_self n hn]
  rw [hs, Int.emod_emod]

private def af : ArithmeticFunction ℤ := ⟨fun n => (A n : ℤ), by simp [A]⟩
private def bf : ArithmeticFunction ℤ := ⟨B, by simp [B]⟩

private theorem zeta_W_prime_pow (p e : ℕ) (hp : p.Prime) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius)) (p ^ e) = if e = 0 then 1 else 2 := by
  rw [ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  simp_rw [W_prime_pow_delta p _ hp]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_range, Nat.zero_lt_succ]
  by_cases h : e = 0
  · subst e; norm_num
  · simp [h, show 1 < e + 1 by omega]

private theorem zeta_W_value (n : ℕ) (hn : n ≠ 0) :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius)) n = (2 : ℤ) ^ n.primeFactors.card := by
  rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    (ArithmeticFunction.isMultiplicative_zeta.natCast.mul W_isMultiplicative) hn,
    Nat.prod_factorization_eq_prod_primeFactors]
  calc
    _ = ∏ _p ∈ n.primeFactors, (2 : ℤ) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [zeta_W_prime_pow _ _ (Nat.prime_of_mem_primeFactors hp),
        ite_eq_right ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
          (Nat.dvd_of_mem_primeFactors hp)).ne']
    _ = _ := by simp

private theorem two_af : (2 : ℤ) • af = 1 + (ArithmeticFunction.zeta : ArithmeticFunction ℤ) * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) := by
  ext n
  simp only [two_smul, ArithmeticFunction.add_apply]
  rw [← two_mul, ArithmeticFunction.one_apply]
  change 2 * (A n : ℤ) = _
  rw [two_A]
  by_cases hn : n = 0
  · subst n; simp
  · rw [ordered_coprime_count n hn, zeta_W_value n hn]
    norm_cast
    omega

private theorem bf_factorization : bf = ArithmeticFunction.moebius * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by
  ext n
  by_cases hn : n = 0
  · subst n; simp
  · exact (convolution_Q ArithmeticFunction.moebius 4 n (by decide) hn).symm

private theorem cf_value (n : ℕ) (hn : n ≠ 0) : cf n = C n := by
  rw [cf, E_apply _ n hn]
  unfold C
  apply Finset.prod_congr rfl
  intro p hp
  rw [cphi, ite_eq_right ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
    (Nat.dvd_of_mem_primeFactors hp)).ne']

private theorem twice_A_B : (2 : ℤ) • (af * bf) = ((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by
  rw [← smul_mul_assoc, two_af, bf_factorization]
  let u : ArithmeticFunction ℤ := ArithmeticFunction.zeta
  let m := ArithmeticFunction.moebius
  have hum : u * m = 1 := ArithmeticFunction.coe_zeta_mul_moebius
  change (1 + u * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius)) * (m * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)) = ((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + m) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)
  calc
    _ = (m + (u * m) * (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius)) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by ring
    _ = _ := by rw [hum]; ring

private theorem twice_H_C : (2 : ℤ) • (hfun * cf) = ((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by
  rw [← smul_mul_assoc, two_hfun, cf_factorization]
  let u : ArithmeticFunction ℤ := ArithmeticFunction.zeta
  let m := ArithmeticFunction.moebius
  have hum : u * m = 1 := ArithmeticFunction.coe_zeta_mul_moebius
  have huw : u * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) = (ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) := zeta_mul_M2
  change (u ^ 3 + u * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta)) * (m * m * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)) = ((ArithmeticFunction.moebius.pmul ArithmeticFunction.moebius) + m) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta)
  calc
    _ = ((u * m) ^ 2 * (u * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius)) + (u * m) * ((SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.zeta) * (SchulteLiouvilleCubeMobius.liftPow 2 ArithmeticFunction.moebius)) * m) * (SchulteLiouvilleCubeMobius.liftPow 4 ArithmeticFunction.zeta) := by ring
    _ = _ := by simp only [hum, huw, Q_two_mul_M2, one_pow, one_mul, mul_one]

private theorem af_bf_value (n : ℕ) :
    (af * bf) n = ∑ d ∈ n.divisors, (A d : ℤ) * B (n / d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => af a * bf b)]
  rfl

private theorem hfun_cf_value (n : ℕ) (hn : n ≠ 0) :
    (hfun * cf) n = ∑ d ∈ n.divisors, hfun d * C (n / d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => hfun a * cf b)]
  apply Finset.sum_congr rfl
  intro d hd
  rw [cf_value _ (Nat.div_pos
    (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hd))
    (Nat.pos_of_mem_divisors hd)).ne']

theorem result : claim := by
  intro n hn
  have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
  have hAB := congrArg (fun f : ArithmeticFunction ℤ => f n) twice_A_B
  have hHC := congrArg (fun f : ArithmeticFunction ℤ => f n) twice_H_C
  simp only [two_smul, ArithmeticFunction.add_apply] at hAB hHC
  rw [← two_mul] at hAB hHC
  have hrange := common_sum_range n hn0
  have hsmall : (hfun * cf) n = 0 ∨ (hfun * cf) n = 1 := by omega
  have heq : (af * bf) n = (hfun * cf) n := by omega
  have hp := convolution_C_mod_two hfun n hn0
  rw [← hfun_cf_value n hn0] at hp
  have hcast : hfun n % 2 = (((∑ d ∈ n.divisors, g d) % 2 : ℕ) : ℤ) :=
    (Nat.ToInt.mod_congr (hfun_literal n).symm rfl).symm
  rw [hcast] at hp
  have hpar : (((∑ d ∈ n.divisors, g d) % 2 : ℕ) : ℤ) = (hfun * cf) n := by omega
  constructor
  · rw [← af_bf_value n, heq]
    exact hpar
  · rw [hpar, hfun_cf_value n hn0]
    exact Finset.sum_congr rfl (fun d _ => congrArg (· * C (n / d)) (hfun_literal d))

end
end D5.S3.Factorization.Combinatorics.KarttunenParityDirichletConvolutions
