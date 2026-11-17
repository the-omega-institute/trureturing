/- GID: D5/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/OeisA378444DivisorNumeratorParity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Karttunen's A378444 divisor count equals the ceiling of half A174273. -/

/- Judgement form.
   proof_shape: r, A083345, A378444, A035263, A174273, claim: definition.
   proof_shape: halfExp, doubleExp: private implementation definitions.
   proof_shape: odd_den_num_parity: bind-only; consumer=numerator_parity.
   proof_shape: numerator_parity: bind-only; consumer=r_parity.
   proof_shape: odd_sum_rep: content; consumer=r_parity.
   proof_shape: r_parity: content; consumer=result.
   proof_shape: halfExp_sum: bind-only; consumer=result.
   proof_shape: compressed_card: bind-only; consumer=result.
   proof_shape: box_eq: bind-only; consumer=box_sign_sum.
   proof_shape: box_sign_sum: bind-only; consumer=box_balance.
   proof_shape: box_balance: bind-only; consumer=box_count.
   proof_shape: box_count: bind-only; consumer=result.
   proof_shape: result: content (finite induction through odd_sum_rep); consumer=none.
   escape_witness: result via r_parity; admission uses the external settling result.
   admission_basis: open-problem-resolution (#23534; Proved).
   Direct frozen dependencies: none (all declarations; no D5 imports).
   Escape audit registration is tracked at https://github.com/the-omega-institute/trureturing/issues/23568;
   the delivered-head current job supplies its status.
   The public definitions retain the source expressions. The implementation halves
   the exponent at 2 and uses its inverse to count divisors in a finite exponent box.
   These are unbounded symbolic statements, not finite enumeration or certification;
   every declaration has computational_content.kind=none.
-/

import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Rat.Floor

import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity

/-- A083345: r(n) = Sum(e/p: n=Product(p^e)), for positive n. -/
def r (n : ℕ) : ℚ :=
  n.factorization.sum (fun p e => (e : ℚ) / (p : ℚ))

/-- The numerator in the reduced rational representation, including num(0)=0. -/
def A083345 (n : ℕ) : ℤ := (r n).num

/-- A378444: number of positive divisors with even A083345 value. -/
def A378444 (n : ℕ) : ℕ :=
  (n.divisors.filter (fun d => A083345 d % 2 = 0)).card

/-- A035263: 1 for an even number of binary trailing zeros, and 0 otherwise. -/
def A035263 (n : ℕ) : ℕ :=
  if n.factorization 2 % 2 = 0 then 1 else 0

/-- A174273: the inverse Moebius transform of A035263. -/
def A174273 (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, A035263 d

/-- A378444 FORMULA, Karttunen's unnumbered ceiling conjecture. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → A378444 n = ⌈(A174273 n : ℚ) / 2⌉₊

open Finset
set_option maxHeartbeats 2000000

private theorem odd_den_num_parity (q : ℚ) (N D : ℤ) (hD : Odd D)
    (hq : q = (N : ℚ) / D) : q.num % 2 = N % 2 := by
  have hd : D ≠ 0 := by
    have := Int.odd_iff.mp hD
    omega
  have hdiv : q = Rat.divInt N D := by simpa only [Rat.divInt_eq_div] using hq
  obtain ⟨c, hN, hc⟩ := Rat.num_den_mk hd hdiv
  have hcodd : c % 2 = 1 := by
    have hmod := congrArg (fun x : ℤ => x % 2) hc
    have hDmod : D % 2 = 1 := Int.odd_iff.mp hD
    by_contra hh
    have hc0 : c % 2 = 0 := by exact Int.emod_two_ne_one.mp hh
    simp only [Int.mul_emod, hc0, zero_mul, Int.zero_emod] at hmod
    omega
  rw [hN, Int.mul_emod, hcodd]
  omega

private theorem numerator_parity (a N D : ℕ) (hD : Odd D) :
    (((a : ℚ) / 2 + (N : ℚ) / D).num % 2 = 0) ↔
      a % 2 = 0 ∧ (a / 2 + N) % 2 = 0 := by
  have hD0 : (D : ℚ) ≠ 0 := by exact_mod_cast (show D ≠ 0 from by have := Nat.odd_iff.mp hD; omega)
  by_cases ha : a % 2 = 0
  · have hsplit : (a : ℚ) / 2 + (N : ℚ) / D =
        ((a / 2 * D + N : ℕ) : ℚ) / D := by
      have ha' : a = a / 2 * 2 := by omega
      conv_lhs => lhs; rw [ha']
      push_cast
      field_simp

    rw [odd_den_num_parity _ ((a / 2 * D + N : ℕ) : ℤ) (D : ℤ) (by exact_mod_cast hD) (by exact_mod_cast hsplit)]
    have hDm : D % 2 = 1 := Nat.odd_iff.mp hD
    norm_cast
    simp [ha, Nat.add_mod, Nat.mul_mod, hDm]
  · have hm : (a * D + 2 * N) % 2 = 1 := by
      have hDm : D % 2 = 1 := Nat.odd_iff.mp hD
      simp [Nat.add_mod, Nat.mul_mod, hDm]
      omega
    have hsplit : (a : ℚ) / 2 + (N : ℚ) / D =
        ((a * D + 2 * N : ℕ) : ℚ) / (2 * D) := by
      push_cast
      field_simp

    have hdiv : (a : ℚ) / 2 + (N : ℚ) / D =
        Rat.divInt (a * D + 2 * N : ℤ) (2 * D) := by
      simpa only [Rat.divInt_eq_div, Int.cast_add, Int.cast_mul, Int.cast_ofNat,
        Int.cast_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hsplit
    have hdvd := Rat.num_dvd (a * D + 2 * N : ℤ) (show (2 * D : ℤ) ≠ 0 by
      exact mul_ne_zero (by norm_num) (by exact_mod_cast (show D ≠ 0 from by have := Nat.odd_iff.mp hD; omega)))
    rw [← hdiv] at hdvd
    constructor
    · intro h
      obtain ⟨k, hk⟩ := hdvd
      have he := congrArg (fun z : ℤ => z % 2) hk
      rw [Int.mul_emod, h] at he
      norm_cast at he
      omega
    · simp [ha]

private theorem odd_sum_rep (s : Finset ℕ) (f : ℕ → ℕ)
    (hs : ∀ p ∈ s, Odd p) :
    ∃ N D : ℕ, Odd D ∧ (∑ p ∈ s, (f p : ℚ) / p) = (N : ℚ) / D ∧
      N % 2 = (∑ p ∈ s, f p) % 2 := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, 1, by simp, by simp, by simp⟩
  | insert p s hp ih =>
    obtain ⟨N, D, hD, hq, hN⟩ := ih (fun q hq => hs q (by simp [hq]))
    have hop := hs p (mem_insert_self _ _)
    have hp0 : (p : ℚ) ≠ 0 := by
      have hm := Nat.odd_iff.mp hop
      exact_mod_cast (show p ≠ 0 from by omega)
    have hD0 : (D : ℚ) ≠ 0 := by
      have hm := Nat.odd_iff.mp hD
      exact_mod_cast (show D ≠ 0 from by omega)
    refine ⟨f p * D + N * p, p * D, hop.mul hD, ?_, ?_⟩
    · rw [sum_insert hp, hq]
      push_cast
      field_simp
    · rw [sum_insert hp]
      simp only [Nat.add_mod, Nat.mul_mod, Nat.odd_iff.mp hop, Nat.odd_iff.mp hD,
        mul_one, hN, Nat.mod_mod]

private theorem r_parity (n : ℕ) : A083345 n % 2 = 0 ↔
    n.factorization 2 % 2 = 0 ∧
      (n.factorization 2 / 2 + (n.factorization.erase 2).sum (fun _ e => e)) % 2 = 0 := by
  classical
  obtain ⟨N, D, hD, hq, hN⟩ := odd_sum_rep (n.factorization.erase 2).support
    (n.factorization.erase 2) (by
      intro p hp
      have hp' : p ∈ n.primeFactors := by
        have := (Finset.mem_erase.mp (by simpa only [Finsupp.support_erase] using hp)).2
        exact this
      exact (Nat.prime_of_mem_primeFactors hp').odd_of_ne_two
        (by
          exact (Finset.mem_erase.mp (by simpa only [Finsupp.support_erase] using hp)).1))
  have hr : r n = (n.factorization 2 : ℚ) / 2 + (N : ℚ) / D := by
    rw [r, ← hq]
    exact (Finsupp.add_sum_erase' n.factorization 2 (fun p e => (e : ℚ) / p)
      (by simp)).symm
  rw [A083345, hr, numerator_parity _ _ _ hD]
  change _ ↔ _ ∧ (_ + ∑ p ∈ (n.factorization.erase 2).support, _) % 2 = 0
  simp only [Nat.add_mod, hN, Nat.mod_mod]

private noncomputable def halfExp (f : ℕ →₀ ℕ) : ℕ →₀ ℕ := f.update 2 (f 2 / 2)
private noncomputable def doubleExp (f : ℕ →₀ ℕ) : ℕ →₀ ℕ := f.update 2 (2 * f 2)

private theorem halfExp_sum (f : ℕ →₀ ℕ) :
    (halfExp f).sum (fun _ e => e) = f 2 / 2 + (f.erase 2).sum (fun _ e => e) := by
  simpa [halfExp, Finsupp.update_apply] using
    (Finsupp.add_sum_erase' (halfExp f) 2 (fun _ e => e) (by simp)).symm

private theorem compressed_card (n : ℕ) (hn : n ≠ 0) (P : (ℕ →₀ ℕ) → Prop)
    [DecidablePred P] :
    (n.divisors.filter (fun d => d.factorization 2 % 2 = 0 ∧ P (halfExp d.factorization))).card =
    ((Finset.Iic (halfExp n.factorization)).filter P).card := by
  classical
  apply Finset.card_bij (fun d hd => halfExp d.factorization)
  · intro d hd
    obtain ⟨hdmem, he, hP⟩ := Finset.mem_filter.mp hd
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Iic.mpr ?_, hP⟩
    have hd0 := ne_zero_of_dvd_ne_zero hn (Nat.dvd_of_mem_divisors hdmem)
    have hle := (Nat.factorization_le_iff_dvd hd0 hn).mpr (Nat.dvd_of_mem_divisors hdmem)
    intro p
    by_cases hp : p = 2
    · subst p
      simpa [halfExp, Finsupp.update_apply] using Nat.div_le_div_right (hle 2)
    · simpa [halfExp, Finsupp.update_apply, hp] using hle p
  · intro d hd e he hde
    obtain ⟨hdmem, hd2, hdP⟩ := Finset.mem_filter.mp hd
    obtain ⟨hemem, he2, heP⟩ := Finset.mem_filter.mp he
    apply Nat.eq_of_factorization_eq' (ne_zero_of_dvd_ne_zero hn (Nat.dvd_of_mem_divisors hdmem))
      (ne_zero_of_dvd_ne_zero hn (Nat.dvd_of_mem_divisors hemem))
    ext p
    have h := congrArg (fun f : ℕ →₀ ℕ => f p) hde
    by_cases hp : p = 2
    · subst p
      simp [halfExp, Finsupp.update_apply] at h
      omega
    · simpa [halfExp, Finsupp.update_apply, hp] using h
  · intro f hf
    obtain ⟨hfmem, hP⟩ := Finset.mem_filter.mp hf
    have hle : doubleExp f ≤ n.factorization := by
      intro p
      have h := (Finset.mem_Iic.mp hfmem) p
      by_cases hp : p = 2
      · subst p
        simp [doubleExp, halfExp, Finsupp.update_apply] at h ⊢
        omega
      · simpa [doubleExp, halfExp, Finsupp.update_apply, hp] using h
    let d := (doubleExp f).prod (fun p e => p ^ e)
    have hdvd : d ∣ n := Nat.prod_pow_dvd_of_le_factorization hle
    have hfact : d.factorization = doubleExp f := Nat.factorization_prod_pow_eq_self_of_le_factorization hle
    have hhalf : halfExp d.factorization = f := by
      rw [hfact]
      simp [halfExp, doubleExp, Finsupp.update_apply]
    refine ⟨d, Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hdvd, hn⟩, ?_, ?_⟩, hhalf⟩
    · rw [hfact]
      simp [doubleExp, Finsupp.update_apply]
    · rwa [hhalf]

private theorem box_eq (f : ℕ →₀ ℕ) :
    Finset.Iic f = f.support.finsupp (fun p => Finset.range (f p + 1)) := by
  classical
  rw [Finset.Iic_eq_Icc, show (⊥ : ℕ →₀ ℕ) = 0 from rfl, Finsupp.Icc_eq]
  simp only [Finsupp.support_zero, Finset.empty_union]
  congr 1
  funext p
  simp [Nat.range_succ_eq_Icc_zero]

private theorem box_sign_sum (f : ℕ →₀ ℕ) :
    (∑ g ∈ Finset.Iic f, (-1 : ℤ) ^ (g.sum (fun _ e => e))) =
      ∏ p ∈ f.support, (if Even (f p + 1) then (0 : ℤ) else 1) := by
  classical
  let : DecidableEq ℕ := Classical.decEq ℕ
  rw [box_eq, Finset.finsupp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  simp_rw [Finsupp.sum_indicator_index_eq_sum_attach (h := fun (_ : ℕ) (e : ℕ) => e) _ (fun _ _ => rfl),
    ← Finset.prod_pow_eq_pow_sum]
  have h := Finset.prod_sum f.support (fun p => range (f p + 1))
    (fun (_ : ℕ) (b : ℕ) => (-1 : ℤ) ^ b)
  simp only [neg_one_geom_sum] at h
  exact h.symm

private theorem box_balance (f : ℕ →₀ ℕ) :
    0 ≤ (∑ g ∈ Finset.Iic f, (-1 : ℤ) ^ (g.sum (fun _ e => e))) ∧
    (∑ g ∈ Finset.Iic f, (-1 : ℤ) ^ (g.sum (fun _ e => e))) ≤ 1 := by
  rw [box_sign_sum]
  constructor
  · exact Finset.prod_nonneg (fun p hp => by split_ifs <;> norm_num)
  · exact Finset.prod_le_one₀ (fun p hp => by split_ifs <;> norm_num)
      (fun p hp => by split_ifs <;> norm_num)

private theorem box_count (f : ℕ →₀ ℕ) :
    ((Finset.Iic f).filter (fun g => g.sum (fun _ e => e) % 2 = 0)).card =
      ⌈(((Finset.Iic f).card : ℚ) / 2)⌉₊ := by
  classical
  let s := Finset.Iic f
  let E := (s.filter (fun g => g.sum (fun _ e => e) % 2 = 0)).card
  have hid : (∑ g ∈ s, (-1 : ℤ) ^ (g.sum (fun _ e => e))) = 2 * E - s.card := by
    have hi : ∀ g : ℕ →₀ ℕ, (-1 : ℤ) ^ (g.sum (fun _ e => e)) =
        2 * (if g.sum (fun _ e => e) % 2 = 0 then 1 else 0) - 1 := by
      intro g
      rw [neg_one_pow_eq_ite]
      simp only [Nat.even_iff]
      split_ifs <;> norm_num
    simp_rw [hi, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [E, Finset.sum_boole]
  have hbal := box_balance f
  change 0 ≤ (∑ g ∈ s, _) ∧ (∑ g ∈ s, _) ≤ 1 at hbal
  rw [hid] at hbal
  change E = ⌈((s.card : ℚ) / 2)⌉₊
  apply le_antisymm
  · by_contra hh
    have ht : ⌈((s.card : ℚ) / 2)⌉₊ < E := by exact Nat.lt_of_not_le hh
    have hc := Nat.le_ceil ((s.card : ℚ) / 2)
    have hni : 2 * ⌈((s.card : ℚ) / 2)⌉₊ < s.card := by omega
    have hq : (2 * ⌈((s.card : ℚ) / 2)⌉₊ : ℚ) < s.card := by exact_mod_cast hni
    linarith
  · apply Nat.ceil_le.mpr
    have hi : (s.card : ℤ) ≤ 2 * E := by omega
    have hq : (s.card : ℚ) ≤ 2 * E := by exact_mod_cast hi
    linarith

theorem result : D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity.claim := by
  classical
  intro n hn
  have hn0 : n ≠ 0 := by exact Nat.ne_zero_of_lt hn
  have hB : A174273 n = (Finset.Iic (halfExp n.factorization)).card := by
    simpa [A174273, A035263] using compressed_card n hn0 (fun _ => True)
  have hfilter : n.divisors.filter (fun d => A083345 d % 2 = 0) =
      n.divisors.filter (fun d => d.factorization 2 % 2 = 0 ∧
        (halfExp d.factorization).sum (fun _ e => e) % 2 = 0) := by
    ext d
    simp only [Finset.mem_filter, r_parity, halfExp_sum]
  rw [A378444, hfilter, compressed_card n hn0
    (fun f => f.sum (fun _ e => e) % 2 = 0), box_count, hB]

end D5.S3.Arith.Divisors.OeisA378444DivisorNumeratorParity
