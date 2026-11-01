/- GID: D5/S3/Factorization/Combinatorics/KageyA350532Binomials
   generality: I
   mirror-B: D5/B/S3/Factorization/Combinatorics/KageyA350532Binomials
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Exact GF(2) sparse perfect-power counts. -/
/-
admission_basis: open-problem-resolution (#18613; Proved)
escape_witness: none.
Direct frozen dependencies: D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary.
Its current declaration statement_id requires the Stage-B scoped report.
Declaration classifications inline same-delivery helpers and stop at pinned upstream owners.
T: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: card_sparse_powers, claim.
coeff_one: proof_shape: bind-only; Direct frozen dependencies: binary;
  escape_witness: none; consumers: sparse_forms, normalized_sparse_power_derivative, sparse_power_even_exponent, ofSupport_support.
expand_two: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: squareEquiv.
support_expand: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: card_support_expand.
card_support_expand: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: normalized_odd_sparse_power, squareEquiv.
eq_one_of_dvd_X_pow: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: normalized_sparse_power_derivative.
sparse_forms: proof_shape: bind-only; Direct frozen dependencies: binary;
  escape_witness: none; consumers: normalized_sparse_power_derivative.
euler_X_pow: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: normalized_sparse_power_derivative.
normalized_sparse_power_derivative: proof_shape: bind-only; Direct frozen dependencies: binary;
  escape_witness: none; consumers: normalized_odd_sparse_power.
normalized_odd_sparse_power: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: sparse_power_even_exponent.
support_shift: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: card_support_shift.
card_support_shift: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: sparse_power_even_exponent.
sparse_power_even_exponent: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: sparse_power_derivative.
sparse_power_derivative: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: proper_sparse_expand_contract.
ofSupport: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: coeff_ofSupport, support_ofSupport, ofSupport_support, ofSupport_insert_spec, supportEquiv.
coeff_ofSupport: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: support_ofSupport, ofSupport_support, ofSupport_insert_spec.
support_ofSupport: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: ofSupport_insert_spec, supportEquiv.
ofSupport_support: proof_shape: bind-only; Direct frozen dependencies: binary;
  escape_witness: none; consumers: supportEquiv.
ofSupport_insert_spec: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: supportEquiv.
supportEquiv: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: card_polynomials.
card_polynomials: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: card_sparse_powers.
proper_sparse_expand_contract: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: squareEquiv.
squareEquiv: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: card_sparse_powers.
card_sparse_powers: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: result, KageyA350532Trinomials.result.
claim: proof_shape: bind-only; Direct frozen dependencies: none;
  escape_witness: none; consumers: result.
result: proof_shape: content; Direct frozen dependencies: binary;
  escape_witness: none; consumers: settling result.
T is the source's cardinality expression over nonzero polynomials.
The binary coefficient case uses the existing public owner directly.
The shared counting theorem is public because the trinomial result uses it.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21875
-/

import D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity

set_option autoImplicit false
noncomputable section

namespace D5.S3.Factorization.Combinatorics.KageyA350532Binomials
open Polynomial

/-- The number of nonzero degree-n proper powers with k nonzero terms over GF(2). -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.card {p : (ZMod 2)[X] // p ≠ 0 ∧ p.natDegree = n ∧ p.support.card = k ∧
    ∃ f : (ZMod 2)[X], ∃ m : ℕ, 1 < m ∧ p = f ^ m}

open Polynomial

private theorem coeff_one {c : ZMod 2} (hc : c ≠ 0) : c = 1 := by
  exact (D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary c).resolve_left hc

private theorem expand_two (f : (ZMod 2)[X]) : expand (ZMod 2) 2 f = f ^ 2 := by
  exact ZMod.expand_card f

private theorem support_expand (f : (ZMod 2)[X]) :
    (expand (ZMod 2) 2 f).support = f.support.image (fun n => n * 2) := by
  ext n
  simp only [mem_support_iff, coeff_expand (by decide : 0 < 2), Finset.mem_image]
  by_cases h : 2 ∣ n
  · rw [ite_eq_left h]
    constructor
    · intro hn
      exact ⟨n / 2, hn, Nat.div_mul_cancel h⟩
    · rintro ⟨a, ha, rfl⟩
      simpa using ha
  · rw [ite_eq_right h]
    simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
    intro a _ eq
    exact h (eq ▸ dvd_mul_left 2 a)

private theorem card_support_expand (f : (ZMod 2)[X]) :
    (expand (ZMod 2) 2 f).support.card = f.support.card := by
  rw [support_expand, Finset.card_image_of_injective]
  exact fun a b h => Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2) h

private theorem eq_one_of_dvd_X_pow {f : (ZMod 2)[X]} (hf : f.coeff 0 = 1) {n : ℕ}
    (hd : f ∣ X ^ n) : f = 1 := by
  obtain ⟨q, hq⟩ := hd
  have hf0 : f ≠ 0 := by intro h; simp [h] at hf
  have hq0 : q ≠ 0 := by
    intro h
    have hz : (X : (ZMod 2)[X]) ^ n = 0 := by simpa [h] using hq
    exact (pow_ne_zero n (X_ne_zero : (X : (ZMod 2)[X]) ≠ 0)) hz
  have hdg := congrArg Polynomial.natDegree hq
  have htl := congrArg Polynomial.natTrailingDegree hq
  rw [natDegree_X_pow, natDegree_mul hf0 hq0] at hdg
  rw [natTrailingDegree_X_pow, natTrailingDegree_mul hf0 hq0,
    natTrailingDegree_eq_zero.mpr (Or.inr (by rw [hf]; exact one_ne_zero)), zero_add] at htl
  have hle := natTrailingDegree_le_natDegree q
  have he : f.natDegree = 0 := by omega
  rw [eq_C_of_natDegree_eq_zero he, hf, C_1]



open Polynomial
open scoped CharTwo

private theorem sparse_forms {p : (ZMod 2)[X]} (h0 : p.coeff 0 = 1) (hc : p.support.card ≤ 3) :
    p = 1 ∨ (∃ a : ℕ, 0 < a ∧ p = 1 + X ^ a) ∨
      (∃ a b : ℕ, 0 < a ∧ a < b ∧ p = 1 + X ^ a + X ^ b) := by
  have hpos : 0 < p.support.card := Finset.card_pos.mpr
    ⟨0, mem_support_iff.mpr (by rw [h0]; exact one_ne_zero)⟩
  have hh : p.support.card = 1 ∨ p.support.card = 2 ∨ p.support.card = 3 := by omega
  rcases hh with hh | hh | hh
  · obtain ⟨k, c, hc, hp⟩ := card_support_eq_one.mp hh
    have hk : k = 0 := by
      by_contra hk
      simp [hp, Ne.symm hk] at h0
    left
    simp [hp, hk, coeff_one hc]
  · obtain ⟨k, a, hka, c, d, hc, hd, hp⟩ := card_support_eq_two.mp hh
    have hk : k = 0 := by
      by_contra hk
      have ha : a ≠ 0 := Nat.ne_zero_of_lt hka
      simp [hp, coeff_add, Ne.symm hk, ha.symm] at h0
    right; left
    refine ⟨a, by omega, ?_⟩
    simp [hp, hk, coeff_one hc, coeff_one hd]
  · obtain ⟨k, a, b, hka, hab, c, d, e, hc, hd, he, hp⟩ := card_support_eq_three.mp hh
    have hk : k = 0 := by
      by_contra hk
      have ha : a ≠ 0 := Nat.ne_zero_of_lt hka
      have hb : b ≠ 0 := Nat.ne_zero_of_lt hab
      simp [hp, coeff_add, Ne.symm hk, ha.symm, hb.symm] at h0
    right; right
    refine ⟨a, b, by omega, hab, ?_⟩
    simp [hp, hk, coeff_one hc, coeff_one hd, coeff_one he]

private theorem euler_X_pow (n : ℕ) :
    X * derivative (X ^ n : (ZMod 2)[X]) = C (n : ZMod 2) * X ^ n := by
  cases n
  · simp
  · rename_i n
    rw [derivative_X_pow_succ]
    simp only [Nat.cast_add, Nat.cast_one]
    ring

private theorem normalized_sparse_power_derivative {f : (ZMod 2)[X]} {m : ℕ}
    (h0 : f.coeff 0 = 1) (hm : 1 < m) (hc : (f ^ m).support.card ≤ 3) :
    derivative (f ^ m) = 0 := by
  have hp0 : (f ^ m).coeff 0 = 1 := by
    rw [coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h0, one_pow]
  have hd : f ∣ derivative (f ^ m) :=
    (dvd_pow_self f (by omega : m - 1 ≠ 0)).trans
      (pow_sub_one_dvd_derivative_of_pow_dvd (dvd_rfl : f ^ m ∣ f ^ m))
  have he : f ∣ X * derivative (f ^ m) := hd.mul_left X
  have hp : f ∣ f ^ m := dvd_pow_self f (by omega : m ≠ 0)
  rcases sparse_forms hp0 hc with hp1 | ⟨a, ha, hpa⟩ | ⟨a, b, ha, hab, hpab⟩
  · simp [hp1]
  · have heq : X * derivative (f ^ m) = C (a : ZMod 2) * X ^ a := by
      rw [hpa, derivative_add, derivative_one, mul_add, mul_zero, zero_add, euler_X_pow]
    by_cases haz : (a : ZMod 2) = 0
    · have hD : X * derivative (f ^ m) = 0 := by simpa [haz] using heq
      exact (mul_eq_zero.mp hD).resolve_left X_ne_zero
    · have hf : f = 1 := eq_one_of_dvd_X_pow h0 (by simpa [heq, coeff_one haz] using he)
      simp [hf]
  · have heq : X * derivative (f ^ m) =
        C (a : ZMod 2) * X ^ a + C (b : ZMod 2) * X ^ b := by
      rw [hpab, derivative_add, derivative_add, derivative_one,
        mul_add, mul_add, mul_zero, zero_add, euler_X_pow, euler_X_pow]
    by_cases haz : (a : ZMod 2) = 0 <;> by_cases hbz : (b : ZMod 2) = 0
    · have hD : X * derivative (f ^ m) = 0 := by simpa [haz, hbz] using heq
      exact (mul_eq_zero.mp hD).resolve_left X_ne_zero
    · have hf : f = 1 := eq_one_of_dvd_X_pow h0
        (by simpa [heq, haz, coeff_one hbz] using he)
      simp [hf]
    · have hf : f = 1 := eq_one_of_dvd_X_pow h0
        (by simpa [heq, coeff_one haz, hbz] using he)
      simp [hf]
    · have hsum : f ^ m + X * derivative (f ^ m) = 1 := by
        rw [heq, hpab, coeff_one haz, coeff_one hbz]
        simp only [C_1, one_mul]
        calc
          1 + X ^ a + X ^ b + (X ^ a + X ^ b) =
              1 + (X ^ a + X ^ b + (X ^ a + X ^ b)) := by abel
          _ = 1 := by simp
      have hf : f = 1 := eq_one_of_dvd_X_pow h0 (n := 0)
        (by simpa [hsum] using hp.add he)
      simp [hf]

private theorem normalized_odd_sparse_power {m : ℕ} (hm : 1 < m) (hmod : Odd m)
    {f : (ZMod 2)[X]} (h0 : f.coeff 0 = 1) (hc : (f ^ m).support.card ≤ 3) : f = 1 := by
  have aux : ∀ n : ℕ, ∀ f : (ZMod 2)[X], f.natDegree = n → f.coeff 0 = 1 →
      (f ^ m).support.card ≤ 3 → f = 1 := by
    intro n
    induction n using Nat.strong_induction_on
    rename_i n ih
    intro f hn h0 hc
    by_cases hn0 : n = 0
    · rw [eq_C_of_natDegree_eq_zero (hn.trans hn0), h0, C_1]
    have hD : derivative f = 0 :=
      (derivative_pow_eq_zero (by rw [hmod.natCast_zmod_two]; exact one_ne_zero)).mp
        (normalized_sparse_power_derivative h0 hm hc)
    let g := contract 2 f
    have hgf : expand (ZMod 2) 2 g = f := expand_contract 2 hD (by decide)
    have hdeg : g.natDegree < n := by
      have he := congrArg Polynomial.natDegree hgf
      rw [natDegree_expand, hn] at he
      omega
    have hg0 : g.coeff 0 = 1 := by simp [g, coeff_contract, h0]
    have hgc : (g ^ m).support.card ≤ 3 := by
      rw [← card_support_expand (g ^ m), map_pow, hgf]
      exact hc
    have hg1 := ih g.natDegree hdeg g rfl hg0 hgc
    rw [← hgf, hg1, map_one]
  exact aux f.natDegree f rfl h0 hc



open Polynomial

private theorem support_shift (f : (ZMod 2)[X]) (n : ℕ) :
    (f * X ^ n).support = f.support.image (fun i => i + n) := by
  ext i
  simp only [mem_support_iff, coeff_mul_X_pow', Finset.mem_image]
  by_cases h : n ≤ i
  · rw [ite_eq_left h]
    constructor
    · intro hi
      exact ⟨i - n, hi, Nat.sub_add_cancel h⟩
    · rintro ⟨j, hj, rfl⟩
      simpa using hj
  · rw [ite_eq_right h]
    simp only [ne_eq, not_true_eq_false, false_iff, not_exists, not_and]
    intro j _ heq
    omega

private theorem card_support_shift (f : (ZMod 2)[X]) (n : ℕ) :
    (f * X ^ n).support.card = f.support.card := by
  rw [support_shift, Finset.card_image_of_injective]
  exact fun a b h => Nat.add_right_cancel h

private theorem sparse_power_even_exponent {f : (ZMod 2)[X]} {m : ℕ}
    (hm : 1 < m) (hc : 2 ≤ (f ^ m).support.card) (hcs : (f ^ m).support.card ≤ 3) :
    Even m := by
  by_contra hme
  have hmo : Odd m := Nat.not_even_iff_odd.mp hme
  have hm0 : m ≠ 0 := Nat.ne_zero_of_lt hm
  have hf0 : f ≠ 0 := by
    intro h
    rw [h, zero_pow hm0, support_zero, Finset.card_empty] at hc
    omega
  obtain ⟨g, he, hg⟩ := f.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hf0 0
  simp only [C_0, sub_zero] at he hg
  have hg0 : g.coeff 0 = 1 := coeff_one (fun h => hg (X_dvd_iff.mpr h))
  have hpow : f ^ m = g ^ m * X ^ (f.rootMultiplicity 0 * m) := by
    calc
      f ^ m = (X ^ (f.rootMultiplicity 0) * g) ^ m := congrArg (fun p : (ZMod 2)[X] => p ^ m) he
      _ = g ^ m * X ^ (f.rootMultiplicity 0 * m) := by
        rw [mul_pow, ← pow_mul]
        exact mul_comm _ _
  have hgc : (g ^ m).support.card ≤ 3 := by
    rw [hpow, card_support_shift] at hcs
    exact hcs
  have hg1 : g = 1 := normalized_odd_sparse_power hm hmo hg0 hgc
  rw [hpow, hg1, one_pow, one_mul, support_X_pow, Finset.card_singleton] at hc
  omega

private theorem sparse_power_derivative {f : (ZMod 2)[X]} {m : ℕ}
    (hm : 1 < m) (hc : 2 ≤ (f ^ m).support.card) (hcs : (f ^ m).support.card ≤ 3) :
    derivative (f ^ m) = 0 := by
  have he := sparse_power_even_exponent hm hc hcs
  rw [derivative_pow, he.natCast_zmod_two, C_0, zero_mul, zero_mul]



open Polynomial Finset

private def ofSupport (s : Finset ℕ) : (ZMod 2)[X] := ∑ i ∈ s, X ^ i

private theorem coeff_ofSupport (s : Finset ℕ) (i : ℕ) :
    (ofSupport s).coeff i = if i ∈ s then 1 else 0 := by
  simp [ofSupport, finsetSum_coeff, coeff_X_pow]

private theorem support_ofSupport (s : Finset ℕ) : (ofSupport s).support = s := by
  ext i
  simp [mem_support_iff, coeff_ofSupport]

private theorem ofSupport_support (p : (ZMod 2)[X]) : ofSupport p.support = p := by
  unfold ofSupport
  calc
    (∑ i ∈ p.support, X ^ i) = ∑ i ∈ p.support, C (p.coeff i) * X ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(D5.S1.Recurrence.Residue.ExponentialSquareWeightCatalanParity.binary
        (p.coeff i)).resolve_left (mem_support_iff.mp hi), C_1, one_mul]
    _ = p := p.as_sum_support_C_mul_X_pow.symm

private theorem ofSupport_insert_spec {n k : ℕ} {s : Finset ℕ}
    (hs : s ∈ (range n).powersetCard k) :
    ofSupport (insert n s) ≠ 0 ∧
    (ofSupport (insert n s)).natDegree = n ∧
    (ofSupport (insert n s)).support.card = k + 1 := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hs
  have hn : n ∉ s := fun h => (mem_range.mp (hsub h)).ne rfl
  have hc : (ofSupport (insert n s)).coeff n ≠ 0 := by simp [coeff_ofSupport]
  refine ⟨(fun he => hc (by rw [he, coeff_zero])), ?_, ?_⟩
  · apply natDegree_eq_of_le_of_coeff_ne_zero _ hc
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    rw [coeff_ofSupport, ite_eq_right]
    simp only [mem_insert, not_or]
    exact ⟨by omega, fun his => by have := mem_range.mp (hsub his); omega⟩
  · rw [support_ofSupport, card_insert_of_notMem hn, hcard]

private def supportEquiv (n k : ℕ) :
    {p : (ZMod 2)[X] // p ≠ 0 ∧ p.natDegree = n ∧ p.support.card = k + 1} ≃
      {s : Finset ℕ // s ∈ (range n).powersetCard k} where
  toFun p := ⟨p.1.support.erase n, by
    apply mem_powersetCard.mpr
    constructor
    · intro i hi
      obtain ⟨hin, hip⟩ := mem_erase.mp hi
      have hle := le_natDegree_of_mem_supp i hip
      rw [p.2.2.1] at hle
      exact mem_range.mpr (lt_of_le_of_ne hle hin)
    · have hn : n ∈ p.1.support := by
        simpa only [p.2.2.1] using natDegree_mem_support_of_nonzero p.2.1
      rw [card_erase_of_mem hn, p.2.2.2, Nat.add_sub_cancel]
    ⟩
  invFun s := ⟨ofSupport (insert n s.1), ofSupport_insert_spec s.2⟩
  left_inv p := by
    apply Subtype.ext
    change ofSupport (insert n (p.1.support.erase n)) = p.1
    have hn : n ∈ p.1.support := by
      simpa only [p.2.2.1] using natDegree_mem_support_of_nonzero p.2.1
    rw [insert_erase hn, ofSupport_support]
  right_inv s := by
    apply Subtype.ext
    change (ofSupport (insert n s.1)).support.erase n = s.1
    rw [support_ofSupport, erase_insert]
    exact fun hn => (mem_range.mp ((mem_powersetCard.mp s.2).1 hn)).ne rfl

private theorem card_polynomials (n k : ℕ) :
    Nat.card {p : (ZMod 2)[X] // p ≠ 0 ∧ p.natDegree = n ∧ p.support.card = k + 1} = n.choose k := by
  rw [Nat.card_congr (supportEquiv n k), Nat.card_eq_finsetCard,
    card_powersetCard, card_range]



open Polynomial

private theorem proper_sparse_expand_contract {k : ℕ} (hk : 1 ≤ k) (hks : k ≤ 2)
    {p : (ZMod 2)[X]} (hp : p.support.card = k + 1)
    (hpow : ∃ f : (ZMod 2)[X], ∃ m : ℕ, 1 < m ∧ p = f ^ m) :
    expand (ZMod 2) 2 (contract 2 p) = p := by
  obtain ⟨f, m, hm, rfl⟩ := hpow
  exact expand_contract 2 (sparse_power_derivative hm (by omega) (by omega)) (by decide)

private def squareEquiv (n k : ℕ) (hk : 1 ≤ k) (hks : k ≤ 2) :
    {p : (ZMod 2)[X] // p ≠ 0 ∧ p.natDegree = 2 * n ∧ p.support.card = k + 1 ∧
      ∃ f : (ZMod 2)[X], ∃ m : ℕ, 1 < m ∧ p = f ^ m} ≃
    {p : (ZMod 2)[X] // p ≠ 0 ∧ p.natDegree = n ∧ p.support.card = k + 1} where
  toFun p := ⟨contract 2 p.1, by
    have he := proper_sparse_expand_contract hk hks p.2.2.2.1 p.2.2.2.2
    refine ⟨?_, ?_, ?_⟩
    · intro h
      apply p.2.1
      rw [← he, h, map_zero]
    · have hd := congrArg Polynomial.natDegree he
      rw [natDegree_expand, p.2.2.1] at hd
      omega
    · rw [← card_support_expand, he, p.2.2.2.1]
    ⟩
  invFun q := ⟨expand (ZMod 2) 2 q.1, by
    refine ⟨(expand_ne_zero (by decide : 0 < 2)).mpr q.2.1, ?_, ?_, ?_⟩
    · rw [natDegree_expand, q.2.2.1, mul_comm]
    · rw [card_support_expand, q.2.2.2]
    · exact ⟨q.1, 2, by decide, expand_two q.1⟩
    ⟩
  left_inv p := by
    apply Subtype.ext
    exact proper_sparse_expand_contract hk hks p.2.2.2.1 p.2.2.2.2
  right_inv q := by
    apply Subtype.ext
    exact contract_expand 2 (by decide)

theorem card_sparse_powers (n k : ℕ) (hk : 1 ≤ k) (hks : k ≤ 2) :
    T (2 * n) (k + 1) = n.choose k := by
  unfold T
  rw [Nat.card_congr (squareEquiv n k hk hks), card_polynomials]

/-- The second conjecture of OEIS A350532, including n = 0. -/
def claim : Prop := ∀ n : ℕ, T (2 * n) 2 = n

theorem result : claim := by
  intro n
  simpa using card_sparse_powers n 1 (by decide) (by decide)

end D5.S3.Factorization.Combinatorics.KageyA350532Binomials
