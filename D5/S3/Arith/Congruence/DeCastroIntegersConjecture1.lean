/- GID: D5/S3/Arith/Congruence/DeCastroIntegersConjecture1
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/DeCastroIntegersConjecture1
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Admissible binomial fractions recover the prime-adic order. -/

/-
admission_basis: open-problem-resolution (#18681; Proved)
proof_shape: bind-only for result and all supporting lemmas; consumers are given below.
escape_witness: none
Direct frozen dependencies: none (Mathlib and same-delivery declarations only).
The definitions and claim have the expressions specified in #18681.
The claim states admissibility through its literal pair of inclusions;
the proof uses Set.Icc membership, whose defining condition is that same pair.
Rat.den is used directly, without a denominator alias.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21956
Declarations:
  den_dvd_n: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.den_dvd_gcd.
  frac_shift: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.den_dvd_k, DeCastroIntegersConjecture1.den_prime_pow.
  den_dvd_k: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.den_dvd_gcd.
  den_dvd_gcd: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.admissible_lcm.
  mul_pred_decomp: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.choose_pred_congr.
  choose_pred_congr: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.den_prime_pow.
  den_prime_pow: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.admissible_lcm.
  admissible_lcm: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.result.
  logarithm_iff: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: DeCastroIntegersConjecture1.result.
  result: proof_shape: bind-only; escape_witness: none; Direct frozen dependencies: none;
    consumers: settling result.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Nth

set_option autoImplicit false

namespace D5.S3.Arith.Congruence.DeCastroIntegersConjecture1

def frac (n k : ℕ) : ℚ := (1 / (n : ℚ)) * (n.choose k : ℚ)

private lemma den_dvd_n (n k : ℕ) : (frac n k).den ∣ n := by
  have h := Rat.den_dvd (n.choose k : ℤ) (n : ℤ)
  have hh : (((frac n k).den : ℕ) : ℤ) ∣ (n : ℤ) := by
    simpa [ frac, Rat.divInt_eq_div, div_eq_mul_inv, mul_comm] using h
  exact_mod_cast hh

private lemma frac_shift (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    frac n k = ((n - 1).choose (k - 1) : ℚ) / k := by
  have h := Nat.add_one_mul_choose_eq (n - 1) (k - 1)
  rw [Nat.sub_add_cancel hn, Nat.sub_add_cancel hk] at h
  have hh : (n : ℚ) * ((n-1).choose (k-1) : ℚ) = (n.choose k : ℚ) * k := by exact_mod_cast h
  unfold frac
  apply (eq_div_iff (by exact_mod_cast hk.ne' : (k : ℚ) ≠ 0)).2
  field_simp
  nlinarith [hh]

lemma den_dvd_k (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (frac n k).den ∣ k := by
  have h := Rat.den_dvd ((n-1).choose (k-1) : ℤ) (k : ℤ)
  have hh : (((frac n k).den : ℕ) : ℤ) ∣ (k : ℤ) := by
    simpa [ frac_shift n k hn hk, Rat.divInt_eq_div] using h
  exact_mod_cast hh

lemma den_dvd_gcd (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (frac n k).den ∣ n.gcd k :=
  Nat.dvd_gcd (den_dvd_n n k) (den_dvd_k n k hn hk)

private lemma mul_pred_decomp (p a : ℕ) (hp : 0 < p) (ha : 0 < a) :
    p*a-1 = (p-1) + p*(a-1) := by
  have h := Nat.mul_sub_left_distrib p a 1
  have hpa : p ≤ p*a := by exact Nat.le_mul_of_pos_right p ha
  omega

private lemma choose_pred_congr (p j : ℕ) (hp : p.Prime) :
    ∀ m : ℕ, 0 < m → (p^j*m-1).choose (p^j-1) ≡ 1 [MOD p] := by
  letI : Fact p.Prime := ⟨hp⟩
  induction j with
  | zero => intro m hm; simp only [pow_zero, one_mul, Nat.sub_self, Nat.choose_zero_right]; rfl
  | succ j ih =>
    intro m hm
    have ha : 0 < p^j*m := Nat.mul_pos (pow_pos hp.pos _) hm
    have hb : 0 < p^j := pow_pos hp.pos _
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
      (p := p) (n := p^(j+1)*m-1) (k := p^(j+1)-1)
    have hd : p^(j+1)*m-1 = (p-1)+p*(p^j*m-1) := by
      rw [pow_succ']; rw [mul_assoc]; exact mul_pred_decomp _ _ hp.pos ha
    have he : p^(j+1)-1 = (p-1)+p*(p^j-1) := by
      rw [pow_succ']; exact mul_pred_decomp _ _ hp.pos hb
    have hlt : p-1 < p := Nat.sub_lt hp.pos (by omega)
    rw [hd, he, Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hp.pos,
      Nat.add_mul_div_left _ _ hp.pos, Nat.div_eq_of_lt hlt, zero_add, zero_add,
      Nat.choose_self, one_mul] at h
    rw [hd, he]
    exact h.trans (ih m hm)

lemma den_prime_pow (n p j : ℕ) (hn : 0 < n) (hp : p.Prime) (hd : p^j ∣ n) :
    (frac n (p^j)).den = p^j := by
  obtain ⟨m, hm⟩ := hd
  have hmpos : 0 < m := Nat.pos_of_mul_pos_left (by simpa only [hm] using hn)
  have hc := choose_pred_congr p j hp m hmpos
  rw [← hm] at hc
  have hcop : Nat.Coprime ((n-1).choose (p^j-1)) p :=
    Nat.coprime_of_mul_modEq_one 1 (by simpa using hc)
  have hcop' := hcop.pow_right j
  have h := Rat.den_div_eq_of_coprime (a := ((n-1).choose (p^j-1) : ℤ))
    (b := (p^j : ℕ)) (by exact_mod_cast (pow_pos hp.pos j)) (by simpa using hcop')
  have hh : (((frac n (p^j)).den : ℕ) : ℤ) = ((p^j : ℕ) : ℤ) := by
    simpa [ frac_shift n (p^j) hn (pow_pos hp.pos _)] using h
  exact_mod_cast hh

/-- `S^min_{p,n} = {(1/n) binomial(n, p_i^j) | i ∈ ℕ*, j ∈ ℕ, gcd(p_i^j, p) = 1, p_i^j ≤ n}`, where `p_i`
is the `i`-th prime. -/
def Smin (p n : ℕ) : Set ℚ :=
  {x | ∃ i j : ℕ, 1 ≤ i ∧ Nat.gcd (Nat.nth Nat.Prime (i - 1) ^ j) p = 1 ∧
    Nat.nth Nat.Prime (i - 1) ^ j ≤ n ∧ x = (1 / (n : ℚ)) * (n.choose (Nat.nth Nat.Prime (i - 1) ^ j) : ℚ)}

/-- `S^max_{p,n} = {(1/n) binomial(n, k) | 0 < k ≤ n, gcd(k, p) = 1}`. -/
def Smax (p n : ℕ) : Set ℚ :=
  {x | ∃ k : ℕ, 0 < k ∧ k ≤ n ∧ Nat.gcd k p = 1 ∧ x = (1 / (n : ℚ)) * (n.choose k : ℚ)}

/-- de Castro, INTEGERS 22 (2022) #A61, Conjecture 1: for every prime `p`, positive integer `n` and
admissible `S_{p,n}`, `v_p(n) = log_p(n / L_{p,n})`, with `L_{p,n}` the least common denominator of the
elements of `S_{p,n}`. -/
def claim : Prop :=
  ∀ p n : ℕ, p.Prime → 1 ≤ n → ∀ S : Finset ℚ,
    (Smin p n ⊆ ↑S ∧ ↑S ⊆ Smax p n) →
    (padicValNat p n : ℝ) = Real.logb p ((n : ℝ) / ((S.lcm Rat.den : ℕ) : ℝ))



private lemma admissible_lcm (p n : ℕ) (hp : p.Prime) (hn : 0 < n)
    (S : Finset ℚ) (hS : (S : Set ℚ) ∈ Set.Icc (Smin p n) (Smax p n)) :
    S.lcm Rat.den = n.divMaxPow p := by
  have hn0 := hn.ne'
  have heq := Nat.pow_padicValNat_mul_divMaxPow p n
  have hTn : n.divMaxPow p ∣ n := ⟨p ^ padicValNat p n, by simpa [Nat.mul_comm] using heq.symm⟩
  have hcopT : Nat.Coprime (n.divMaxPow p) p :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_divMaxPow hp.one_lt hn0)).symm
  apply Nat.dvd_antisymm
  · apply Finset.lcm_dvd
    intro x hx
    obtain ⟨k, hk, hkn, hkp, rfl⟩ := hS.2 hx
    have hbound := den_dvd_gcd n k hn hk
    have hc : Nat.Coprime ((frac n k).den) p :=
      (show Nat.Coprime k p from hkp).of_dvd_left
        (hbound.trans (Nat.gcd_dvd_right n k))
    have hd : (frac n k).den ∣ p ^ padicValNat p n * n.divMaxPow p := by
      rw [heq]; exact hbound.trans (Nat.gcd_dvd_left n k)
    exact (hc.pow_right _).dvd_of_dvd_mul_left hd
  · apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro r j hr hd
    have hd' := hd.trans hTn
    have hle := Nat.le_of_dvd hn hd'
    have hc : Nat.gcd (r^j) p = 1 := (hcopT.of_dvd_left hd).gcd_eq_one
    have hm : frac n (r^j) ∈ S := hS.1
      ⟨Nat.count Nat.Prime r + 1, j, by omega, by simpa [Nat.nth_count hr] using hc,
        by simpa [Nat.nth_count hr] using hle, by simp [Nat.nth_count hr, frac]⟩
    have hden := Finset.dvd_lcm (f := Rat.den) hm
    change (frac n (r^j)).den ∣ S.lcm Rat.den at hden
    rwa [den_prime_pow n r j hn hr hd'] at hden

lemma logarithm_iff (q n l e : ℕ) (hq : 1 < q) (hn : 0 < n) (hl : 0 < l) :
    (e : ℝ) = Real.logb q ((n : ℝ)/(l : ℝ)) ↔ q^e*l=n := by
  rw [eq_comm, Real.logb_eq_iff_rpow_eq (by exact_mod_cast (lt_trans Nat.zero_lt_one hq))
    (by exact_mod_cast (Nat.ne_of_gt hq)) (div_pos (by exact_mod_cast hn) (by exact_mod_cast hl)),
    Real.rpow_natCast, eq_div_iff (by exact_mod_cast hl.ne' : (l : ℝ) ≠ 0)]
  norm_cast

theorem result : claim := by
  intro p n hp hn S hS
  have h := admissible_lcm p n hp (by omega) S hS
  have hl : 0 < S.lcm Rat.den := Nat.pos_of_ne_zero
    ((Finset.lcm_ne_zero_iff).mpr (fun x hx => x.den_nz))
  apply (logarithm_iff p n (S.lcm Rat.den) (padicValNat p n) hp.one_lt (by omega) hl).mpr
  rw [h]
  exact Nat.pow_padicValNat_mul_divMaxPow p n

end D5.S3.Arith.Congruence.DeCastroIntegersConjecture1
