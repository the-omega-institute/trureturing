/- GID: D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A347855 fractional-factorial integrality. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18691; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19874
The fractional factorial and sequence definitions retain the source expressions.
No finite computational declaration refutes the claim; utility is none.
Declarations (all dependencies outside this delivery are pinned Mathlib):
  a: proof_shape: bind-only; escape_witness: none;
    consumers: a_formula, claim, multiple_three_formula, result. Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  residue_count: proof_shape: bind-only; escape_witness: none;
    consumers: progression_count. Direct frozen dependencies: none.
  residue_mod_three_iff: proof_shape: bind-only; escape_witness: none;
    consumers: progression_count. Direct frozen dependencies: none.
  progression_count: proof_shape: bind-only; escape_witness: none;
    consumers: third_dvd. Direct frozen dependencies: none.
  third_local_bound: proof_shape: bind-only; escape_witness: none;
    consumers: third_dvd. Direct frozen dependencies: none.
  progression: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347855BalaAuxBIntegral.denominator_dvd, OeisA347855BalaAuxCIntegral.denominator_dvd, a_formula, progression_ne_zero, progression_padic, result, third_dvd. Direct frozen dependencies: none.
  progression_ne_zero: proof_shape: bind-only; escape_witness: none;
    consumers: result, third_dvd. Direct frozen dependencies: none.
  padic_finset_prod: proof_shape: bind-only; escape_witness: none;
    consumers: progression_padic, third_dvd. Direct frozen dependencies: none.
  padic_eq_card: proof_shape: bind-only; escape_witness: none;
    consumers: progression_padic. Direct frozen dependencies: none.
  progression_padic: proof_shape: bind-only; escape_witness: none;
    consumers: third_dvd. Direct frozen dependencies: none.
  third_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347855BalaAuxBIntegral.denominator_dvd, OeisA347855BalaAuxCIntegral.denominator_dvd, result. Direct frozen dependencies: none.
  a_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  multiple_three_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  result: proof_shape: bind-only; escape_witness: none;
    consumers: settling result. Direct frozen dependencies: none.
-/

import Mathlib.Data.Int.CardIntervalMod
import D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

/-- A347855: `a(n) = (4*n)!/((2*n)!*(n)!) * (n/3)!/(4*n/3)!`. -/
noncomputable def a (n : ℕ) : ℝ :=
  (Nat.factorial (4 * n) : ℝ) / ((Nat.factorial (2 * n) : ℝ) * (Nat.factorial n : ℝ)) *
    (ffact ((n : ℝ) / 3) / ffact (4 * (n : ℝ) / 3))

/-- A347855 ("The sequence is conjectured to be integral."). -/
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, (z : ℝ) = a n

end D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

set_option maxHeartbeats 800000

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

private lemma residue_count (a b r : ℕ) (hr : r = 1 ∨ r = 2) :
    ((Finset.Ioc a b).filter (fun l => l % 3 = r)).card =
      (b+3-r)/3 - (a+3-r)/3 := by
    classical
    have hrb : r < 3 := by omega
    have hf (x : ℕ) : ⌊((x : ℚ)-r)/3⌋ = (((x+3-r)/3 : ℕ) : ℤ)-1 := by
      apply Int.floor_eq_iff.mpr
      have hcast : ((x+3-r : ℕ) : ℚ) = (x : ℚ)+3-r := by
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring
      have hlo : (3 : ℚ)*((x+3-r)/3 : ℕ) ≤ (x : ℚ)+3-r := by
        rw [← hcast]
        exact_mod_cast Nat.mul_div_le (x+3-r) 3
      have hhi : (x : ℚ)+3-r < 3*(((x+3-r)/3 : ℕ)+1) := by
        rw [← hcast]
        exact_mod_cast Nat.lt_mul_div_succ (x+3-r) (by decide : 0 < 3)
      simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast]
      constructor
      · apply (le_div_iff₀ (by norm_num : (0 : ℚ) < 3)).mpr
        linarith
      · apply (div_lt_iff₀ (by norm_num : (0 : ℚ) < 3)).mpr
        linarith
    have he : ((Finset.Ioc a b).filter (fun l => l%3 = r)) =
        ((Finset.Ioc a b).filter (fun l => l ≡ r [MOD 3])) := by
      ext l
      simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hrb]
    have hh := Nat.Ioc_filter_modEq_card a b (r := 3) (by decide) r
    rw [he]
    simp only [Nat.cast_ofNat] at hh
    rw [hf a, hf b] at hh
    omega

private lemma residue_mod_three_iff (n q l : ℕ) (hq : ¬3 ∣ q) :
    q*l % 3 = n % 3 ↔ l % 3 = (n*q) % 3 := by
    have hqm : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rw [Nat.mul_mod q l 3, Nat.mul_mod n q 3]
    rcases hqm with hqm | hqm <;> rw [hqm] <;> omega

private lemma progression_count (n q : ℕ) (hq : 0 < q) (h3n : ¬3 ∣ n) (h3q : ¬3 ∣ q) :
    ((Finset.range n).filter (fun j => q ∣ n+3*(j+1))).card =
      (4*n/q+3-(n*q)%3)/3 - (n/q+3-(n*q)%3)/3 := by
    classical
    have hr : (n*q)%3 = 1 ∨ (n*q)%3 = 2 := by
      have hn : n%3 = 1 ∨ n%3 = 2 := by omega
      have hqm : q%3 = 1 ∨ q%3 = 2 := by omega
      rcases hn with hn | hn <;> rcases hqm with hqm | hqm <;>
        simp [Nat.mul_mod, hn, hqm]
    calc
      _ = ((Finset.Ioc (n/q) (4*n/q)).filter (fun l => l%3 = (n*q)%3)).card := by
        apply Finset.card_bij (fun j _ => (n+3*(j+1))/q)
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_range] at hj
          have he : q*((n+3*(j+1))/q) = n+3*(j+1) := Nat.mul_div_cancel' hj.2
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          refine ⟨⟨(Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith),
            (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)⟩, ?_⟩
          apply (residue_mod_three_iff n q _ h3q).mp
          rw [he]
          omega
        · intro j hj k hk heq
          simp only [Finset.mem_filter, Finset.mem_range] at hj hk
          have hej := Nat.mul_div_cancel' hj.2
          have hek := Nat.mul_div_cancel' hk.2
          rw [heq] at hej
          omega
        · intro l hl
          simp only [Finset.mem_filter, Finset.mem_Ioc] at hl
          have hlo : n < q*l := by
            have := (Nat.div_lt_iff_lt_mul hq).mp hl.1.1
            nlinarith
          have hhi : q*l ≤ 4*n := by
            have := (Nat.le_div_iff_mul_le hq).mp hl.1.2
            nlinarith
          have hm : q*l % 3 = n % 3 := (residue_mod_three_iff n q l h3q).mpr hl.2
          let t := (q*l-n)/3
          have ht : q*l = n+3*t := by dsimp [t]; omega
          have htpos : 0 < t := by omega
          have htmax : t ≤ n := by omega
          have hj : n+3*((t-1)+1) = q*l := by omega
          refine ⟨t-1, ?_, ?_⟩
          · simp only [Finset.mem_filter, Finset.mem_range]
            exact ⟨by omega, hj ▸ dvd_mul_right q l⟩
          · rw [hj, Nat.mul_div_right _ hq]
      _ = _ := residue_count _ _ _ hr

private lemma third_local_bound (n q r : ℕ) (hq : 0 < q) (hr : r = 1 ∨ r = 2) :
    (4*n/q+3-r)/3 + 2*n/q + n/q ≤ 4*n/q + (n/q+3-r)/3 := by
    let s := n % (3*q)
    have hs : s < 3*q := Nat.mod_lt n (by omega)
    have split (c : ℕ) : c*n/q = 3*c*(n/(3*q))+c*s/q := by
      change c*n/q = 3*c*(n/(3*q))+c*(n%(3*q))/q
      simpa only [Nat.mul_assoc, Nat.mul_div_mul_left _ _ (by decide : 0 < 3)] using
        D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.mul_div_reduce (3*c) n (3*q) (by omega)
    have hs1 : n/q = 3*(n/(3*q))+s/q := by simpa only [Nat.one_mul, Nat.mul_one] using split 1
    rw [split 4, split 2, hs1]
    have h1 : 1*s/q = (4*s/q)/4 := D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.grid_floor 4 1 4 s q hq (by decide) (by decide)
    have h2 : 2*s/q = (4*s/q)/2 := D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.grid_floor 4 2 2 s q hq (by decide) (by decide)
    simp only [Nat.one_mul] at h1
    have hb : 4*s/q < 12 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [h1, h2]
    have small (t v r : ℕ) (hv : v < 12) (hr : r = 1 ∨ r = 2) :
        (12*t+v+3-r)/3 + (6*t+v/2) + (3*t+v/4) ≤
          12*t+v+(3*t+v/4+3-r)/3 := by
      rcases hr with rfl | rfl <;> omega
    convert small (n/(3*q)) (4*s/q) r hb hr using 1 <;> congr 2 <;> omega

end D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

def progression (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (n+3*(k+1))

private lemma progression_ne_zero (n : ℕ) : progression n ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    omega

private lemma padic_finset_prod {ι : Type*} (p : ℕ) [hp : Fact p.Prime] (S : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ S, f i ≠ 0) :
    padicValNat p (∏ i ∈ S, f i) = ∑ i ∈ S, padicValNat p (f i) := by
  have hh : (padicValNat p (∏ i ∈ S, f i) : ℕ∞) =
      ((∑ i ∈ S, padicValNat p (f i) : ℕ) : ℕ∞) := by
    rw [padicValNat_eq_emultiplicity (Finset.prod_ne_zero_iff.mpr hf), Nat.cast_sum]
    exact (Finset.emultiplicity_prod (Nat.prime_iff.mp hp.out) S f).trans
      (Finset.sum_congr rfl (fun i hi => (padicValNat_eq_emultiplicity (hf i hi)).symm))
  exact_mod_cast hh

private lemma padic_eq_card (p n b : ℕ) [hp : Fact p.Prime] (hn : 0 < n) (hb : p.log n < b) :
    padicValNat p n = ((Finset.Ico 1 b).filter (fun k => p^k ∣ n)).card := by
    exact_mod_cast ((padicValNat_eq_emultiplicity (p := p) hn.ne') ▸
      Nat.emultiplicity_eq_card_pow_dvd hp.out.ne_one hn hb)

private lemma progression_padic (n p : ℕ) [hp : Fact p.Prime] :
    padicValNat p (progression n) =
      ∑ k ∈ Finset.Ico 1 (4*n+1),
        ((Finset.range n).filter (fun j => p^k ∣ n+3*(j+1))).card := by
    classical
    rw [progression, padic_finset_prod p _ _ (by intro i hi; omega)]
    have one (j : ℕ) (hj : j ∈ Finset.range n) :
        padicValNat p (n+3*(j+1)) =
          ∑ k ∈ Finset.Ico 1 (4*n+1), if p^k ∣ n+3*(j+1) then 1 else 0 := by
      rw [padic_eq_card p (n+3*(j+1)) (4*n+1) (by omega) (lt_of_le_of_lt (p.log_le_self _) (by simp only [Finset.mem_range] at hj; omega))]
      exact (Finset.sum_boole (fun k : ℕ => p^k ∣ n+3*(j+1)) (Finset.Ico 1 (4*n+1))).symm
    rw [show (∑ j ∈ Finset.range n, padicValNat p (n+3*(j+1))) =
      ∑ j ∈ Finset.range n, ∑ k ∈ Finset.Ico 1 (4*n+1),
        if p^k ∣ n+3*(j+1) then 1 else 0 from Finset.sum_congr rfl one]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    exact Finset.sum_boole _ _

lemma third_dvd (n : ℕ) (hn : ¬3 ∣ n) :
    (2*n).factorial * n.factorial * progression n ∣ (4*n).factorial := by
    classical
    apply (Nat.factorization_prime_le_iff_dvd
      (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (progression_ne_zero n)) (Nat.factorial_ne_zero _)).mp
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (progression_ne_zero n),
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
    by_cases hp3 : p = 3
    · subst p
      have hz : padicValNat 3 (progression n) = 0 := by
        rw [progression, padic_finset_prod 3 _ _ (by intro i hi; omega)]
        apply Finset.sum_eq_zero
        intro j hj
        apply padicValNat.eq_zero_of_not_dvd
        omega
      rw [hz, add_zero]
      have hd : (2*n).factorial*n.factorial ∣ (4*n).factorial :=
        (Nat.factorial_mul_factorial_dvd_factorial_add (2*n) n).trans
          (Nat.factorial_dvd_factorial (by omega))
      have hh := (Nat.factorization_prime_le_iff_dvd
        (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
        (Nat.factorial_ne_zero _)).mpr hd 3 (by decide)
      simpa only [Nat.factorization_def _ (by decide : Nat.Prime 3),
        padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] using hh
    · have vf (m : ℕ) (hm : m ≤ 4*n) :
          padicValNat p m.factorial = ∑ k ∈ Finset.Ico 1 (4*n+1), m / p^k :=
        padicValNat_factorial (lt_of_le_of_lt (p.log_le_self m) (by omega))
      rw [vf (2*n) (by omega), vf n (by omega), vf (4*n) (by omega), progression_padic]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro k hk
      have hq : 0 < p^k := pow_pos hp.pos k
      have h3q : ¬3 ∣ p^k := by
        intro hd
        have hd' := Nat.prime_three.dvd_of_dvd_pow hd
        have hp' : p = 3 := ((Nat.dvd_prime hp).mp hd' |>.resolve_left (by decide)).symm
        exact hp3 hp'
      rw [progression_count n (p^k) hq hn h3q]
      have hr : (n*p^k)%3 = 1 ∨ (n*p^k)%3 = 2 := by
        have hnm : n%3 = 1 ∨ n%3 = 2 := by omega
        have hqm : p^k%3 = 1 ∨ p^k%3 = 2 := by omega
        rcases hnm with hnm | hnm <;> rcases hqm with hqm | hqm <;>
          simp [Nat.mul_mod, hnm, hqm]
      have hb := third_local_bound n (p^k) ((n*p^k)%3) hq hr
      have hm0 : n/p^k ≤ 4*n/p^k := Nat.div_le_div_right (by omega)
      have hm1 : n/p^k+3-(n*p^k)%3 ≤ 4*n/p^k+3-(n*p^k)%3 :=
        Nat.sub_le_sub_right (by omega) _
      have hm2 : (n/p^k+3-(n*p^k)%3)/3 ≤ (4*n/p^k+3-(n*p^k)%3)/3 :=
        Nat.div_le_div_right hm1
      omega

end D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral

namespace D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma a_formula (n : ℕ) : a n = (3 : ℝ)^n *
    ((4*n).factorial : ℝ) / ((2*n).factorial * (n.factorial : ℝ) * progression n) := by
    simp only [a, ffact]
    rw [gamma_third_ratio]
    simp only [progression, Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    field_simp <;> ring

private lemma multiple_three_formula (m : ℕ) : a (3*m) =
    ((12*m).factorial : ℝ) * m.factorial /
      ((6*m).factorial * (4*m).factorial * ((3*m).factorial : ℝ)) := by
    simp only [a, ffact, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (3*(m : ℝ))/3 = m by ring,
      show 4*(3*(m : ℝ))/3 = 4*m by ring]
    rw [gamma_nat, show (4 : ℝ)*m = ((4*m : ℕ) : ℝ) by push_cast; ring, gamma_nat]
    norm_num [show 4*(3*m) = 12*m by omega, show 2*(3*m) = 6*m by omega]
    field_simp

theorem result : claim := by
    intro n
    by_cases h3 : 3 ∣ n
    · obtain ⟨m, rfl⟩ := h3
      rw [multiple_three_formula]
      obtain ⟨z, hz⟩ := quotient_cast_integral (D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.even_dvd m) (by positivity)
      exact ⟨z, by simpa only [Nat.cast_mul, Nat.one_mul] using hz⟩
    · rw [a_formula]
      obtain ⟨z, hz⟩ := quotient_cast_integral (third_dvd n h3)
        (by have := progression_ne_zero n; positivity)
      refine ⟨(3 : ℤ)^n*z, ?_⟩
      push_cast
      rw [hz]
      push_cast
      ring

end D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral
