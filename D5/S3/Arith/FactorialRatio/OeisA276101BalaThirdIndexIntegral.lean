/- GID: D5/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA276101BalaThirdIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala A276101 integrality at every natural index. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#21665; Proved)
Direct frozen dependencies: declaration statement_ids are listed per declaration.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/21712
The sequence and claim retain the source expressions; Gamma values at natural arguments use Nat.factorial.
Declarations:
  Parameters: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: local_bound, progression_floor_bound, nonmultiple_dvd.
  progression: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: progression_ne_zero, progression_padic, nonmultiple_dvd, gamma_ratio.
  residue_count: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: progression_count.
  progression_count: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: progression_floor_bound.
  local_bound: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor [sha256:e963adde13e1fbae007e049b0ccb577832f09cabe40e61c63d54ebfb82f2b952]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce [sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9]; proof_shape: bind-only; escape_witness: none; consumers: progression_floor_bound.
  progression_floor_bound: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor [sha256:e963adde13e1fbae007e049b0ccb577832f09cabe40e61c63d54ebfb82f2b952]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce [sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9]; proof_shape: bind-only; escape_witness: none; consumers: nonmultiple_dvd.
  progression_ne_zero: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: nonmultiple_dvd, gamma_ratio, result, OeisA276102BalaFifthIndexIntegral.result.
  progression_padic: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_eq_card [sha256:e4281962b49fa51ec1364954053a1b0e8f1c72b92d6a15bbba18f4b776f0c204]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_finset_prod [sha256:c47bf88627299240e509a07dcd3b58785e73ab4ee9b88013f9786c295bffd815]; proof_shape: bind-only; escape_witness: none; consumers: nonmultiple_dvd.
  nonmultiple_dvd: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor [sha256:e963adde13e1fbae007e049b0ccb577832f09cabe40e61c63d54ebfb82f2b952]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce [sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_eq_card [sha256:e4281962b49fa51ec1364954053a1b0e8f1c72b92d6a15bbba18f4b776f0c204]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_finset_prod [sha256:c47bf88627299240e509a07dcd3b58785e73ab4ee9b88013f9786c295bffd815]; proof_shape: bind-only; escape_witness: none; consumers: result, OeisA276102BalaFifthIndexIntegral.result.
  gamma_ratio: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_shift_product [sha256:6517f62c7c80056802b298d90f84d911ed7d49b29d306b5d64d2ebb8de39f3e9]; proof_shape: bind-only; escape_witness: none; consumers: a_formula, OeisA276102BalaFifthIndexIntegral.a_formula.
  ordinary_dvd: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality [sha256:3e2d5f42dd7144ba1552ae8375b786e0fb26a427c8949ec94a2cbcf3457c52d9]; proof_shape: bind-only; escape_witness: none; consumers: result, OeisA276102BalaFifthIndexIntegral.result.
  a: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: claim, a_formula, multiple_formula.
  claim: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: result.
  a_formula: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_shift_product [sha256:6517f62c7c80056802b298d90f84d911ed7d49b29d306b5d64d2ebb8de39f3e9]; proof_shape: bind-only; escape_witness: none; consumers: result.
  multiple_formula: Direct frozen dependencies: none; proof_shape: bind-only; escape_witness: none; consumers: result.
  result: Direct frozen dependencies: D5/S3/Arith/FactorialRatio/BalaChebyshevFiveDivisibility.bala_five_integrality [sha256:3e2d5f42dd7144ba1552ae8375b786e0fb26a427c8949ec94a2cbcf3457c52d9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.gamma_shift_product [sha256:6517f62c7c80056802b298d90f84d911ed7d49b29d306b5d64d2ebb8de39f3e9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.grid_floor [sha256:e963adde13e1fbae007e049b0ccb577832f09cabe40e61c63d54ebfb82f2b952]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.mul_div_reduce [sha256:efd40ec129eaf47b98931b54d218f23ba6af1038ded8e8765adab500e978e1c9]; D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral.quotient_cast_integral [sha256:b533be952af020be1d656bd9f901c785871ba09c5551733ebab4e1c2e0527e46]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_eq_card [sha256:e4281962b49fa51ec1364954053a1b0e8f1c72b92d6a15bbba18f4b776f0c204]; D5/S3/Arith/FactorialRatio/OeisA347855BalaThirdIndexIntegral.padic_finset_prod [sha256:c47bf88627299240e509a07dcd3b58785e73ab4ee9b88013f9786c295bffd815]; proof_shape: bind-only; escape_witness: none; consumers: none (settling result).
-/

import D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral
import D5.S3.Arith.FactorialRatio.BalaChebyshevFiveDivisibility

set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators

namespace D5.S3.Arith.FactorialRatio.OeisA276101BalaThirdIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

def Parameters (d M B C L : ℕ) : Prop :=
  (d = 3 ∧ M = 10 ∧ B = 5 ∧ C = 2 ∧ L = 3) ∨
  (d = 5 ∧ M = 6 ∧ B = 3 ∧ C = 2 ∧ L = 1)

def progression (d L n : ℕ) : ℕ := ∏ k ∈ Finset.range (L*n), (n+d*(k+1))

private lemma residue_count (a b d r : ℕ) (hd : 0 < d) (hrd : r < d) :
    ((Finset.Ioc a b).filter (fun l => l % d = r)).card =
      (b+d-r)/d - (a+d-r)/d := by
  classical
  have hf (x : ℕ) : ⌊((x : ℚ)-r)/d⌋ = (((x+d-r)/d : ℕ) : ℤ)-1 := by
    apply Int.floor_eq_iff.mpr
    have hcast : ((x+d-r : ℕ) : ℚ) = (x : ℚ)+d-r := by
      rw [Nat.cast_sub (by omega)]
      push_cast
      ring
    have hlo : (d : ℚ)*((x+d-r)/d : ℕ) ≤ (x : ℚ)+d-r := by
      rw [← hcast]
      exact_mod_cast Nat.mul_div_le (x+d-r) d
    have hhi : (x : ℚ)+d-r < d*(((x+d-r)/d : ℕ)+1) := by
      rw [← hcast]
      exact_mod_cast Nat.lt_mul_div_succ (x+d-r) hd
    simp only [Int.cast_sub, Int.cast_one, Int.cast_natCast]
    constructor
    · apply (le_div_iff₀ (by exact_mod_cast hd)).mpr
      nlinarith
    · apply (div_lt_iff₀ (by exact_mod_cast hd)).mpr
      nlinarith
  have he : ((Finset.Ioc a b).filter (fun l => l%d = r)) =
      ((Finset.Ioc a b).filter (fun l => l ≡ r [MOD d])) := by
    ext l
    simp only [Finset.mem_filter, Nat.ModEq, Nat.mod_eq_of_lt hrd]
  have hh := Nat.Ioc_filter_modEq_card a b hd r
  rw [he]
  rw [hf a, hf b] at hh
  omega

private lemma progression_count (n d L q r : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hrd : r < d)
    (hlaw : ∀ l, q*l % d = n % d ↔ l % d = r) :
    ((Finset.range (L*n)).filter (fun j => q ∣ n+d*(j+1))).card =
      ((1+d*L)*n/q+d-r)/d - (n/q+d-r)/d := by
  classical
  calc
    _ = ((Finset.Ioc (n/q) ((1+d*L)*n/q)).filter (fun l => l%d = r)).card := by
      apply Finset.card_bij (fun j _ => (n+d*(j+1))/q)
      · intro j hj
        simp only [Finset.mem_filter, Finset.mem_range] at hj
        have he : q*((n+d*(j+1))/q) = n+d*(j+1) := Nat.mul_div_cancel' hj.2
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨(Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith),
          (Nat.le_div_iff_mul_le hq).mpr (by nlinarith)⟩, ?_⟩
        apply (hlaw _).mp
        rw [he]
        simp [Nat.add_mod]
      · intro j hj k hk heq
        simp only [Finset.mem_filter, Finset.mem_range] at hj hk
        have hej := Nat.mul_div_cancel' hj.2
        have hek := Nat.mul_div_cancel' hk.2
        rw [heq] at hej
        nlinarith
      · intro l hl
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hl
        have hlo : n < q*l := by
          have := (Nat.div_lt_iff_lt_mul hq).mp hl.1.1
          nlinarith
        have hhi : q*l ≤ (1+d*L)*n := by
          have := (Nat.le_div_iff_mul_le hq).mp hl.1.2
          nlinarith
        have hm : q*l % d = n % d := (hlaw l).mpr hl.2
        have hdvd : d ∣ q*l-n := (Nat.modEq_iff_dvd' hlo.le).mp hm.symm
        obtain ⟨t, ht⟩ := hdvd
        have ht' : q*l = n+d*t := by omega
        have htpos : 0 < t := by nlinarith
        have htmax : t ≤ L*n := by nlinarith
        have hj : n+d*((t-1)+1) = q*l := by rw [Nat.sub_add_cancel htpos]; omega
        refine ⟨t-1, ?_, ?_⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, hj ▸ dvd_mul_right q l⟩
        · rw [hj, Nat.mul_div_right _ hq]
    _ = _ := residue_count _ _ _ _ hd hrd

private lemma local_bound (d M B C L n q r : ℕ) (hpar : Parameters d M B C L)
    (hq : 0 < q) (hrd : r < d) :
    (M*n/q+d-r)/d + B*n/q + C*n/q ≤ M*n/q + (n/q+d-r)/d := by
  rcases hpar with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩
  · let s := n % (3*q)
    have hs : s < 3*q := Nat.mod_lt n (by omega)
    have split (c : ℕ) : c*n/q = 3*c*(n/(3*q))+c*s/q := by
      simpa only [Nat.mul_assoc, Nat.mul_div_mul_left _ _ (by decide : 0 < 3)] using
        mul_div_reduce (3*c) n (3*q) (by omega)
    have hs1 : n/q = 3*(n/(3*q))+s/q := by simpa using split 1
    rw [split 10, split 5, split 2, hs1]
    have h1 : s/q = (10*s/q)/10 := by simpa using grid_floor 10 1 10 s q hq (by decide) (by decide)
    have h5 : 5*s/q = (10*s/q)/2 := grid_floor 10 5 2 s q hq (by decide) (by decide)
    have h2 : 2*s/q = (10*s/q)/5 := grid_floor 10 2 5 s q hq (by decide) (by decide)
    have hb : 10*s/q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [h1,h5,h2]
    have small (t v r : ℕ) (hv : v < 30) (hrd : r < 3) :
        (30*t+v+3-r)/3 + (15*t+v/2) + (6*t+v/5) ≤
          30*t+v+(3*t+v/10+3-r)/3 := by
      interval_cases v <;> interval_cases r <;> omega
    exact small (n/(3*q)) (10*s/q) r hb hrd
  · let s := n % (5*q)
    have hs : s < 5*q := Nat.mod_lt n (by omega)
    have split (c : ℕ) : c*n/q = 5*c*(n/(5*q))+c*s/q := by
      simpa only [Nat.mul_assoc, Nat.mul_div_mul_left _ _ (by decide : 0 < 5)] using
        mul_div_reduce (5*c) n (5*q) (by omega)
    have hs1 : n/q = 5*(n/(5*q))+s/q := by simpa using split 1
    rw [split 6, split 3, split 2, hs1]
    have h1 : s/q = (6*s/q)/6 := by simpa using grid_floor 6 1 6 s q hq (by decide) (by decide)
    have h3 : 3*s/q = (6*s/q)/2 := grid_floor 6 3 2 s q hq (by decide) (by decide)
    have h2 : 2*s/q = (6*s/q)/3 := grid_floor 6 2 3 s q hq (by decide) (by decide)
    have hb : 6*s/q < 30 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [h1,h3,h2]
    have small (t v r : ℕ) (hv : v < 30) (hrd : r < 5) :
        (30*t+v+5-r)/5 + (15*t+v/2) + (10*t+v/3) ≤
          30*t+v+(5*t+v/6+5-r)/5 := by
      interval_cases v <;> interval_cases r <;> omega
    exact small (n/(5*q)) (6*s/q) r hb hrd

private lemma progression_floor_bound (d M B C L n q : ℕ) (hpar : Parameters d M B C L)
    (hq : 0 < q) (hcop : Nat.Coprime q d) :
    B*n/q + C*n/q + ((Finset.range (L*n)).filter (fun j => q ∣ n+d*(j+1))).card ≤ M*n/q := by
  have hd : 0 < d := by rcases hpar with h|h <;> omega
  have hM : M = 1+d*L := by rcases hpar with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ <;> norm_num
  obtain ⟨r, hrd, hqr⟩ := Nat.exists_mul_mod_eq_of_coprime n hcop hd.ne'
  have hlaw (l : ℕ) : q*l % d = n % d ↔ l % d = r := by
    constructor
    · intro h
      have hm : q*l ≡ q*r [MOD d] := h.trans hqr.symm
      have hc := Nat.ModEq.cancel_left_of_coprime hcop.symm hm
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hrd] using hc
    · intro h
      have hm : l ≡ r [MOD d] := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt hrd] using h
      exact (hm.mul_left q).trans hqr
  rw [progression_count n d L q r hd hq hrd hlaw, ← hM]
  have hb := local_bound d M B C L n q r hpar hq hrd
  have hm : (n/q+d-r)/d ≤ (M*n/q+d-r)/d := by
    apply Nat.div_le_div_right
    apply Nat.sub_le_sub_right
    have hmn : n ≤ M*n := Nat.le_mul_of_pos_left n (by rw [hM]; omega)
    exact Nat.add_le_add_right (Nat.div_le_div_right hmn) _
  omega


lemma progression_ne_zero (d L n : ℕ) (hd : 0 < d) : progression d L n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  positivity

private lemma progression_padic (d M L n p : ℕ) [hp : Fact p.Prime]
    (hd : 0 < d) (hM : M = 1+d*L) :
    padicValNat p (progression d L n) =
      ∑ k ∈ Finset.Ico 1 (M*n+1),
        ((Finset.range (L*n)).filter (fun j => p^k ∣ n+d*(j+1))).card := by
  classical
  rw [progression, D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral.padic_finset_prod p _ _ (by intro i hi; positivity)]
  have one (j : ℕ) (hj : j ∈ Finset.range (L*n)) :
      padicValNat p (n+d*(j+1)) =
        ∑ k ∈ Finset.Ico 1 (M*n+1), if p^k ∣ n+d*(j+1) then 1 else 0 := by
    rw [D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral.padic_eq_card p (n+d*(j+1)) (M*n+1) (by positivity)
      (lt_of_le_of_lt (p.log_le_self _) (by
        simp only [Finset.mem_range] at hj
        rw [hM]
        nlinarith))]
    exact (Finset.sum_boole (fun k : ℕ => p^k ∣ n+d*(j+1)) (Finset.Ico 1 (M*n+1))).symm
  rw [show (∑ j ∈ Finset.range (L*n), padicValNat p (n+d*(j+1))) =
    ∑ j ∈ Finset.range (L*n), ∑ k ∈ Finset.Ico 1 (M*n+1),
      if p^k ∣ n+d*(j+1) then 1 else 0 from Finset.sum_congr rfl one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  exact Finset.sum_boole _ _

lemma nonmultiple_dvd (d M B C L n : ℕ) (hpar : Parameters d M B C L) (hn : ¬d ∣ n) :
    (B*n).factorial * (C*n).factorial * progression d L n ∣ (M*n).factorial := by
  classical
  have hd : 0 < d := by rcases hpar with h|h <;> omega
  have hprime : d.Prime := by rcases hpar with h|h <;> rcases h with ⟨rfl,-,-,-,-⟩ <;> decide
  have hM : M = 1+d*L := by rcases hpar with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ <;> norm_num
  have hBC : B+C ≤ M := by rcases hpar with ⟨rfl,rfl,rfl,rfl,rfl⟩ | ⟨rfl,rfl,rfl,rfl,rfl⟩ <;> norm_num
  apply (Nat.factorization_prime_le_iff_dvd
    (mul_ne_zero (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (progression_ne_zero d L n hd)) (Nat.factorial_ne_zero _)).mp
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
    padicValNat.mul (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (progression_ne_zero d L n hd),
    padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  by_cases hpd : p = d
  · subst p
    have hz : padicValNat d (progression d L n) = 0 := by
      rw [progression, D5.S3.Arith.FactorialRatio.OeisA347855BalaThirdIndexIntegral.padic_finset_prod d _ _ (by intro i hi; positivity)]
      apply Finset.sum_eq_zero
      intro j hj
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      apply hn
      exact (Nat.dvd_add_iff_left (dvd_mul_right d (j+1))).mpr h
    rw [hz, add_zero]
    have hdiv : (B*n).factorial*(C*n).factorial ∣ (M*n).factorial :=
      (Nat.factorial_mul_factorial_dvd_factorial_add (B*n) (C*n)).trans
        (Nat.factorial_dvd_factorial (by nlinarith))
    have hh := (Nat.factorization_prime_le_iff_dvd
      (mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _))
      (Nat.factorial_ne_zero _)).mpr hdiv d hp
    simpa only [Nat.factorization_def _ hp,
      padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)] using hh
  · have vf (m : ℕ) (hm : m ≤ M*n) :
        padicValNat p m.factorial = ∑ k ∈ Finset.Ico 1 (M*n+1), m / p^k :=
      padicValNat_factorial (lt_of_le_of_lt (p.log_le_self m) (by omega))
    rw [vf (B*n) (by nlinarith), vf (C*n) (by nlinarith), vf (M*n) le_rfl,
      progression_padic d M L n p hd hM]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro k hk
    have hcop : Nat.Coprime (p^k) d := (hp.coprime_iff_not_dvd.mpr (by
      intro hdiv
      have he : p = d := ((Nat.dvd_prime hprime).mp hdiv).resolve_left hp.ne_one
      exact hpd he)).pow_left k
    exact progression_floor_bound d M B C L n (p^k) hpar (pow_pos hp.pos k) hcop

lemma gamma_ratio (d L n : ℕ) (hd : 0 < d) :
    Real.Gamma ((n : ℝ)/d+1) / Real.Gamma (((1+d*L : ℕ) : ℝ)*n/d+1) =
      (d : ℝ)^(L*n) / (progression d L n : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hx : (0 : ℝ) < (n : ℝ)/d+1 := by positivity
  have he : (((1+d*L : ℕ) : ℝ)*(n : ℝ)/d+1) = (n/d+1)+(L*n : ℕ) := by
    push_cast
    field_simp
    ring
  rw [he, D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral.gamma_shift_product _ hx]
  have hprod : (∏ k ∈ Finset.range (L*n), ((n : ℝ)/d+1+k)) * (d : ℝ)^(L*n) =
      (progression d L n : ℝ) := by
    rw [show (d : ℝ)^(L*n) = ∏ _k ∈ Finset.range (L*n), (d : ℝ) by simp,
      ← Finset.prod_mul_distrib]
    simp only [progression, Nat.cast_prod, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    apply Finset.prod_congr rfl
    intro k hk
    field_simp
    ring
  have hnR : (progression d L n : ℝ) ≠ 0 := by exact_mod_cast progression_ne_zero d L n hd
  have hG : Real.Gamma ((n : ℝ)/d+1) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
  have hGprod : (∏ k ∈ Finset.range (L*n), ((n : ℝ)/d+1+k)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    positivity
  apply (div_eq_div_iff (mul_ne_zero hG hGprod) hnR).mpr
  rw [← hprod]
  ring

lemma ordinary_dvd (m : ℕ) :
    (15*m).factorial*(10*m).factorial*(6*m).factorial ∣ (30*m).factorial*m.factorial := by
  have hb := D5.S3.Arith.FactorialRatio.BalaChebyshevFiveDivisibility.bala_five_integrality m
  have hid : (5*m+1)*(15*m).factorial*(10*m).factorial*(6*m).factorial =
      (5*m+1)*((15*m).factorial*(10*m).factorial*(6*m).factorial) := by ring
  rw [hid] at hb
  exact (dvd_mul_left _ _).trans hb


noncomputable def a (n : ℕ) : ℝ :=
  ((10 * n).factorial : ℝ) * Real.Gamma ((n : ℝ) / 3 + 1) /
    (((5 * n).factorial : ℝ) * Real.Gamma ((10 * (n : ℝ)) / 3 + 1) * ((2 * n).factorial : ℝ))

def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, a n = (z : ℝ)


private lemma a_formula (n : ℕ) : a n = (3 : ℝ)^(3*n) *
    ((10*n).factorial : ℝ) /
      ((5*n).factorial * ((2*n).factorial : ℝ) * progression 3 3 n) := by
  have hr := gamma_ratio 3 3 n (by decide)
  norm_num only [Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at hr
  calc
    a n = ((10*n).factorial : ℝ) / ((5*n).factorial * ((2*n).factorial : ℝ)) *
        (Real.Gamma ((n : ℝ)/3+1) / Real.Gamma ((10*(n : ℝ))/3+1)) := by
      unfold a
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      rw [hr]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private lemma multiple_formula (m : ℕ) : a (3*m) =
    ((30*m).factorial : ℝ) * m.factorial /
      ((15*m).factorial * ((10*m).factorial : ℝ) * ((6*m).factorial : ℝ)) := by
  unfold a
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show (3*(m : ℝ))/3+1 = m+1 by ring,
    show (10*(3*(m : ℝ)))/3+1 = (10*m : ℕ)+1 by push_cast; ring,
    Real.Gamma_nat_eq_factorial, Real.Gamma_nat_eq_factorial]
  norm_num [show 10*(3*m) = 30*m by omega,
    show 5*(3*m) = 15*m by omega,
    show 2*(3*m) = 6*m by omega]

theorem result : claim := by
  intro n
  by_cases hn : 3 ∣ n
  · obtain ⟨m,rfl⟩ := hn
    rw [multiple_formula]
    obtain ⟨z,hz⟩ := quotient_cast_integral (ordinary_dvd m) (by positivity)
    exact ⟨z, by simpa only [Nat.cast_mul] using hz.symm⟩
  · rw [a_formula]
    obtain ⟨z,hz⟩ := quotient_cast_integral
      (nonmultiple_dvd 3 10 5 2 3 n (by norm_num [Parameters]) hn)
      (by have := progression_ne_zero 3 3 n (by decide); positivity)
    refine ⟨(3 : ℤ)^(3*n)*z, ?_⟩
    push_cast
    rw [hz]
    push_cast
    ring

end D5.S3.Arith.FactorialRatio.OeisA276101BalaThirdIndexIntegral
