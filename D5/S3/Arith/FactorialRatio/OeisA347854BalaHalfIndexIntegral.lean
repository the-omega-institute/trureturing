/- GID: D5/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral
   generality: I
   mirror-B: D5/B/S3/Arith/FactorialRatio/OeisA347854BalaHalfIndexIntegral
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Bala's A347854 fractional-factorial integrality. -/

/-
escape_witness: none
admission_basis: open-problem-resolution (#18690; Proved)
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19874
The fractional factorial and sequence definitions retain the source expressions.
No finite computational declaration refutes the claim; utility is none.
Declarations (all dependencies outside this delivery are pinned Mathlib):
  ffact: proof_shape: bind-only; escape_witness: none;
    consumers: a, even_formula, OeisA347855BalaThirdIndexIntegral.a, OeisA347855BalaThirdIndexIntegral.multiple_three_formula, OeisA347856BalaHalfIndexIntegral.a, OeisA347856BalaHalfIndexIntegral.even_formula, OeisA347857BalaHalfIndexIntegral.a, OeisA347857BalaHalfIndexIntegral.even_formula, OeisA347858BalaHalfIndexIntegral.a, OeisA347858BalaHalfIndexIntegral.even_formula. Direct frozen dependencies: none.
  a: proof_shape: bind-only; escape_witness: none;
    consumers: claim, even_formula, odd_formula, result. Direct frozen dependencies: none.
  claim: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  factorial_prod_ne_zero: proof_shape: bind-only; escape_witness: none;
    consumers: factorial_prod_dvd_of_floor. Direct frozen dependencies: none.
  padic_prod_factorial: proof_shape: bind-only; escape_witness: none;
    consumers: factorial_prod_dvd_of_floor. Direct frozen dependencies: none.
  factorial_prod_dvd_of_floor: proof_shape: bind-only; escape_witness: none;
    consumers: even_dvd, odd_dvd, OeisA347856BalaHalfIndexIntegral.even_dvd, OeisA347856BalaHalfIndexIntegral.odd_dvd, OeisA347857BalaHalfIndexIntegral.even_dvd, OeisA347857BalaHalfIndexIntegral.odd_dvd, OeisA347858BalaHalfIndexIntegral.even_dvd, OeisA347858BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  quotient_cast_integral: proof_shape: bind-only; escape_witness: none;
    consumers: result, OeisA347855BalaThirdIndexIntegral.result, OeisA347856BalaHalfIndexIntegral.result, OeisA347857BalaHalfIndexIntegral.result, OeisA347858BalaHalfIndexIntegral.result. Direct frozen dependencies: none.
  mul_div_reduce: proof_shape: bind-only; escape_witness: none;
    consumers: h854_nonneg, h856_nonneg, h857_nonneg, h858_nonneg, k854_nonneg, k856_nonneg, k857_nonneg, k858_nonneg, OeisA347855BalaThirdIndexIntegral.third_local_bound. Direct frozen dependencies: none.
  grid_floor: proof_shape: bind-only; escape_witness: none;
    consumers: h854_nonneg, h856_nonneg, h857_nonneg, h858_nonneg, k854_nonneg, k856_nonneg, k857_nonneg, k858_nonneg, odd_dvd, OeisA347855BalaThirdIndexIntegral.third_local_bound, OeisA347856BalaHalfIndexIntegral.odd_dvd, OeisA347857BalaHalfIndexIntegral.odd_dvd, OeisA347858BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  h854: proof_shape: bind-only; escape_witness: none;
    consumers: even_dvd, h854_nonneg. Direct frozen dependencies: none.
  h854_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: even_dvd. Direct frozen dependencies: none.
  h856: proof_shape: bind-only; escape_witness: none;
    consumers: h856_nonneg, OeisA347856BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  h856_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347856BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  h857: proof_shape: bind-only; escape_witness: none;
    consumers: h857_nonneg, OeisA347857BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  h857_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347857BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  h858: proof_shape: bind-only; escape_witness: none;
    consumers: h858_nonneg, OeisA347858BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  h858_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347858BalaHalfIndexIntegral.even_dvd. Direct frozen dependencies: none.
  k854: proof_shape: bind-only; escape_witness: none;
    consumers: k854_nonneg, odd_dvd. Direct frozen dependencies: none.
  k854_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: odd_dvd. Direct frozen dependencies: none.
  k856: proof_shape: bind-only; escape_witness: none;
    consumers: k856_nonneg, OeisA347856BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  k856_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347856BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  k857: proof_shape: bind-only; escape_witness: none;
    consumers: k857_nonneg, OeisA347857BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  k857_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347857BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  k858: proof_shape: bind-only; escape_witness: none;
    consumers: k858_nonneg, OeisA347858BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  k858_nonneg: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347858BalaHalfIndexIntegral.odd_dvd. Direct frozen dependencies: none.
  gamma_half: proof_shape: bind-only; escape_witness: none;
    consumers: gamma_half_of_odd. Direct frozen dependencies: none.
  gamma_half_of_odd: proof_shape: bind-only; escape_witness: none;
    consumers: gamma_ratio_half. Direct frozen dependencies: none.
  gamma_nat: proof_shape: bind-only; escape_witness: none;
    consumers: even_formula, OeisA347855BalaThirdIndexIntegral.multiple_three_formula, OeisA347856BalaHalfIndexIntegral.even_formula, OeisA347857BalaHalfIndexIntegral.even_formula, OeisA347858BalaHalfIndexIntegral.even_formula. Direct frozen dependencies: none.
  gamma_ratio_half: proof_shape: bind-only; escape_witness: none;
    consumers: odd_formula, OeisA347856BalaHalfIndexIntegral.odd_formula, OeisA347857BalaHalfIndexIntegral.odd_formula, OeisA347858BalaHalfIndexIntegral.odd_formula. Direct frozen dependencies: none.
  gamma_shift_product: proof_shape: bind-only; escape_witness: none;
    consumers: gamma_third_ratio. Direct frozen dependencies: none.
  gamma_third_ratio: proof_shape: bind-only; escape_witness: none;
    consumers: OeisA347855BalaThirdIndexIntegral.a_formula. Direct frozen dependencies: none.
  even_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: result, OeisA347855BalaThirdIndexIntegral.result. Direct frozen dependencies: none.
  even_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  odd_dvd: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  odd_formula: proof_shape: bind-only; escape_witness: none;
    consumers: result. Direct frozen dependencies: none.
  result: proof_shape: bind-only; escape_witness: none;
    consumers: settling result. Direct frozen dependencies: none.
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

set_option autoImplicit false

namespace D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

/-- Fractional factorials are defined using the Gamma function: `x! := Γ(1 + x)`. -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (1 + x)

/-- A347854: `a(n) = (6*n)!/((3*n)!*(2*n)!) * (n/2)!/(3*n/2)!`. -/
noncomputable def a (n : ℕ) : ℝ :=
  (Nat.factorial (6 * n) : ℝ) / ((Nat.factorial (3 * n) : ℝ) * (Nat.factorial (2 * n) : ℝ)) *
    (ffact ((n : ℝ) / 2) / ffact (3 * (n : ℝ) / 2))

/-- A347854 ("The sequence is conjectured to be integral."). -/
def claim : Prop := ∀ n : ℕ, ∃ z : ℤ, (z : ℝ) = a n

end D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

set_option maxHeartbeats 800000

set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma factorial_prod_ne_zero (L : List ℕ) : (L.map Nat.factorial).prod ≠ 0 := by
  simp [Nat.factorial_ne_zero]

private lemma padic_prod_factorial (p : ℕ) [hp : Fact p.Prime] (L : List ℕ) :
    padicValNat p (L.map Nat.factorial).prod = (L.map (fun n => padicValNat p n.factorial)).sum := by
  rw [← Fin.prod_univ_fun_getElem L Nat.factorial, ← Fin.sum_univ_fun_getElem L (fun n => padicValNat p n.factorial)]
  have hf (i : Fin L.length) (_hi : i ∈ Finset.univ) : (L[i.val]).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hh : (padicValNat p (∏ i : Fin L.length, (L[i.val]).factorial) : ℕ∞) =
      ((∑ i : Fin L.length, padicValNat p (L[i.val]).factorial : ℕ) : ℕ∞) := by
    rw [padicValNat_eq_emultiplicity (Finset.prod_ne_zero_iff.mpr hf), Nat.cast_sum]
    exact (Finset.emultiplicity_prod (Nat.prime_iff.mp hp.out) Finset.univ (fun i : Fin L.length => (L[i.val]).factorial)).trans
      (Finset.sum_congr rfl (fun i hi => (padicValNat_eq_emultiplicity (hf i hi)).symm))
  exact_mod_cast hh

lemma factorial_prod_dvd_of_floor (A B : List ℕ)
    (h : ∀ q : ℕ, 0 < q →
      (B.map (fun n => n / q)).sum ≤ (A.map (fun n => n / q)).sum) :
    (B.map Nat.factorial).prod ∣ (A.map Nat.factorial).prod := by
    classical
    apply (Nat.factorization_prime_le_iff_dvd (factorial_prod_ne_zero B)
      (factorial_prod_ne_zero A)).mp
    intro p hp
    letI : Fact p.Prime := ⟨hp⟩
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp,
      padic_prod_factorial, padic_prod_factorial]
    let bound := (A ++ B).sum + 1
    have vf (m : ℕ) (hm : m ∈ A ++ B) :
        padicValNat p m.factorial = ∑ j ∈ Finset.Ico 1 bound, m / p^j := by
      apply padicValNat_factorial
      have hh : m ≤ (A ++ B).sum := List.le_sum_of_mem hm
      exact lt_of_le_of_lt (p.log_le_self m) (by dsimp [bound]; omega)
    have swap (L : List ℕ) (hL : ∀ x ∈ L, x ∈ A ++ B) :
        (L.map (fun n => padicValNat p n.factorial)).sum =
          ∑ j ∈ Finset.Ico 1 bound, (L.map (fun n => n / p^j)).sum := by
      calc
        _ = (L.map (fun n => ∑ j ∈ Finset.Ico 1 bound, n / p^j)).sum := by
          congr 1
          apply List.map_congr_left
          intro n hn
          exact vf n (hL n hn)
        _ = _ := by
          simpa only [Multiset.map_coe, Multiset.sum_coe] using
            (Multiset.sum_map_sum (m := (L : Multiset ℕ)) (s := Finset.Ico 1 bound) (f := fun n j => n / p^j))
    rw [swap B (by intro x hx; exact List.mem_append_right A hx),
      swap A (by intro x hx; exact List.mem_append_left B hx)]
    exact Finset.sum_le_sum (fun j _ => h (p^j) (pow_pos hp.pos j))

lemma quotient_cast_integral {A B : ℕ} (h : B ∣ A) (hB : B ≠ 0) :
    ∃ z : ℤ, (z : ℝ) = (A : ℝ) / (B : ℝ) := by
    obtain ⟨k, hk⟩ := h
    refine ⟨(k : ℤ), ?_⟩
    rw [hk]
    push_cast
    field_simp

lemma mul_div_reduce (c n q : ℕ) (hq : 0 < q) :
    c*n/q = c*(n/q)+c*(n%q)/q := by
    calc
      c*n/q = (q*(c*(n/q))+c*(n%q))/q := by
        congr 1
        have := Nat.div_add_mod n q
        nlinarith
      _ = c*(n/q)+c*(n%q)/q := by rw [Nat.mul_add_div hq]

lemma grid_floor (L c d r q : ℕ) (hq : 0 < q) (hd : 0 < d) (hcd : L = c*d) :
    c*r/q = (L*r/q)/d := by
    rw [Nat.div_div_eq_div_mul, hcd,
      show c*d*r = d*(c*r) by ring,
      show q*d = d*q by ring, Nat.mul_div_mul_left _ _ hd]

end D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral


set_option autoImplicit false
namespace D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private def h854 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ) - (((6*n/q : ℕ) : ℤ) + ((4*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ))

private lemma h854_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ h854 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : h854 n q = h854 r q := by
      unfold h854
      rw [split 12, split 6, split 4, split 3, split 1]
      push_cast
      ring
    rw [red]
    unfold h854
    have g1 : 1*r/q = (12*r/q)/12 := grid_floor 12 1 12 r q hq (by decide) (by decide)
    have g3 : 3*r/q = (12*r/q)/4 := grid_floor 12 3 4 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (12*r/q)/3 := grid_floor 12 4 3 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (12*r/q)/2 := grid_floor 12 6 2 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (12*r/q)/1 := grid_floor 12 12 1 r q hq (by decide) (by decide)
    have hb : 12*r/q < 12 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g3, g4, g6, g12]
    omega

def h856 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ) - (((8*n/q : ℕ) : ℤ) + ((2*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ))

lemma h856_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ h856 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : h856 n q = h856 r q := by
      unfold h856
      rw [split 12, split 8, split 3, split 2, split 1]
      push_cast
      ring
    rw [red]
    unfold h856
    have g1 : 1*r/q = (24*r/q)/24 := grid_floor 24 1 24 r q hq (by decide) (by decide)
    have g2 : 2*r/q = (24*r/q)/12 := grid_floor 24 2 12 r q hq (by decide) (by decide)
    have g3 : 3*r/q = (24*r/q)/8 := grid_floor 24 3 8 r q hq (by decide) (by decide)
    have g8 : 8*r/q = (24*r/q)/3 := grid_floor 24 8 3 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (24*r/q)/2 := grid_floor 24 12 2 r q hq (by decide) (by decide)
    have hb : 24*r/q < 24 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g2, g3, g8, g12]
    omega

def h857 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ) - (((6*n/q : ℕ) : ℤ) + ((4*n/q : ℕ) : ℤ) + ((5*n/q : ℕ) : ℤ))

lemma h857_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ h857 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : h857 n q = h857 r q := by
      unfold h857
      rw [split 12, split 6, split 5, split 4, split 3]
      push_cast
      ring
    rw [red]
    unfold h857
    have g3 : 3*r/q = (60*r/q)/20 := grid_floor 60 3 20 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (60*r/q)/15 := grid_floor 60 4 15 r q hq (by decide) (by decide)
    have g5 : 5*r/q = (60*r/q)/12 := grid_floor 60 5 12 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (60*r/q)/10 := grid_floor 60 6 10 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (60*r/q)/5 := grid_floor 60 12 5 r q hq (by decide) (by decide)
    have hb : 60*r/q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g3, g4, g5, g6, g12]
    omega

def h858 (n q : ℕ) : ℤ := ((18*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ) - (((6*n/q : ℕ) : ℤ) + ((4*n/q : ℕ) : ℤ) + ((9*n/q : ℕ) : ℤ))

lemma h858_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ h858 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : h858 n q = h858 r q := by
      unfold h858
      rw [split 18, split 9, split 6, split 4, split 1]
      push_cast
      ring
    rw [red]
    unfold h858
    have g1 : 1*r/q = (36*r/q)/36 := grid_floor 36 1 36 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (36*r/q)/9 := grid_floor 36 4 9 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (36*r/q)/6 := grid_floor 36 6 6 r q hq (by decide) (by decide)
    have g9 : 9*r/q = (36*r/q)/4 := grid_floor 36 9 4 r q hq (by decide) (by decide)
    have g18 : 18*r/q = (36*r/q)/2 := grid_floor 36 18 2 r q hq (by decide) (by decide)
    have hb : 36*r/q < 36 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g4, g6, g9, g18]
    omega

private def k854 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((2*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ) - (((6*n/q : ℕ) : ℤ) + ((6*n/q : ℕ) : ℤ) + ((4*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ))

private lemma k854_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ k854 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : k854 n q = k854 r q := by
      unfold k854
      rw [split 12, split 6, split 4, split 3, split 2, split 1]
      push_cast
      ring
    rw [red]
    unfold k854
    have g1 : 1*r/q = (12*r/q)/12 := grid_floor 12 1 12 r q hq (by decide) (by decide)
    have g2 : 2*r/q = (12*r/q)/6 := grid_floor 12 2 6 r q hq (by decide) (by decide)
    have g3 : 3*r/q = (12*r/q)/4 := grid_floor 12 3 4 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (12*r/q)/3 := grid_floor 12 4 3 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (12*r/q)/2 := grid_floor 12 6 2 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (12*r/q)/1 := grid_floor 12 12 1 r q hq (by decide) (by decide)
    have hb : 12*r/q < 12 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g2, g3, g4, g6, g12]
    omega

def k856 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ) - (((8*n/q : ℕ) : ℤ) + ((6*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ))

lemma k856_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ k856 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : k856 n q = k856 r q := by
      unfold k856
      rw [split 12, split 8, split 6, split 3, split 1]
      push_cast
      ring
    rw [red]
    unfold k856
    have g1 : 1*r/q = (24*r/q)/24 := grid_floor 24 1 24 r q hq (by decide) (by decide)
    have g3 : 3*r/q = (24*r/q)/8 := grid_floor 24 3 8 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (24*r/q)/4 := grid_floor 24 6 4 r q hq (by decide) (by decide)
    have g8 : 8*r/q = (24*r/q)/3 := grid_floor 24 8 3 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (24*r/q)/2 := grid_floor 24 12 2 r q hq (by decide) (by decide)
    have hb : 24*r/q < 24 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g3, g6, g8, g12]
    omega

def k857 (n q : ℕ) : ℤ := ((12*n/q : ℕ) : ℤ) + ((5*n/q : ℕ) : ℤ) - (((4*n/q : ℕ) : ℤ) + ((10*n/q : ℕ) : ℤ) + ((3*n/q : ℕ) : ℤ))

lemma k857_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ k857 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : k857 n q = k857 r q := by
      unfold k857
      rw [split 12, split 10, split 5, split 4, split 3]
      push_cast
      ring
    rw [red]
    unfold k857
    have g3 : 3*r/q = (60*r/q)/20 := grid_floor 60 3 20 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (60*r/q)/15 := grid_floor 60 4 15 r q hq (by decide) (by decide)
    have g5 : 5*r/q = (60*r/q)/12 := grid_floor 60 5 12 r q hq (by decide) (by decide)
    have g10 : 10*r/q = (60*r/q)/6 := grid_floor 60 10 6 r q hq (by decide) (by decide)
    have g12 : 12*r/q = (60*r/q)/5 := grid_floor 60 12 5 r q hq (by decide) (by decide)
    have hb : 60*r/q < 60 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g3, g4, g5, g10, g12]
    omega

def k858 (n q : ℕ) : ℤ := ((2*n/q : ℕ) : ℤ) + ((9*n/q : ℕ) : ℤ) - (((6*n/q : ℕ) : ℤ) + ((4*n/q : ℕ) : ℤ) + ((1*n/q : ℕ) : ℤ))

lemma k858_nonneg (n q : ℕ) (hq : 0 < q) : 0 ≤ k858 n q := by
    let r := n % q
    have hr : r < q := Nat.mod_lt n hq
    have split (c : ℕ) : c*n/q = c*(n/q)+c*r/q := mul_div_reduce c n q hq
    have red : k858 n q = k858 r q := by
      unfold k858
      rw [split 9, split 6, split 4, split 2, split 1]
      push_cast
      ring
    rw [red]
    unfold k858
    have g1 : 1*r/q = (36*r/q)/36 := grid_floor 36 1 36 r q hq (by decide) (by decide)
    have g2 : 2*r/q = (36*r/q)/18 := grid_floor 36 2 18 r q hq (by decide) (by decide)
    have g4 : 4*r/q = (36*r/q)/9 := grid_floor 36 4 9 r q hq (by decide) (by decide)
    have g6 : 6*r/q = (36*r/q)/6 := grid_floor 36 6 6 r q hq (by decide) (by decide)
    have g9 : 9*r/q = (36*r/q)/4 := grid_floor 36 9 4 r q hq (by decide) (by decide)
    have hb : 36*r/q < 36 := (Nat.div_lt_iff_lt_mul hq).mpr (by nlinarith)
    rw [g1, g2, g4, g6, g9]
    omega

end D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral


set_option autoImplicit false
open scoped BigOperators
namespace D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

private lemma gamma_half (h : ℕ) :
    Real.Gamma (1 + (2*(h : ℝ)+1)/2) =
      ((2*h+1).factorial : ℝ) * Real.Gamma (1/2) /
        (2^(2*h+1) * (h.factorial : ℝ)) := by
  rw [show (1 : ℝ) + (2*(h : ℝ)+1)/2 = (h : ℝ)+1+1/2 by ring,
    Real.Gamma_nat_add_one_add_half, Real.Gamma_one_half_eq,
    Nat.factorial_eq_mul_doubleFactorial, Nat.doubleFactorial_two_mul]
  push_cast
  rw [show 2*h+1 = h+h+1 by omega]
  simp only [pow_add, pow_one]
  field_simp
  <;> ring

private lemma gamma_half_of_odd (t : ℕ) (ht : t % 2 = 1) :
    Real.Gamma (1 + (t : ℝ)/2) =
      (t.factorial : ℝ) * Real.Gamma (1/2) /
        (2^t * ((t/2).factorial : ℝ)) := by
    have he : t = 2*(t/2)+1 := by omega
    have hh := gamma_half (t/2)
    have her : (2 : ℝ)*((t/2 : ℕ) : ℝ)+1 = (t : ℝ) := by exact_mod_cast he.symm
    rw [her, ← he] at hh
    exact hh

lemma gamma_nat (n : ℕ) : Real.Gamma (1 + (n : ℝ)) = (n.factorial : ℝ) := by
  simpa [add_comm] using Real.Gamma_nat_eq_factorial n

lemma gamma_ratio_half (r s : ℕ) (hr : r % 2 = 1) (hs : s % 2 = 1) (hrs : r ≤ s) :
    Real.Gamma (1 + (r : ℝ)/2) / Real.Gamma (1 + (s : ℝ)/2) =
      2^(s-r) * ((r.factorial : ℝ) * ((s/2).factorial : ℝ) /
        ((s.factorial : ℝ) * ((r/2).factorial : ℝ))) := by
    rw [gamma_half_of_odd r hr, gamma_half_of_odd s hs]
    have hG : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
    have hp : (2 : ℝ)^s = 2^(s-r)*2^r := (pow_sub_mul_pow 2 hrs).symm
    rw [hp]
    field_simp <;> ring

private lemma gamma_shift_product (x : ℝ) (hx : 0 < x) (n : ℕ) :
    Real.Gamma (x + n) = Real.Gamma x * ∏ k ∈ Finset.range n, (x + k) := by
  have hz (k : ℕ) : (x : ℂ) ≠ -(k : ℂ) := by
    intro he
    have hre := congrArg Complex.re he
    simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
    have hk := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hp : (ascPochhammer ℂ n).eval (x : ℂ) =
      ∏ k ∈ Finset.range n, ((x : ℂ) + k) := by
    have hv := ascPochhammer_eval_neg_eq_descPochhammer ℂ (-(x : ℂ)) n
    rw [neg_neg, descPochhammer_eval_eq_prod_range] at hv
    simp_rw [show ∀ k : ℕ, -(x : ℂ) - (k : ℂ) = -((x : ℂ) + (k : ℂ)) by intro k; ring] at hv
    rw [Finset.prod_neg, Finset.card_range] at hv
    simpa only [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul] using hv
  have hg := Complex.Gamma_add_nat_div_Gamma_eq (n := n) (x : ℂ) hz
  rw [hp] at hg
  have hreal : Real.Gamma (x + n) / Real.Gamma x = ∏ k ∈ Finset.range n, (x + k) := by
    apply Complex.ofReal_injective
    push_cast
    simpa only [← Complex.ofReal_natCast, ← Complex.ofReal_add, Complex.Gamma_ofReal] using hg
  simpa only [mul_comm] using (div_eq_iff (Real.Gamma_pos_of_pos hx).ne').mp hreal

lemma gamma_third_ratio (n : ℕ) :
    Real.Gamma (1+(n : ℝ)/3) / Real.Gamma (1+4*(n : ℝ)/3) =
      (3 : ℝ)^n / ∏ k ∈ Finset.range n, ((n : ℝ)+3*(k+1)) := by
    have hx : (0 : ℝ) < 1+(n : ℝ)/3 := by positivity
    have he : (1 : ℝ)+4*n/3 = (1+n/3)+n := by ring
    rw [he, gamma_shift_product _ hx]
    have hprod : (∏ k ∈ Finset.range n, ((1 : ℝ)+n/3+k)) * 3^n =
        ∏ k ∈ Finset.range n, ((n : ℝ)+3*(k+1)) := by
      rw [show (3 : ℝ)^n = ∏ _k ∈ Finset.range n, (3 : ℝ) by simp, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro k hk
      ring
    have hn : (∏ k ∈ Finset.range n, ((n : ℝ)+3*(k+1))) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro k hk
      positivity
    have hG : Real.Gamma (1+(n : ℝ)/3) ≠ 0 := (Real.Gamma_pos_of_pos hx).ne'
    field_simp
    calc
      _ = (∏ k ∈ Finset.range n, ((1 : ℝ)+n/3+k)) * 3^n := hprod.symm
      _ = _ := by
        congr 1
        apply Finset.prod_congr rfl
        intro k hk
        ring

end D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

namespace D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
open D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral

lemma even_dvd (m : ℕ) : (6*m).factorial*(4*m).factorial*(3*m).factorial ∣ (12*m).factorial*(1*m).factorial := by
    have hh := factorial_prod_dvd_of_floor [12*m, 1*m] [6*m, 4*m, 3*m]
      (by
        intro q hq
        have hc := h854_nonneg m q hq
        simp only [h854] at hc
        simpa [add_assoc] using (show 6*m/q + 4*m/q + 3*m/q ≤ 12*m/q + 1*m/q by omega))
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma even_formula (m : ℕ) : a (2*m) = (((12*m).factorial : ℝ)*((1*m).factorial : ℝ)) / (((6*m).factorial : ℝ)*((4*m).factorial : ℝ)*((3*m).factorial : ℝ)) := by
    simp only [a, ffact, Nat.cast_mul, Nat.cast_ofNat]
    rw [show (2*(m : ℝ))/2 = m by ring, show (3 : ℝ)*(2*m)/2 = (3*m) by ring]
    rw [gamma_nat, show (3 : ℝ)*(m : ℝ) = ((3*m : ℕ) : ℝ) by push_cast; ring, gamma_nat]
    norm_num [show 6*(2*m) = 12*m by omega, show 3*(2*m) = 6*m by omega, show 2*(2*m) = 4*m by omega]
    field_simp

private lemma odd_dvd (n : ℕ) : (3*n).factorial*(3*n).factorial*(2*n).factorial*(n/2).factorial ∣ (6*n).factorial*(n).factorial*(3*n/2).factorial := by
    have hh := factorial_prod_dvd_of_floor [6*n, n, 3*n/2] [3*n, 3*n, 2*n, n/2]
      (by
        intro q hq
        have hc := k854_nonneg n (2*q) (by omega)
        simp only [k854] at hc
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.div_div_eq_div_mul]
        have g1 : 1*n/q = 2*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 2 1 2 n q hq (by decide) (by decide)
        have g2 : 2*n/q = 4*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 4 2 2 n q hq (by decide) (by decide)
        have g3 : 3*n/q = 6*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 6 3 2 n q hq (by decide) (by decide)
        have g6 : 6*n/q = 12*n/(2*q) := by
          simpa only [Nat.div_div_eq_div_mul, Nat.mul_comm] using
            grid_floor 12 6 2 n q hq (by decide) (by decide)
        simp only [Nat.one_mul] at *
        omega)
    simpa only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, mul_assoc] using hh

private lemma odd_formula (n : ℕ) (hn : n % 2 = 1) : a n = (2 : ℝ)^(2*n) * ((((6*n).factorial : ℝ)*((n).factorial : ℝ)*((3*n/2).factorial : ℝ)) / (((3*n).factorial : ℝ)*((3*n).factorial : ℝ)*((2*n).factorial : ℝ)*((n/2).factorial : ℝ))) := by
    have hr : (1*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hs : (3*n) % 2 = 1 := Nat.odd_mul_odd rfl hn
    have hratio := gamma_ratio_half (1*n) (3*n) hr hs (by omega)
    rw [show 3*n-1*n = 2*n by omega] at hratio
    simp only [Nat.cast_mul, Nat.cast_ofNat, one_mul] at hratio
    simp only [a, ffact]
    rw [hratio]
    field_simp

theorem result : claim := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have he : n = 2*(n/2) := by omega
      rw [he, even_formula]
      obtain ⟨z, hz⟩ := quotient_cast_integral (even_dvd (n/2)) (by positivity)
      exact ⟨z, by simpa only [Nat.cast_mul] using hz⟩
    · rw [odd_formula n hn]
      obtain ⟨z, hz⟩ := quotient_cast_integral (odd_dvd n) (by positivity)
      refine ⟨(2 : ℤ)^(2*n)*z, ?_⟩
      push_cast
      rw [hz]
      push_cast
      ring

end D5.S3.Arith.FactorialRatio.OeisA347854BalaHalfIndexIntegral
