/- GID: D5/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution
   generality: G
   mirror-B: D5/B/S3/Arith/Divisors/OeisA252505FourthPowerFreeConvolution
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The whole A252505 fourth-power-free divisor convolution. -/

/- The complete result has admission_basis=open-problem-resolution (#27491).
   The independent rational-solution count, exponent-box convolution and integer
   parity argument are on its live proof path. The theorem includes n=1.
   Definitions and library-only interfaces are implementation structure; the
   finite residue calculations support the universal symbolic proof.
   The unfinished source-family audit is
   https://github.com/the-omega-institute/trureturing/issues/27506.
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Factorization.Divisors
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution

open Finset ArithmeticFunction
noncomputable section

/-- No prime fourth power divides the positive integer being counted. -/
def FourthPowerFree (d : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p ^ 4 ∣ d

/-- A252505, defined by its positive-divisor counting problem. -/
def a (n : ℕ) : ℤ := by
  classical
  exact ((n.divisors.filter (fun d => FourthPowerFree d)).card : ℤ)

/-- The original rational equation, including equal denominators. -/
def UnitFractionPair (n : ℕ) (xy : ℕ × ℕ) : Prop :=
  0 < xy.1 ∧ 0 < xy.2 ∧ xy.1 ≤ xy.2 ∧
    (1 / (n : ℚ) = 1 / (xy.1 : ℚ) + 1 / (xy.2 : ℚ))

/-- A018892 counts the actual positive solutions, rather than a divisor formula. -/
def b (n : ℕ) : ℤ := (Nat.card {xy : ℕ × ℕ // UnitFractionPair n xy} : ℤ)

/-- Ordinary positive divisor count. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- A140773 uses the ordinary ceiling after rational division. -/
def h (n : ℕ) : ℤ := ∑ d ∈ n.divisors, (⌈(tau d : ℚ) / 2⌉₊ : ℤ)

/-- A369255 is the integer remainder, with values zero and one. -/
def g (n : ℕ) : ℤ := h n % 2

private theorem g_one : g 1 = 1 := by
  have hc : ⌈(1 : ℚ) / 2⌉₊ = 1 := (Nat.ceil_eq_iff (by decide)).mpr (by norm_num)
  norm_num [g, h, tau, hc]

private def gFunction : ArithmeticFunction ℤ :=
  ⟨g, by simp [g, h]⟩

@[instance_reducible] private def gOneInvertible : Invertible (gFunction 1) := by
  have he : gFunction 1 = 1 := g_one
  rw [he]
  exact invertibleOne

/-- A378214, the canonical recursive Dirichlet inverse of the independently defined g. -/
def c (n : ℕ) : ℤ := ArithmeticFunction.dirichletInverse gFunction gOneInvertible n

/-- The unchanged all-positive-integer OEIS A252505 conjecture. -/
def claim : Prop :=
  ∀ n : ℕ, 1 ≤ n → a n = ∑ d ∈ n.divisors, b d * c (n / d)

/-- The independent source recursion, without its irrelevant value at zero. -/
def InverseRecursion (v : ℕ → ℤ) : Prop :=
  v 1 = 1 ∧ ∀ n : ℕ, 1 < n →
    v n = - ∑ d ∈ n.properDivisors, g (n / d) * v d

private theorem unit_fraction_iff_factor {n x y : ℕ}
    (hn : 0 < n) (hx : 0 < x) (hy : 0 < y) :
    (1 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ)) ↔
      n < x ∧ n < y ∧ (x - n) * (y - n) = n ^ 2 := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hxq : (x : ℚ) ≠ 0 := by exact_mod_cast hx.ne'
  have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
  have heq : (1 / (n : ℚ) = 1 / (x : ℚ) + 1 / (y : ℚ)) ↔
      x * y = n * (x + y) := by
    constructor
    · intro H
      field_simp at H
      exact_mod_cast (show (x : ℚ) * y = n * (x + y) by nlinarith [H])
    · intro H
      have Hq : (x : ℚ) * y = n * (x + y) := by exact_mod_cast H
      field_simp
      nlinarith [Hq]
  rw [heq]
  constructor
  · intro H
    have hnx : n < x := by
      by_contra hh
      have hh' : x ≤ n := by omega
      have := Nat.mul_le_mul_right y hh'
      nlinarith
    have hny : n < y := by
      by_contra hh
      have hh' : y ≤ n := by omega
      have := Nat.mul_le_mul_left x hh'
      nlinarith
    refine ⟨hnx, hny, ?_⟩
    have hxn : x = n + (x - n) := by omega
    have hyn : y = n + (y - n) := by omega
    nlinarith
  · rintro ⟨hnx, hny, H⟩
    have hxn : x = n + (x - n) := by omega
    have hyn : y = n + (y - n) := by omega
    nlinarith


/-- Positive factor pairs, ordered by size; the diagonal is retained. -/
def factorPairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (n ^ 2).divisorsAntidiagonal.filter (fun uv => uv.1 ≤ uv.2)

private def unitFractionEquiv (n : ℕ) (hn : 0 < n) :
    {xy : ℕ × ℕ // UnitFractionPair n xy} ≃ ↥(factorPairs n) where
  toFun xy := by
    have H := (unit_fraction_iff_factor hn xy.property.1 xy.property.2.1).mp
      xy.property.2.2.2
    exact ⟨(xy.val.1 - n, xy.val.2 - n),
      Finset.mem_filter.mpr ⟨Nat.mem_divisorsAntidiagonal.mpr
        ⟨H.2.2, pow_ne_zero _ hn.ne'⟩,
        Nat.sub_le_sub_right xy.property.2.2.1 n⟩⟩
  invFun uv := by
    have H := Finset.mem_filter.mp uv.property
    have hu := Nat.left_ne_zero_of_mem_divisorsAntidiagonal H.1
    have hv := Nat.right_ne_zero_of_mem_divisorsAntidiagonal H.1
    refine ⟨(n + uv.val.1, n + uv.val.2), ?_⟩
    refine ⟨by omega, by omega, by simpa using H.2, ?_⟩
    apply (unit_fraction_iff_factor hn (by omega) (by omega)).mpr
    refine ⟨by omega, by omega, ?_⟩
    simpa using (Nat.mem_divisorsAntidiagonal.mp H.1).1
  left_inv xy := by
    apply Subtype.ext
    have H := (unit_fraction_iff_factor hn xy.property.1 xy.property.2.1).mp
      xy.property.2.2.2
    exact Prod.ext (by dsimp; omega) (by dsimp; omega)
  right_inv uv := by
    apply Subtype.ext
    simp

/-- The actual rational solutions are counted by the ordered positive factor pairs. -/
theorem unit_fraction_count (n : ℕ) (hn : 0 < n) :
    b n = ((factorPairs n).card : ℤ) := by
  have H := Nat.card_congr (unitFractionEquiv n hn)
  simpa only [b, Nat.card_eq_fintype_card, Fintype.card_coe] using
    congrArg (fun k : ℕ => (k : ℤ)) H

private theorem c_recursion : InverseRecursion c := by
  let : Invertible (gFunction 1) := gOneInvertible
  have hi : ⅟(gFunction 1) = 1 := invOf_eq_iff_right.mpr (by
    change g 1 * 1 = 1
    rw [g_one, mul_one])
  constructor
  · change ArithmeticFunction.dirichletInverseFun gFunction gOneInvertible 1 = 1
    rw [ArithmeticFunction.dirichletInverseFun_apply_one, hi]
  · intro n hn
    change ArithmeticFunction.dirichletInverseFun gFunction gOneInvertible n = _
    rw [ArithmeticFunction.dirichletInverseFun_apply_ne (f := gFunction) (hf := gOneInvertible) (n := n) (by omega) (by omega), hi]
    simp only [neg_mul, one_mul]
    rfl

private theorem factor_pair_balance (n : ℕ) (hn : 0 < n) :
    2 * ((factorPairs n).card : ℤ) = (tau (n ^ 2) : ℤ) + 1 := by
  let s := (n ^ 2).divisorsAntidiagonal
  have hswap :
      (s.filter (fun uv => uv.2 ≤ uv.1)).card = (factorPairs n).card := by
    have he :
        (s.filter (fun uv => uv.2 ≤ uv.1)).map
          (Equiv.prodComm ℕ ℕ).toEmbedding = factorPairs n := by
      ext uv
      simp [s, factorPairs, Nat.mem_divisorsAntidiagonal, mul_comm]
    have := congrArg Finset.card he
    simpa using this
  have hdiag : s.filter (fun uv => uv.1 = uv.2) = {(n, n)} := by
    ext uv
    rcases uv with ⟨u, v⟩
    simp only [s, Finset.mem_filter, Nat.mem_divisorsAntidiagonal,
      Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨⟨H, H0⟩, huv⟩
      dsimp at *
      constructor <;> nlinarith
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨by ring, pow_ne_zero _ hn.ne'⟩, rfl⟩
  have hcard : s.card = (n ^ 2).divisors.card := by
    have H := congrArg Finset.card (Nat.map_div_right_divisors (n := n ^ 2))
    simpa [s] using H.symm
  have H : ∀ uv : ℕ × ℕ,
      (if uv.1 ≤ uv.2 then (1 : ℤ) else 0) +
        (if uv.2 ≤ uv.1 then (1 : ℤ) else 0) =
      1 + (if uv.1 = uv.2 then (1 : ℤ) else 0) := by
    intro uv
    split_ifs <;> omega
  have HH := Finset.sum_congr (s₁ := s) rfl (fun uv _ => H uv)
  simp only [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_const,
    nsmul_eq_mul, mul_one] at HH
  rw [hswap, hdiag] at HH
  simp only [Finset.card_singleton] at HH
  change ((factorPairs n).card : ℤ) + (factorPairs n).card = (s.card : ℤ) + 1 at HH
  rw [hcard] at HH
  change 2 * ((factorPairs n).card : ℤ) = ((n ^ 2).divisors.card : ℤ) + 1
  linarith

/-- The divisor formula is derived from the actual rational solution count. -/
theorem unit_fraction_divisor_formula (n : ℕ) (hn : 0 < n) :
    2 * b n = (tau (n ^ 2) : ℤ) + 1 := by
  rw [unit_fraction_count n hn]
  exact factor_pair_balance n hn

private def cappedExponents (f : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  f.mapRange (fun e => min e 3) (by decide)

private theorem fourth_power_free_iff {d : ℕ} (hd : d ≠ 0) :
    FourthPowerFree d ↔ ∀ p : ℕ, d.factorization p ≤ 3 := by
  constructor
  · intro H p
    by_cases hp : p.Prime
    · have hh := H p hp
      rw [hp.pow_dvd_iff_le_factorization hd] at hh
      omega
    · rw [Nat.factorization_eq_zero_of_not_prime d hp]
      omega
  · intro H p hp hdiv
    have hh := (hp.pow_dvd_iff_le_factorization hd).mp hdiv
    have := H p
    omega

private theorem capped_le (f : ℕ →₀ ℕ) : cappedExponents f ≤ f := by
  intro p
  exact min_le_left _ _

/-- The fourth-power-free divisors form the full capped exponent box. -/
private theorem fourth_power_free_divisor_box (n : ℕ) (hn : 0 < n) :
    a n = ((Finset.Iic (cappedExponents n.factorization)).card : ℤ) := by
  classical
  have hn0 := hn.ne'
  rw [a, Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hn0,
    Finset.filter_map]
  have hf : ∀ v : ↥(Finset.Iic n.factorization),
      FourthPowerFree (v.val.prod (· ^ ·)) ↔ v.val ≤ cappedExponents n.factorization := by
    intro v
    have hv : v.val ≤ n.factorization := Finset.mem_Iic.mp v.property
    have hd : v.val.prod (· ^ ·) ≠ 0 :=
      ne_zero_of_dvd_ne_zero hn0 (Nat.prod_pow_dvd_of_le_factorization hv)
    rw [fourth_power_free_iff hd, Nat.factorization_prod_pow_eq_self_of_le_factorization hv]
    constructor
    · intro H p
      exact le_min (hv p) (H p)
    · intro H p
      exact (le_min_iff.mp (H p)).2
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.card_map]
  simp only [Function.comp_apply]
  simp_rw [hf]
  have he :
      ((Finset.Iic n.factorization).attach.filter
        (fun v => v.val ≤ cappedExponents n.factorization)).card =
        (Finset.Iic (cappedExponents n.factorization)).card := by
    apply Finset.card_bij (fun v _ => v.val)
    · intro v hv
      exact Finset.mem_Iic.mpr (Finset.mem_filter.mp hv).2
    · intro u hu v hv huv
      exact Subtype.ext huv
    · intro v hv
      have hv' := Finset.mem_Iic.mp hv
      refine ⟨⟨v, Finset.mem_Iic.mpr (hv'.trans (capped_le _))⟩, ?_, rfl⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hv'⟩
  exact_mod_cast he

/-- All prime exponents contribute, with precisely the fourth-power-free cap. -/
private theorem fourth_power_free_divisor_count (n : ℕ) (hn : 0 < n) :
    a n = ((∏ p ∈ n.primeFactors, (min (n.factorization p) 3 + 1)) : ℕ) := by
  rw [fourth_power_free_divisor_box n hn, Finsupp.card_Iic]
  have hs : (cappedExponents n.factorization).support = n.primeFactors := by
    ext p
    simp [cappedExponents, Finsupp.mem_support_iff, Nat.mem_primeFactors,
      Nat.factorization_eq_zero_iff]
  rw [hs]
  simp only [Nat.card_Iic, cappedExponents, Finsupp.mapRange_apply]

/-- The native ceiling divisor sum is a full exponent-box staircase sum. -/
private theorem ceiling_sum_exponent_box (n : ℕ) (hn : 0 < n) :
    h n = ∑ f ∈ Finset.Iic n.factorization,
      (⌈(((Finset.Iic f).card : ℚ) / 2)⌉₊ : ℤ) := by
  classical
  rw [h, Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hn.ne', Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have ht : ∀ v : ↥(Finset.Iic n.factorization),
      tau (v.val.prod (· ^ ·)) = (Finset.Iic v.val).card := by
    intro v
    have hv : v.val ≤ n.factorization := Finset.mem_Iic.mp v.property
    have hd : v.val.prod (· ^ ·) ≠ 0 :=
      ne_zero_of_dvd_ne_zero hn.ne' (Nat.prod_pow_dvd_of_le_factorization hv)
    rw [tau, Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hd,
      Finset.card_map, Finset.card_attach,
      Nat.factorization_prod_pow_eq_self_of_le_factorization hv]
  simp_rw [ht]
  exact Finset.sum_attach (Finset.Iic n.factorization)
    (fun f : ℕ →₀ ℕ => (⌈(((Finset.Iic f).card : ℚ) / 2)⌉₊ : ℤ))

private theorem boxSum (f : ℕ →₀ ℕ) (L : ℕ → ℕ → ℤ) :
    (∑ v ∈ Iic f, ∏ p ∈ f.support, L p (v p)) =
    ∏ p ∈ f.support, ∑ k ∈ range (f p + 1), L p k := by
  classical
  rw [Finset.Iic_eq_Icc, show (⊥ : ℕ →₀ ℕ) = 0 from rfl, Finsupp.Icc_eq]
  simp only [Finsupp.support_zero, Finset.empty_union]
  rw [Finset.finsupp, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_sum]
  apply Finset.sum_congr
  · congr 2 <;> first | exact Subsingleton.elim _ _ | (funext p; simp [Finsupp.rangeIcc, Nat.range_succ_eq_Icc_zero])
  · intro v hv
    rw [← Finset.prod_attach]
    apply Finset.prod_congr rfl
    intro p hp
    rw [Finsupp.indicator_of_mem p.property]

private theorem ceilDouble (m : ℕ) : 2 * (⌈(m : ℚ) / 2⌉₊ : ℤ) = (m : ℤ) + m % 2 := by
  rw [Int.natCast_ceil_eq_ceil (by positivity)]
  have hc := Rat.ceil_natCast_div_natCast m 2
  norm_num only [Nat.cast_ofNat] at hc
  rw [hc]
  omega

private def E (k : ℕ) : ℤ := if k % 2 = 0 then 1 else 0
private def T (e : ℕ) : ℤ := ∑ k ∈ range (e+1), ((k : ℤ)+1)
private def U (e : ℕ) : ℤ := ∑ k ∈ range (e+1), E k
private def S (e : ℕ) : ℤ := if e % 4 ≤ 1 then 1 else 0
private def R (e : ℕ) : ℤ := if e % 4 = 0 then 1 else if e % 4 = 1 then -1 else 0
private def A (e : ℕ) : ℤ := (min e 3 : ℕ) + 1

private theorem eprod (s : Finset ℕ) (v : ℕ → ℕ) :
    (∏ p ∈ s, ((v p : ℤ)+1)) % 2 = ∏ p ∈ s, E (v p) := by
  classical
  have hb : ∀ p, E (v p) = 0 ∨ E (v p) = 1 := by intro p; unfold E; split_ifs <;> simp
  have hprod : (∏ p ∈ s, E (v p)) = 0 ∨ (∏ p ∈ s, E (v p)) = 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih => rw [prod_insert hp]; rcases hb p with h|h <;> rw [h] <;> simp_all
  have H : (∏ p ∈ s, ((v p : ℤ)+1)) ≡ ∏ p ∈ s, E (v p) [ZMOD 2] := by
    apply Int.ModEq.prod
    intro p hp
    change ((v p : ℤ)+1)%2 = E (v p)%2
    unfold E
    split_ifs with hh <;> omega
  change _ % 2 = _ % 2 at H
  rcases hprod with h|h <;> simpa [h] using H

private theorem t_formula (e : ℕ) : 2*T e = ((e : ℤ)+1)*((e : ℤ)+2) := by
  have hn := Finset.sum_range_id_mul_two (e+1)
  simp only [Nat.add_sub_cancel] at hn
  have hz : (∑ k ∈ range (e+1), (k : ℤ))*2 = ((e : ℤ)+1)*e := by
    exact_mod_cast hn
  unfold T
  rw [sum_add_distrib]
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one]
  nlinarith

private theorem u_formula (e : ℕ) : U e = ((e / 2 : ℕ) : ℤ) + 1 := by
  induction e using Nat.twoStepInduction with
  | zero => change E 0 = 1; norm_num [E]
  | one => change E 0 + E 1 = 1; norm_num [E]
  | more e ih _ =>
    have he : E (e+1) + E (e+2) = 1 := by unfold E; split_ifs <;> omega
    have hstep : U (e+2) = U e + 1 := by
      unfold U
      rw [show e+2+1 = (e+1)+1+1 by omega, sum_range_succ, sum_range_succ]
      linarith
    rw [hstep, ih, show (e+2)/2=e/2+1 by omega]
    simp only [Nat.cast_add, Nat.cast_one]

private theorem local_convolution (e : ℕ) :
    (∑ k ∈ range (e+1), A (e-k)*S k) = 2*(e:ℤ)+1 ∧
    (∑ k ∈ range (e+1), A (e-k)*R k) = 1 := by
  have recur (L : ℕ → ℤ) (hL : ∀ k, L (k+4) = L k) (h2 : L 2=0) (h3 : L 3=0) (e : ℕ) :
      (∑ k ∈ range (e+4+1), A (e+4-k)*L k) =
      4*(L 0+L 1+L 2+L 3) + ∑ k ∈ range (e+1), A (e-k)*L k := by
    rw [show e+4+1 = 4+(e+1) by omega, sum_range_add]
    have htail : (∑ k ∈ range (e+1), A (e+4-(4+k))*L (4+k)) =
        ∑ k ∈ range (e+1), A (e-k)*L k := by
      apply sum_congr rfl
      intro k hk
      rw [show e+4-(4+k)=e-k by omega, Nat.add_comm 4 k, hL]
    rw [htail]
    have hA (k : ℕ) (hk : 3 ≤ k) : A k = 4 := by
      unfold A
      rw [Nat.min_eq_right hk]
      norm_num
    simp only [sum_range_succ, sum_range_zero, zero_add, h2, h3, mul_zero, add_zero]
    rw [hA _ (by omega), hA _ (by omega)]
    ring
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e < 4
    · interval_cases e <;> decide +kernel
    · obtain ⟨q, rfl⟩ : ∃ q, e=q+4 := ⟨e-4, by omega⟩
      have hq := ih q (by omega)
      rw [recur S (by intro k; simp [S]) (by norm_num [S]) (by norm_num [S]),
        recur R (by intro k; simp [R]) (by norm_num [R]) (by norm_num [R])]
      norm_num [S, R] at *
      constructor <;> linarith [hq.1, hq.2]

private def PairOK (x y : ZMod 4) : Prop := x^2=y^2 ∧ x+y=x^2+x*y
private theorem pairOK_mul : ∀ x y u v : ZMod 4,
    PairOK x y → PairOK u v → PairOK (x*u) (y*v) := by unfold PairOK; decide +kernel

private theorem local_residue (e : ℕ) :
    (T e : ZMod 4)^2 = (S e : ℤ) ∧
    (T e : ZMod 4)*(U e : ZMod 4) = (R e : ℤ) ∧
    PairOK (T e) (U e) := by
  have ht (q : ℕ) : (T (q+8) : ZMod 4) = (T q : ZMod 4) := by
    have hq := t_formula q
    have hq8 := t_formula (q+8)
    push_cast at hq8
    have hh : T (q+8) = T q + 8*(q:ℤ)+44 := by nlinarith
    rw [hh]
    push_cast
    have h8 : (8 : ZMod 4) = 0 := by decide
    have h44 : (44 : ZMod 4) = 0 := by decide
    rw [h8, h44]
    ring
  have hu (q : ℕ) : (U (q+8) : ZMod 4) = (U q : ZMod 4) := by
    have hh : U (q+8) = U q + 4 := by rw [u_formula, u_formula]; push_cast; omega
    rw [hh]
    push_cast
    have h4 : (4 : ZMod 4) = 0 := by decide
    rw [h4, add_zero]
  induction e using Nat.strong_induction_on with
  | h e ih =>
    by_cases he : e < 8
    · interval_cases e <;> (unfold PairOK; decide +kernel)
    · obtain ⟨q, rfl⟩ : ∃ q, e=q+8 := ⟨e-8, by omega⟩
      have hi := ih q (by omega)
      simpa [ht, hu, S, R, Nat.add_mod] using hi

private theorem product_residue (s : Finset ℕ) (v : ℕ → ℕ) :
    (∏ p ∈ s, T (v p)) + (∏ p ∈ s, U (v p)) ≡
      (∏ p ∈ s, S (v p)) + (∏ p ∈ s, R (v p)) [ZMOD 4] := by
  classical
  have ho : PairOK (∏ p ∈ s, (T (v p) : ZMod 4)) (∏ p ∈ s, (U (v p) : ZMod 4)) := by
    induction s using Finset.induction_on with
    | empty => norm_num [PairOK]
    | @insert p s hp ih =>
      rw [prod_insert hp, prod_insert hp]
      exact pairOK_mul _ _ _ _ (local_residue (v p)).2.2 ih
  have hs : (∏ p ∈ s, (T (v p) : ZMod 4))^2 = ∏ p ∈ s, (S (v p) : ZMod 4) := by
    rw [← Finset.prod_pow]
    exact prod_congr rfl (fun p hp => (local_residue (v p)).1)
  have hr : (∏ p ∈ s, (T (v p) : ZMod 4)) * (∏ p ∈ s, (U (v p) : ZMod 4)) =
      ∏ p ∈ s, (R (v p) : ZMod 4) := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl (fun p hp => (local_residue (v p)).2.1)
  apply (ZMod.intCast_eq_intCast_iff _ _ 4).mp
  push_cast
  exact ho.2.trans (by rw [hs, hr])

private def P (f : ℕ →₀ ℕ) (L : ℕ → ℤ) : ℤ := f.prod (fun _ e => L e)
private theorem pad (f v : ℕ →₀ ℕ) (hv : v ≤ f) (L : ℕ → ℤ) (hL : L 0 = 1) :
    P v L = ∏ p ∈ f.support, L (v p) := by
  exact Finsupp.prod_of_support_subset _ (Finsupp.support_mono hv) _ (by intro p hp; exact hL)

private theorem card_pad (f v : ℕ →₀ ℕ) (hv : v ≤ f) :
    (Iic v).card = ∏ p ∈ f.support, (v p+1) := by
  rw [Finsupp.card_Iic]
  simp only [Nat.card_Iic]
  exact Finset.prod_subset (Finsupp.support_mono hv) (by intro p hp hn; rw [Finsupp.notMem_support_iff.mp hn]; rfl)

private def Hbox (f : ℕ →₀ ℕ) : ℤ := ∑ v ∈ Iic f, (⌈((Iic v).card : ℚ)/2⌉₊ : ℤ)
private theorem hbox_formula (f : ℕ →₀ ℕ) :
    2*Hbox f = P f T + P f U := by
  classical
  unfold Hbox
  rw [mul_sum]
  calc
    (∑ v ∈ Iic f, 2*(⌈((Iic v).card : ℚ)/2⌉₊ : ℤ)) =
        ∑ v ∈ Iic f, ((∏ p ∈ f.support, ((v p : ℤ)+1)) + ∏ p ∈ f.support, E (v p)) := by
      apply sum_congr rfl
      intro v hv
      rw [ceilDouble, card_pad f v (mem_Iic.mp hv)]
      simp only [Nat.cast_prod, Nat.cast_add, Nat.cast_one]
      rw [eprod]
    _ = P f T + P f U := by
      rw [sum_add_distrib, boxSum f (fun _ k => (k:ℤ)+1), boxSum f (fun _ k => E k)]
      rfl

private def Gamma (f : ℕ →₀ ℕ) : ℤ := (P f S+P f R)/2
private theorem gamma_law (f : ℕ →₀ ℕ) :
    2*Gamma f = P f S+P f R ∧ (Gamma f=0 ∨ Gamma f=1) := by
  classical
  have hi (s : Finset ℕ) :
      ((∏ p ∈ s, S (f p))=0 ∧ (∏ p ∈ s, R (f p))=0) ∨
      ((∏ p ∈ s, S (f p))=1 ∧ ((∏ p ∈ s, R (f p))=1 ∨ (∏ p ∈ s, R (f p))= -1)) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      rw [prod_insert hp, prod_insert hp]
      have hl : (S (f p)=0 ∧ R (f p)=0) ∨ (S (f p)=1 ∧ (R (f p)=1 ∨ R (f p)= -1)) := by
        unfold S R
        split_ifs <;> omega
      rcases hl with ⟨hs,hr⟩ | ⟨hs,hr|hr⟩ <;>
        rcases ih with ⟨hss,hrr⟩ | ⟨hss,hrr|hrr⟩ <;> simp [hs,hr,hss,hrr]
  have hh := hi f.support
  unfold Gamma P
  rcases hh with ⟨hs,hr⟩ | ⟨hs,hr|hr⟩ <;> simp only [Finsupp.prod] at * <;> rw [hs,hr] <;> norm_num

private theorem hbox_parity (f : ℕ →₀ ℕ) : Hbox f % 2 = Gamma f := by
  have hf := hbox_formula f
  have hg := gamma_law f
  have hr := product_residue f.support f
  change (P f T+P f U)%4=(P f S+P f R)%4 at hr
  omega

private theorem box_convolution (f : ℕ →₀ ℕ) :
    2*(∑ v ∈ Iic f, P v A * Gamma (f-v)) =
      (∏ p ∈ f.support, (2*(f p:ℤ)+1))+1 := by
  classical
  rw [mul_sum]
  calc
    (∑ v ∈ Iic f, 2*(P v A * Gamma (f-v))) =
        ∑ v ∈ Iic f, ((∏ p ∈ f.support, A (v p)*S (f p-v p)) +
          ∏ p ∈ f.support, A (v p)*R (f p-v p)) := by
      apply sum_congr rfl
      intro v hv
      have hh := (gamma_law (f-v)).1
      rw [show 2*(P v A * Gamma (f-v))=P v A*(2*Gamma (f-v)) by ring, hh]
      rw [pad f v (mem_Iic.mp hv) A (by norm_num [A]),
        pad f (f-v) tsub_le_self S (by norm_num [S]),
        pad f (f-v) tsub_le_self R (by norm_num [R])]
      simp only [Finsupp.tsub_apply]
      rw [mul_add, ←prod_mul_distrib, ←prod_mul_distrib]
    _ = (∏ p ∈ f.support, (2*(f p:ℤ)+1))+1 := by
      rw [sum_add_distrib, boxSum f (fun p k => A k*S (f p-k)), boxSum f (fun p k => A k*R (f p-k))]
      have hc (e : ℕ) (L : ℕ → ℤ) :
          (∑ k ∈ range (e+1), A k*L (e-k)) = ∑ k ∈ range (e+1), A (e-k)*L k := by
        rw [←sum_range_reflect (fun k => A k*L (e-k))]
        apply sum_congr rfl
        intro k hk
        have hk' := mem_range.mp hk
        congr 2 <;> omega
      simp_rw [hc, (local_convolution _).1, (local_convolution _).2]
      simp


private theorem a_product (n : ℕ) (hn : 0 < n) : a n = P n.factorization A := by
  rw [fourth_power_free_divisor_count n hn]
  unfold P Finsupp.prod A
  rw [Nat.support_factorization]
  push_cast
  rfl

private theorem g_gamma (n : ℕ) (hn : 0 < n) : g n = Gamma n.factorization := by
  rw [g, ceiling_sum_exponent_box n hn]
  exact hbox_parity n.factorization

private theorem tau_square (n : ℕ) (hn : 0 < n) :
    (tau (n^2) : ℤ) = ∏ p ∈ n.factorization.support, (2*(n.factorization p:ℤ)+1) := by
  rw [tau, Nat.card_divisors (pow_ne_zero _ hn.ne')]
  rw [Nat.primeFactors_pow n (by decide : 2≠0), Nat.factorization_pow]
  rw [Nat.support_factorization]
  push_cast
  rfl

/-- The independently defined counts satisfy the full positive-domain convolution. -/
private theorem native_convolution (n : ℕ) (hn : 0 < n) :
    b n = ∑ d ∈ n.divisors, a d*g (n/d) := by
  classical
  have hs : (∑ d ∈ n.divisors, a d*g (n/d)) =
      ∑ v ∈ Iic n.factorization, P v A*Gamma (n.factorization-v) := by
    rw [Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hn.ne', sum_map]
    simp only [Function.Embedding.coeFn_mk]
    calc
      (∑ v ∈ (Iic n.factorization).attach,
        a (v.val.prod (· ^ ·))*g (n/(v.val.prod (· ^ ·)))) =
          ∑ v ∈ (Iic n.factorization).attach, P v.val A*Gamma (n.factorization-v.val) := by
        apply sum_congr rfl
        intro v hv
        have hle : v.val ≤ n.factorization := mem_Iic.mp v.property
        have hdvd := Nat.prod_pow_dvd_of_le_factorization hle
        have hd0 := ne_zero_of_dvd_ne_zero hn.ne' hdvd
        have hdiv : 0<n/(v.val.prod (· ^ ·)) := Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_ne_zero hd0)
        rw [a_product _ (Nat.pos_of_ne_zero hd0), g_gamma _ hdiv,
          Nat.factorization_div hdvd, Nat.factorization_prod_pow_eq_self_of_le_factorization hle]
      _ = _ := Finset.sum_attach (Iic n.factorization)
        (fun v : ℕ →₀ ℕ => P v A * Gamma (n.factorization-v))
  have hc := box_convolution n.factorization
  have hb := unit_fraction_divisor_formula n hn
  rw [tau_square n hn] at hb
  rw [hs]
  linarith

/-- The complete, unrestricted A252505 convolution, including n=1. -/
theorem result : claim := by
  let af : ArithmeticFunction ℤ := ⟨a, by simp [a]⟩
  let bf : ArithmeticFunction ℤ := ⟨fun n => if n = 0 then 0 else b n, by simp⟩
  let gf : ArithmeticFunction ℤ := ⟨g, by simp [g, h]⟩
  let cf : ArithmeticFunction ℤ := ⟨c, by simp [c]⟩
  have hi : gf * cf = 1 := by
    change gf * ArithmeticFunction.dirichletInverse _ _ = 1
    exact ArithmeticFunction.self_mul_dirichletInverse _ _
  have hbg : bf = af * gf := by
    ext n
    by_cases hn : n = 0
    · subst n
      simp
    · rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => af x * gf y)]
      change (if n = 0 then 0 else b n) = _
      rw [ite_eq_right hn]
      exact native_convolution n (Nat.pos_of_ne_zero hn)
  have H : af = bf * cf := by rw [hbg, mul_assoc, hi, mul_one]
  intro n hn
  have Hn := congrArg (fun f : ArithmeticFunction ℤ => f n) H
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => bf x * cf y)] at Hn
  change a n = _ at Hn
  refine Hn.trans ?_
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := ne_zero_of_dvd_ne_zero (by omega : n ≠ 0) (Nat.mem_divisors.mp hd).1
  change (if d = 0 then 0 else b d) * c (n / d) = _
  rw [ite_eq_right hd0]

/-- The source recursion has a unique positive-domain solution. -/
theorem inverse_recursion_unique (v : ℕ → ℤ) (hv : InverseRecursion v) :
    ∀ n : ℕ, 0 < n → v n = c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases h1 : n = 1
    · subst n
      exact hv.1.trans c_recursion.1.symm
    · rw [hv.2 n (by omega), c_recursion.2 n (by omega)]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [ih d (Nat.mem_properDivisors.mp hd).2
        (Nat.pos_of_dvd_of_pos (Nat.mem_properDivisors.mp hd).1 hn)]


end
end D5.S3.Arith.Divisors.OeisA252505FourthPowerFreeConvolution
