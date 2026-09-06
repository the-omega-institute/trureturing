/- GID: D5/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/WeilMellinPrimeIntertwining
   mirror-E: none(waiver:actual-prime-action-with-separate-Gamma-and-domain-analysis)
   anchors: []
   digest: Collapse the actual finite von Mangoldt translation action on an arithmetic Mellin window, retaining support cutoffs and the odd correction after evenization. -/

import D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The actual prime action on the explicit Mellin model

The classical arithmetic input is the existing `vonMangoldt_sum`, not a
new Dirichlet-convolution theorem. The new content is its action on the
supported arithmetic model: the 1/sqrt(n) prime coefficient cancels the
half-density under translation, including all prime powers and the exact
finite-window cutoff. No smoothness or spectral hypothesis is required for
this pointwise identity.

Evenization does not commute with the one-sided prime action. The second
main theorem keeps the complete odd-model correction. Gamma and pole terms,
L2/form-domain estimates and an unbounded-scale eigenmode approximation are
not conclusions of this source.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining

open scoped BigOperators
open Finset Set
open D5.S3.Weil.ZetaBridge.WeilPolynomialMellinWindow

/-- The arithmetic Mellin synthesis with its actual logarithmic window.
Closed endpoints make reflection exact. The earlier Ioc polynomial convention
agrees away from the single lower endpoint. -/
def windowMellinSum (a : ℝ) (M : ℕ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Icc (-a) a).indicator
    (fun x => 4 * (Real.exp (x / 2) : ℂ) *
      ∑ m ∈ Finset.Icc 1 M, h ((m : ℝ) * Real.exp x)) x

/-- The actual one-sided finite prime-power translation, compressed to the
same window. The n=1 summand vanishes by vonMangoldt_apply_one. -/
def primeForward (a : ℝ) (M : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Icc (-a) a).indicator
    (fun x => ∑ n ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        f (x + Real.log (n : ℝ))) x

/-- The full unsigned translation block; its negative is the prime operator
in the canonical Weil form. Both directions are specified independently. Terms beyond
exp(2a) vanish; equality at the cutoff can affect endpoints only, hence does
not change the L2 operator or its quadratic form. -/
def primeSymmetric (a : ℝ) (M : ℕ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Set.Icc (-a) a).indicator
    (fun x => ∑ n ∈ Finset.Icc 1 M,
      ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
        (f (x + Real.log (n : ℝ)) + f (x - Real.log (n : ℝ)))) x

/-- The zero-extended polynomial seed already used by the finite endpoint
Fourier evaluator. No prolate or spectral data enter this definition. -/
def cutPolynomialSeed (a : ℝ) (d : ℕ) (A : ℕ → ℂ) (t : ℝ) : ℂ :=
  if t ≤ Real.exp a then ∑ r ∈ Finset.range d, A r * (t : ℂ) ^ (2 * r) else 0

private theorem finite_mangoldt_synthesis (M : ℕ) (F : ℕ → ℂ)
    (hF : ∀ k, M < k → F k = 0) :
    (∑ n ∈ Finset.Icc 1 M, ∑ m ∈ Finset.Icc 1 M,
      (ArithmeticFunction.vonMangoldt n : ℂ) * F (n * m)) =
      ∑ k ∈ Finset.Icc 1 M, (Real.log (k : ℝ) : ℂ) * F k := by
  classical
  let B := (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M)
  let S := B.filter (fun p : ℕ × ℕ => p.1 * p.2 ≤ M)
  let W := fun p : ℕ × ℕ => (ArithmeticFunction.vonMangoldt p.1 : ℂ) * F (p.1 * p.2)
  have htrim : (∑ p ∈ B, W p) = ∑ p ∈ S, W p := by
    dsimp [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p hp
    by_cases h : p.1 * p.2 ≤ M
    · simp [h]
    · simp [h, W, hF _ (lt_of_not_ge h)]
  have hmaps : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 M := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpB, hpM⟩
    rcases Finset.mem_product.mp hpB with ⟨hn, hm⟩
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos
      (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hm).1, hpM⟩
  have hfiber (k : ℕ) (hk : k ∈ Finset.Icc 1 M) :
      S.filter (fun p : ℕ × ℕ => p.1 * p.2 = k) = k.divisorsAntidiagonal := by
    ext p
    constructor
    · intro hp
      have he := (Finset.mem_filter.mp hp).2
      exact Nat.mem_divisorsAntidiagonal.mpr
        ⟨he, ne_of_gt (Finset.mem_Icc.mp hk).1⟩
    · intro hp
      obtain ⟨he, hk0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
      have hprod : 0 < p.1 * p.2 := by rw [he]; exact (Finset.mem_Icc.mp hk).1
      have hn : 0 < p.1 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
      have hm : 0 < p.2 := Nat.pos_of_ne_zero (fun h => by simp [h] at hprod)
      have hpm : p.1 * p.2 ≤ M := by rw [he]; exact (Finset.mem_Icc.mp hk).2
      have hnM : p.1 ≤ M := (Nat.le_mul_of_pos_right _ hm).trans
        hpm
      have hmM : p.2 ≤ M := (Nat.le_mul_of_pos_left _ hn).trans
        hpm
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hn, hnM⟩,
          Finset.mem_Icc.mpr ⟨hm, hmM⟩⟩, hpm⟩, he⟩
  calc
    _ = ∑ p ∈ B, W p := by simp only [B, W, Finset.sum_product]
    _ = ∑ p ∈ S, W p := htrim
    _ = ∑ k ∈ Finset.Icc 1 M, ∑ p ∈ S with p.1 * p.2 = k, W p :=
      (Finset.sum_fiberwise_of_maps_to hmaps W).symm
    _ = ∑ k ∈ Finset.Icc 1 M, (Real.log (k : ℝ) : ℂ) * F k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hfiber k hk]
      calc
        _ = ∑ p ∈ k.divisorsAntidiagonal,
            (ArithmeticFunction.vonMangoldt p.1 : ℂ) * F k := by
          apply Finset.sum_congr rfl
          intro p hp
          dsimp [W]
          rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
        _ = (∑ p ∈ k.divisorsAntidiagonal,
            (ArithmeticFunction.vonMangoldt p.1 : ℂ)) * F k := by rw [Finset.sum_mul]
        _ = (Real.log (k : ℝ) : ℂ) * F k := by
          rw [Nat.sum_divisorsAntidiagonal (fun n _ =>
            (ArithmeticFunction.vonMangoldt n : ℂ))]
          congr 1
          exact_mod_cast (ArithmeticFunction.vonMangoldt_sum (n := k))

private theorem raw_above_window (a : ℝ) (M : ℕ) (h : ℝ → ℂ)
    (hs : ∀ t, Real.exp a < t → h t = 0) {x : ℝ} (hx : a < x) :
    (∑ m ∈ Finset.Icc 1 M, h ((m : ℝ) * Real.exp x)) = 0 := by
  apply Finset.sum_eq_zero
  intro m hm
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  apply hs
  calc
    Real.exp a < Real.exp x := Real.exp_lt_exp.mpr hx
    _ ≤ (m : ℝ) * Real.exp x := by nlinarith [Real.exp_pos x]

private theorem window_eq_raw_of_lower (a : ℝ) (M : ℕ) (h : ℝ → ℂ)
    (hs : ∀ t, Real.exp a < t → h t = 0) {x : ℝ} (hx : -a ≤ x) :
    windowMellinSum a M h x = 4 * (Real.exp (x / 2) : ℂ) *
      ∑ m ∈ Finset.Icc 1 M, h ((m : ℝ) * Real.exp x) := by
  classical
  by_cases hu : x ≤ a
  · exact Set.indicator_of_mem ⟨hx, hu⟩ _
  · rw [windowMellinSum, Set.indicator_of_not_mem (fun hh => hu hh.2),
      raw_above_window a M h hs (lt_of_not_ge hu)]
    simp

private theorem polynomial_seed_upper (a : ℝ) (d : ℕ) (A : ℕ → ℂ)
    (t : ℝ) (ht : Real.exp a < t) : cutPolynomialSeed a d A t = 0 := by
  simp only [cutPolynomialSeed, if_neg (not_le.mpr ht)]

private theorem polynomial_seed_summand (a x : ℝ) (d : ℕ) (A : ℕ → ℂ)
    (m : ℕ) (hm : 0 < m) (hx : -a < x) :
    (Real.exp (x / 2) : ℂ) * cutPolynomialSeed a d A ((m : ℝ) * Real.exp x) =
      ∑ r ∈ Finset.range d, A r * mellinMonomial a m r x := by
  classical
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have he : (m : ℝ) * Real.exp x = Real.exp (x + Real.log (m : ℝ)) := by
    rw [Real.exp_add, Real.exp_log hmR]
    ring
  have hiff : (m : ℝ) * Real.exp x ≤ Real.exp a ↔ x ≤ a - Real.log (m : ℝ) := by
    rw [he, Real.exp_le_exp]
    constructor <;> intro h <;> linarith
  by_cases ht : (m : ℝ) * Real.exp x ≤ Real.exp a
  · have hmem : x ∈ Set.Ioc (-a) (a - Real.log (m : ℝ)) := ⟨hx, hiff.mp ht⟩
    rw [cutPolynomialSeed, if_pos ht, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [mellin_monomial_polynomial_value, Set.indicator_of_mem hmem]
    have hhalf : (Real.exp (x / 2) : ℂ) = Complex.exp ((x : ℂ) / 2) := by simp
    have harg : (((m : ℝ) * Real.exp x : ℝ) : ℂ) =
        (m : ℂ) * Complex.exp (x : ℂ) := by simp
    rw [hhalf, harg]
    ring
  · have hmem : x ∉ Set.Ioc (-a) (a - Real.log (m : ℝ)) :=
      fun h => ht (hiff.mpr h.2)
    simp only [cutPolynomialSeed, if_neg ht, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro r hr
    rw [mellinMonomial, Set.indicator_of_not_mem hmem, mul_zero]

/-- Agreement with the previously defined polynomial arithmetic model.
The sole excluded endpoint is the earlier Ioc convention's lower endpoint;
thus the represented L2 functions and their integrable Fourier transforms agree. -/
theorem polynomial_window_agreement (a : ℝ) (M d : ℕ) (A : ℕ → ℂ)
    (x : ℝ) (hx : x ≠ -a) :
    windowMellinSum a M (cutPolynomialSeed a d A) x =
      polynomialMellinWindow a M d A x := by
  classical
  by_cases hl : -a < x
  · rw [window_eq_raw_of_lower a M _ (polynomial_seed_upper a d A) hl.le]
    rw [polynomialMellinWindow, mul_assoc, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro m hm
    exact polynomial_seed_summand a x d A m (Finset.mem_Icc.mp hm).1 hl
  · have hlt : x < -a := by
      rcases lt_or_eq_of_le (le_of_not_gt hl) with h | h
      · exact h
      · exact False.elim (hx h)
    have hn : x ∉ Set.Icc (-a) a := fun h => (not_le.mpr hlt) h.1
    have hz (m r : ℕ) : mellinMonomial a m r x = 0 := by
      exact Set.indicator_of_not_mem (fun h => (not_lt.mpr (le_of_lt hlt)) h.1) _
    simp only [windowMellinSum, Set.indicator_of_not_mem hn,
      polynomialMellinWindow, hz, mul_zero, Finset.sum_const_zero]

private theorem shifted_half_density (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (4 * (Real.exp ((x + Real.log (n : ℝ)) / 2) : ℂ)) =
      4 * (Real.exp (x / 2) : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [add_div, Real.exp_add, Real.exp_half (Real.log (n : ℝ)), Real.exp_log hnR]
  push_cast
  have hs : (Real.sqrt (n : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr hnR))
  field_simp [hs]
  <;> ring

/-- Exact action of the actual weighted prime-power translations on the
supported arithmetic model. The finite cutoff and the half-density weights
are discharged in the proof. Only the seed's upper support and enough integer
terms to cover the window are inputs; no residual/gap or desired action is assumed. -/
theorem prime_forward_mellin_identity (a : ℝ) (M : ℕ) (h : ℝ → ℂ)
    (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0) (x : ℝ) :
    primeForward a M (windowMellinSum a M h) x =
      windowMellinSum a M (fun t => (Real.log t : ℂ) * h t) x -
        (x : ℂ) * windowMellinSum a M h x := by
  classical
  by_cases hx : x ∈ Set.Icc (-a) a
  · have hlower : Real.exp a ≤ (M : ℝ) * Real.exp x := by
      calc
        Real.exp a = Real.exp (2 * a) * Real.exp (-a) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ (M : ℝ) * Real.exp x := mul_le_mul hcap
          (Real.exp_le_exp.mpr hx.1) (Real.exp_pos _).le (Nat.cast_nonneg M)
    have htail (k : ℕ) (hk : M < k) : h ((k : ℝ) * Real.exp x) = 0 := by
      apply hs
      have hkr : (M : ℝ) < (k : ℝ) := by exact_mod_cast hk
      exact hlower.trans_lt (mul_lt_mul_of_pos_right hkr (Real.exp_pos x))
    have hshift (n : ℕ) (hn : n ∈ Finset.Icc 1 M) :
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          windowMellinSum a M h (x + Real.log (n : ℝ)) =
          4 * (Real.exp (x / 2) : ℂ) *
            ∑ m ∈ Finset.Icc 1 M,
              (ArithmeticFunction.vonMangoldt n : ℂ) * h (((n * m : ℕ) : ℝ) * Real.exp x) := by
      have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hlog := Real.log_nonneg hn1
      rw [window_eq_raw_of_lower a M h hs (by linarith : -a ≤ x + Real.log (n : ℝ)),
        ← mul_assoc, shifted_half_density x (Finset.mem_Icc.mp hn).1,
        mul_assoc, Finset.mul_sum]
      apply congrArg (fun s : ℂ => 4 * (Real.exp (x / 2) : ℂ) * s)
      apply Finset.sum_congr rfl
      intro m hm
      rw [Real.exp_add, Real.exp_log hnR, Nat.cast_mul]
      congr 2
      ring
    rw [primeForward, Set.indicator_of_mem hx]
    have hsum : (∑ n ∈ Finset.Icc 1 M,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          windowMellinSum a M h (x + Real.log (n : ℝ))) =
        ∑ n ∈ Finset.Icc 1 M, 4 * (Real.exp (x / 2) : ℂ) *
          ∑ m ∈ Finset.Icc 1 M, (ArithmeticFunction.vonMangoldt n : ℂ) *
            h (((n * m : ℕ) : ℝ) * Real.exp x) :=
      Finset.sum_congr rfl hshift
    rw [hsum]
    rw [← Finset.mul_sum,
      finite_mangoldt_synthesis M (fun k => h ((k : ℝ) * Real.exp x)) htail,
      windowMellinSum, Set.indicator_of_mem hx,
      windowMellinSum, Set.indicator_of_mem hx]
    have hlog (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
        Real.log ((m : ℝ) * Real.exp x) = Real.log (m : ℝ) + x := by
      rw [Real.log_mul (by exact_mod_cast ne_of_gt (Finset.mem_Icc.mp hm).1)
        (Real.exp_ne_zero x), Real.log_exp]
    have hsplit : (∑ m ∈ Finset.Icc 1 M,
        (Real.log ((m : ℝ) * Real.exp x) : ℂ) * h ((m : ℝ) * Real.exp x)) =
        (∑ m ∈ Finset.Icc 1 M, (Real.log (m : ℝ) : ℂ) * h ((m : ℝ) * Real.exp x)) +
        (x : ℂ) * ∑ m ∈ Finset.Icc 1 M, h ((m : ℝ) * Real.exp x) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro m hm
      rw [hlog m hm, Complex.ofReal_add, add_mul]
    rw [hsplit]
    ring
  · simp [primeForward, windowMellinSum, hx]

private theorem neg_mem_window (a x : ℝ) :
    -x ∈ Set.Icc (-a) a ↔ x ∈ Set.Icc (-a) a := by
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

private theorem prime_symmetric_even (a : ℝ) (M : ℕ) (f : ℝ → ℂ)
    (he : ∀ x, f (-x) = f x) (x : ℝ) :
    primeSymmetric a M f x = primeForward a M f x + primeForward a M f (-x) := by
  classical
  by_cases hx : x ∈ Set.Icc (-a) a
  · have hnx := (neg_mem_window a x).mpr hx
    simp only [primeSymmetric, primeForward, Set.indicator_of_mem hx,
      Set.indicator_of_mem hnx]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    have hf : f (x - Real.log (n : ℝ)) = f (-x + Real.log (n : ℝ)) := by
      rw [← he (x - Real.log (n : ℝ))]
      congr 1
      ring
    rw [hf]
    ring
  · have hnx : -x ∉ Set.Icc (-a) a := fun h => hx ((neg_mem_window a x).mp h)
    simp [primeSymmetric, primeForward, hx, hnx]

private theorem prime_forward_split (a : ℝ) (M : ℕ) (p : ℝ → ℂ) (x : ℝ) :
    primeForward a M (fun t => (p t + p (-t)) / 2) x =
      primeForward a M p x - primeForward a M (fun t => (p t - p (-t)) / 2) x := by
  classical
  by_cases hx : x ∈ Set.Icc (-a) a
  · simp only [primeForward, Set.indicator_of_mem hx]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  · simp [primeForward, hx]

/-- The full prime block on the evenized actual model retains its odd-model
correction. In particular, evenization cannot silently be commuted past the
one-sided arithmetic action. This is an all-window pointwise identity. -/
theorem prime_even_mellin_identity (a : ℝ) (M : ℕ) (h : ℝ → ℂ)
    (hcap : Real.exp (2 * a) ≤ (M : ℝ))
    (hs : ∀ t, Real.exp a < t → h t = 0) (x : ℝ) :
    let p := windowMellinSum a M h
    let q := windowMellinSum a M (fun t => (Real.log t : ℂ) * h t)
    let r := fun t => (p t - p (-t)) / 2
    primeSymmetric a M (fun t => (p t + p (-t)) / 2) x =
      q x + q (-x) - 2 * (x : ℂ) * r x -
        primeForward a M r x - primeForward a M r (-x) := by
  dsimp only
  rw [prime_symmetric_even a M _ (by intro t; simp only [neg_neg, add_comm]) x,
    prime_forward_split, prime_forward_split,
    prime_forward_mellin_identity a M h hcap hs x,
    prime_forward_mellin_identity a M h hcap hs (-x)]
  push_cast
  ring

#print axioms polynomial_window_agreement
#print axioms prime_forward_mellin_identity
#print axioms prime_even_mellin_identity

end D5.S3.Weil.ZetaBridge.WeilMellinPrimeIntertwining
