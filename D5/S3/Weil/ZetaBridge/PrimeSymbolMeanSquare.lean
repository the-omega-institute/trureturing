/- GID: D5/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaBridge/PrimeSymbolMeanSquare
   mirror-E: none(waiver:general-analytic-identity-and-tail-estimate)
   anchors: []
   utility: none
   digest: Finite prime-symbol block estimates, discrete Abel majorization and complex arithmetic tails. -/

/-
SOURCE_ONLY_UNCOMPILED. Canonical-path source candidate from the pinned integrated
T2 snapshot. Lean elaboration, kernel acceptance, sorry and axiom-closure checks,
scoped reports, Scribe emission, Reg, required CI and delivery remain unverified.
Every retained signature, definition and proof below preserves the pinned bytes.

The cutoff retains every integer in [2,c), including all higher prime powers.
The geometric estimate uses ordered unequal pairs, with factor 2 per ordered
pair. Discrete summation by parts uses the imported AbelSummation backend.
Complex coefficients, boundary moments and exact pi normalization are retained;
physical operator identification and signed-form positivity are not established.

Utility classification: none. Every declaration is a parameterized definition,
identity, phase-geometry argument, geometric block estimate, discrete Abel
estimate or convergent-tail argument, including the private proof helpers and
symbolic arithmetic first-jet applications. Finite sums have arbitrary cutoff
or finite-set inputs; they are not a delivered bounded enumeration or a fixed
certified instance. No declaration supplies a checker/reflection algorithm or
a reduction whose conclusion awaits a numerical certificate. Thus all retained
declarations fall outside bounded-enumeration, checker, numeric-reduction and
certified-instance. Other utility fields are not-applicable(kind=none).
Generality I records the arithmetic prime-symbol specialization, independently
of this computational-content classification.
-/
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare

open scoped BigOperators ComplexConjugate
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- All indices, without discarding higher prime powers. -/
def primeIndices (c : ℕ) : Finset ℕ := Finset.Ico 2 c

def theta (c q : ℕ) : ℝ := Real.log (q : ℝ) / logLength c

/-- circleMap 0 1 t is exactly exp(t*I). -/
def primePhase (c q : ℕ) : ℂ := circleMap 0 1 (2 * Real.pi * theta c q)

def primeSymbol (c : ℕ) (m : ℤ) : ℝ :=
  ∑ q ∈ primeIndices c, primeWeight q * Real.sin (2 * Real.pi * (m : ℝ) * theta c q)

def primeSquareMass (c : ℕ) : ℝ := ∑ q ∈ primeIndices c, primeWeight q ^ 2

/-- Ordered unequal pairs: each unordered pair occurs twice. -/
def orderedCross (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) : ℝ :=
  ∑ p ∈ s, ∑ q ∈ s,
    if p = q then 0 else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖

def primeCross (c : ℕ) : ℝ := orderedCross (primeIndices c) primeWeight (primePhase c)

theorem logLength_pos {c : ℕ} (hc : 2 ≤ c) : 0 < logLength c := by
  apply Real.log_pos
  exact_mod_cast (show 1 < c by lia)

theorem phase_geometry {c q : ℕ} (hc : 2 ≤ c) (hq : q ∈ primeIndices c) :
    0 < theta c q ∧ theta c q < 1 := by
  obtain ⟨hq2, hqc⟩ := Finset.mem_Ico.mp hq
  have hqR : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by lia)
  have hqcR : (q : ℝ) < c := by exact_mod_cast hqc
  have hL := logLength_pos hc
  constructor
  · exact div_pos (Real.log_pos hqR) hL
  · apply (div_lt_one hL).mpr
    exact Real.log_lt_log (by linarith) hqcR

private theorem actual_log_gap {c p q : ℕ} (hc : 2 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) :
    |Real.log (p : ℝ) - Real.log (q : ℝ)| < logLength c := by
  have hL := logLength_pos hc
  obtain ⟨hp0, hp1⟩ := phase_geometry hc hp
  obtain ⟨hq0, hq1⟩ := phase_geometry hc hq
  have hpLo : 0 < Real.log (p : ℝ) := by
    exact (div_pos_iff_of_pos_right hL).mp hp0
  have hqLo : 0 < Real.log (q : ℝ) := by
    exact (div_pos_iff_of_pos_right hL).mp hq0
  have hpHi : Real.log (p : ℝ) < logLength c := (div_lt_one hL).mp hp1
  have hqHi : Real.log (q : ℝ) < logLength c := (div_lt_one hL).mp hq1
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

theorem primePhase_norm (c q : ℕ) : ‖primePhase c q‖ = 1 := by
  simp [primePhase]

/-- Noncollision is proved from the actual logarithms, without a spacing premise. -/
theorem primePhase_noncollision {c p q : ℕ} (hc : 2 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) (hpq : p ≠ q) :
    primePhase c p * conj (primePhase c q) ≠ 1 := by
  intro h
  have hsame : primePhase c p = primePhase c q := by
    have hm := congrArg (fun w : ℂ => w * primePhase c q) h
    simpa only [mul_assoc, Complex.conj_mul', primePhase_norm, one_pow,
      Complex.ofReal_one, mul_one, one_mul] using hm
  have hL := logLength_pos hc
  have hgap := actual_log_gap hc hp hq
  have hdist : |2 * Real.pi * theta c p - 2 * Real.pi * theta c q| < 2 * Real.pi := by
    have hid : 2 * Real.pi * theta c p - 2 * Real.pi * theta c q =
        (2 * Real.pi / logLength c) * (Real.log (p : ℝ) - Real.log (q : ℝ)) := by
      dsimp [theta]
      ring
    rw [hid, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi / logLength c)]
    calc
      _ < (2 * Real.pi / logLength c) * logLength c :=
        mul_lt_mul_of_pos_left hgap (by positivity)
      _ = 2 * Real.pi := by field_simp [hL.ne']
  have hangle : 2 * Real.pi * theta c p = 2 * Real.pi * theta c q :=
    eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) hdist hsame
  have htheta : theta c p = theta c q :=
    mul_left_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) hangle
  have hlog : Real.log (p : ℝ) = Real.log (q : ℝ) := by
    have hm := congrArg (fun t : ℝ => t * logLength c) htheta
    simpa only [theta, div_mul_cancel₀ _ hL.ne'] using hm
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by
    have := (Finset.mem_Ico.mp hp).1; lia)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by
    have := (Finset.mem_Ico.mp hq).1; lia)
  have hpqR := Real.log_injOn_pos hpR hqR hlog
  exact hpq (by exact_mod_cast hpqR)

private theorem lattice_angle (c q : ℕ) (m : ℤ) :
    frequency c m * Real.log (q : ℝ) = 2 * Real.pi * (m : ℝ) * theta c q := by
  dsimp [frequency, theta]
  ring

private theorem owner_term_zero (c : ℕ) (m : ℤ) :
    primeWeight 0 * Real.sin (frequency c m * Real.log (0 : ℝ)) = 0 := by simp

private theorem owner_term_one (c : ℕ) (m : ℤ) :
    primeWeight 1 * Real.sin (frequency c m * Real.log (1 : ℝ)) = 0 := by simp

/-- The omitted upper endpoint vanishes for every integer lattice mode. -/
theorem owner_term_cutoff {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :
    primeWeight c * Real.sin (frequency c m * Real.log (c : ℝ)) = 0 := by
  have hL := logLength_pos hc
  have hid : frequency c m * Real.log (c : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    dsimp [frequency, logLength] at *
    push_cast
    field_simp [hL.ne']
    <;> ring
  rw [hid, Real.sin_int_mul_pi, mul_zero]

/-- Exact finite prime sum appearing with a minus sign in the owner symbol. -/
theorem owner_prime_sum_eq (c : ℕ) (m : ℤ) :
    (∑ q ∈ Finset.range c, primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =
      primeSymbol c m := by
  classical
  have hsub : primeIndices c ⊆ Finset.range c := by
    intro q hq
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hq).2
  calc
    _ = ∑ q ∈ primeIndices c, primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ)) := by
      symm
      apply Finset.sum_subset hsub
      intro q hqr hqs
      have hq : q < 2 := by
        have hqc := Finset.mem_range.mp hqr
        by_contra hn
        exact hqs (Finset.mem_Ico.mpr ⟨by lia, hqc⟩)
      have heq : q = 0 ∨ q = 1 := by lia
      rcases heq with rfl | rfl
      · simpa only [Nat.cast_zero] using owner_term_zero c m
      · simpa only [Nat.cast_one] using owner_term_one c m
    _ = primeSymbol c m := by simp only [primeSymbol, lattice_angle]

/-- Including q=c also gives the same finite symbol. -/
theorem owner_prime_sum_inclusive {c : ℕ} (hc : 2 ≤ c) (m : ℤ) :
    (∑ q ∈ Finset.range (c + 1), primeWeight q * Real.sin (frequency c m * Real.log (q : ℝ))) =
      primeSymbol c m := by
  rw [Finset.sum_range_succ, owner_term_cutoff hc, add_zero, owner_prime_sum_eq]

private theorem complex_re_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ q ∈ s, f q).re = ∑ q ∈ s, (f q).re :=
  map_sum Complex.reAddGroupHom f s

private theorem complex_im_sum (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ q ∈ s, f q).im = ∑ q ∈ s, (f q).im :=
  map_sum Complex.imAddGroupHom f s

private theorem phase_power_im (c q : ℕ) (m : ℤ) :
    ((primePhase c q) ^ m).im = Real.sin (2 * Real.pi * (m : ℝ) * theta c q) := by
  rw [primePhase, circleMap_zero_zpow, circleMap_zero_im]
  simp only [one_zpow, one_mul]
  congr 1
  ring

theorem primeSymbol_is_im (c : ℕ) (m : ℤ) :
    primeSymbol c m =
      (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m).im := by
  rw [complex_im_sum]
  unfold primeSymbol
  apply Finset.sum_congr rfl
  intro q _
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, add_zero, phase_power_im]

private theorem primeSymbol_square_le (c : ℕ) (m : ℤ) :
    primeSymbol c m ^ 2 ≤
      ‖∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m‖ ^ 2 := by
  rw [primeSymbol_is_im]
  have h := Complex.sq_norm_sub_sq_im
    (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m)
  nlinarith [sq_nonneg
    (∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m).re]

/-- The only geometric-series estimate. It invokes the existing finite sum formula. -/
theorem geometric_block_norm {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1)
    (M : ℤ) (K : ℕ) :
    ‖∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))‖ ≤ 2 / ‖1 - z‖ := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, norm_zero] at hz
    norm_num at hz
  calc
    _ = ‖z ^ M * ∑ j ∈ Finset.range K, z ^ j‖ := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [zpow_add₀ hz0, zpow_natCast]
    _ = ‖∑ j ∈ Finset.range K, z ^ j‖ := by simp [norm_mul, norm_zpow, hz]
    _ = ‖z ^ K - 1‖ / ‖z - 1‖ := by rw [geom_sum_eq hz1, norm_div]
    _ ≤ 2 / ‖z - 1‖ := by
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      simpa only [norm_pow, hz, one_pow, norm_one, one_add_one_eq_two] using norm_sub_le (z ^ K) 1
    _ = 2 / ‖1 - z‖ := by rw [norm_sub_rev]

theorem norm_square_expansion (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) (m : ℤ) :
    ‖∑ p ∈ s, (a p : ℂ) * z p ^ m‖ ^ 2 =
      ∑ p ∈ s, ∑ q ∈ s, (((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m).re := by
  have hterm (p q : ℕ) :
      ((a p : ℂ) * z p ^ m) * conj ((a q : ℂ) * z q ^ m) =
        ((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m := by
    simp only [map_mul, map_zpow₀, Complex.conj_ofReal, Complex.ofReal_mul, mul_zpow]
    ring
  calc
    _ = ((∑ p ∈ s, (a p : ℂ) * z p ^ m) *
        conj (∑ q ∈ s, (a q : ℂ) * z q ^ m)).re := by
      rw [Complex.mul_conj']
      simp only [← Complex.ofReal_pow, Complex.ofReal_re]
    _ = (∑ p ∈ s, ∑ q ∈ s,
        ((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ m).re := by
      congr 1
      simp only [map_sum, Finset.sum_mul, Finset.mul_sum, hterm]
      exact Finset.sum_comm
    _ = _ := by simp_rw [complex_re_sum]

private theorem exponential_block_bound (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ)
    (hz : ∀ p ∈ s, ‖z p‖ = 1)
    (hneq : ∀ p ∈ s, ∀ q ∈ s, p ≠ q → z p * conj (z q) ≠ 1)
    (M : ℤ) (K : ℕ) :
    (∑ j ∈ Finset.range K, ‖∑ p ∈ s, (a p : ℂ) * z p ^ (M + (j : ℤ))‖ ^ 2) ≤
      (K : ℝ) * (∑ p ∈ s, a p ^ 2) + orderedCross s a z := by
  classical
  let T (p q : ℕ) : ℂ := ∑ j ∈ Finset.range K,
    ((a p * a q : ℝ) : ℂ) * (z p * conj (z q)) ^ (M + (j : ℤ))
  have hexpand :
      (∑ j ∈ Finset.range K, ‖∑ p ∈ s, (a p : ℂ) * z p ^ (M + (j : ℤ))‖ ^ 2) =
        ∑ p ∈ s, ∑ q ∈ s, (T p q).re := by
    simp_rw [norm_square_expansion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    exact (complex_re_sum _ _).symm
  have hpair (p : ℕ) (hp : p ∈ s) (q : ℕ) (hq : q ∈ s) :
      (T p q).re ≤ if p = q then (K : ℝ) * a p ^ 2
        else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖ := by
    by_cases hpq : p = q
    · subst q
      have hr : z p * conj (z p) = 1 := by rw [Complex.mul_conj', hz p hp]; norm_num
      simp [T, hr, nsmul_eq_mul, pow_two, mul_assoc]
    · rw [if_neg hpq]
      have hr : ‖z p * conj (z q)‖ = 1 := by simp [norm_mul, hz p hp, hz q hq]
      have hg := geometric_block_norm hr (hneq p hp q hq hpq) M K
      calc
        (T p q).re ≤ ‖T p q‖ := Complex.re_le_norm _
        _ = |a p * a q| * ‖∑ j ∈ Finset.range K,
            (z p * conj (z q)) ^ (M + (j : ℤ))‖ := by
          dsimp [T]
          rw [← Finset.mul_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ |a p * a q| * (2 / ‖1 - z p * conj (z q)‖) :=
          mul_le_mul_of_nonneg_left hg (abs_nonneg _)
        _ = _ := by ring
  rw [hexpand]
  calc
    _ ≤ ∑ p ∈ s, ∑ q ∈ s,
        if p = q then (K : ℝ) * a p ^ 2 else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖ :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq => hpair p hp q hq))
    _ = (K : ℝ) * (∑ p ∈ s, a p ^ 2) + orderedCross s a z := by
      unfold orderedCross
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      calc
        _ = ∑ q ∈ s, ((if p = q then (K : ℝ) * a p ^ 2 else 0) +
              (if p = q then 0 else 2 * |a p * a q| / ‖1 - z p * conj (z q)‖)) := by
          apply Finset.sum_congr rfl
          intro q _
          split_ifs <;> ring
        _ = _ := by rw [Finset.sum_add_distrib]; simp [hp]

/-- Candidate finite-block theorem, with arbitrary integer start and K=0 admitted. -/
theorem prime_symbol_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ) :
    (∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) ≤
      (K : ℝ) * primeSquareMass c + primeCross c := by
  calc
    _ ≤ ∑ j ∈ Finset.range K,
        ‖∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ (M + (j : ℤ))‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => primeSymbol_square_le c _)
    _ ≤ _ := exponential_block_bound (primeIndices c) primeWeight (primePhase c)
      (fun p _ => primePhase_norm c p)
      (fun p hp q hq hpq => primePhase_noncollision hc hp hq hpq) M K

private theorem primeSquareMass_nonneg (c : ℕ) : 0 ≤ primeSquareMass c :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

private theorem primeCross_nonneg (c : ℕ) : 0 ≤ primeCross c := by
  unfold primeCross orderedCross
  apply Finset.sum_nonneg
  intro p _
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact le_rfl
  · exact div_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) (norm_nonneg _)

private theorem abel_affine_identity (w : ℕ → ℝ) (D C : ℝ) (K : ℕ) :
    w K * (((K + 1 : ℕ) : ℝ) * D + C) +
      (∑ i ∈ Finset.range K, (w i - w (i + 1)) * (((i + 1 : ℕ) : ℝ) * D + C)) =
        D * (∑ i ∈ Finset.range (K + 1), w i) + C * w 0 := by
  induction K with
  | zero => simp; ring
  | succ K ih =>
      rw [Finset.sum_range_succ (f := fun i =>
        (w i - w (i + 1)) * (((i + 1 : ℕ) : ℝ) * D + C)),
        Finset.sum_range_succ (f := w)]
      simp only [Nat.cast_add, Nat.cast_one] at ih ⊢
      linear_combination ih

/-- Discrete Abel majorization, using Mathlib's actual summation-by-parts theorem. -/
theorem finite_abel_majorant (x w : ℕ → ℝ) (D C : ℝ)
    (hC : 0 ≤ C) (hw : ∀ i, 0 ≤ w i) (hanti : ∀ i, w (i + 1) ≤ w i)
    (hA : ∀ K, (∑ i ∈ Finset.range K, x i) ≤ (K : ℝ) * D + C) (K : ℕ) :
    (∑ i ∈ Finset.range K, x i * w i) ≤
      D * (∑ i ∈ Finset.range K, w i) + C * w 0 := by
  cases K with
  | zero => simpa using mul_nonneg hC (hw 0)
  | succ K =>
      have hab := Finset.sum_range_by_parts w x (K + 1)
      simp only [smul_eq_mul, Nat.add_sub_cancel] at hab
      have hneg :
          -(∑ i ∈ Finset.range K, (w (i + 1) - w i) * ∑ k ∈ Finset.range (i + 1), x k) =
            ∑ i ∈ Finset.range K, (w i - w (i + 1)) * ∑ k ∈ Finset.range (i + 1), x k := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [sub_eq_add_neg, hneg] at hab
      calc
        _ = ∑ i ∈ Finset.range (K + 1), w i * x i := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = _ := hab
        _ ≤ w K * (((K + 1 : ℕ) : ℝ) * D + C) +
            ∑ i ∈ Finset.range K, (w i - w (i + 1)) * (((i + 1 : ℕ) : ℝ) * D + C) :=
          add_le_add (mul_le_mul_of_nonneg_left (hA (K + 1)) (hw K))
            (Finset.sum_le_sum (fun i _ =>
              mul_le_mul_of_nonneg_left (hA (i + 1)) (sub_nonneg.mpr (hanti i))))
        _ = _ := abel_affine_identity w D C K

def inverseSquareWeight (M j : ℕ) : ℝ := (((M : ℝ) + (j : ℝ) + 1)⁻¹) ^ 2

def primeTailBudget (c M : ℕ) : ℝ :=
  primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2

theorem inverseSquareWeight_antitone {M : ℕ} (hM : 0 < M) (i : ℕ) :
    inverseSquareWeight M (i + 1) ≤ inverseSquareWeight M i := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  unfold inverseSquareWeight
  apply pow_le_pow_left₀ (by positivity)
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (by push_cast; linarith)

private theorem prime_tail_partial {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ≤
        primeTailBudget c M := by
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hA (k : ℕ) :
      (∑ j ∈ Finset.range k, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2) ≤
        (k : ℝ) * primeSquareMass c + primeCross c := by
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]
      using prime_symbol_block hc ((M : ℤ) + 1) k
  have hab := finite_abel_majorant
    (fun j => primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2) (inverseSquareWeight M)
    (primeSquareMass c) (primeCross c) (primeCross_nonneg c)
    (fun j => sq_nonneg _) (inverseSquareWeight_antitone hM) hA K
  have hweights : (∑ j ∈ Finset.range K, inverseSquareWeight M j) ≤ (M : ℝ)⁻¹ :=
    D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage.inverse_square_partial_le hMR K
  calc
    _ ≤ primeSquareMass c * (∑ j ∈ Finset.range K, inverseSquareWeight M j) +
        primeCross c * inverseSquareWeight M 0 := hab
    _ ≤ primeSquareMass c * (M : ℝ)⁻¹ + primeCross c * inverseSquareWeight M 0 :=
      add_le_add (mul_le_mul_of_nonneg_left hweights (primeSquareMass_nonneg c))
        (le_refl (primeCross c * inverseSquareWeight M 0))
    _ = _ := by simp [primeTailBudget, inverseSquareWeight, div_eq_mul_inv, inv_pow]

/-- The genuine infinite tail, indexed bijectively by m=M+j+1, j : Nat.
Summability is obtained from the nonnegative uniformly bounded partial sums,
so no totalized divergent tsum is used. -/
theorem prime_symbol_square_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) :
    Summable (fun j : ℕ =>
      primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ∧
    (∑' j : ℕ, primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) ≤
      primeTailBudget c M := by
  have hnon (j : ℕ) :
      0 ≤ primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hnon (prime_tail_partial hc hM),
    Real.tsum_le_of_sum_range_le hnon (prime_tail_partial hc hM)⟩

theorem complex_prime_energy (c M j : ℕ) (β : ℂ) :
    ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2 =
      ‖β‖ ^ 2 * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight M j) := by
  have hm : ‖((M + j + 1 : ℕ) : ℂ)‖ = (M : ℝ) + (j : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Complex.norm_natCast (M + j + 1))
  rw [norm_div, norm_mul, div_pow, mul_pow, hm, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [inverseSquareWeight, div_eq_mul_inv, inv_pow]
  ring

/-- Actual complex arithmetic consumer; beta has no reality or vanishing premise. -/
theorem complex_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M) (β : ℂ) :
    Summable (fun j : ℕ =>
      ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧
    (∑' j : ℕ,
      ‖β * (primeSymbol c ((M + j + 1 : ℕ) : ℤ) : ℂ) / ((M + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
        ‖β‖ ^ 2 * (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2) := by
  obtain ⟨hs, hb⟩ := prime_symbol_square_tail hc hM
  constructor
  · exact (hs.mul_left (‖β‖ ^ 2)).congr (fun j => (complex_prime_energy c M j β).symm)
  · simp_rw [complex_prime_energy]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

/-- Retained physical boundary moment; A may include orthonormal basis amplitudes.
The angular frequency factor is the existing owner frequency, not a second definition. -/
def retainedBoundaryMoment (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)
    (v : ℕ → ℂ) (j : ℕ) : ℂ :=
  ∑ n ∈ S, (-1 : ℂ) ^ n * (A n : ℂ) * v n *
    (frequency c (n : ℤ) : ℂ) ^ (2 * j)

/-- A finite sum of actual prime-symbol columns for the retained coefficients.
κ is an explicit complex normalization multiplier, supplied by the caller. -/
def retainedArithmeticColumn (c : ℕ) (S : Finset ℕ) (A : ℕ → ℝ)
    (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ S, κ * ((-1 : ℂ) ^ n * (A n : ℂ) * v n *
    (frequency c (n : ℤ) : ℂ) ^ (2 * j)) * (primeSymbol c (m : ℤ) : ℂ) / (m : ℂ)

private theorem retainedArithmeticColumn_collect (c : ℕ) (S : Finset ℕ)
    (A : ℕ → ℝ) (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) (m : ℕ) :
    retainedArithmeticColumn c S A v j κ m =
      (κ * retainedBoundaryMoment c S A v j) * (primeSymbol c (m : ℤ) : ℂ) / (m : ℂ) := by
  unfold retainedArithmeticColumn retainedBoundaryMoment
  rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_div]

/-- The leading coefficient retains the exact complex boundary moment. -/
theorem retained_arithmetic_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℕ) (A : ℕ → ℝ) (v : ℕ → ℂ) (j : ℕ) (κ : ℂ) :
    Summable (fun k : ℕ => ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ∧
    (∑' k : ℕ, ‖retainedArithmeticColumn c S A v j κ (M + k + 1)‖ ^ 2) ≤
      ‖κ‖ ^ 2 * ‖retainedBoundaryMoment c S A v j‖ ^ 2 *
        (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2) := by
  simpa only [retainedArithmeticColumn_collect, norm_mul, mul_pow, mul_assoc]
    using complex_prime_tail hc hM (κ * retainedBoundaryMoment c S A v j)

/-- The positive sign is forced by s_m = (s_m+P_m)-P_m in B-s_m*beta. -/
def canonicalPrimeFirstJetFar (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) : ℂ :=
  (primeSymbol c m : ℂ) * (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ))

/-- Exact algebraic connection to the existing signed arithmetic first jet.
The first term retains the full interior symbol. The second retains the
exterior symbol with its prime component removed; the last is the bounded
arithmetic far term. No physical full-symbol bridge is imported. -/
theorem canonical_first_jet_split (c : ℕ) (S : Finset ℤ) (v : ℤ → ℂ) (m : ℤ) :
    couplingFirstJet c S v m =
      (∑ n ∈ S, (arithmeticBoundarySymbol c n : ℂ) * v n) /
        ((Real.pi : ℂ) * (m : ℂ)) -
      ((arithmeticBoundarySymbol c m + primeSymbol c m : ℝ) : ℂ) *
        (∑ n ∈ S, v n) / ((Real.pi : ℂ) * (m : ℂ)) +
      canonicalPrimeFirstJetFar c S v m := by
  unfold couplingFirstJet canonicalPrimeFirstJetFar
  push_cast
  simp only [Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- Correct pi normalization for the actual existing first-jet arithmetic term. -/
theorem canonical_first_jet_prime_tail {c M : ℕ} (hc : 2 ≤ c) (hM : 0 < M)
    (S : Finset ℤ) (v : ℤ → ℂ) :
    Summable (fun k : ℕ => ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ∧
    (∑' k : ℕ, ‖canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ)‖ ^ 2) ≤
      (‖∑ n ∈ S, v n‖ ^ 2 / Real.pi ^ 2) *
        (primeSquareMass c / (M : ℝ) + primeCross c / ((M : ℝ) + 1) ^ 2) := by
  have hid (k : ℕ) : canonicalPrimeFirstJetFar c S v ((M + k + 1 : ℕ) : ℤ) =
      ((∑ n ∈ S, v n) / (Real.pi : ℂ)) *
        (primeSymbol c ((M + k + 1 : ℕ) : ℤ) : ℂ) / ((M + k + 1 : ℕ) : ℂ) := by
    dsimp [canonicalPrimeFirstJetFar]
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hnorm : ‖(∑ n ∈ S, v n) / (Real.pi : ℂ)‖ ^ 2 =
      ‖∑ n ∈ S, v n‖ ^ 2 / Real.pi ^ 2 := by
    rw [norm_div, div_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simpa only [hid, hnorm] using complex_prime_tail hc hM ((∑ n ∈ S, v n) / (Real.pi : ℂ))

end D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
