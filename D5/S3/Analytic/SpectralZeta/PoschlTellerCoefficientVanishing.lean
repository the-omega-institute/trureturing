/- GID: D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing
   generality: I
   mirror-B: D5/B/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.claim; result=D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.result; claim=D5/S3/Analytic/SpectralZeta/PoschlTellerCoefficientVanishing.claim
   digest: Reflection cancels a logarithmic coefficient, refuting Fucci-Stanfill nonvanishing. -/

/-
proof_shape: result: bind-only (coefficient identities and arithmetic normalization)
escape_witness: none
admission_basis: open-problem-resolution (#15069; Refuted)
Direct frozen dependencies: none (pinned Mathlib only).
The public result is the designated refutation result (`basis=refutes`) and is exempt
from four-slot escape registration (CLAUDE.md §3.9).
All private lemmas are consumed bind-only helpers:
  generalizedBernoulliSeries_constant -> G_zero
  G_zero -> P_one_coeff_one
  P_one_coeff_one, E_one_reflection -> Omega_one_coeff_one
  sparseSeries_coeff_at, sparseSeries_23_square, sparseSeries_23_higher
    -> logOnePlus_sparse_23
  sparseSeries_coeff_below -> sparseSeries_X_pow_dvd, sparseSeries_23_square
  sparseSeries_X_pow_dvd -> sparseSeries_23_higher
  sparseSeries_23_gap -> sparseSeries_23_square
  logOnePlus_sparse_23 -> S_23
  S_23, Omega_one_coeff_one -> g_23_vanish
  admissible_23, one_le_order_23, g_23_vanish, beta_witness -> result
The formal conclusion concerns the source's coefficient convention, with the polynomial
indeterminate representing the logarithmic denominator factor. Analytic continuation
and the all-coprime-parameter family are outside this module's conclusion.
-/

import Mathlib.NumberTheory.Bernoulli
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

noncomputable section
open scoped BigOperators
namespace D5.S3.Analytic.SpectralZeta.PoschlTellerCoefficientVanishing

-- DLMF 24.16.1: binomial power of t/(exp(t)-1), multiplied by exp(x*t).
def bernoulliPower (a : ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun n => ∑ k ∈ Finset.range (n + 1),
    ((descPochhammer ℝ k).eval a / (k.factorial : ℝ)) *
      PowerSeries.coeff n ((bernoulliPowerSeries ℝ - 1) ^ k)

def generalizedBernoulliSeries (a x : ℝ) : PowerSeries ℝ :=
  bernoulliPower a * PowerSeries.rescale x (PowerSeries.exp ℝ)

def generalizedBernoulli (n : ℕ) (a x : ℝ) : ℝ :=
  (n.factorial : ℝ) * PowerSeries.coeff n (generalizedBernoulliSeries a x)

def C (m : ℕ) (y : ℝ) : ℂ :=
  ∑ j ∈ Finset.range m, ((2*m-1).choose (2*j) : ℂ) *
    (2^(2*m) * (y : ℂ)^(2*j) / (m-j : ℕ)) * (bernoulli (2*(m-j)) : ℂ)

def E (k : ℕ) (y : ℝ) : ℂ :=
  2*(2*(y : ℂ))^(2*k-1) - (2*(y : ℂ))^(2*k) / (k : ℂ) - C k y

def G (k : ℕ) (x y : ℝ) : ℂ :=
  (((descPochhammer ℝ k).eval (x-y) / (k.factorial : ℝ)) * generalizedBernoulli k (x-y+1) x : ℝ)

def scriptE (j : ℕ) (y : ℝ) : Polynomial ℂ :=
  if j = 0 then 1 else Polynomial.C (E j y / 2) * Polynomial.X

def P (k : ℕ) (y : ℝ) : Polynomial ℂ :=
  if k = 0 then 1 else ∑ j ∈ Finset.range (k+1),
    4^(k-j) * scriptE j y * Polynomial.C (G (2*(k-j)) (1-y) y)

def Omega0 (nu beta : ℝ) : ℂ :=
  (Real.rpow 2 (2*nu-1) : ℂ) * Complex.Gamma (1+(nu : ℂ)) /
    Complex.Gamma (-(nu : ℂ)) * (Real.cot beta : ℂ) *
    Complex.exp (Complex.I * (Real.pi : ℂ) * (nu : ℂ))

def Pbar (nu beta : ℝ) (k : ℕ) : Polynomial ℂ :=
  Polynomial.C (Omega0 nu beta) * P k ((1+nu)/2)

def Omega (nu beta : ℝ) : ℕ → Polynomial ℂ
  | 0 => Polynomial.C (Omega0 nu beta)
  | k+1 => Pbar nu beta (k+1) - ∑ l : Fin (k+1),
      P (k+1-l.val) ((1-nu)/2) * Omega nu beta l.val
termination_by k => k

-- The witness is unique whenever q > 0, the range used in claim.
def sparseSeries {R : Type*} [Semiring R] (p q : ℕ) (A : ℕ → R) : PowerSeries R :=
  by
    classical
    exact PowerSeries.mk fun d => if h : ∃ k, d = p+k*q then A h.choose else 0

def W (p q : ℕ) (beta : ℝ) : PowerSeries (Polynomial ℂ) :=
  sparseSeries p q (Omega ((p : ℝ)/q) beta)

def logOnePlus (w : PowerSeries (Polynomial ℂ)) : PowerSeries (Polynomial ℂ) :=
  PowerSeries.mk fun d => ∑ n ∈ Finset.Icc 1 d,
    (((-1 : ℂ)^(n+1)/(n : ℂ)) • PowerSeries.coeff d (w^n))

def S (p q : ℕ) (beta : ℝ) (m : ℕ) : Polynomial ℂ :=
  PowerSeries.coeff (m+p) (logOnePlus (W p q beta))

def g (p q : ℕ) (beta : ℝ) (m j : ℕ) : ℂ := (S p q beta m).coeff j

def admissible (p q m : ℕ) : Prop := ∃ l k : ℕ, l*p+k*q=m

def order (p q m : ℕ) : ℕ := sSup {k : ℕ | ∃ l : ℕ, l*p+k*q=m}

def claim : Prop := ∀ p q : ℕ, 0 < p → p < q → Nat.Coprime p q →
  ∀ beta : ℝ, beta ∈ Set.Ioo 0 Real.pi → beta ≠ Real.pi/2 →
  ∀ m j : ℕ, admissible p q m → j ≤ order p q m → g p q beta m j ≠ 0

private lemma generalizedBernoulliSeries_constant (a x : ℝ) :
    PowerSeries.coeff 0 (generalizedBernoulliSeries a x) = 1 := by
  simp [generalizedBernoulliSeries, PowerSeries.coeff_mul,
    bernoulliPower, PowerSeries.coeff_rescale]

private lemma G_zero (x y : ℝ) : G 0 x y = 1 := by
  simp [G, generalizedBernoulli, generalizedBernoulliSeries_constant]

private lemma P_one_coeff_one (y : ℝ) : (P 1 y).coeff 1 = E 1 y / 2 := by
  simp [P, Finset.sum_range_succ, scriptE, G_zero]

private lemma E_one_reflection (y : ℝ) : E 1 (1-y) = E 1 y := by
  simp [E, C]
  ring

private lemma Omega_one_coeff_one (nu beta : ℝ) : (Omega nu beta 1).coeff 1 = 0 := by
  have href : (1+nu)/2 = 1-(1-nu)/2 := by ring
  simp [Omega, Pbar, Polynomial.coeff_mul_C, P_one_coeff_one, href, E_one_reflection]
  ring

private lemma sparseSeries_coeff_at {R : Type*} [Semiring R] (p q : ℕ)
    (hq : 0 < q) (A : ℕ → R) (k : ℕ) :
    PowerSeries.coeff (p+k*q) (sparseSeries p q A) = A k := by
  classical
  have hex : ∃ l, p+k*q=p+l*q := ⟨k, rfl⟩
  simp only [sparseSeries, PowerSeries.coeff_mk, dif_pos hex]
  congr 1
  have hh := hex.choose_spec
  nlinarith

private lemma sparseSeries_coeff_below {R : Type*} [Semiring R] (p q : ℕ)
    (A : ℕ → R) (d : ℕ) (hd : d < p) :
    PowerSeries.coeff d (sparseSeries p q A) = 0 := by
  classical
  have hex : ¬ ∃ k, d=p+k*q := by rintro ⟨k, hk⟩; omega
  simp [sparseSeries, hex]

private lemma sparseSeries_X_pow_dvd {R : Type*} [Semiring R] (p q : ℕ)
    (A : ℕ → R) : (PowerSeries.X : PowerSeries R)^p ∣ sparseSeries p q A := by
  rw [PowerSeries.X_pow_dvd_iff]
  exact fun d hd => sparseSeries_coeff_below p q A d hd

private lemma sparseSeries_23_gap {R : Type*} [Semiring R] (A : ℕ → R)
    (d : ℕ) (hd : d < 5) (hne : d ≠ 2) :
    PowerSeries.coeff d (sparseSeries 2 3 A) = 0 := by
  classical
  have hex : ¬ ∃ k, d=2+k*3 := by rintro ⟨k, hk⟩; omega
  simp [sparseSeries, hex]

private lemma sparseSeries_23_square (A : ℕ → Polynomial ℂ) :
    PowerSeries.coeff 5 (sparseSeries 2 3 A ^ 2) = 0 := by
  rw [pow_two, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hs : ij.1+ij.2=5 := Finset.mem_antidiagonal.mp hij
  by_cases h : ij.1=2
  · rw [show ij.2=3 by omega,
      sparseSeries_23_gap A 3 (by omega) (by omega), mul_zero]
  · by_cases hlt : ij.1 < 5
    · rw [sparseSeries_23_gap A ij.1 hlt h, zero_mul]
    · rw [show ij.2=0 by omega,
        sparseSeries_coeff_below 2 3 A 0 (by omega), mul_zero]

private lemma sparseSeries_23_higher (A : ℕ → Polynomial ℂ) (n : ℕ) (hn : 3 ≤ n) :
    PowerSeries.coeff 5 (sparseSeries 2 3 A ^ n) = 0 := by
  have hdvd : (PowerSeries.X : PowerSeries (Polynomial ℂ))^(2*n) ∣
      sparseSeries 2 3 A ^ n := by
    rw [pow_mul]
    exact pow_dvd_pow_of_dvd (sparseSeries_X_pow_dvd 2 3 A) n
  exact PowerSeries.X_pow_dvd_iff.mp hdvd 5 (by omega)

private lemma logOnePlus_sparse_23 (A : ℕ → Polynomial ℂ) :
    PowerSeries.coeff 5 (logOnePlus (sparseSeries 2 3 A)) = A 1 := by
  classical
  rw [logOnePlus, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single 1]
  · simp only [pow_one]
    rw [show (5 : ℕ)=2+1*3 by omega, sparseSeries_coeff_at 2 3 (by omega)]
    norm_num
  · intro n hn hne
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    by_cases hn2 : n=2
    · subst n
      rw [sparseSeries_23_square, smul_zero]
    · rw [sparseSeries_23_higher A n (by omega), smul_zero]
  · simp

private lemma S_23 (beta : ℝ) : S 2 3 beta 3 = Omega ((2 : ℝ)/3) beta 1 := by
  exact logOnePlus_sparse_23 (Omega ((2 : ℝ)/3) beta)

private lemma admissible_23 : admissible 2 3 3 := ⟨0, 1, by norm_num⟩

private lemma one_le_order_23 : 1 ≤ order 2 3 3 := by
  apply le_csSup
  · refine ⟨1, ?_⟩
    rintro k ⟨l, hl⟩
    omega
  · exact ⟨0, by norm_num⟩

private lemma g_23_vanish (beta : ℝ) : g 2 3 beta 3 1 = 0 := by
  rw [g, S_23, Omega_one_coeff_one]

private lemma beta_witness : Real.pi/4 ∈ Set.Ioo 0 Real.pi ∧ Real.pi/4 ≠ Real.pi/2 := by
  have hp := Real.pi_pos
  constructor
  · constructor <;> linarith
  · linarith

theorem result : ¬ claim := by
  intro h
  have hc := h 2 3 (by norm_num) (by norm_num) (by norm_num)
    (Real.pi/4) beta_witness.1 beta_witness.2 3 1 admissible_23 one_le_order_23
  exact hc (g_23_vanish (Real.pi/4))

end D5.S3.Analytic.SpectralZeta.PoschlTellerCoefficientVanishing
