/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentArithmetic
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual arithmetic translation and finite-prefix estimates for the full moment certificate. -/

import D5.S3.Weil.Mertens.WeightedMangoldtRate
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelPrefixPerturbation
import D5.S3.Analytic.Interpolation.MomentExponentialCoercivity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
open MeasureTheory Set Filter Asymptotics
open scoped BigOperators Topology
open D5.S3.Analytic.Interpolation.AtomicPrefixEnergy
open D5.S3.Arith.Robin.CompleteMertensPeak

namespace D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate

variable {I : Type u} [Fintype I]

def relativeError (t : ℝ) : ℝ :=
  Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1

/-- The only arithmetic data in the telescope. Existence is proved below
from actual unconditional MediumPNT, including the entire initial interval. -/
structure PNTConstants where
  C : ℝ
  alpha : ℝ
  one_le_C : 1 ≤ C
  alpha_pos : 0 < alpha
  bound : ∀ t : ℝ, 0 ≤ t →
    |relativeError t| ≤ C * Real.exp (-alpha * t ^ ((1 : ℝ) / 10))

private lemma exists_pnt_constants : Nonempty PNTConstants := by
  obtain ⟨alpha, ha, hO⟩ := MediumPNT
  obtain ⟨L, hL, hb⟩ := isBigO_iff'.mp hO
  obtain ⟨X, hX⟩ := eventually_atTop.mp hb
  let T : ℝ := max 0 (Real.log (max X 1))
  let P : ℝ := Chebyshev.psi (Real.exp T) + 1
  let C : ℝ := max 1 (max L (P * Real.exp (alpha * T ^ ((1 : ℝ) / 10))))
  have hT : 0 ≤ T := le_max_left _ _
  have hC : 1 ≤ C := le_max_left _ _
  have hCL : L ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hCP : P * Real.exp (alpha * T ^ ((1 : ℝ) / 10)) ≤ C :=
    (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨⟨C, alpha, hC, ha, ?_⟩⟩
  intro t ht
  by_cases htail : T ≤ t
  · have hbase : 0 < max X 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hXt : X ≤ Real.exp t := by
      calc
        X ≤ max X 1 := le_max_left _ _
        _ = Real.exp (Real.log (max X 1)) := (Real.exp_log hbase).symm
        _ ≤ Real.exp t := Real.exp_le_exp.mpr ((le_max_right _ _).trans htail)
    have h := hX (Real.exp t) hXt
    have he : relativeError t = Real.exp (-t) *
        (Chebyshev.psi (Real.exp t) - Real.exp t) := by
      dsimp [relativeError]
      rw [mul_sub, ← Real.exp_add]
      simp
    rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-t) * (L *
          (Real.exp t * Real.exp (-alpha * t ^ ((1 : ℝ) / 10)))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
        simpa only [Pi.sub_apply, id_eq, Real.norm_eq_abs, abs_mul,
          abs_of_pos (Real.exp_pos _), Real.log_exp] using h
      _ = L * Real.exp (-alpha * t ^ ((1 : ℝ) / 10)) := by
        calc
          _ = (Real.exp (-t) * Real.exp t) *
              (L * Real.exp (-alpha * t ^ ((1 : ℝ) / 10))) := by ring
          _ = _ := by rw [← Real.exp_add]; simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hCL (Real.exp_nonneg _)
  · have htT : t ≤ T := le_of_lt (lt_of_not_ge htail)
    have hpsi : Real.exp (-t) * Chebyshev.psi (Real.exp t) ≤
        Chebyshev.psi (Real.exp T) := by
      calc
        _ ≤ Chebyshev.psi (Real.exp t) :=
          mul_le_of_le_one_left (Chebyshev.psi_nonneg _)
            (Real.exp_le_one_iff.mpr (by linarith))
        _ ≤ _ := Chebyshev.psi_mono (Real.exp_le_exp.mpr htT)
    have hr : |relativeError t| ≤ P := by
      apply abs_le.mpr
      dsimp [relativeError, P]
      constructor
      · nlinarith [Chebyshev.psi_nonneg (Real.exp T),
          mul_nonneg (Real.exp_nonneg (-t)) (Chebyshev.psi_nonneg (Real.exp t))]
      · linarith
    have hp : 0 ≤ P := by dsimp [P]; positivity
    have hpow := Real.rpow_le_rpow ht htT (by norm_num : (0 : ℝ) ≤ 1 / 10)
    have he : Real.exp (-alpha * T ^ ((1 : ℝ) / 10)) ≤
        Real.exp (-alpha * t ^ ((1 : ℝ) / 10)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpow (by linarith))
    calc
      _ ≤ P := hr
      _ = (P * Real.exp (alpha * T ^ ((1 : ℝ) / 10))) *
          Real.exp (-alpha * T ^ ((1 : ℝ) / 10)) := by
        rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ C * Real.exp (-alpha * T ^ ((1 : ℝ) / 10)) :=
        mul_le_mul_of_nonneg_right hCP (Real.exp_nonneg _)
      _ ≤ _ := mul_le_mul_of_nonneg_left he (by linarith)

/-- One fixed unconditional choice, made before D or the atomic family. -/
def pnt : PNTConstants := Classical.choice exists_pnt_constants

def B (p : PNTConstants) : ℝ :=
  p.C * (1 + (Nat.factorial 10 : ℝ) * (2 / p.alpha) ^ 10)

def d0 : ℝ := Real.eulerMascheroniConstant - 1 + Real.log (2 * Real.pi)
def M (D : ℝ) : ℝ := Real.exp (D / 2)
def epsilon (p : PNTConstants) (D : ℝ) : ℝ :=
  p.C * (Real.exp (-p.alpha * (D / 4) ^ ((1 : ℝ) / 10)) + Real.exp (-D / 4))
def beta (p : PNTConstants) (D : ℝ) : ℝ := M D * (1 + epsilon p D) + D + B p
def curvature (p : PNTConstants) (D : ℝ) : ℝ :=
  ((9 + 4 * p.C + 2 * B p) * M D + D + 3) / 4

/-- Exactly the displayed original N; the parenthesization is intentional. -/
def order (p : PNTConstants) (D : ℝ) : ℕ :=
  ⌈max 1 (max (D * Real.sqrt (curvature p D) / 2)
    ((5 * D / 4) * Real.exp (beta p D + d0 + 2)))⌉₊

def primes (t : ℝ) : Finset ℕ := Finset.Icc 2 ⌊Real.exp t⌋₊
def F (t : ℝ) : ℝ := ∑ n ∈ primes t, ArithmeticFunction.vonMangoldt n / (n : ℝ)
def b (t : ℝ) : ℝ := F t - t + Real.eulerMascheroniConstant

def P (t : ℝ) : ℝ := Real.exp (-|t| / 2) * trivialT |t|
def fullR (t : ℝ) : ℝ :=
  Real.exp (-|t| / 2) * (U (Real.exp |t|) - Real.log (2 * Real.pi))

def quadratic {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ)
    (f : ℝ → ℝ) : ℂ :=
  ∑ i, ∑ j, star (a i) * a j * (f (x i - x j) : ℂ)

def energy {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ) : ℝ :=
  ∫ v : ℝ, ‖«prefix» x a v‖ ^ 2

lemma B_ge_C (p : PNTConstants) : p.C ≤ B p := by
  dsimp [B]
  have hC : 0 ≤ p.C := le_trans zero_le_one p.one_le_C
  nlinarith [mul_nonneg hC (show 0 ≤ (Nat.factorial 10 : ℝ) * (2 / p.alpha) ^ 10 by
    positivity)]

lemma F_eq_Ioc (t : ℝ) : F t =
    ∑ n ∈ Finset.Ioc 0 ⌊Real.exp t⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
  classical
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨hl, hu⟩
    exact Finset.mem_Ioc.mpr ⟨by omega, hu⟩
  · intro n hn hnot
    have hnn := Finset.mem_Ioc.mp hn
    have hsmall : n < 2 := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, hnn.2⟩)
    have : n = 1 := by omega
    simp [this]

private lemma rate_mass {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ in Ioi 0, Real.exp (-c * t ^ ((1 : ℝ) / 10))) =
      (Nat.factorial 10 : ℝ) * (1 / c) ^ 10 := by
  rw [← integral_comp_rpow_Ioi_of_pos (p := (10 : ℝ)) (by norm_num)]
  have he (x : ℝ) (hx : x ∈ Ioi (0 : ℝ)) :
      (10 * x ^ ((10 : ℝ) - 1)) *
          Real.exp (-c * (x ^ (10 : ℝ)) ^ ((1 : ℝ) / 10)) =
        10 * (x ^ ((10 : ℝ) - 1) * Real.exp (-(c * x))) := by
    rw [← Real.rpow_mul hx.le]
    norm_num
    ring
  calc
    _ = ∫ x : ℝ in Ioi 0, 10 * (x ^ ((10 : ℝ) - 1) * Real.exp (-(c * x))) :=
      setIntegral_congr_fun measurableSet_Ioi he
    _ = 10 * ((1 / c) ^ (10 : ℝ) * Real.Gamma 10) := by
      rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num) hc]
    _ = _ := by
      have hg : Real.Gamma (10 : ℝ) = (Nat.factorial 9 : ℝ) := by
        convert Real.Gamma_nat_eq_factorial 9 using 1 <;> norm_num
      have hp : (1 / c) ^ (10 : ℝ) = (1 / c) ^ (10 : ℕ) := Real.rpow_natCast _ _
      rw [hg, hp]
      norm_num [Nat.factorial] <;> ring

private lemma weight_mass {c : ℝ} (hc : 0 < c) :
    (∫ u : ℝ in Ioi 1, WeightedMangoldtRate.weight c u) =
      (Nat.factorial 10 : ℝ) * (1 / c) ^ 10 := by
  have h := integral_comp_log_Ioi
    (fun t : ℝ => Real.exp (-c * t ^ ((1 : ℝ) / 10))) (a := 1) one_pos
  rw [Real.log_one, rate_mass hc] at h
  simpa only [WeightedMangoldtRate.weight, WeightedMangoldtRate.rate,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

private lemma b_tail (t : ℝ) (ht : Real.log 2 ≤ t) :
    b t = relativeError t -
      ∫ u : ℝ in Ioi (Real.exp t), (Chebyshev.psi u - u) / u ^ 2 := by
  have hx : (2 : ℝ) ≤ Real.exp t := by
    calc
      2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr ht
  have hid := CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    WeightedPrimeLimit.chebyshev_error_kernel_integrable hx
  have he : Real.exp (-t) = (Real.exp t)⁻¹ := Real.exp_neg t
  rw [Real.log_exp, ← F_eq_Ioc] at hid
  dsimp [b, relativeError]
  rw [he]
  simp only [div_eq_mul_inv] at hid ⊢
  linarith only [hid]

lemma relativeError_le (p : PNTConstants) {t : ℝ} (ht : 0 ≤ t) :
    |relativeError t| ≤ p.C := by
  calc
    _ ≤ p.C * Real.exp (-p.alpha * t ^ ((1 : ℝ) / 10)) := p.bound t ht
    _ ≤ p.C := mul_le_of_le_one_right (by linarith [p.one_le_C])
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (by linarith [p.alpha_pos]) (Real.rpow_nonneg ht _)))

private lemma relativeError_decay (p : PNTConstants) {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    |relativeError t| ≤ p.C * Real.exp (-p.alpha * s ^ ((1 : ℝ) / 10)) := by
  refine (p.bound t (hs.trans hst)).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith [p.one_le_C])
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (Real.rpow_le_rpow hs hst (by norm_num)) (by linarith [p.alpha_pos])

lemma b_bound (p : PNTConstants) (t : ℝ) (ht : 0 ≤ t) :
    |b t| ≤ B p := by
  by_cases hsmall : t < Real.log 2
  · have he : Real.exp t < (2 : ℝ) := by
      calc
        _ < Real.exp (Real.log 2) := Real.exp_lt_exp.mpr hsmall
        _ = _ := Real.exp_log (by norm_num)
    have hempty : primes t = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rcases Finset.mem_Icc.mp hn with ⟨hl, hu⟩
      have hnle := (Nat.le_floor_iff (Real.exp_nonneg t)).mp hu
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hl
      linarith
    have hlog : Real.log (2 : ℝ) ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    have hg0 : 0 ≤ Real.eulerMascheroniConstant :=
      le_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant.le
    have hg1 : Real.eulerMascheroniConstant ≤ 1 := by
      linarith [Real.eulerMascheroniConstant_lt_two_thirds]
    have hb1 : |b t| ≤ 1 := by
      simp only [b, F, hempty, Finset.sum_empty, zero_sub]
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    exact hb1.trans (p.one_le_C.trans (B_ge_C p))
  · have hlog : Real.log 2 ≤ t := le_of_not_gt hsmall
    have hx : (2 : ℝ) ≤ Real.exp t := by
      calc
        2 = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
        _ ≤ _ := Real.exp_le_exp.mpr hlog
    have hpsi (u : ℝ) (hu : (2 : ℝ) ≤ u) :
        |Chebyshev.psi u - u| ≤ p.C *
          (u * WeightedMangoldtRate.rate (2 * (p.alpha / 2)) u) := by
      have hu0 : 0 < u := by linarith
      have hlu : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
      have h := p.bound (Real.log u) hlu
      simp only [relativeError, Real.exp_neg, Real.exp_log hu0] at h
      have he : u * (u⁻¹ * Chebyshev.psi u - 1) = Chebyshev.psi u - u := by
        field_simp
      rw [← he, abs_mul, abs_of_pos hu0]
      have h' := mul_le_mul_of_nonneg_left h hu0.le
      dsimp only [WeightedMangoldtRate.rate]
      rw [show 2 * (p.alpha / 2) = p.alpha by ring]
      nlinarith only [h']
    have htail := WeightedMangoldtRate.chebyshev_tail_bound
      (half_pos p.alpha_pos) (show 0 ≤ p.C by linarith [p.one_le_C])
      (show (2 : ℝ) ≤ 2 from le_rfl) hx hpsi
    rw [weight_mass (half_pos p.alpha_pos)] at htail
    have he : WeightedMangoldtRate.rate (p.alpha / 2) (Real.exp t) ≤ 1 := by
      dsimp [WeightedMangoldtRate.rate]
      rw [Real.log_exp]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (by linarith [p.alpha_pos]) (Real.rpow_nonneg ht _))
    have hmass : 0 ≤ p.C * ((Nat.factorial 10 : ℝ) * (1 / (p.alpha / 2)) ^ 10) := by
      have hC : 0 ≤ p.C := by linarith [p.one_le_C]
      positivity
    have htail' := htail.trans (mul_le_of_le_one_right hmass he)
    rw [b_tail t hlog]
    calc
      _ ≤ |relativeError t| +
          |∫ u : ℝ in Ioi (Real.exp t), (Chebyshev.psi u - u) / u ^ 2| := abs_sub _ _
      _ ≤ p.C + p.C * ((Nat.factorial 10 : ℝ) * (1 / (p.alpha / 2)) ^ 10) :=
        add_le_add (relativeError_le p ht) htail'
      _ = _ := by dsimp [B]; congr 1 <;> ring

private lemma F_upper (p : PNTConstants) (t : ℝ) (ht : 0 ≤ t) : F t ≤ t + B p := by
  have hg : 0 ≤ Real.eulerMascheroniConstant :=
    le_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant.le
  have h := (abs_le.mp (b_bound p t ht)).2
  dsimp [b] at h
  linarith

/- The arithmetic row is a literal finite sum, including both endpoints.
   It is not an operator supplied through an analytic hypothesis. -/
def g (D u : ℝ) : ℝ := Real.exp (u / 2) + Real.exp ((D - u) / 2)
def weight (n : ℕ) : ℝ := ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)
def row (D u : ℝ) : ℝ := ∑ n ∈ primes D, weight n *
  ((Icc (0 : ℝ) D).indicator (g D) (u + Real.log n) +
    (Icc (0 : ℝ) D).indicator (g D) (u - Real.log n))

lemma g_pos (D u : ℝ) : 0 < g D u := by dsimp [g]; positivity
private lemma weight_nonneg (n : ℕ) : 0 ≤ weight n :=
  mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.exp_nonneg _)

lemma weight_eq_sqrt (n : ℕ) (hn : 2 ≤ n) :
    weight n = ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have he : Real.exp (Real.log n / 2) ^ 2 = (n : ℝ) := by
    rw [pow_two, ← Real.exp_add, show Real.log (n : ℝ) / 2 + Real.log n / 2 =
      Real.log n by ring, Real.exp_log hn0]
  have hs := Real.sq_sqrt hn0.le
  have hroot : Real.sqrt n = Real.exp (Real.log n / 2) := by
    nlinarith [Real.sqrt_nonneg (n : ℝ), Real.exp_pos (Real.log n / 2)]
  rw [hroot, weight, show -Real.log (n : ℝ) / 2 = -(Real.log n / 2) by ring,
    Real.exp_neg]
  simp only [div_eq_mul_inv]

lemma log_cut_iff (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    Real.log (n : ℝ) ≤ t ↔ n ≤ ⌊Real.exp t⌋₊ := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.le_floor_iff (Real.exp_nonneg _)]
  constructor
  · intro h
    simpa only [Real.exp_log hp] using Real.exp_le_exp.mpr h
  · intro h
    simpa only [Real.log_exp] using Real.log_le_log hp h

lemma indices (D t : ℝ) (ht : t ≤ D) :
    (primes D).filter (fun n : ℕ => Real.log (n : ℝ) ≤ t) = primes t := by
  classical
  ext n
  simp only [Finset.mem_filter, primes, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨hn, hN⟩, hlog⟩
    exact ⟨hn, (log_cut_iff n hn t).mp hlog⟩
  · rintro ⟨hn, hN⟩
    have hlog := (log_cut_iff n hn t).mpr hN
    exact ⟨⟨hn, (log_cut_iff n hn D).mp (hlog.trans ht)⟩, hlog⟩

lemma cumulative (t : ℝ) :
    (∑ n ∈ primes t, ArithmeticFunction.vonMangoldt n) = Chebyshev.psi (Real.exp t) := by
  classical
  change (∑ n ∈ Finset.Icc 2 ⌊Real.exp t⌋₊, ArithmeticFunction.vonMangoldt n) = _
  rw [Chebyshev.psi]
  apply Finset.sum_subset
  · intro n hn
    have h := Finset.mem_Icc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, h.2⟩
  · intro n hn hnot
    have h := Finset.mem_Ioc.mp hn
    have hsmall : n < 2 := by
      by_contra hh
      exact hnot (Finset.mem_Icc.mpr ⟨by omega, h.2⟩)
    have : n = 1 := by omega
    simp [this]

private lemma weighted_forward (D u : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    weight n * g D (u + Real.log n) =
      Real.exp (u / 2) * ArithmeticFunction.vonMangoldt n +
        Real.exp ((D - u) / 2) * (ArithmeticFunction.vonMangoldt n / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  dsimp [weight, g]
  rw [mul_add]
  have h1 : Real.exp (-Real.log (n : ℝ) / 2) * Real.exp ((u + Real.log n) / 2) =
      Real.exp (u / 2) := by rw [← Real.exp_add]; congr 1 <;> ring
  have h2 : Real.exp (-Real.log (n : ℝ) / 2) * Real.exp ((D - (u + Real.log n)) / 2) =
      Real.exp ((D - u) / 2) / n := by
    calc
      _ = Real.exp ((D - u) / 2 - Real.log n) := by
        rw [← Real.exp_add]; congr 1 <;> ring
      _ = Real.exp ((D - u) / 2) / Real.exp (Real.log n) := Real.exp_sub _ _
      _ = _ := by rw [Real.exp_log hn0]
  calc
    _ = ArithmeticFunction.vonMangoldt n *
          (Real.exp (-Real.log n / 2) * Real.exp ((u + Real.log n) / 2)) +
        ArithmeticFunction.vonMangoldt n *
          (Real.exp (-Real.log n / 2) * Real.exp ((D - (u + Real.log n)) / 2)) := by ring
    _ = _ := by rw [h1, h2]; ring

private lemma weighted_backward (D u : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    weight n * g D (u - Real.log n) =
      Real.exp (u / 2) * (ArithmeticFunction.vonMangoldt n / n) +
        Real.exp ((D - u) / 2) * ArithmeticFunction.vonMangoldt n := by
  have h := weighted_forward D (D - u) n hn
  have hg (v : ℝ) : g D (D - v) = g D v := by
    dsimp [g]
    rw [sub_sub_cancel]
    exact add_comm _ _
  have harg : u - Real.log (n : ℝ) = D - (D - u + Real.log n) := by ring
  rw [harg, hg]
  simpa only [sub_sub_cancel, add_comm] using h

/-- Literal complete Mangoldt row identity, valid also at every cutoff entry. -/
private theorem actual_weighted_row (D u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) :
    row D u =
      Real.exp (u / 2) * (Chebyshev.psi (Real.exp (D - u)) + F u) +
        Real.exp ((D - u) / 2) * (Chebyshev.psi (Real.exp u) + F (D - u)) := by
  classical
  have hterm (n : ℕ) (hn : n ∈ primes D) :
      weight n * ((Icc (0 : ℝ) D).indicator (g D) (u + Real.log n) +
        (Icc (0 : ℝ) D).indicator (g D) (u - Real.log n)) =
      (if Real.log (n : ℝ) ≤ D - u then weight n * g D (u + Real.log n) else 0) +
        (if Real.log (n : ℝ) ≤ u then weight n * g D (u - Real.log n) else 0) := by
    have hn2 := (Finset.mem_Icc.mp hn).1
    have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
    have hright : u + Real.log (n : ℝ) ∈ Icc (0 : ℝ) D ↔ Real.log n ≤ D - u := by
      simp only [Set.mem_Icc]; constructor <;> intro h
      · linarith [h.2]
      · exact ⟨by linarith [hu.1], by linarith⟩
    have hleft : u - Real.log (n : ℝ) ∈ Icc (0 : ℝ) D ↔ Real.log n ≤ u := by
      simp only [Set.mem_Icc]; constructor <;> intro h
      · linarith [h.1]
      · exact ⟨by linarith, by linarith [hu.2]⟩
    by_cases hr : Real.log (n : ℝ) ≤ D - u <;>
      by_cases hl : Real.log (n : ℝ) ≤ u <;>
      simp [Set.indicator, hright, hleft, hr, hl, mul_add]
  rw [row, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, indices D (D - u) (by linarith [hu.1]),
    indices D u hu.2]
  have hf := Finset.sum_congr rfl (fun n (hn : n ∈ primes (D - u)) =>
    weighted_forward D u n (Finset.mem_Icc.mp hn).1)
  have hb := Finset.sum_congr rfl (fun n (hn : n ∈ primes u) =>
    weighted_backward D u n (Finset.mem_Icc.mp hn).1)
  rw [hf, hb, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    cumulative, cumulative]
  dsimp only [F]
  ring

private lemma psi_eq (t : ℝ) :
    Chebyshev.psi (Real.exp t) = Real.exp t * (1 + relativeError t) := by
  dsimp [relativeError]
  have he : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hz : 1 + (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1) =
      Real.exp (-t) * Chebyshev.psi (Real.exp t) := by ring
  rw [hz, ← mul_assoc, he, one_mul]

private lemma psi_row_exact (D u : ℝ) :
    Real.exp (u / 2) * Chebyshev.psi (Real.exp (D - u)) +
      Real.exp ((D - u) / 2) * Chebyshev.psi (Real.exp u) =
    M D * (g D u + Real.exp (u / 2) * relativeError u +
      Real.exp ((D - u) / 2) * relativeError (D - u)) := by
  rw [psi_eq, psi_eq]
  have h1 : Real.exp (u / 2) * Real.exp (D - u) =
      M D * Real.exp ((D - u) / 2) := by
    dsimp [M]; rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> ring
  have h2 : Real.exp ((D - u) / 2) * Real.exp u = M D * Real.exp (u / 2) := by
    dsimp [M]; rw [← Real.exp_add, ← Real.exp_add]; congr 1 <;> ring
  calc
    _ = (Real.exp (u / 2) * Real.exp (D - u)) * (1 + relativeError (D - u)) +
        (Real.exp ((D - u) / 2) * Real.exp u) * (1 + relativeError u) := by ring
    _ = _ := by rw [h1, h2]; dsimp [g]; ring

private lemma weighted_error (p : PNTConstants) (D u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) D) :
    Real.exp (u / 2) * relativeError u +
      Real.exp ((D - u) / 2) * relativeError (D - u) ≤ epsilon p D * g D u := by
  let e : ℝ := Real.exp (-p.alpha * (D / 4) ^ ((1 : ℝ) / 10))
  let z : ℝ := Real.exp (-D / 4)
  let x : ℝ := Real.exp (u / 2)
  let y : ℝ := Real.exp ((D - u) / 2)
  have hD : 0 ≤ D := hu.1.trans hu.2
  have hx : 0 ≤ x := Real.exp_nonneg _
  have hy : 0 ≤ y := Real.exp_nonneg _
  have he : 0 ≤ e := Real.exp_nonneg _
  have hz : 0 ≤ z := Real.exp_nonneg _
  have hC : 0 ≤ p.C := by linarith [p.one_le_C]
  change x * relativeError u + y * relativeError (D - u) ≤ (p.C * (e + z)) * (x + y)
  by_cases hl : u < D / 4
  · have hxy : x ≤ z * y := by
      dsimp [x, z, y]
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hru := le_trans (le_abs_self _) (relativeError_le p hu.1)
    have hrv := le_trans (le_abs_self _) (relativeError_decay p (by linarith : 0 ≤ D / 4)
      (by linarith : D / 4 ≤ D - u))
    have h1 := mul_le_mul_of_nonneg_left hru hx
    have h2 := mul_le_mul_of_nonneg_left hrv hy
    have h3 := mul_le_mul_of_nonneg_left hxy hC
    nlinarith [mul_nonneg (mul_nonneg hC he) hx,
      mul_nonneg (mul_nonneg hC hz) hx]
  · by_cases hr : 3 * D / 4 < u
    · have hyx : y ≤ z * x := by
        dsimp [y, z, x]
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have hru := le_trans (le_abs_self _) (relativeError_decay p (by linarith : 0 ≤ D / 4)
        (by linarith : D / 4 ≤ u))
      have hrv := le_trans (le_abs_self _) (relativeError_le p (by linarith [hu.2] : 0 ≤ D - u))
      have h1 := mul_le_mul_of_nonneg_left hru hx
      have h2 := mul_le_mul_of_nonneg_left hrv hy
      have h3 := mul_le_mul_of_nonneg_left hyx hC
      nlinarith [mul_nonneg (mul_nonneg hC he) hy,
        mul_nonneg (mul_nonneg hC hz) hy]
    · have hru := le_trans (le_abs_self _) (relativeError_decay p (by linarith : 0 ≤ D / 4)
        (by linarith : D / 4 ≤ u))
      have hrv := le_trans (le_abs_self _) (relativeError_decay p (by linarith : 0 ≤ D / 4)
        (by linarith : D / 4 ≤ D - u))
      have h1 := mul_le_mul_of_nonneg_left hru hx
      have h2 := mul_le_mul_of_nonneg_left hrv hy
      nlinarith [mul_nonneg (mul_nonneg hC hz) (add_nonneg hx hy)]

/-- The actual complete weighted row has the original coefficient-one beta.
There is no row, norm, correlation or Fourier supplier in the assumptions. -/
private theorem actual_weighted_row_bound (p : PNTConstants) (D u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) D) : row D u ≤ beta p D * g D u := by
  rw [actual_weighted_row D u hu]
  have hF1 := F_upper p u hu.1
  have hF2 := F_upper p (D - u) (by linarith [hu.2])
  have hx := Real.exp_nonneg (u / 2)
  have hy := Real.exp_nonneg ((D - u) / 2)
  have hprime : Real.exp (u / 2) * Chebyshev.psi (Real.exp (D - u)) +
      Real.exp ((D - u) / 2) * Chebyshev.psi (Real.exp u) ≤
      M D * (1 + epsilon p D) * g D u := by
    rw [psi_row_exact]
    have he := mul_le_mul_of_nonneg_left (weighted_error p D u hu)
      (Real.exp_nonneg (D / 2))
    dsimp only [M] at *
    nlinarith only [he]
  have hs : Real.exp (u / 2) * F u + Real.exp ((D - u) / 2) * F (D - u) ≤
      (D + B p) * g D u := by
    have h1 := mul_le_mul_of_nonneg_left hF1 hx
    have h2 := mul_le_mul_of_nonneg_left hF2 hy
    have hu0 := mul_nonneg hu.1 hy
    have huD := mul_nonneg (sub_nonneg.mpr hu.2) hx
    dsimp [g]
    nlinarith only [h1, h2, hu0, huD]
  dsimp only [beta]
  nlinarith only [hprime, hs]

/- Real-space realization of the row estimate. Only literal finite shifts
   of the original prefix occur; no abstract operator is postulated. -/
private def density (D t : ℝ) (f : ℝ → ℂ) (u : ℝ) : ℝ :=
  if u ∈ Icc (0 : ℝ) D ∧ u + t ∈ Icc (0 : ℝ) D then
    g D (u + t) / g D u * ‖f u‖ ^ 2 else 0

private lemma g_lower (D u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) : 1 ≤ g D u := by
  have he : 1 ≤ Real.exp (u / 2) := Real.one_le_exp_iff.mpr (by linarith [hu.1])
  dsimp [g]
  linarith [Real.exp_pos ((D - u) / 2)]

private lemma g_upper (D u : ℝ) (hu : u ∈ Icc (0 : ℝ) D) : g D u ≤ 2 * M D := by
  have h1 : Real.exp (u / 2) ≤ M D := Real.exp_le_exp.mpr (by linarith [hu.2])
  have h2 : Real.exp ((D - u) / 2) ≤ M D := Real.exp_le_exp.mpr (by linarith [hu.1])
  dsimp [g]
  linarith

private lemma density_integrable (D t : ℝ) (f : ℝ → ℂ)
    (hm : Measurable f) (hi : Integrable (fun u : ℝ => ‖f u‖ ^ 2)) :
    Integrable (density D t f) := by
  have hS : MeasurableSet {u : ℝ | u ∈ Icc (0 : ℝ) D ∧ u + t ∈ Icc (0 : ℝ) D} :=
    measurableSet_Icc.inter (measurableSet_Icc.preimage (by fun_prop))
  have hg : Continuous (fun u : ℝ => g D (u + t) / g D u) := by
    apply Continuous.div
    · unfold g; fun_prop
    · unfold g; fun_prop
    · intro u; exact (g_pos D u).ne'
  have hd : AEStronglyMeasurable (density D t f) volume := by
    change AEStronglyMeasurable
      (fun u => if u ∈ Icc (0 : ℝ) D ∧ u + t ∈ Icc (0 : ℝ) D then
        g D (u + t) / g D u * ‖f u‖ ^ 2 else 0) volume
    exact ((hg.measurable.mul (hm.norm.pow_const 2)).ite hS measurable_const).aestronglyMeasurable
  apply (hi.const_mul (2 * M D)).mono' hd
  apply ae_of_all
  intro u
  by_cases hu : u ∈ Icc (0 : ℝ) D ∧ u + t ∈ Icc (0 : ℝ) D
  · have hratio : g D (u + t) / g D u ≤ 2 * M D := by
      apply (div_le_iff₀ (g_pos D u)).mpr
      exact (g_upper D (u + t) hu.2).trans
        (le_mul_of_one_le_right (by dsimp [M]; positivity) (g_lower D u hu.1))
    have hnonneg : 0 ≤ g D (u + t) / g D u * ‖f u‖ ^ 2 := by
      exact mul_nonneg (div_nonneg (g_pos D (u + t)).le (g_pos D u).le) (sq_nonneg _)
    rw [density, if_pos hu, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact mul_le_mul_of_nonneg_right hratio (sq_nonneg _)
  · simp only [density, if_neg hu, norm_zero]
    dsimp [M]
    positivity

lemma weighted_complex_pair (X Y : ℝ) (hX : 0 < X) (hY : 0 < Y) (z w : ℂ) :
    2 * (star z * w).re ≤ (Y / X) * ‖w‖ ^ 2 + (X / Y) * ‖z‖ ^ 2 := by
  have hcomplex : (star z * w).re ≤ ‖z‖ * ‖w‖ := by
    simpa only [norm_mul, norm_star] using Complex.re_le_norm (star z * w)
  have h1 : 2 * (star z * w).re * (X * Y) ≤
      Y ^ 2 * ‖w‖ ^ 2 + X ^ 2 * ‖z‖ ^ 2 := by
    have hp := mul_le_mul_of_nonneg_right hcomplex (show 0 ≤ 2 * (X * Y) by positivity)
    nlinarith [sq_nonneg (Y * ‖w‖ - X * ‖z‖)]
  calc
    _ ≤ (Y ^ 2 * ‖w‖ ^ 2 + X ^ 2 * ‖z‖ ^ 2) / (X * Y) :=
      (le_div_iff₀ (mul_pos hX hY)).mpr h1
    _ = _ := by field_simp [hX.ne', hY.ne']

private lemma pair_density (D t : ℝ) (f : ℝ → ℂ)
    (hs : ∀ u : ℝ, u ∉ Icc (0 : ℝ) D → f u = 0) (u : ℝ) :
    2 * (star (f (u + t)) * f u).re ≤
      density D t f u + density D (-t) f (u + t) := by
  by_cases hu : u ∈ Icc (0 : ℝ) D
  · by_cases hv : u + t ∈ Icc (0 : ℝ) D
    · have h := weighted_complex_pair (g D u) (g D (u + t))
        (g_pos D u) (g_pos D (u + t)) (f (u + t)) (f u)
      simpa only [density, hu, hv, add_neg_cancel_right, and_self, if_true] using h
    · simp [density, hv, hs (u + t) hv]
  · simp [density, hu, hs u hu]

private lemma density_row (D : ℝ) (f : ℝ → ℂ) (u : ℝ)
    (hu : u ∈ Icc (0 : ℝ) D) :
    (∑ n ∈ primes D, weight n *
      (density D (Real.log n) f u + density D (-Real.log n) f u)) =
      row D u / g D u * ‖f u‖ ^ 2 := by
  classical
  rw [row, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : u + Real.log (n : ℝ) ∈ Icc (0 : ℝ) D <;>
    by_cases hm : u - Real.log (n : ℝ) ∈ Icc (0 : ℝ) D <;>
    simp only [sub_eq_add_neg] at hm ⊢ <;>
    simp only [density, Set.indicator, hu, hp, hm, true_and, ite_true, ite_false] <;> ring

private lemma prefix_measurable {I : Type u} [Fintype I] (x : I → ℝ) (a : I → ℂ) :
    Measurable («prefix» x a) := by
  classical
  unfold «prefix»
  apply Finset.measurable_sum
  intro i hi
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma prefix_support {I : Type u} [Fintype I] (D : ℝ)
    (x : I → ℝ) (a : I → ℂ) (hx : ∀ i, x i ∈ Icc (0 : ℝ) D)
    (ha : ∑ i, a i = 0) (t : ℝ) (ht : t ∉ Icc (0 : ℝ) D) :
    «prefix» x a t = 0 := by
  classical
  by_cases ht0 : t < 0
  · apply Finset.sum_eq_zero
    intro i hi
    exact if_neg (by linarith [(hx i).1])
  · have hDt : D < t := by
      by_contra h
      exact ht ⟨by linarith, by linarith⟩
    simpa [«prefix», fun i => (hx i).2.trans hDt.le] using ha

def primeQuadratic {I : Type u} [Fintype I]
    (D : ℝ) (x : I → ℝ) (a : I → ℂ) : ℝ :=
  2 * ∑ n ∈ primes D, ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    (∫ v : ℝ, star («prefix» x a (v + Real.log n)) * «prefix» x a v).re

/-- Direct finite-translation quadratic estimate for arbitrary original
complex finite atoms. It assumes neither an operator realization nor a
Fourier/correlation arithmetic bridge. All prime powers are included. -/
theorem actual_weighted_mangoldt_translation_bound (p : PNTConstants)
    (D : ℝ) (x : I → ℝ) (a : I → ℂ)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) D) (ha : ∑ i, a i = 0) :
    primeQuadratic D x a ≤ beta p D * energy x a := by
  classical
  let f : ℝ → ℂ := «prefix» x a
  have hf := (shifted_hinge_prefix_energy x a ha 0).2.1
  have hm : Measurable f := prefix_measurable x a
  have hs : ∀ u : ℝ, u ∉ Icc (0 : ℝ) D → f u = 0 := prefix_support D x a hx ha
  have hd (t : ℝ) : Integrable (density D t f) := density_integrable D t f hm hf
  have hc (t : ℝ) : Integrable (fun u : ℝ => star (f (u + t)) * f u) :=
    (shifted_hinge_prefix_energy x a ha t).1
  have hlocal (t : ℝ) :
      2 * (∫ u : ℝ, star (f (u + t)) * f u).re ≤
        (∫ u : ℝ, density D t f u) + ∫ u : ℝ, density D (-t) f u := by
    have hmono := integral_mono ((hc t).re.const_mul 2)
      ((hd t).add ((hd (-t)).comp_add_right t)) (pair_density D t f hs)
    simp only [Pi.add_apply] at hmono
    rw [integral_const_mul, integral_re (hc t),
      integral_add (hd t) ((hd (-t)).comp_add_right t),
      integral_add_right_eq_self] at hmono
    simpa only [RCLike.re_to_complex] using hmono
  have hsum : primeQuadratic D x a ≤
      ∫ u : ℝ, ∑ n ∈ primes D, weight n *
        (density D (Real.log n) f u + density D (-Real.log n) f u) := by
    have hfin := Finset.sum_le_sum (s := primes D) (fun (n : ℕ) hn =>
      mul_le_mul_of_nonneg_left (hlocal (Real.log (n : ℝ))) (weight_nonneg n))
    have hsumint : (∫ u : ℝ, ∑ n ∈ primes D, weight n *
        (density D (Real.log n) f u + density D (-Real.log n) f u)) =
        ∑ n ∈ primes D, ∫ u : ℝ, weight n *
          (density D (Real.log n) f u + density D (-Real.log n) f u) :=
      integral_finsetSum _ (fun (n : ℕ) hn =>
        ((hd (Real.log n)).add (hd (-Real.log n))).const_mul (weight n))
    rw [hsumint]
    have hsplit (n : ℕ) : (∫ u : ℝ, weight n *
        (density D (Real.log n) f u + density D (-Real.log n) f u)) =
        weight n * ((∫ u : ℝ, density D (Real.log n) f u) +
          ∫ u : ℝ, density D (-Real.log n) f u) := by
      rw [integral_const_mul]
      exact congrArg (fun z => weight n * z) (integral_add (hd _) (hd _))
    simp_rw [hsplit]
    dsimp [primeQuadratic]
    rw [Finset.mul_sum]
    convert hfin using 1
    apply Finset.sum_congr rfl
    intro n hn
    rw [weight_eq_sqrt n (Finset.mem_Icc.mp hn).1]
    change 2 * (ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (∫ u : ℝ, star (f (u + Real.log n)) * f u).re) =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (2 * (∫ u : ℝ, star (f (u + Real.log n)) * f u).re)
    ring
  have hint : Integrable (fun u : ℝ => ∑ n ∈ primes D, weight n *
      (density D (Real.log n) f u + density D (-Real.log n) f u)) :=
    integrable_finsetSum _ (fun (n : ℕ) hn =>
      ((hd (Real.log n)).add (hd (-Real.log n))).const_mul (weight n))
  have hpoint (u : ℝ) :
      (∑ n ∈ primes D, weight n *
        (density D (Real.log n) f u + density D (-Real.log n) f u)) ≤
      beta p D * ‖f u‖ ^ 2 := by
    by_cases hu : u ∈ Icc (0 : ℝ) D
    · rw [density_row D f u hu]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact (div_le_iff₀ (g_pos D u)).mpr (actual_weighted_row_bound p D u hu)
    · simp [density, hu, hs u hu]
  exact hsum.trans (by
    have h := integral_mono hint (hf.const_mul (beta p D)) hpoint
    simpa only [energy, f, integral_const_mul] using h)

end D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelMomentCertificate
