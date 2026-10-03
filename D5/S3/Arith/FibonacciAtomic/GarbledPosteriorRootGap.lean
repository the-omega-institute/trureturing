/- GID: D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A garbled window teacher has a uniform risk gap for scalar softmax roots. -/

import D5.S3.Arith.FibonacciAtomic.FirstRejectionCutCapacity
import D5.S3.TotalVariation.Pinsker
import Mathlib.Algebra.BigOperators.Expect

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap

open LiteralWindowEnd
open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open scoped BigOperators

/-- Independent whole windows, including every tail word. -/
abbrev Input (m : ℕ) := FirstRejectionCutCapacity.Word (m + 2)

/-- The class is 1 at the first selected seam, 2 at the second seam only
when the first is absent, and 0 otherwise. -/
def teacher {m : ℕ} (x : Input m) : Fin 3 :=
  if last (x 0) && first (x 1) then 1
  else if last (x 1) && first (x 2) then 2 else 0

def mu : ℝ := (11 - 6 * Real.sqrt 2) / 12

def channel : Fin 3 → Fin 3 → ℝ := ![
  ![5 / 12, Real.sqrt 2 / 2 - 1 / 3, mu],
  ![7 / 24, 5 / 12, 7 / 24],
  ![mu, Real.sqrt 2 / 2 - 1 / 3, 5 / 12]]

def posterior {m : ℕ} (x : Input m) : Fin 3 → ℝ := channel (teacher x)

def uniformMass (m : ℕ) : ℝ := 1 / (5 : ℝ) ^ (m + 3)

def jointMass {m : ℕ} (x : Input m) (j : Fin 3) : ℝ :=
  uniformMass m * posterior x j

def mean {m : ℕ} (f : Input m → ℝ) : ℝ := Finset.expect Finset.univ f

/-- Every scalar root is allowed. A zero-dimensional root embeds by z = 0;
there is no restriction on trees, peaks, encodings, or internal parameters. -/
def softmax {m : ℕ} (z : Input m → ℝ) (u v : Fin 3 → ℝ)
    (x : Input m) (i : Fin 3) : ℝ :=
  Real.exp (u i * z x + v i) / ∑ j, Real.exp (u j * z x + v j)

def brierRisk {m : ℕ} (p : Input m → Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ j, jointMass x j * ∑ i, (p x i - if j = i then 1 else 0) ^ 2

def brierBayes (m : ℕ) : ℝ := mean (m := m) (fun x => 1 - ∑ i, posterior x i ^ 2)

/-- Used only for probability predictions with positive coordinates, as supplied by softmax here.
The source's extended-real convention of +∞ for zero true-class probability
is outside this definition. -/
def logRisk {m : ℕ} (p : Input m → Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ j, jointMass x j * (-Real.log (p x j))

def logBayes (m : ℕ) : ℝ :=
  mean (m := m) (fun x => -∑ j, posterior x j * Real.log (posterior x j))

def kappa : ℝ := mu ^ 2 * (Real.log (125 / 98 : ℝ)) ^ 2 / 1875

/-- Squared strip-distance bound for the three log-odds vertices.
The same class is separated from the entire affine line. -/
private theorem strip_distance (η ξ lam δ a b offset : ℝ)
    (hδ : 0 < δ) (hlam : δ ≤ lam) (hmid : 2 * (ξ - η) - lam = δ)
    (hunit : a ^ 2 + b ^ 2 = 1) :
    ∃ i : Fin 3, δ ^ 2 / 20 ≤
      (![a * η - b * lam - offset, a * ξ - offset,
          a * (η + lam) + b * lam - offset] i) ^ 2 := by
  let d : Fin 3 → ℝ := ![a * η - b * lam - offset, a * ξ - offset,
    a * (η + lam) + b * lam - offset]
  let t := max |d 0| (max |d 1| |d 2|)
  have ht : 0 ≤ t := (abs_nonneg (d 0)).trans (le_max_left _ _)
  have hd0 : -t ≤ d 0 ∧ d 0 ≤ t := abs_le.mp (le_max_left _ _)
  have hd1 : -t ≤ d 1 ∧ d 1 ≤ t :=
    abs_le.mp ((le_max_left _ _).trans (le_max_right _ _))
  have hd2 : -t ≤ d 2 ∧ d 2 ≤ t :=
    abs_le.mp ((le_max_right _ _).trans (le_max_right _ _))
  have hidA : δ * a = 2 * d 1 - d 0 - d 2 := by dsimp [d]; linear_combination -a * hmid
  have hidB : 2 * lam * (δ * b) =
      (lam - δ) * d 0 - 2 * lam * d 1 + (lam + δ) * d 2 := by
    dsimp [d]
    linear_combination (a * lam) * hmid
  have hlampos : 0 < lam := hδ.trans_le hlam
  have hlamδ : 0 ≤ lam - δ := sub_nonneg.mpr hlam
  have hlamsum : 0 ≤ lam + δ := by linarith
  have ha : -4 * t ≤ δ * a ∧ δ * a ≤ 4 * t := by
    constructor <;> linarith [hd0.1, hd0.2, hd1.1, hd1.2, hd2.1, hd2.2]
  have hb : -2 * t ≤ δ * b ∧ δ * b ≤ 2 * t := by
    constructor
    · have h := add_nonneg
        (mul_nonneg hlamδ (show 0 ≤ d 0 + t by linarith [hd0.1]))
        (add_nonneg (mul_nonneg (show 0 ≤ 2 * lam by linarith)
          (show 0 ≤ t - d 1 by linarith [hd1.2]))
          (mul_nonneg hlamsum (show 0 ≤ d 2 + t by linarith [hd2.1])))
      nlinarith
    · have h := add_nonneg
        (mul_nonneg hlamδ (show 0 ≤ t - d 0 by linarith [hd0.2]))
        (add_nonneg (mul_nonneg (show 0 ≤ 2 * lam by linarith)
          (show 0 ≤ d 1 + t by linarith [hd1.1]))
          (mul_nonneg hlamsum (show 0 ≤ t - d 2 by linarith [hd2.2])))
      nlinarith
  have haSq : (δ * a) ^ 2 ≤ 16 * t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 * t - δ * a by linarith [ha.2])
      (show 0 ≤ 4 * t + δ * a by linarith [ha.1])]
  have hbSq : (δ * b) ^ 2 ≤ 4 * t ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 2 * t - δ * b by linarith [hb.2])
      (show 0 ≤ 2 * t + δ * b by linarith [hb.1])]
  have hbound : δ ^ 2 / 20 ≤ t ^ 2 := by
    nlinarith [sq_nonneg δ, congrArg (fun r : ℝ => δ ^ 2 * r) hunit]
  change ∃ i : Fin 3, δ ^ 2 / 20 ≤ d i ^ 2
  by_cases h0 : max |d 1| |d 2| ≤ |d 0|
  · refine ⟨0, ?_⟩
    simpa only [t, max_eq_left h0, sq_abs] using hbound
  · by_cases h1 : |d 2| ≤ |d 1|
    · refine ⟨1, ?_⟩
      simpa only [t, max_eq_right (le_of_not_ge h0), max_eq_left h1, sq_abs]
        using hbound
    · refine ⟨2, ?_⟩
      simpa only [t, max_eq_right (le_of_not_ge h0),
        max_eq_right (le_of_not_ge h1), sq_abs] using hbound

/-- Interior and large-error branches convert log-odds separation to
squared probability error without a compact parameter domain. -/
private theorem probability_separation (p q : Fin 3 → ℝ) (μ δ : ℝ)
    (hμ : 0 < μ) (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, μ ≤ q i)
    (hsep : δ ^ 2 / 20 ≤
      (Real.log (p 1 / p 0) - Real.log (q 1 / q 0)) ^ 2 +
      (Real.log (p 2 / p 0) - Real.log (q 2 / q 0)) ^ 2) :
    μ ^ 2 * δ ^ 2 / 240 ≤ ∑ i, (p i - q i) ^ 2 := by
  have hqpos (i : Fin 3) : 0 < q i := hμ.trans_le (hq i)
  let e := ∑ i, (p i - q i) ^ 2
  by_cases hsmall : e ≤ μ ^ 2 / 4
  · have hpmin (i : Fin 3) : μ / 2 ≤ p i := by
      have hi : (p i - q i) ^ 2 ≤ e :=
        Finset.single_le_sum (fun j _ => sq_nonneg (p j - q j)) (Finset.mem_univ i)
      have hiabs : |p i - q i| ≤ μ / 2 := by
        apply (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ μ / 2)).mp
        rw [sq_abs]
        nlinarith
      have := (abs_le.mp hiabs).1
      linarith [hq i]
    have log_bound (x y : ℝ) (hx : μ / 2 ≤ x) (hy : μ / 2 ≤ y)
        (hyx : y ≤ x) : μ * (Real.log x - Real.log y) ≤ 2 * (x - y) := by
      have hxpos : 0 < x := by linarith
      have hypos : 0 < y := by linarith
      have hlognonneg : 0 ≤ Real.log x - Real.log y :=
        sub_nonneg.mpr (Real.log_le_log hypos hyx)
      have hlog : Real.log x - Real.log y ≤ x / y - 1 := by
        rw [← Real.log_div hxpos.ne' hypos.ne']
        exact Real.log_le_sub_one_of_pos (div_pos hxpos hypos)
      have hmul := mul_le_mul_of_nonneg_left hlog hypos.le
      have hminmul := mul_le_mul_of_nonneg_right hy hlognonneg
      have hcancel : y * (x / y) = x := mul_div_cancel₀ x hypos.ne'
      nlinarith
    have log_sq (x y : ℝ) (hx : μ / 2 ≤ x) (hy : μ / 2 ≤ y) :
        μ ^ 2 * (Real.log x - Real.log y) ^ 2 ≤ 4 * (x - y) ^ 2 := by
      by_cases hyx : y ≤ x
      · have hb := log_bound x y hx hy hyx
        have hl : 0 ≤ Real.log x - Real.log y :=
          sub_nonneg.mpr (Real.log_le_log (by linarith) hyx)
        nlinarith only [mul_nonneg
          (show 0 ≤ 2 * (x - y) - μ * (Real.log x - Real.log y) by linarith)
          (show 0 ≤ 2 * (x - y) + μ * (Real.log x - Real.log y) by nlinarith [mul_nonneg hμ.le hl])]
      · have hb := log_bound y x hy hx (le_of_not_ge hyx)
        have hl : 0 ≤ Real.log y - Real.log x :=
          sub_nonneg.mpr (Real.log_le_log (by linarith) (le_of_not_ge hyx))
        nlinarith only [mul_nonneg
          (show 0 ≤ 2 * (y - x) - μ * (Real.log y - Real.log x) by linarith)
          (show 0 ≤ 2 * (y - x) + μ * (Real.log y - Real.log x) by nlinarith [mul_nonneg hμ.le hl])]
    let l : Fin 3 → ℝ := fun i => Real.log (p i) - Real.log (q i)
    have hl (i : Fin 3) : μ ^ 2 * (l i) ^ 2 ≤ 4 * (p i - q i) ^ 2 :=
      log_sq (p i) (q i) (hpmin i) (by linarith [hq i])
    have hmatrix : (l 1 - l 0) ^ 2 + (l 2 - l 0) ^ 2 ≤
        3 * (l 0 ^ 2 + l 1 ^ 2 + l 2 ^ 2) := by
      nlinarith only [sq_nonneg (l 0 + l 1 + l 2), sq_nonneg (l 1 - l 2)]
    have hsep' : δ ^ 2 / 20 ≤ (l 1 - l 0) ^ 2 + (l 2 - l 0) ^ 2 := by
      simpa only [Real.log_div (hp 1).ne' (hp 0).ne',
        Real.log_div (hp 2).ne' (hp 0).ne',
        Real.log_div (hqpos 1).ne' (hqpos 0).ne',
        Real.log_div (hqpos 2).ne' (hqpos 0).ne', l, sub_sub_sub_comm] using hsep
    have hm := mul_le_mul_of_nonneg_left hmatrix (sq_nonneg μ)
    have hs := mul_le_mul_of_nonneg_left hsep' (sq_nonneg μ)
    change μ ^ 2 * δ ^ 2 / 240 ≤ ∑ i, (p i - q i) ^ 2
    rw [Fin.sum_univ_three]
    nlinarith only [hm, hs, hl 0, hl 1, hl 2]
  · have hδsq : δ ^ 2 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hδsq (sq_nonneg μ)
    change μ ^ 2 * δ ^ 2 / 240 ≤ e
    nlinarith [sq_nonneg μ]

-- Exact three-window class counts require a larger local elaboration budget.
set_option maxHeartbeats 1600000 in
-- The class-count subproof expands 125 three-window configurations.
/-- The risk is scored under the joint law, with its own Bayes value.
The lower bound includes arbitrary scalar roots and free affine heads. -/
theorem result (m : ℕ) (z : Input m → ℝ) (u v : Fin 3 → ℝ) :
    kappa ≤ brierRisk (softmax z u v) - brierBayes m ∧
    kappa ≤ logRisk (softmax z u v) - logBayes m ∧
    kappa = (193 - 132 * Real.sqrt 2) / 270000 *
      (Real.log (125 / 98 : ℝ)) ^ 2 ∧
    0 < kappa := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hslo : (4 / 3 : ℝ) < Real.sqrt 2 :=
    (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hshi : Real.sqrt 2 < (3 / 2 : ℝ) :=
    (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  have hμ : 0 < mu := by dsimp [mu]; linarith
  have hA : 0 < Real.sqrt 2 / 2 - (1 / 3 : ℝ) := by linarith
  have hrows (c : Fin 3) : (∀ i, 0 < channel c i) ∧ ∑ i, channel c i = 1 := by
    constructor
    · intro i
      fin_cases c <;> fin_cases i <;> norm_num [channel, mu] <;> linarith
    · fin_cases c <;> norm_num [channel, mu, Fin.sum_univ_succ] <;> ring
  have hmin (c i : Fin 3) : mu ≤ channel c i := by
    fin_cases c <;> fin_cases i <;> norm_num [channel, mu] <;> linarith
  let δ := Real.log (125 / 98 : ℝ)
  have hδ : 0 < δ := Real.log_pos (by norm_num)
  have hδlt : δ < 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 125 / 98 by norm_num)
    dsimp [δ]; linarith
  let η := Real.log ((Real.sqrt 2 / 2 - 1 / 3) / (5 / 12 : ℝ))
  let ξ := Real.log ((5 / 12 : ℝ) / (7 / 24 : ℝ))
  let lam := Real.log ((5 / 12 : ℝ) / mu)
  have hlam : δ < lam := by
    apply Real.log_lt_log (by norm_num)
    apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 98) hμ).mpr
    dsimp [mu]; linarith
  have hmid : 2 * (ξ - η) - lam = δ := by
    have hAA : (Real.sqrt 2 / 2 - (1 / 3 : ℝ)) ^ 2 = 2 / 3 * mu := by
      dsimp [mu]; nlinarith
    have hratio : ((5 / 12 : ℝ) / (7 / 24 : ℝ)) ^ 2 /
        (((Real.sqrt 2 / 2 - 1 / 3) / (5 / 12 : ℝ)) ^ 2 *
          ((5 / 12 : ℝ) / mu)) = 125 / 98 := by
      simp only [div_pow]
      rw [hAA]
      field_simp [ne_of_gt hμ]
      <;> ring
    have hlog := congrArg Real.log hratio
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity)
      (by positivity), Real.log_pow, Real.log_pow] at hlog
    dsimp [η, ξ, lam, δ]
    linarith
  have hconstant : kappa = (193 - 132 * Real.sqrt 2) / 270000 * δ ^ 2 := by
    dsimp [kappa, mu, δ]
    linear_combination (Real.log (125 / 98 : ℝ)) ^ 2 / 7500 * hs
  have hk : 0 < kappa := by dsimp [kappa]; positivity
  let p := softmax z u v
  have hden (x : Input m) : 0 < ∑ j, Real.exp (u j * z x + v j) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  have hp (x : Input m) (i : Fin 3) : 0 < p x i :=
    div_pos (Real.exp_pos _) (hden x)
  have hpsum (x : Input m) : ∑ i, p x i = 1 := by
    dsimp [p, softmax]
    rw [← Finset.sum_div, div_self (hden x).ne']
  have hlogit (x : Input m) (i : Fin 3) :
      Real.log (p x i / p x 0) = (u i - u 0) * z x + (v i - v 0) := by
    have hratio : p x i / p x 0 =
        Real.exp (u i * z x + v i) / Real.exp (u 0 * z x + v 0) := by
      dsimp [p, softmax]
      field_simp [(hden x).ne', (Real.exp_pos (u 0 * z x + v 0)).ne']
    rw [hratio, Real.log_div (Real.exp_pos _).ne' (Real.exp_pos _).ne',
      Real.log_exp, Real.log_exp]
    ring
  have htarget (c : Fin 3) :
      Real.log (channel c 1 / channel c 0) = ![η, ξ, η + lam] c ∧
      Real.log (channel c 2 / channel c 0) = ![-lam, 0, lam] c := by
    fin_cases c
    · change Real.log ((Real.sqrt 2 / 2 - 1 / 3) / (5 / 12 : ℝ)) = η ∧
        Real.log (mu / (5 / 12 : ℝ)) = -lam
      constructor
      · rfl
      · dsimp [lam]
        rw [Real.log_div hμ.ne' (by norm_num), Real.log_div (by norm_num) hμ.ne']
        ring
    · change Real.log ((5 / 12 : ℝ) / (7 / 24 : ℝ)) = ξ ∧
        Real.log ((7 / 24 : ℝ) / (7 / 24 : ℝ)) = 0
      exact ⟨rfl, by norm_num⟩
    · change Real.log ((Real.sqrt 2 / 2 - 1 / 3) / mu) = η + lam ∧
        Real.log ((5 / 12 : ℝ) / mu) = lam
      constructor
      · dsimp [η, lam]
        rw [Real.log_div hA.ne' hμ.ne', Real.log_div hA.ne' (by norm_num),
          Real.log_div (by norm_num) hμ.ne']
        ring
      · rfl
  have hnormal : ∃ a b : ℝ, a ^ 2 + b ^ 2 = 1 ∧
      a * (u 1 - u 0) + b * (u 2 - u 0) = 0 := by
    by_cases hzero : (u 1 - u 0) ^ 2 + (u 2 - u 0) ^ 2 = 0
    · refine ⟨1, 0, by norm_num, ?_⟩
      nlinarith [sq_nonneg (u 1 - u 0), sq_nonneg (u 2 - u 0)]
    · let r := Real.sqrt ((u 1 - u 0) ^ 2 + (u 2 - u 0) ^ 2)
      have hrpos : 0 < r := Real.sqrt_pos.mpr (lt_of_le_of_ne
        (add_nonneg (sq_nonneg _) (sq_nonneg _)) (Ne.symm hzero))
      have hrsq : r ^ 2 = (u 1 - u 0) ^ 2 + (u 2 - u 0) ^ 2 :=
        Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
      refine ⟨-(u 2 - u 0) / r, (u 1 - u 0) / r, ?_, ?_⟩
      · field_simp [hrpos.ne']
        nlinarith only [hrsq]
      · ring
  obtain ⟨a, b, hunit, horth⟩ := hnormal
  let offset := a * (v 1 - v 0) + b * (v 2 - v 0)
  have hline (x : Input m) :
      a * Real.log (p x 1 / p x 0) + b * Real.log (p x 2 / p x 0) = offset := by
    rw [hlogit, hlogit]
    dsimp [offset]
    linear_combination z x * horth
  obtain ⟨c, hc⟩ := strip_distance η ξ lam δ a b offset hδ hlam.le hmid hunit
  have herror (x : Input m) (hx : teacher x = c) :
      mu ^ 2 * δ ^ 2 / 240 ≤ ∑ i, (p x i - posterior x i) ^ 2 := by
    have hq1 := (htarget c).1
    have hq2 := (htarget c).2
    have hpoint :
        ![a * η - b * lam - offset, a * ξ - offset,
          a * (η + lam) + b * lam - offset] c =
        a * Real.log (channel c 1 / channel c 0) +
          b * Real.log (channel c 2 / channel c 0) - offset := by
      rw [hq1, hq2]
      fin_cases c <;> simp <;> ring
    rw [hpoint] at hc
    let e1 := Real.log (p x 1 / p x 0) - Real.log (channel c 1 / channel c 0)
    let e2 := Real.log (p x 2 / p x 0) - Real.log (channel c 2 / channel c 0)
    have hid : a * Real.log (channel c 1 / channel c 0) +
        b * Real.log (channel c 2 / channel c 0) - offset = -(a * e1 + b * e2) := by
      dsimp [e1, e2]
      linear_combination hline x
    rw [hid, neg_sq] at hc
    have hcs : (a * e1 + b * e2) ^ 2 ≤ e1 ^ 2 + e2 ^ 2 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (![a, b] : Fin 2 → ℝ) (![e1, e2] : Fin 2 → ℝ)
      simpa [Fin.sum_univ_two, hunit] using h
    have hdist : δ ^ 2 / 20 ≤ e1 ^ 2 + e2 ^ 2 := hc.trans hcs
    simpa only [posterior, hx] using
      probability_separation (p x) (channel c) mu δ hμ hδ.le hδlt.le
        (hp x) (hmin c) hdist
  let error := fun x : Input m => ∑ i, (p x i - posterior x i) ^ 2
  have hcard : Fintype.card Window = 5 := by decide
  have mean_eq (f : Input m → ℝ) : mean f = uniformMass m * ∑ x, f x := by
    simp only [mean, Fintype.expect_eq_sum_div_card, Fintype.card_fun, Fintype.card_fin, hcard,
      Nat.cast_pow, Nat.cast_ofNat]
    dsimp [uniformMass]
    ring
  have peel (n : ℕ) (f : (Fin (n + 1) → Window) → ℝ) :
      (∑ x, f x) = ∑ w : Window, ∑ tail : Fin n → Window, f (Fin.cons w tail) := by
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Window)).sum_comp f,
      Fintype.sum_prod_type]
    rfl
  have window_sum (f : Window → ℝ) :
      (∑ w, f w) = f .zero + f .low + f .middle + f .ends + f .high := by
    change (∑ w ∈ ({.zero, .low, .middle, .ends, .high} : Finset Window), f w) = _
    simp
    <;> ring
  have cons_two (n : ℕ) (a b : Window) (f : Fin (n + 1) → Window) :
      (Fin.cons a (Fin.cons b f) : Fin (n + 3) → Window) 2 = f 0 := by
    change Matrix.vecCons a (Matrix.vecCons b f) 2 = f 0
    simpa only [Matrix.head_cons, Matrix.tail_cons, Matrix.vecHead] using
      Matrix.cons_val_two a (Matrix.vecCons b f)
  have hcount : (∑ x : Input m, if teacher x = c then (1 : ℝ) else 0) =
      (5 : ℝ) ^ m * (![89, 20, 16] c) := by
    rw [peel (m + 2)]
    simp_rw [peel (m + 1), peel m]
    simp only [window_sum]
    fin_cases c <;>
      norm_num [teacher, first, last, Fin.cons_zero, Fin.cons_one, cons_two, Fin.cons_succ,
        Finset.sum_const, Fintype.card_fun, hcard, Fin.ext_iff]
    <;> ring
  have hclass : (16 / 125 : ℝ) ≤ mean (fun x : Input m => if teacher x = c then 1 else 0) := by
    rw [mean_eq, hcount, uniformMass, pow_add]
    fin_cases c <;> norm_num
    all_goals field_simp <;> nlinarith [pow_pos (show (0 : ℝ) < 5 by norm_num) m]
  have hmean : kappa ≤ mean error := by
    have hpwise (x : Input m) :
        (mu ^ 2 * δ ^ 2 / 240) * (if teacher x = c then 1 else 0) ≤ error x := by
      by_cases hx : teacher x = c
      · simpa only [hx, ite_true, mul_one, error] using herror x hx
      · simp only [hx, ite_false, mul_zero]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hpwise x)
    have hsumw := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ uniformMass m by dsimp [uniformMass]; positivity)
    have hk0 : 0 ≤ mu ^ 2 * δ ^ 2 / 240 := by positivity
    calc
      kappa = (mu ^ 2 * δ ^ 2 / 240) * (16 / 125) := by dsimp [kappa, δ]; ring
      _ ≤ (mu ^ 2 * δ ^ 2 / 240) *
          mean (fun x : Input m => if teacher x = c then 1 else 0) :=
        mul_le_mul_of_nonneg_left hclass hk0
      _ = uniformMass m * ∑ x : Input m,
          (mu ^ 2 * δ ^ 2 / 240) * (if teacher x = c then 1 else 0) := by
        rw [← Finset.mul_sum]
        rw [mean_eq]
        ring
      _ ≤ mean error := by simpa only [mean_eq] using hsumw
  have hbrier : brierRisk p - brierBayes m = mean error := by
    have point (x : Input m) :
        (∑ j, posterior x j * ∑ i, (p x i - if j = i then 1 else 0) ^ 2) =
        1 - ∑ i, posterior x i ^ 2 + error x := by
      have hmass := (hrows (teacher x)).2
      change (∑ i, posterior x i) = 1 at hmass
      simp only [Fin.sum_univ_three] at hmass
      dsimp [error]
      simp only [Fin.sum_univ_three]
      norm_num [Fin.ext_iff]
      linear_combination (p x 0 ^ 2 + p x 1 ^ 2 + p x 2 ^ 2 + 1) * hmass
    have hrisk : brierRisk p =
        mean (fun x : Input m => 1 - ∑ i, posterior x i ^ 2 + error x) := by
      unfold brierRisk
      rw [mean_eq]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp only [jointMass, mul_assoc, ← Finset.mul_sum]
      rw [point]
    rw [hrisk]
    simp only [mean_eq, brierBayes, Finset.sum_add_distrib, mul_add]
    ring
  have hlog : logRisk p - logBayes m = mean (fun x => klDivergence (posterior x) (p x)) := by
    unfold logRisk logBayes
    simp only [mean_eq, klDivergence, jointMass, mul_assoc, ← Finset.mul_sum]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    simp only [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.log_div (ne_of_gt (show 0 < posterior x i from (hrows (teacher x)).1 i))
      (hp x i).ne']
    ring
  have hkl (x : Input m) : error x ≤ klDivergence (posterior x) (p x) := by
    have hpost := hrows (teacher x)
    have hpk := pinsker_inequality (posterior x) (p x)
      ⟨fun i => (hpost.1 i).le, hpost.2⟩ ⟨fun i => (hp x i).le, hpsum x⟩
      (fun i h => False.elim ((hp x i).ne' h))
    have hmass : ∑ i, (p x i - posterior x i) = 0 := by
      rw [Finset.sum_sub_distrib, hpsum x]
      change 1 - ∑ i, channel (teacher x) i = 0
      rw [hpost.2, sub_self]
    simp only [Fin.sum_univ_three] at hmass
    have hL2 : error x ≤ 2 * totalVariation (posterior x) (p x) ^ 2 := by
      dsimp [error, totalVariation]
      simp only [Fin.sum_univ_three, abs_sub_comm (posterior x 0),
        abs_sub_comm (posterior x 1), abs_sub_comm (posterior x 2)]
      have h01 := mul_nonneg (abs_nonneg (p x 0 - posterior x 0))
        (abs_nonneg (p x 1 - posterior x 1))
      have h02 := mul_nonneg (abs_nonneg (p x 0 - posterior x 0))
        (abs_nonneg (p x 2 - posterior x 2))
      have h12 := mul_nonneg (abs_nonneg (p x 1 - posterior x 1))
        (abs_nonneg (p x 2 - posterior x 2))
      rcases le_total 0 (p x 0 - posterior x 0) with h0 | h0 <;>
        rcases le_total 0 (p x 1 - posterior x 1) with h1 | h1 <;>
        rcases le_total 0 (p x 2 - posterior x 2) with h2 | h2
      all_goals simp only [abs_of_nonneg, abs_of_nonpos, h0, h1, h2] at h01 h02 h12 ⊢
      all_goals nlinarith only [h01, h02, h12,
        congrArg (fun t : ℝ => t ^ 2) hmass]
    exact hL2.trans hpk
  refine ⟨?_, ?_, hconstant, hk⟩
  · rw [hbrier]
    exact hmean
  · rw [hlog]
    exact hmean.trans (by
      rw [mean_eq, mean_eq]
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun x _ => hkl x))
        (show 0 ≤ uniformMass m by dsimp [uniformMass]; positivity))

end D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
