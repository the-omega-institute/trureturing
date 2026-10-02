/- GID: D5/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/GarbledPosteriorRootGap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A scalar root with an unrestricted affine softmax head has a uniform positive proper-risk gap for the garbled three-class window teacher. -/

import D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
import D5.S3.TotalVariation.Pinsker

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap

open LiteralWindowEnd
open D5.S3.Divergence.ClassicalDPI
open D5.S3.TotalVariation.Pinsker
open scoped BigOperators

/-- Independent whole windows, including every tail word. -/
abbrev Input (m : ℕ) := Fin (m + 3) → Window

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

def mean {m : ℕ} (f : Input m → ℝ) : ℝ := uniformMass m * ∑ x, f x

/-- Every scalar root is allowed. A zero-dimensional root embeds by z = 0;
there is no restriction on trees, peaks, encodings, or internal parameters. -/
def softmax {m : ℕ} (z : Input m → ℝ) (u v : Fin 3 → ℝ)
    (x : Input m) (i : Fin 3) : ℝ :=
  Real.exp (u i * z x + v i) / ∑ j, Real.exp (u j * z x + v j)

def brierRisk {m : ℕ} (p : Input m → Fin 3 → ℝ) : ℝ :=
  ∑ x, ∑ j, jointMass x j * ∑ i, (p x i - if j = i then 1 else 0) ^ 2

def brierBayes (m : ℕ) : ℝ := mean (m := m) (fun x => 1 - ∑ i, posterior x i ^ 2)

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
  refine ⟨?_, ?_, hconstant, hk⟩
  · sorry
  · sorry

#print axioms probability_separation
#print axioms strip_distance
#print axioms result

end D5.S3.Arith.FibonacciAtomic.GarbledPosteriorRootGap
