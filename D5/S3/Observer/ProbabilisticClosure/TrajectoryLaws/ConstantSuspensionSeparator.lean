/- GID: D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/TrajectoryLaws/ConstantSuspensionSeparator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Constant suspended emission excludes simultaneous endpoint centers for complete laws. -/

import D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
import Mathlib.MeasureTheory.Measure.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open Finset

namespace D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator

structure StationaryTable (X : Type*) [Fintype X] where
  pi : X → ℝ
  C : X → X → ℝ
  pi_nonneg : ∀ x, 0 ≤ pi x
  pi_sum : ∑ x, pi x = 1
  C_nonneg : ∀ x y, 0 ≤ C x y
  C_sum : ∀ x, ∑ y, C x y = 1
  stationary : ∀ y, ∑ x, pi x * C x y = pi y

namespace StationaryTable

variable {X : Type*} [Fintype X] (T : StationaryTable X)

def mean (f : X → ℝ) : ℝ := ∑ x, T.pi x * f x
def step (f : X → ℝ) (x : X) : ℝ := ∑ y, T.C x y * f y

private lemma step_const (k : ℝ) (x : X) : T.step (fun _ => k) x = k := by
  simp [step, ← Finset.sum_mul, T.C_sum]

private lemma mean_const (k : ℝ) : T.mean (fun _ => k) = k := by
  simp [mean, ← Finset.sum_mul, T.pi_sum]

private lemma mean_step (f : X → ℝ) : T.mean (T.step f) = T.mean f := by
  simp only [mean, step, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, T.stationary]

private lemma step_add (f g : X → ℝ) (x : X) :
    T.step (fun y => f y + g y) x = T.step f x + T.step g x := by
  simp [step, mul_add, Finset.sum_add_distrib]

private lemma step_smul (k : ℝ) (f : X → ℝ) (x : X) :
    T.step (fun y => k * f y) x = k * T.step f x := by
  simp only [step, Finset.mul_sum]
  congr 1
  funext y
  ring

private lemma mean_add (f g : X → ℝ) :
    T.mean (fun y => f y + g y) = T.mean f + T.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

private lemma mean_smul (k : ℝ) (f : X → ℝ) :
    T.mean (fun y => k * f y) = k * T.mean f := by
  simp only [mean, Finset.mul_sum]
  congr 1
  funext y
  ring

def avg4 (f : X → X → X → X → ℝ) : ℝ :=
  T.mean fun i => T.step (fun j => T.step (fun k => T.step (f i j k) k) j) i

private lemma avg4_mono (f g : X → X → X → X → ℝ)
    (h : ∀ i j k l, f i j k l ≤ g i j k l) : T.avg4 f ≤ T.avg4 g := by
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_left _ (T.pi_nonneg i)
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_left _ (T.C_nonneg i j)
  apply Finset.sum_le_sum
  intro k hk
  apply mul_le_mul_of_nonneg_left _ (T.C_nonneg j k)
  apply Finset.sum_le_sum
  intro l hl
  exact mul_le_mul_of_nonneg_left (h i j k l) (T.C_nonneg k l)

private lemma avg4_const (a : ℝ) : T.avg4 (fun _ _ _ _ => a) = a := by
  simp only [avg4, step_const, mean_const]

private lemma avg4_add (f g : X → X → X → X → ℝ) :
    T.avg4 (fun i j k l => f i j k l + g i j k l) = T.avg4 f + T.avg4 g := by
  simp only [avg4, step_add, mean_add]

private lemma avg4_smul (a : ℝ) (f : X → X → X → X → ℝ) :
    T.avg4 (fun i j k l => a * f i j k l) = a * T.avg4 f := by
  simp only [avg4, step_smul, mean_smul]

private lemma avg4_marginals (f : X → ℝ) :
    T.avg4 (fun i _ _ _ => f i) = T.mean f ∧
    T.avg4 (fun _ j _ _ => f j) = T.mean f ∧
    T.avg4 (fun _ _ k _ => f k) = T.mean f ∧
    T.avg4 (fun _ _ _ l => f l) = T.mean f := by
  simp only [avg4, step_const, mean_step, and_self]


private theorem four_box_product_lower_bound (x₀ x₁ x₂ x₃ : ℝ)
    (h₀ : 3 / 5 ≤ x₀ ∧ x₀ ≤ 2 / 3)
    (h₁ : 3 / 5 ≤ x₁ ∧ x₁ ≤ 2 / 3)
    (h₂ : 3 / 5 ≤ x₂ ∧ x₂ ≤ 2 / 3)
    (h₃ : 3 / 5 ≤ x₃ ∧ x₃ ≤ 2 / 3) :
    (4 / 15 : ℝ) * (x₀ + x₁ + x₂ + x₃ - 29 / 15) ≤ x₀ * x₁ * x₂ * x₃ := by
  let y₀ : ℝ := 15 * x₀ - 9
  let y₁ : ℝ := 15 * x₁ - 9
  let y₂ : ℝ := 15 * x₂ - 9
  let y₃ : ℝ := 15 * x₃ - 9
  have hy₀ : 0 ≤ y₀ ∧ y₀ ≤ 1 := by dsimp [y₀]; constructor <;> nlinarith [h₀.1, h₀.2]
  have hy₁ : 0 ≤ y₁ ∧ y₁ ≤ 1 := by dsimp [y₁]; constructor <;> nlinarith [h₁.1, h₁.2]
  have hy₂ : 0 ≤ y₂ ∧ y₂ ≤ 1 := by dsimp [y₂]; constructor <;> nlinarith [h₂.1, h₂.2]
  have hy₃ : 0 ≤ y₃ ∧ y₃ ≤ 1 := by dsimp [y₃]; constructor <;> nlinarith [h₃.1, h₃.2]
  have hpoly :
      x₀ * x₁ * x₂ * x₃ - (4 / 15 : ℝ) *
          (x₀ + x₁ + x₂ + x₃ - 29 / 15) =
        (29 / 5625 : ℝ) * (1 - y₀) * (1 - y₁) * (1 - y₂) * (1 - y₃) +
        (2 / 1125 : ℝ) *
          (y₀ * (1 - y₁) * (1 - y₂) * (1 - y₃) +
            (1 - y₀) * y₁ * (1 - y₂) * (1 - y₃) +
            (1 - y₀) * (1 - y₁) * y₂ * (1 - y₃) +
            (1 - y₀) * (1 - y₁) * (1 - y₂) * y₃) +
        (4 / 2025 : ℝ) * y₀ * y₁ * y₂ * y₃ := by
    dsimp [y₀, y₁, y₂, y₃]
    ring
  apply sub_nonneg.mp
  rw [hpoly]
  have := hy₀.1; have := hy₁.1; have := hy₂.1; have := hy₃.1
  have : 0 ≤ 1-y₀ := by linarith [hy₀.2]
  have : 0 ≤ 1-y₁ := by linarith [hy₁.2]
  have : 0 ≤ 1-y₂ := by linarith [hy₂.2]
  have : 0 ≤ 1-y₃ := by linarith [hy₃.2]
  positivity

private lemma avg4_product_mono (U : X → ℝ)
    (hU : ∀ i, 3 / 5 ≤ U i ∧ U i ≤ 2 / 3) :
    (4 / 15 : ℝ) * (4 * T.mean U - 29 / 15) ≤
      T.avg4 (fun i j k l => U i * U j * U k * U l) := by
  have hp : ∀ i j k l, (4 / 15 : ℝ) *
      (U i + U j + U k + U l - 29 / 15) ≤ U i * U j * U k * U l := by
    intro i j k l
    exact four_box_product_lower_bound _ _ _ _ (hU i) (hU j) (hU k) (hU l)
  have hm := T.avg4_mono _ _ hp
  have he : T.avg4 (fun i j k l => (4 / 15 : ℝ) *
      (U i + U j + U k + U l - 29 / 15)) =
      (4 / 15 : ℝ) * (4 * T.mean U - 29 / 15) := by
    simp only [sub_eq_add_neg, avg4_add, avg4_smul, (T.avg4_marginals U).1,
      (T.avg4_marginals U).2.1, (T.avg4_marginals U).2.2.1,
      (T.avg4_marginals U).2.2.2, avg4_const]
    ring
  rw [← he]
  exact hm

private lemma quadratic_chord (x y : ℝ)
    (hx : 3/5 ≤ x ∧ x ≤ 2/3) (hy : 3/5 ≤ y ∧ y ≤ 2/3) :
    x*y ≤ (19/15)*((x+y)/2) - 2/5 := by
  have h₁ := mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2)
  have h₂ := mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2)
  nlinarith [sq_nonneg (x-y)]

private lemma cubic_chord (x y z : ℝ)
    (hx : 3/5 ≤ x ∧ x ≤ 2/3) (hy : 3/5 ≤ y ∧ y ≤ 2/3)
    (hz : 3/5 ≤ z ∧ z ≤ 2/3) :
    x*y*z ≤ (271/225)*((x+y+z)/3) - 38/75 := by
  have cx := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr hx.2))
    (show 0 ≤ x+3/5+2/3 by linarith)
  have cy := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hy.1) (sub_nonneg.mpr hy.2))
    (show 0 ≤ y+3/5+2/3 by linarith)
  have cz := mul_nonneg
    (mul_nonneg (sub_nonneg.mpr hz.1) (sub_nonneg.mpr hz.2))
    (show 0 ≤ z+3/5+2/3 by linarith)
  have a := mul_nonneg (show 0 ≤ x+y+z by linarith)
    (add_nonneg (add_nonneg (sq_nonneg (x-y)) (sq_nonneg (y-z))) (sq_nonneg (z-x)))
  nlinarith


private lemma avg4_mul_right (f : X → X → X → X → ℝ) (a : ℝ) :
    T.avg4 (fun i j k l => f i j k l * a) = T.avg4 f * a := by
  simpa only [mul_comm] using T.avg4_smul a f

private lemma avg4_div (f : X → X → X → X → ℝ) (a : ℝ) :
    T.avg4 (fun i j k l => f i j k l / a) = T.avg4 f / a := by
  simpa only [div_eq_mul_inv] using T.avg4_mul_right f a⁻¹

private lemma moment_bounds (U : X → ℝ)
    (hU : ∀ i, 3/5 ≤ U i ∧ U i ≤ 2/3) :
    T.avg4 (fun i j _ _ => U i * U j) ≤ (19/15)*T.mean U - 2/5 ∧
    T.avg4 (fun i j k _ => U i * U j * U k) ≤ (271/225)*T.mean U - 38/75 ∧
    (4/15)*(4*T.mean U-29/15) ≤ T.avg4 (fun i j k l => U i*U j*U k*U l) := by
  have h2 := T.avg4_mono _ _ (fun i j k l => quadratic_chord (U i) (U j) (hU i) (hU j))
  have h3 := T.avg4_mono _ _ (fun i j k l => cubic_chord (U i) (U j) (U k) (hU i) (hU j) (hU k))
  have h2e : T.avg4 (fun i j _ _ => (19/15)*((U i+U j)/2)-2/5) =
      (19/15)*T.mean U-2/5 := by
    simp only [sub_eq_add_neg, avg4_add, avg4_smul, avg4_div,
      (T.avg4_marginals U).1, (T.avg4_marginals U).2.1, avg4_const]
    ring
  have h3e : T.avg4 (fun i j k _ => (271/225)*((U i+U j+U k)/3)-38/75) =
      (271/225)*T.mean U-38/75 := by
    simp only [sub_eq_add_neg, avg4_add, avg4_smul, avg4_div,
      (T.avg4_marginals U).1, (T.avg4_marginals U).2.1,
      (T.avg4_marginals U).2.2.1, avg4_const]
    ring
  rw [h2e] at h2
  rw [h3e] at h3
  exact ⟨h2, h3, T.avg4_product_mono U hU⟩


private lemma transition_support (i j : X) (hi : 0 < T.pi i) (hij : T.C i j ≠ 0) :
    0 < T.pi j := by
  rw [← T.stationary j]
  exact (mul_pos hi (lt_of_le_of_ne (T.C_nonneg i j) (Ne.symm hij))).trans_le
    (Finset.single_le_sum (fun z _ => mul_nonneg (T.pi_nonneg z) (T.C_nonneg z j))
      (Finset.mem_univ i))

private lemma step_congr_support (f g : X → ℝ)
    (hfg : ∀ i, 0 < T.pi i → f i = g i) (i : X) (hi : 0 < T.pi i) :
    T.step f i = T.step g i := by
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hC : T.C i j = 0
  · simp [hC]
  · rw [hfg j (T.transition_support i j hi hC)]

private lemma mean_congr_support (f g : X → ℝ)
    (hfg : ∀ i, 0 < T.pi i → f i = g i) : T.mean f = T.mean g := by
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hpi : T.pi i = 0
  · simp [hpi]
  · rw [hfg i (lt_of_le_of_ne (T.pi_nonneg i) (Ne.symm hpi))]

def pathProduct (T : StationaryTable X) (U : X → ℝ) : ℕ → X → ℝ
  | 0 => fun _ => 1
  | n+1 => fun i => U i * T.step (pathProduct T U n) i

private lemma path_moments (U : X → ℝ) :
    T.mean (T.pathProduct U 1) = T.mean U ∧
    T.mean (T.pathProduct U 2) = T.avg4 (fun i j _ _ => U i * U j) ∧
    T.mean (T.pathProduct U 3) = T.avg4 (fun i j k _ => U i * U j * U k) ∧
    T.mean (T.pathProduct U 4) = T.avg4 (fun i j k l => U i * U j * U k * U l) := by
  simp only [pathProduct, avg4, mul_assoc, step_const, step_smul, mul_one,
    and_self]

end StationaryTable

open MeasureTheory
open D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FourthSegmentStoppedLaw
open scoped Classical

def prefixRaw (a : Letter) : RawTail → RawTail := Option.map (List.cons a)

structure RegularTable (X Y : Type*) [Fintype X] [Fintype Y] where
  pi : X → ℝ
  tau : Y → ℝ
  B : X → Y → ℝ
  A : Y → X → ℝ
  u : X → ℝ
  v : Y → ℝ
  pi_nonneg : ∀ x, 0 ≤ pi x
  tau_nonneg : ∀ y, 0 ≤ tau y
  pi_sum : ∑ x, pi x = 1
  tau_sum : ∑ y, tau y = 1
  B_nonneg : ∀ x y, 0 ≤ B x y
  A_nonneg : ∀ y x, 0 ≤ A y x
  B_sum : ∀ x, ∑ y, B x y = 1
  A_sum : ∀ y, ∑ x, A y x = 1
  pi_B : ∀ y, ∑ x, pi x * B x y = tau y
  tau_A : ∀ x, ∑ y, tau y * A y x = pi x
  u_box : ∀ x, 1/3 ≤ u x ∧ u x ≤ 2/5
  v_box : ∀ y, 1/3 ≤ v y ∧ v y ≤ 2/5
  Q : X → Measure RawTail
  W : Y → Measure RawTail
  Qprob : ∀ x, IsProbabilityMeasure (Q x)
  Wprob : ∀ y, IsProbabilityMeasure (W y)
  q_generate : ∀ x (E : Set RawTail),
    (Q x).real E = u x * (if some [0] ∈ E then 1 else 0) +
      (1-u x) * ∑ y, B x y * (W y).real ((prefixRaw 1) ⁻¹' E)
  w_generate : ∀ y (E : Set RawTail),
    (W y).real E = (1-v y) * (if some [1] ∈ E then 1 else 0) +
      v y * ∑ x, A y x * (Q x).real ((prefixRaw 0) ⁻¹' E)

namespace RegularTable
variable {X Y : Type*} [Fintype X] [Fintype Y] (R : RegularTable X Y)

def circulation : StationaryTable X where
  pi := R.pi
  C x z := ∑ y, R.B x y * R.A y z
  pi_nonneg := R.pi_nonneg
  pi_sum := R.pi_sum
  C_nonneg x z := Finset.sum_nonneg (fun y _ => mul_nonneg (R.B_nonneg x y) (R.A_nonneg y z))
  C_sum x := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, R.A_sum, mul_one]
    exact R.B_sum x
  stationary z := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← Finset.sum_mul, R.pi_B]
    exact R.tau_A z

private lemma B_support (x : X) (y : Y) (hx : 0 < R.pi x) (hy : R.B x y ≠ 0) :
    0 < R.tau y := by
  rw [← R.pi_B y]
  exact (mul_pos hx (lt_of_le_of_ne (R.B_nonneg x y) (Ne.symm hy))).trans_le
    (Finset.single_le_sum (fun z _ => mul_nonneg (R.pi_nonneg z) (R.B_nonneg z y))
      (Finset.mem_univ x))

private lemma prefix_singleton (a : Letter) (w : List Letter) :
    (prefixRaw a) ⁻¹' {some (a :: w)} = {some w} := by
  ext r
  cases r <;> simp [prefixRaw]

private lemma prefix_other (a b : Letter) (w : List Letter) (h : a ≠ b) :
    (prefixRaw a) ⁻¹' {some (b :: w)} = ∅ := by
  ext r
  cases r <;> simp [prefixRaw, h]

private lemma w_beta (y : Y) : (R.W y).real {some [1]} = 1-R.v y := by
  rw [R.w_generate]
  rw [prefix_other 0 1 [] (by decide)]
  simp

private lemma w_alpha (y : Y) (w : List Letter) :
    (R.W y).real {some (0 :: w)} = R.v y * ∑ x, R.A y x * (R.Q x).real {some w} := by
  rw [R.w_generate, prefix_singleton]
  simp

private lemma q_marker (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (x : X) (hx : 0 < R.pi x) :
    (R.Q x).real {some (pWord 0 1)} = (1-s)*(1-R.u x) := by
  rw [show pWord 0 1 = [1,1] by rfl, R.q_generate, prefix_singleton]
  simp only [Set.mem_singleton_iff, Option.some.injEq, List.cons.injEq,
    Fin.zero_ne_one, false_and, ↓reduceIte, mul_zero, zero_add]
  simp_rw [R.w_beta]
  have he : ∑ y, R.B x y * (1-R.v y) = 1-s := by
    calc
      _ = ∑ y, R.B x y * (1-s) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hb : R.B x y = 0
        · simp [hb]
        · rw [hs y (R.B_support x y hx hb)]
      _ = _ := by rw [← Finset.sum_mul, R.B_sum]; ring
  rw [he]
  ring

private lemma q_return (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (x : X) (hx : 0 < R.pi x) (w : List Letter) :
    (R.Q x).real {some (1 :: 0 :: w)} =
      s*(1-R.u x) * R.circulation.step (fun z => (R.Q z).real {some w}) x := by
  rw [R.q_generate, prefix_singleton]
  simp only [Set.mem_singleton_iff, Option.some.injEq, List.cons.injEq,
    Fin.zero_ne_one, false_and, ↓reduceIte, mul_zero, zero_add]
  simp_rw [R.w_alpha]
  have he : (∑ y, R.B x y * (R.v y * ∑ z, R.A y z * (R.Q z).real {some w})) =
      s * R.circulation.step (fun z => (R.Q z).real {some w}) x := by
    calc
      _ = ∑ y, R.B x y * (s * ∑ z, R.A y z * (R.Q z).real {some w}) := by
        apply Finset.sum_congr rfl
        intro y hy
        by_cases hb : R.B x y = 0
        · simp [hb]
        · rw [hs y (R.B_support x y hx hb)]
      _ = _ := by
        simp only [StationaryTable.step, circulation, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z hz
        apply Finset.sum_congr rfl
        intro y hy
        ring
  rw [he]
  ring


private lemma q_word (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (j : ℕ) (x : X) (hx : 0 < R.pi x) :
    (R.Q x).real {some (pWord j 1)} =
      ((1-s)*s^j) * R.circulation.pathProduct (fun z => 1-R.u z) (j+1) x := by
  induction j generalizing x with
  | zero =>
      simpa only [pow_zero, mul_one, StationaryTable.pathProduct,
        StationaryTable.step_const] using R.q_marker s hs x hx
  | succ j ih =>
      rw [p_word_succ, R.q_return s hs x hx]
      have he := R.circulation.step_congr_support
        (fun z => (R.Q z).real {some (pWord j 1)})
        (fun z => ((1-s)*s^j) * R.circulation.pathProduct (fun z => 1-R.u z) (j+1) z)
        (fun z hz => ih z hz) x hx
      conv_rhs => rw [StationaryTable.pathProduct]
      rw [he, StationaryTable.step_smul, pow_succ]
      ring

def qMean (E : Set RawTail) : ℝ := ∑ x, R.pi x * (R.Q x).real E
def wMean (E : Set RawTail) : ℝ := ∑ y, R.tau y * (R.W y).real E

private lemma q_mean_word (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (j : ℕ) :
    R.qMean {some (pWord j 1)} =
      ((1-s)*s^j) * R.circulation.mean
        (R.circulation.pathProduct (fun z => 1-R.u z) (j+1)) := by
  change R.circulation.mean (fun x => (R.Q x).real {some (pWord j 1)}) = _
  rw [R.circulation.mean_congr_support _ _ (fun x hx => R.q_word s hs j x hx)]
  exact R.circulation.mean_smul _ _

private lemma w_mean_generate (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (E : Set RawTail) :
    R.wMean E = (1-s)*(if some [1] ∈ E then 1 else 0) +
      s * R.qMean ((prefixRaw 0) ⁻¹' E) := by
  unfold wMean
  simp_rw [R.w_generate]
  calc
    _ = ∑ y, R.tau y * ((1-s)*(if some [1] ∈ E then 1 else 0) +
        s * ∑ x, R.A y x * (R.Q x).real ((prefixRaw 0) ⁻¹' E)) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases ht : R.tau y = 0
      · simp [ht]
      · rw [hs y (lt_of_le_of_ne (R.tau_nonneg y) (Ne.symm ht))]
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, R.tau_sum, one_mul]
      congr 1
      simp only [qMean, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc]
      conv_lhs => arg 2; ext x; arg 2; ext y; rw [mul_comm (R.tau y) s]
      simp only [mul_assoc, ← Finset.mul_sum]
      simp_rw [← mul_assoc, ← Finset.sum_mul, R.tau_A]

def betaEvent : Set RawTail := {some [1], some (0 :: pWord 0 1)}

private lemma beta_event_mean (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s) :
    R.wMean betaEvent = 1-s+s*(1-s)*R.circulation.mean (fun z => 1-R.u z) := by
  rw [R.w_mean_generate s hs]
  have he : (prefixRaw 0) ⁻¹' betaEvent = {some (pWord 0 1)} := by
    ext r
    cases r <;> simp [prefixRaw, betaEvent]
  rw [he, R.q_mean_word s hs 0, (R.circulation.path_moments _).1]
  simp only [betaEvent, Set.mem_insert_iff, true_or, ↓reduceIte, mul_one, pow_zero]
  ring


def pEvent : Finset RawTail :=
  {some (pWord 0 1), some (pWord 1 1), some (pWord 2 1)}

private lemma q_mean_finite (E : Finset RawTail) :
    R.qMean E = ∑ w ∈ E, R.qMean {w} := by
  have he (x : X) : (R.Q x).real E = ∑ w ∈ E, (R.Q x).real {w} := by
    letI := R.Qprob x
    exact (sum_measureReal_singleton E).symm
  simp only [qMean, he, Finset.mul_sum]
  rw [Finset.sum_comm]

private lemma p_event_mean (s : ℝ) (hs : ∀ y, 0 < R.tau y → R.v y = s) :
    R.qMean pEvent = (1-s) *
      (R.circulation.mean (fun z => 1-R.u z) +
        s * R.circulation.avg4 (fun i j _ _ => (1-R.u i)*(1-R.u j)) +
        s^2 * R.circulation.avg4 (fun i j k _ => (1-R.u i)*(1-R.u j)*(1-R.u k))) := by
  have h01 : some (pWord 0 1) ≠ some (pWord 1 1) := by decide
  have h02 : some (pWord 0 1) ≠ some (pWord 2 1) := by decide
  have h12 : some (pWord 1 1) ≠ some (pWord 2 1) := by decide
  rw [R.q_mean_finite]
  simp only [pEvent, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h01, h02, h12, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [R.q_mean_word s hs 0, R.q_mean_word s hs 1, R.q_mean_word s hs 2]
  rw [(R.circulation.path_moments _).1, (R.circulation.path_moments _).2.1,
    (R.circulation.path_moments _).2.2.1]
  ring

private lemma same_law_estimates (s : ℝ) (hbox : 1/3 ≤ s ∧ s ≤ 2/5)
    (hs : ∀ y, 0 < R.tau y → R.v y = s) :
    s * R.qMean pEvent ≤
      (1+(19/15)*s+(271/225)*s^2) * (R.wMean betaEvent-1+s) -
        (2/5)*s^2*(1-s)*(1+(19/15)*s) ∧
    (4/15)*s^2*(4*(R.wMean betaEvent-1+s)-s*(1-s)*(29/15)) ≤
      R.qMean {some (pWord 3 1)} := by
  have hU : ∀ x, 3/5 ≤ 1-R.u x ∧ 1-R.u x ≤ 2/3 := by
    intro x
    constructor <;> linarith [(R.u_box x).1, (R.u_box x).2]
  obtain ⟨h2,h3,h4⟩ := R.circulation.moment_bounds (fun x => 1-R.u x) hU
  have hs0 : 0 ≤ s := by linarith [hbox.1]
  have h1s : 0 ≤ 1-s := by linarith [hbox.2]
  have h2s := mul_le_mul_of_nonneg_left h2 (mul_nonneg hs0 (mul_nonneg h1s hs0))
  have h3s := mul_le_mul_of_nonneg_left h3 (mul_nonneg hs0 (mul_nonneg h1s (sq_nonneg s)))
  have h4s := mul_le_mul_of_nonneg_left h4 (mul_nonneg h1s (pow_nonneg hs0 3))
  rw [R.p_event_mean s hs, R.beta_event_mean s hs, R.q_mean_word s hs 3,
    (R.circulation.path_moments _).2.2.2]
  constructor <;> nlinarith

end RegularTable


def responseF (s : ℝ) : ℝ :=
  (1-(1489/6750)/s)*(1+(19/15)*s+(271/225)*s^2)-
    (2/5)*s*(1-s)*(1+(19/15)*s)

def responseG (s : ℝ) : ℝ :=
  (4/15)*((31/15)*s^3+(29/15)*s^4-4*(1489/6750)*s^2)

private lemma responseF_mul (s : ℝ) (hs : s ≠ 0) :
    s*responseF s =
      (1+(19/15)*s+(271/225)*s^2)*(s-1489/6750) -
        (2/5)*s^2*(1-s)*(1+(19/15)*s) := by
  unfold responseF
  field_simp
  all_goals ring

private lemma responseF_expand (s : ℝ) (hs : s ≠ 0) :
    responseF s = 1-(19/15)*(1489/6750)-(1489/6750)/s +
      (13/15-(271/225)*(1489/6750))*s+(247/225)*s^2+(38/75)*s^3 := by
  unfold responseF
  field_simp
  all_goals ring

private lemma responseF_mono {x y : ℝ} (hx : 1/3 ≤ x) (hxy : x ≤ y) :
    responseF x ≤ responseF y := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := hx0.trans_le hxy
  rw [responseF_expand x hx0.ne', responseF_expand y hy0.ne']
  have hdiv := div_le_div_of_nonneg_left (show (0:ℝ) ≤ 1489/6750 by norm_num) hx0 hxy
  have h2 : x^2 ≤ y^2 := pow_le_pow_left₀ hx0.le hxy 2
  have h3 : x^3 ≤ y^3 := pow_le_pow_left₀ hx0.le hxy 3
  nlinarith

private lemma responseG_factor (s : ℝ) :
    responseG s = (4/15)*s^2*((31/15)*s+(29/15)*s^2-4*(1489/6750)) := by
  unfold responseG
  ring

private lemma responseG_mono {x y : ℝ} (hx : 1/3 ≤ x) (hxy : x ≤ y) :
    responseG x ≤ responseG y := by
  have hx0 : 0 ≤ x := by linarith
  have h2 : x^2 ≤ y^2 := pow_le_pow_left₀ hx0 hxy 2
  have hl : (1/3:ℝ)^2 ≤ x^2 := pow_le_pow_left₀ (by norm_num) hx 2
  have hpos : 0 ≤ (31/15)*x+(29/15)*x^2-4*(1489/6750) := by nlinarith
  have hinc : (31/15)*x+(29/15)*x^2-4*(1489/6750) ≤
      (31/15)*y+(29/15)*y^2-4*(1489/6750) := by nlinarith
  rw [responseG_factor, responseG_factor]
  exact mul_le_mul (by nlinarith) hinc hpos (by positivity)

private lemma scalar_cut (s ep eb : ℝ) (hs : 1/3 ≤ s ∧ s ≤ 2/5)
    (hF : 11758471/22781250-responseF s ≤ ep+5*eb)
    (hG : responseG s-1944/390625 ≤ 2*ep+eb/5) :
    1/35200 < max ep eb := by
  have hFcut : (1/4000:ℝ) < 11758471/22781250-responseF (3679/10000) := by
    norm_num [responseF]
  have hGcut : (1/16000:ℝ) < responseG (3679/10000)-1944/390625 := by
    norm_num [responseG]
  have hp := le_max_left ep eb
  have hb := le_max_right ep eb
  by_cases hc : s ≤ 3679/10000
  · have hm := responseF_mono hs.1 hc
    linarith
  · have hm := responseG_mono (show (1/3:ℝ) ≤ 3679/10000 by norm_num) (le_of_not_ge hc)
    linarith



namespace RegularTable
variable {X Y : Type*} [Fintype X] [Fintype Y] (R : RegularTable X Y)

private lemma response_constraints (s ep eb : ℝ)
    (hbox : 1/3 ≤ s ∧ s ≤ 2/5)
    (hs : ∀ y, 0 < R.tau y → R.v y = s) (heb : 0 ≤ eb)
    (hEp : 11758471/22781250-ep ≤ R.qMean pEvent)
    (hEb : |R.wMean betaEvent-5261/6750| ≤ eb)
    (hZ : R.qMean {some (pWord 3 1)} ≤ 1944/390625+2*ep) :
    11758471/22781250-responseF s ≤ ep+5*eb ∧
    responseG s-1944/390625 ≤ 2*ep+eb/5 := by
  obtain ⟨hupper,hlower⟩ := R.same_law_estimates s hbox hs
  have hs0 : 0 < s := by linarith [hbox.1]
  have ht0 : 0 ≤ 1+(19/15)*s+(271/225)*s^2 := by positivity
  have ht5 : 1+(19/15)*s+(271/225)*s^2 ≤ 5*s := by
    have hb := mul_nonneg hs0.le (show 0 ≤ 2/5-s by linarith [hbox.2])
    nlinarith [hbox.1]
  have htbound := mul_le_mul_of_nonneg_right ht5 heb
  have hd := abs_le.mp hEb
  have hderr := mul_le_mul_of_nonneg_left hd.2 ht0
  have hq := mul_le_mul_of_nonneg_left hEp hs0.le
  have hF := responseF_mul s hs0.ne'
  have hfirst : 11758471/22781250-responseF s ≤ ep+5*eb := by
    apply (mul_le_mul_iff_right₀ hs0).mp
    nlinarith
  have hk : (16/15)*s^2 ≤ (1/5:ℝ) := by
    have hh := pow_le_pow_left₀ hs0.le hbox.2 2
    nlinarith
  have hkb := mul_le_mul_of_nonneg_right hk heb
  have hdlower := mul_le_mul_of_nonneg_left hd.1 (show 0 ≤ (16/15)*s^2 by positivity)
  have hG : responseG s = (4/15)*s^2*(4*(s-1489/6750)-s*(1-s)*(29/15)) := by
    unfold responseG
    ring
  refine ⟨hfirst, ?_⟩
  rw [hG]
  nlinarith

end RegularTable



def endpointA : unitInterval := ⟨1/3, by norm_num⟩
def endpointB : unitInterval := ⟨2/5, by norm_num⟩

lemma endpoint_probability (phase : ActivePhase) (r : unitInterval) :
    IsProbabilityMeasure (explicitStoppedWordLaw phase r) := by
  rw [← (actual_fourth_segment_stopped_word_law r phase).2]
  exact Measure.isProbabilityMeasure_map
    (measurable_stopped_read_word phase).aemeasurable

private lemma endpoint_p_word (r : unitInterval) (j : ℕ) :
    (explicitStoppedWordLaw .p r).real {some (pWord j 1)} =
      (1-(r:ℝ))^2*((r:ℝ)*(1-r))^j := by
  rw [Measure.real, explicit_finite_mass, if_pos (show ∃ b, WordFamily .p b (pWord j 1) from ⟨1,j,rfl⟩), p_word_mass]
  simp [alphaMass, betaMass, ENNReal.toReal_mul, ENNReal.toReal_pow, unitInterval.coe_symm_eq]

lemma endpoint_p_event (r : unitInterval) :
    (explicitStoppedWordLaw .p r).real RegularTable.pEvent =
      (1-(r:ℝ))^2*(1+(r:ℝ)*(1-r)+((r:ℝ)*(1-r))^2) := by
  haveI := endpoint_probability .p r
  rw [← sum_measureReal_singleton]
  have h01 : some (pWord 0 1) ≠ some (pWord 1 1) := by decide
  have h02 : some (pWord 0 1) ≠ some (pWord 2 1) := by decide
  have h12 : some (pWord 1 1) ≠ some (pWord 2 1) := by decide
  simp only [RegularTable.pEvent, Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    h01, h02, h12, or_self, not_false_eq_true, Finset.sum_singleton]
  rw [endpoint_p_word, endpoint_p_word, endpoint_p_word]
  ring

lemma endpoint_beta_event (r : unitInterval) :
    (explicitStoppedWordLaw .beta r).real RegularTable.betaEvent =
      1-(r:ℝ)+(r:ℝ)*(1-r)^2 := by
  haveI := endpoint_probability .beta r
  have he : RegularTable.betaEvent =
      (↑({some [1], some (0::pWord 0 1)} : Finset RawTail) : Set RawTail) := by
    ext w
    simp [RegularTable.betaEvent]
  rw [he, ← sum_measureReal_singleton]
  have h : (some [1] : RawTail) ≠ some (0::pWord 0 1) := by decide
  simp only [Finset.sum_insert, Finset.mem_singleton, h, not_false_eq_true, Finset.sum_singleton]
  have hf : ∃ b, WordFamily .beta b [1] := ⟨1, Or.inl ⟨rfl,rfl⟩⟩
  have hg : ∃ b, WordFamily .beta b (0::pWord 0 1) := ⟨1, Or.inr ⟨0,rfl⟩⟩
  simp only [Measure.real, explicit_finite_mass, if_pos hf, if_pos hg]
  norm_num [wordMass, pWord, loopWord, ProbabilityTheory.bernoulliMeasure,
    ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_pow,
    unitInterval.coe_symm_eq, pow_two]

private def extendedPEvent : Finset RawTail := insert (some (pWord 3 1)) RegularTable.pEvent

private lemma endpoint_p_extended (r : unitInterval) :
    (explicitStoppedWordLaw .p r).real extendedPEvent =
      (explicitStoppedWordLaw .p r).real RegularTable.pEvent +
        (1-(r:ℝ))^2*((r:ℝ)*(1-r))^3 := by
  haveI := endpoint_probability .p r
  rw [← sum_measureReal_singleton]
  have hz : some (pWord 3 1) ∉ RegularTable.pEvent := by decide
  rw [extendedPEvent, Finset.sum_insert hz, sum_measureReal_singleton, endpoint_p_word]
  ring

namespace RegularTable
variable {X Y : Type*} [Fintype X] [Fintype Y] (R : RegularTable X Y)

private lemma q_mean_extended :
    R.qMean extendedPEvent = R.qMean pEvent + R.qMean {some (pWord 3 1)} := by
  rw [R.q_mean_finite]
  have hz : some (pWord 3 1) ∉ pEvent := by decide
  rw [extendedPEvent, Finset.sum_insert hz, ← R.q_mean_finite]
  ring

end RegularTable


def FullTVBound (mean : Set RawTail → ℝ) (law : Measure RawTail) (radius : ℝ) : Prop :=
  ∀ E : Set RawTail, |mean E-law.real E| ≤ radius

namespace RegularTable
variable {X Y : Type*} [Fintype X] [Fintype Y] (R : RegularTable X Y)

theorem constant_suspension_separator (s ep eb : ℝ)
    (hbox : 1/3 ≤ s ∧ s ≤ 2/5)
    (hs : ∀ y, 0 < R.tau y → R.v y = s)
    (_hep : 0 ≤ ep) (heb : 0 ≤ eb)
    (hQ : ∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.qMean (explicitStoppedWordLaw .p r) (1116529/22781250+ep))
    (hW : ∀ r : unitInterval, (r:ℝ) = 1/3 ∨ (r:ℝ) = 2/5 →
      FullTVBound R.wMean (explicitStoppedWordLaw .beta r) (239/6750+eb)) :
    1/35200 < max ep eb := by
  have hqa := hQ endpointA (Or.inl rfl) pEvent
  have hqb := hQ endpointB (Or.inr rfl) extendedPEvent
  have hwa := hW endpointA (Or.inl rfl) betaEvent
  have hwb := hW endpointB (Or.inr rfl) betaEvent
  rw [endpoint_p_event] at hqa
  rw [endpoint_p_extended, endpoint_p_event, R.q_mean_extended] at hqb
  rw [endpoint_beta_event] at hwa hwb
  norm_num [endpointA, endpointB] at hqa hqb hwa hwb
  have hlow : 11758471/22781250-ep ≤ R.qMean pEvent := by
    have := (abs_le.mp hqa).1
    linarith
  have hbeta : |R.wMean betaEvent-5261/6750| ≤ eb := by
    obtain ⟨hla,hua⟩ := abs_le.mp hwa
    obtain ⟨hlb,hub⟩ := abs_le.mp hwb
    apply abs_le.mpr
    constructor <;> linarith
  have hword : R.qMean {some (pWord 3 1)} ≤ 1944/390625+2*ep := by
    have := (abs_le.mp hqb).2
    linarith
  obtain ⟨hF,hG⟩ := R.response_constraints s ep eb hbox hs heb hlow hbeta hword
  exact scalar_cut s ep eb hbox hF hG

end RegularTable

end D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.ConstantSuspensionSeparator
