/- GID: D5/S3/Observer/ProbabilisticClosure/ParityMarkedMoment
   generality: G
   mirror-B: D5/B/S3/Observer/ProbabilisticClosure/ParityMarkedMoment
   mirror-E: none(waiver:unbounded-complex-moment-estimate)
   anchors: [mathlib/module/Mathlib.Analysis.Complex.Exponential]
   utility: none
   digest: Actual parity pair and path moments have uniform quadratic normalized error. -/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.LinearCombination

open scoped BigOperators

namespace D5.S3.Observer.ProbabilisticClosure.ParityMarkedMoment

/-- Uniform second-order normalized moments of the actual stationary pair and
consecutive-path experiments. A true Boolean selects reversal or a path, respectively. -/
theorem uniform_marked_moment_bound
    {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (χ b : X → ℝ) (u v : X → ℂ)
    (hχ : ∀ x, χ x = 1 ∨ χ x = -1)
    (hχsum : ∑ x : X, χ x = 0) (hbsum : ∑ x : X, b x = 0)
    (hb : ∀ x, |b x| ≤ 1)
    (hsupport : ∀ x, χ x = -1 → b x = 0 ∧ u x = 0 ∧ v x = 0) :
    let n : ℕ := Fintype.card X
    let K : Bool → X → X → ℝ := fun reverse x y =>
      if reverse then (1 + b y * χ x) / (n : ℝ)
      else (1 + b x * χ y) / (n : ℝ)
    let w : X → X → ℂ := fun x y => 1 + u x + v x * (χ y : ℂ)
    let mean : Bool → ℂ := fun reverse =>
      if reverse then (∑ x : X, u x) / (n : ℂ)
      else (∑ x : X, (u x + (b x : ℂ) * v x)) / (n : ℂ)
    let δ : ℝ := (∑ x : X, (‖u x‖ + ‖v x‖)) / (n : ℝ)
    δ ≤ 1 / 64 → ∀ (reverse path : Bool) (s : ℕ),
      ‖(if path then
          (n : ℂ)⁻¹ * ∑ p : Fin (s + 1) → X,
            ∏ t : Fin s, ((K reverse (p t.castSucc) (p t.succ) : ℂ) *
              w (p t.castSucc) (p t.succ))
        else ∑ p : Fin s → X × X,
          ∏ t : Fin s, (((K reverse (p t).1 (p t).2 : ℂ) / (n : ℂ)) *
            w (p t).1 (p t).2)) * Complex.exp (-(s : ℂ) * mean reverse) - 1‖ ≤
        64 * (s : ℝ) * δ ^ 2 * Real.exp (64 * (s : ℝ) * δ ^ 2) := by
  classical
  intro n K w mean δ hsmall
  have hn : n ≠ 0 := Fintype.card_ne_zero
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hδ : 0 ≤ δ := div_nonneg (Finset.sum_nonneg (by intro x _; positivity)) hnR.le
  let H : ℝ := 1 + 22 * δ ^ 2
  have hH : 1 ≤ H := by dsimp [H]; nlinarith [sq_nonneg δ]
  have hH0 : 0 ≤ H := le_trans zero_le_one hH
  have hexp : Real.exp δ ≤ 64 / 63 := by
    calc
      Real.exp δ ≤ Real.exp (1 / 64) := Real.exp_le_exp.mpr hsmall
      _ ≤ 1 / (1 - (1 / 64 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 64 / 63 := by norm_num
  have scalar (a : ℂ) (ha : ‖a‖ ≤ δ) :
      ‖Complex.exp (-a)‖ ≤ 64 / 63 ∧
      ‖Complex.exp (-a) * (1 + a) - 1‖ ≤ 2 * δ ^ 2 := by
    have hq : ‖Complex.exp (-a)‖ ≤ 64 / 63 := by
      calc
        _ ≤ Real.exp ‖-a‖ := Complex.norm_exp_le_exp_norm _
        _ ≤ Real.exp δ := by rw [norm_neg]; exact Real.exp_le_exp.mpr ha
        _ ≤ _ := hexp
    refine ⟨hq, ?_⟩
    have ht := Complex.norm_exp_sub_one_sub_id_le (ha.trans (by linarith : δ ≤ 1))
    have hid : Complex.exp (-a) * (1 + a) - 1 =
        -(Complex.exp (-a) * (Complex.exp a - 1 - a)) := by
      have he : Complex.exp (-a) * Complex.exp a = 1 := by
        rw [← Complex.exp_add]; simp
      linear_combination he
    rw [hid, norm_neg, norm_mul]
    calc
      _ ≤ (64 / 63) * ‖a‖ ^ 2 := mul_le_mul hq ht (norm_nonneg _) (by norm_num)
      _ ≤ (64 / 63) * δ ^ 2 := by gcongr
      _ ≤ 2 * δ ^ 2 := by nlinarith [sq_nonneg δ]
  have coupled (x : ℕ → ℂ) (Y : ℕ → ℝ)
      (hx : x 0 = 1) (hy : Y 0 = 0)
      (hstep : ∀ t, ‖x (t + 1) - x t‖ ≤ 2 * δ ^ 2 * ‖x t‖ + 2 * δ * Y t)
      (htail : ∀ t, Y (t + 1) ≤ 5 * δ * ‖x t‖ + (1 / 2) * Y t) :
      ∀ t, ‖x t‖ ≤ H ^ t ∧ Y t ≤ 10 * δ * H ^ t ∧
        ‖x t - 1‖ ≤ 22 * (t : ℝ) * δ ^ 2 * H ^ t := by
    intro t
    induction t with
    | zero => simp [hx, hy, hδ]
    | succ t ih =>
      have hp : 0 ≤ H ^ t := pow_nonneg hH0 _
      have hmono : H ^ t ≤ H ^ (t + 1) := by
        simpa only [pow_succ, mul_one] using mul_le_mul_of_nonneg_left hH hp
      have hs : ‖x (t + 1) - x t‖ ≤ 22 * δ ^ 2 * H ^ t := by
        calc
          _ ≤ 2 * δ ^ 2 * ‖x t‖ + 2 * δ * Y t := hstep t
          _ ≤ 2 * δ ^ 2 * H ^ t + 2 * δ * (10 * δ * H ^ t) :=
            add_le_add (mul_le_mul_of_nonneg_left ih.1 (by positivity))
              (mul_le_mul_of_nonneg_left ih.2.1 (by positivity))
          _ = _ := by ring
      refine ⟨?_, ?_, ?_⟩
      · calc
          ‖x (t + 1)‖ ≤ ‖x (t + 1) - x t‖ + ‖x t‖ := norm_le_norm_sub_add _ _
          _ ≤ 22 * δ ^ 2 * H ^ t + H ^ t := add_le_add hs ih.1
          _ = H ^ (t + 1) := by rw [pow_succ]; dsimp [H]; ring
      · calc
          Y (t + 1) ≤ 5 * δ * ‖x t‖ + (1 / 2) * Y t := htail t
          _ ≤ 5 * δ * H ^ t + (1 / 2) * (10 * δ * H ^ t) :=
            add_le_add (mul_le_mul_of_nonneg_left ih.1 (by positivity))
              (mul_le_mul_of_nonneg_left ih.2.1 (by norm_num))
          _ = 10 * δ * H ^ t := by ring
          _ ≤ 10 * δ * H ^ (t + 1) := mul_le_mul_of_nonneg_left hmono (by positivity)
      · calc
          ‖x (t + 1) - 1‖ ≤ ‖x (t + 1) - x t‖ + ‖x t - 1‖ := by
            simpa only [sub_add_sub_cancel] using
              norm_add_le (x (t + 1) - x t) (x t - 1)
          _ ≤ 22 * δ ^ 2 * H ^ t + 22 * (t : ℝ) * δ ^ 2 * H ^ t :=
            add_le_add hs ih.2.2
          _ = 22 * ((t + 1 : ℕ) : ℝ) * δ ^ 2 * H ^ t := by push_cast; ring
          _ ≤ 22 * ((t + 1 : ℕ) : ℝ) * δ ^ 2 * H ^ (t + 1) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
  have envelope (t : ℕ) :
      22 * (t : ℝ) * δ ^ 2 * H ^ t ≤
        64 * (t : ℝ) * δ ^ 2 * Real.exp (64 * (t : ℝ) * δ ^ 2) := by
    have hpow : H ^ t ≤ Real.exp (22 * (t : ℝ) * δ ^ 2) := by
      calc
        H ^ t ≤ (Real.exp (22 * δ ^ 2)) ^ t := by
          apply pow_le_pow_left₀ hH0
          simpa [H, add_comm] using Real.add_one_le_exp (22 * δ ^ 2)
        _ = Real.exp (22 * (t : ℝ) * δ ^ 2) := by
          rw [← Real.exp_nat_mul]; congr 1; ring
    apply le_trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    apply mul_le_mul
    · nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (sq_nonneg δ)]
    · apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) t) (sq_nonneg δ)]
    · positivity
    · positivity
  have transfer (a g d e : ℂ)
      (ha : ‖a‖ ≤ δ) (hg : ‖g‖ ≤ δ) (hd : ‖d‖ ≤ δ) (he : ‖e‖ ≤ δ)
      (x y z : ℕ → ℂ) (hx : x 0 = 1) (hy : y 0 = 0) (hz : z 0 = 0)
      (hrx : ∀ t, x (t + 1) = (1 + a) * x t + g * y t + (a + g) * z t)
      (hry : ∀ t, y (t + 1) = a * x t + g * y t + (1 + a + g) * z t)
      (hrz : ∀ t, z (t + 1) = d * x t + e * y t + (d + e) * z t) :
      ∀ t, ‖x t * Complex.exp (-(t : ℂ) * a) - 1‖ ≤
        64 * (t : ℝ) * δ ^ 2 * Real.exp (64 * (t : ℝ) * δ ^ 2) := by
    let q := Complex.exp (-a)
    let X := fun t => q ^ t * x t
    let Y := fun t => q ^ t * y t
    let Z := fun t => q ^ t * z t
    let W := fun t => max ‖Y t‖ (4 * ‖Z t‖)
    obtain ⟨hq, hqa⟩ := scalar a ha
    have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
    have hxrec (t : ℕ) : X (t + 1) - X t =
        (q * (1 + a) - 1) * X t + q * (g * Y t + (a + g) * Z t) := by
      dsimp [X, Y, Z]; rw [hrx, pow_succ]; ring
    have hyrec (t : ℕ) : Y (t + 1) =
        q * (a * X t + g * Y t + (1 + a + g) * Z t) := by
      dsimp [X, Y, Z]; rw [hry, pow_succ]; ring
    have hzrec (t : ℕ) : Z (t + 1) =
        q * (d * X t + e * Y t + (d + e) * Z t) := by
      dsimp [X, Y, Z]; rw [hrz, pow_succ]; ring
    have hW0 (t : ℕ) : 0 ≤ W t := le_trans (norm_nonneg _) (le_max_left _ _)
    have hYW (t : ℕ) : ‖Y t‖ ≤ W t := le_max_left _ _
    have hZW (t : ℕ) : ‖Z t‖ ≤ W t / 4 := by
      have := le_max_right ‖Y t‖ (4 * ‖Z t‖); dsimp [W]; linarith
    have hag : ‖a + g‖ ≤ 2 * δ := (norm_add_le _ _).trans (by linarith)
    have hde : ‖d + e‖ ≤ 2 * δ := (norm_add_le _ _).trans (by linarith)
    have h1ag : ‖1 + a + g‖ ≤ 1 + 2 * δ := by
      calc
        _ ≤ ‖1 + a‖ + ‖g‖ := norm_add_le _ _
        _ ≤ ‖(1 : ℂ)‖ + ‖a‖ + ‖g‖ := add_le_add (norm_add_le _ _) le_rfl
        _ ≤ _ := by rw [norm_one]; linarith
    have hstep (t : ℕ) : ‖X (t + 1) - X t‖ ≤
        2 * δ ^ 2 * ‖X t‖ + 2 * δ * W t := by
      rw [hxrec]
      calc
        _ ≤ ‖(q * (1 + a) - 1) * X t‖ + ‖q * (g * Y t + (a + g) * Z t)‖ :=
          norm_add_le _ _
        _ ≤ 2 * δ ^ 2 * ‖X t‖ + ‖q‖ * (‖g‖ * ‖Y t‖ + ‖a + g‖ * ‖Z t‖) := by
          simp only [norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right hqa (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (by
              simpa only [norm_mul] using norm_add_le (g * Y t) ((a + g) * Z t)) hq0)
        _ ≤ 2 * δ ^ 2 * ‖X t‖ + (64 / 63) * (δ * W t + 2 * δ * (W t / 4)) := by
          gcongr <;> first | exact hYW t | exact hZW t
        _ ≤ _ := by nlinarith [mul_nonneg hδ (hW0 t)]
    have htail (t : ℕ) : W (t + 1) ≤ 5 * δ * ‖X t‖ + (1 / 2) * W t := by
      apply max_le
      · rw [hyrec, norm_mul]
        have hn : ‖a * X t + g * Y t + (1 + a + g) * Z t‖ ≤
            ‖a‖ * ‖X t‖ + ‖g‖ * ‖Y t‖ + ‖1 + a + g‖ * ‖Z t‖ := by
          calc
            _ ≤ ‖a * X t + g * Y t‖ + ‖(1 + a + g) * Z t‖ := norm_add_le _ _
            _ ≤ _ := by simpa only [norm_mul] using
              (add_le_add (norm_add_le (a * X t) (g * Y t)) (le_refl ‖(1 + a + g) * Z t‖))
        calc
          _ ≤ (64 / 63) * (δ * ‖X t‖ + δ * W t + (1 + 2 * δ) * (W t / 4)) := by
            apply mul_le_mul hq (hn.trans ?_) (norm_nonneg _) (by norm_num)
            gcongr <;> first | exact hYW t | exact hZW t
          _ ≤ _ := by
            nlinarith [hW0 t, mul_nonneg hδ (norm_nonneg (X t)),
              mul_le_mul_of_nonneg_right hsmall (hW0 t)]
      · rw [hzrec, norm_mul]
        have hn : ‖d * X t + e * Y t + (d + e) * Z t‖ ≤
            ‖d‖ * ‖X t‖ + ‖e‖ * ‖Y t‖ + ‖d + e‖ * ‖Z t‖ := by
          calc
            _ ≤ ‖d * X t + e * Y t‖ + ‖(d + e) * Z t‖ := norm_add_le _ _
            _ ≤ _ := by simpa only [norm_mul] using
              (add_le_add (norm_add_le (d * X t) (e * Y t)) (le_refl ‖(d + e) * Z t‖))
        calc
          _ ≤ 4 * ((64 / 63) * (δ * ‖X t‖ + δ * W t + 2 * δ * (W t / 4))) := by
            apply mul_le_mul_of_nonneg_left ?_ (by norm_num)
            apply mul_le_mul hq (hn.trans ?_) (norm_nonneg _) (by norm_num)
            gcongr <;> first | exact hYW t | exact hZW t
          _ ≤ _ := by
            nlinarith [hW0 t, mul_nonneg hδ (norm_nonneg (X t)),
              mul_le_mul_of_nonneg_right hsmall (hW0 t)]
    have hc := coupled X W (by simp [X, hx]) (by simp [W, Y, Z, hy, hz]) hstep htail
    intro t
    have hid : x t * Complex.exp (-(t : ℂ) * a) = X t := by
      dsimp [X, q]
      rw [show -(t : ℂ) * a = (t : ℂ) * (-a) by ring, Complex.exp_nat_mul]
      ring
    rw [hid]
    exact (hc t).2.2.trans (envelope t)
  let av : (X → ℂ) → ℂ := fun f => (∑ x : X, f x) / (n : ℂ)
  have av_add (f g : X → ℂ) : av (fun x => f x + g x) = av f + av g := by
    simp only [av, Finset.sum_add_distrib, add_div]
  have av_one : av (fun _ => 1) = 1 := by simp [av, n, hn]
  have av_chi : av (fun x => (χ x : ℂ)) = 0 := by
    dsimp [av]
    rw [← Complex.ofReal_sum, hχsum, Complex.ofReal_zero, zero_div]
  have av_b : av (fun x => (b x : ℂ)) = 0 := by
    dsimp [av]
    rw [← Complex.ofReal_sum, hbsum, Complex.ofReal_zero, zero_div]
  have sup_chi (x : X) :
      (χ x : ℂ) * u x = u x ∧ (χ x : ℂ) * v x = v x ∧
      (χ x : ℂ) * (b x : ℂ) = (b x : ℂ) := by
    rcases hχ x with hp | hm
    · simp [hp]
    · obtain ⟨hb0, hu0, hv0⟩ := hsupport x hm
      simp [hb0, hu0, hv0]
  have chi_sq (x : X) : (χ x : ℂ) * (χ x : ℂ) = 1 := by
    rcases hχ x with hp | hp <;> simp [hp]
  have av_norm (f : X → ℂ) : ‖av f‖ ≤ (∑ x : X, ‖f x‖) / (n : ℝ) := by
    change ‖(∑ x : X, f x) / (n : ℂ)‖ ≤ _
    rw [norm_div, Complex.norm_natCast]
    exact div_le_div_of_nonneg_right (norm_sum_le _ _) hnR.le
  have hbnorm (x : X) : ‖(b x : ℂ)‖ ≤ 1 := by simpa using hb x
  have av_dom (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ ‖u x‖ + ‖v x‖) : ‖av f‖ ≤ δ := by
    exact (av_norm f).trans (div_le_div_of_nonneg_right
      (Finset.sum_le_sum fun x _ => hf x) hnR.le)
  let Af := av (fun x => u x + (b x : ℂ) * v x)
  let B := av (fun x => v x + (b x : ℂ) * u x)
  let A := av u
  let G := av v
  let D := av (fun x => (b x : ℂ) * u x)
  let E := av (fun x => (b x : ℂ) * v x)
  have hAf : ‖Af‖ ≤ δ := av_dom _ (by
    intro x
    calc
      _ ≤ ‖u x‖ + ‖(b x : ℂ) * v x‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; nlinarith [hbnorm x, norm_nonneg (v x)])
  have hB : ‖B‖ ≤ δ := av_dom _ (by
    intro x
    calc
      _ ≤ ‖v x‖ + ‖(b x : ℂ) * u x‖ := norm_add_le _ _
      _ ≤ _ := by rw [norm_mul]; nlinarith [hbnorm x, norm_nonneg (u x)])
  have hAG : ‖A‖ + ‖G‖ ≤ δ := by
    calc
      _ ≤ (∑ x : X, ‖u x‖) / (n : ℝ) + (∑ x : X, ‖v x‖) / (n : ℝ) :=
        add_le_add (av_norm u) (av_norm v)
      _ = δ := by simp only [δ, Finset.sum_add_distrib, add_div]
  have hDE : ‖D‖ + ‖E‖ ≤ δ := by
    calc
      _ ≤ (∑ x : X, ‖(b x : ℂ) * u x‖) / (n : ℝ) +
          (∑ x : X, ‖(b x : ℂ) * v x‖) / (n : ℝ) :=
        add_le_add (av_norm _) (av_norm _)
      _ = (∑ x : X, (‖(b x : ℂ) * u x‖ + ‖(b x : ℂ) * v x‖)) / (n : ℝ) := by
        rw [Finset.sum_add_distrib, add_div]
      _ ≤ δ := by
        apply div_le_div_of_nonneg_right _ hnR.le
        apply Finset.sum_le_sum
        intro x _
        simp only [norm_mul]
        nlinarith [hbnorm x, norm_nonneg (u x), norm_nonneg (v x)]
  let T : Bool → Matrix X X ℂ := fun reverse x y =>
    (K reverse x y : ℂ) * w x y
  let f : X → ℂ := fun x => 1 + u x + (b x : ℂ) * v x
  let h : X → ℂ := fun x => (b x : ℂ) + v x + (b x : ℂ) * u x
  let j : X → ℂ := fun x => (χ x : ℂ) + u x + v x
  have forward_factor (x y : X) :
      T false x y = (f x + h x * (χ y : ℂ)) / (n : ℂ) := by
    dsimp [T, K, w, f, h]
    simp only [Complex.ofReal_div,
      Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]
    rcases hχ y with hp | hp <;> simp [hp] <;> ring
  have reverse_factor (x y : X) :
      T true x y = ((1 + u x) + v x * (χ y : ℂ) + j x * (b y : ℂ)) / (n : ℂ) := by
    dsimp [T, K, w, j]
    simp only [Complex.ofReal_div, Complex.ofReal_add,
      Complex.ofReal_one, Complex.ofReal_mul, Complex.ofReal_natCast]
    rcases hχ x with hx | hx
    · rcases hχ y with hy | hy
      · simp [hx, hy]; ring
      · obtain ⟨hyb, _, _⟩ := hsupport y hy
        simp [hx, hy, hyb]; ring
    · obtain ⟨_, hxu, hxv⟩ := hsupport x hx
      simp [hx, hxu, hxv]
  have forward_op (a : X → ℂ) (x : X) :
      (T false).mulVec a x = f x * av a + h x * av (fun y => (χ y : ℂ) * a y) := by
    simp only [Matrix.mulVec, dotProduct, forward_factor]
    dsimp [av]
    simp_rw [add_div, add_mul, div_mul_eq_mul_div, mul_assoc]
    rw [Finset.sum_add_distrib]
    simp_rw [← (Finset.sum_div (K := ℂ)), ← (Finset.mul_sum (R := ℂ))]
    ring
  have reverse_op (a : X → ℂ) (x : X) :
      (T true).mulVec a x = (1 + u x) * av a + v x * av (fun y => (χ y : ℂ) * a y) +
        j x * av (fun y => (b y : ℂ) * a y) := by
    simp only [Matrix.mulVec, dotProduct, reverse_factor]
    dsimp [av]
    simp_rw [add_div, add_mul, div_mul_eq_mul_div, mul_assoc]
    simp_rw [Finset.sum_add_distrib]
    simp_rw [← (Finset.sum_div (K := ℂ)), ← (Finset.mul_sum (R := ℂ))]
    ring
  /-
  Copyright (c) 2026 Zayn Blore. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zayn Blore

  The local weight definition and next three proof bodies are adapted from
  CsdLean4/Mathlib/LinearAlgebra/Matrix/PathSum.lean at immutable revision
  211c6ffd52e388d928fca719f99d5adb5de38044 of https://github.com/zblore/csd-lean4.
  Adaptations: complex scalars, local names, proof-local statements, and `change`
  in place of `show`. The original induction and finite-index reindexing are retained.
  Full license and immutable source hashes: Library/Observer/blore2026pathsum.md.
  No NOTICE file occurs in that revision's complete Git tree.
  Retirement: replace these local proofs with direct application when an equivalent
  declaration exists at the Mathlib revision actually adopted by this repository,
  preserving the quantified contract and standard axiom closure.
  -/
  let weight (M : Matrix X X ℂ) {k : ℕ} (p : Fin (k + 1) → X) : ℂ :=
    ∏ t : Fin k, M (p t.castSucc) (p t.succ)
  have weight_one (M : Matrix X X ℂ) (p : Fin 2 → X) :
      weight M p = M (p 0) (p 1) := by simp [weight]
  have weight_cons (M : Matrix X X ℂ) {k : ℕ} (i : X) (p : Fin (k + 1) → X) :
      weight M (Fin.cons i p) = M i (p 0) * weight M p := by
    simp only [weight, Fin.prod_univ_succ, Fin.castSucc_zero, Fin.cons_zero,
      Fin.castSucc_succ, Fin.cons_succ]
  have pathpow (M : Matrix X X ℂ) (k : ℕ) (i j : X) :
      (M ^ (k + 1)) i j =
        ∑ p : Fin k → X, weight M (Fin.cons i (Fin.snoc p j)) := by
    induction k generalizing i with
    | zero =>
      rw [pow_succ, pow_zero, one_mul, Fintype.sum_unique, weight_one,
        Fin.cons_zero, Fin.cons_one]
      congr 1
    | succ k ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp_rw [ih]
      rw [← (Fin.consEquiv fun _ => X).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      change M i m * weight M (Fin.cons m (Fin.snoc p j)) =
        weight M (Fin.cons i (Fin.snoc (Fin.cons m p) j))
      rw [← Fin.cons_snoc_eq_snoc_cons, weight_cons M i, Fin.cons_zero]
  have total_paths (M : Matrix X X ℂ) (k : ℕ) :
      (∑ p : Fin (k + 1) → X, weight M p) = ∑ x : X, ∑ y : X, (M ^ k) x y := by
    cases k with
    | zero => simp [weight, Matrix.one_apply]
    | succ k =>
      simp_rw [pathpow]
      rw [← (Fin.consEquiv fun _ : Fin (k + 2) => X).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← (Fin.snocEquiv fun _ : Fin (k + 1) => X).sum_comp, Fintype.sum_prod_type]
      rfl
  let evol : Bool → ℕ → X → ℂ := fun reverse k => (T reverse ^ k).mulVec (fun _ => 1)
  have evol_zero (reverse : Bool) : evol reverse 0 = fun _ => 1 := by simp [evol]
  have evol_step (reverse : Bool) (k : ℕ) :
      evol reverse (k + 1) = (T reverse).mulVec (evol reverse k) := by
    simp only [evol, pow_succ', Matrix.mulVec_mulVec]
  have path_identification (reverse : Bool) (k : ℕ) :
      (n : ℂ)⁻¹ * (∑ p : Fin (k + 1) → X,
        ∏ t : Fin k, ((K reverse (p t.castSucc) (p t.succ) : ℂ) *
          w (p t.castSucc) (p t.succ))) = av (evol reverse k) := by
    change (n : ℂ)⁻¹ * (∑ p : Fin (k + 1) → X, weight (T reverse) p) = _
    rw [total_paths]
    simp only [av, evol, Matrix.mulVec, dotProduct, div_eq_mul_inv, mul_comm, one_mul]
  have av_scale (a : X → ℂ) (c : ℂ) : av (fun x => a x * c) = av a * c := by
    dsimp [av]; rw [← Finset.sum_mul]; ring
  have av_f : av f = 1 + Af := by
    simp only [f, av_add, av_one, Af]
    ring
  have av_h : av h = B := by
    simp only [h, av_add, av_b, B, zero_add]
  have av_chif : av (fun x => (χ x : ℂ) * f x) = Af := by
    have hid : (fun x => (χ x : ℂ) * f x) =
        (fun x => (χ x : ℂ) + (u x + (b x : ℂ) * v x)) := by
      funext x
      simp only [f, mul_add, mul_one, ← (mul_assoc (G := ℂ)), (sup_chi x).1, (sup_chi x).2.2]
      ring
    rw [hid, av_add, av_chi, zero_add]
  have av_chih : av (fun x => (χ x : ℂ) * h x) = B := by
    have hid : (fun x => (χ x : ℂ) * h x) = h := by
      funext x
      simp only [h, mul_add, ← (mul_assoc (G := ℂ)), (sup_chi x).2.1, (sup_chi x).2.2]
    rw [hid, av_h]
  have av_j : av j = A + G := by simp only [j, av_add, av_chi, zero_add, A, G]
  have av_chij : av (fun x => (χ x : ℂ) * j x) = 1 + A + G := by
    have hid : (fun x => (χ x : ℂ) * j x) = (fun x => 1 + u x + v x) := by
      funext x
      simp only [j, mul_add, chi_sq, (sup_chi x).1, (sup_chi x).2.1]
    rw [hid, av_add, av_add, av_one]
  have av_bj : av (fun x => (b x : ℂ) * j x) = D + E := by
    have hid : (fun x => (b x : ℂ) * j x) =
        (fun x => (b x : ℂ) + (b x : ℂ) * u x + (b x : ℂ) * v x) := by
      funext x
      simp only [j, mul_add, mul_comm (b x : ℂ) (χ x : ℂ), (sup_chi x).2.2]
    rw [hid, av_add, av_add, av_b, zero_add]
  -- In coordinates (av a, av (chi * a)), the exact matrix is [[1+Af,B],[Af,B]].
  have forward_coordinates (a : X → ℂ) :
      av ((T false).mulVec a) = (1 + Af) * av a + B * av (fun x => (χ x : ℂ) * a x) ∧
      av (fun x => (χ x : ℂ) * (T false).mulVec a x) =
        Af * av a + B * av (fun x => (χ x : ℂ) * a x) := by
    constructor
    · change av (fun x => (T false).mulVec a x) = _
      simp only [forward_op, av_add, av_scale, av_f, av_h]
    · simp only [forward_op, mul_add, ← (mul_assoc (G := ℂ)), av_add, av_scale, av_chif, av_chih]
  -- In coordinates (av a, av (chi * a), av (b * a)), the exact matrix is
  -- [[1+A,G,A+G],[A,G,1+A+G],[D,E,D+E]], including its unit nilpotent entry.
  have reverse_coordinates (a : X → ℂ) :
      av ((T true).mulVec a) = (1 + A) * av a + G * av (fun x => (χ x : ℂ) * a x) +
        (A + G) * av (fun x => (b x : ℂ) * a x) ∧
      av (fun x => (χ x : ℂ) * (T true).mulVec a x) =
        A * av a + G * av (fun x => (χ x : ℂ) * a x) +
          (1 + A + G) * av (fun x => (b x : ℂ) * a x) ∧
      av (fun x => (b x : ℂ) * (T true).mulVec a x) =
        D * av a + E * av (fun x => (χ x : ℂ) * a x) +
          (D + E) * av (fun x => (b x : ℂ) * a x) := by
    refine ⟨?_, ?_, ?_⟩
    · change av (fun x => (T true).mulVec a x) = _
      simp only [reverse_op, av_add, av_scale, av_one, av_j, A, G]
    · simp only [reverse_op, mul_add, ← (mul_assoc (G := ℂ)), av_add, av_scale,
        av_chi, av_chij, mul_one, zero_add, A, G,
        fun x => (sup_chi x).1, fun x => (sup_chi x).2.1]
    · simp only [reverse_op, mul_add, ← (mul_assoc (G := ℂ)), av_add, av_scale,
        av_b, av_bj, mul_one, zero_add, D, E]
  have path_bound (reverse : Bool) (s : ℕ) :
      ‖av (evol reverse s) * Complex.exp (-(s : ℂ) * mean reverse) - 1‖ ≤
        64 * (s : ℝ) * δ ^ 2 * Real.exp (64 * (s : ℝ) * δ ^ 2) := by
    cases reverse with
    | false =>
      have ht := transfer Af B 0 0 hAf hB (by simpa using hδ) (by simpa using hδ)
        (fun t => av (evol false t))
        (fun t => av (fun x => (χ x : ℂ) * evol false t x)) (fun _ => 0)
        (by rw [evol_zero, av_one]) (by simpa only [evol_zero, mul_one] using av_chi) rfl
        (by intro t; simpa only [evol_step, mul_zero, add_zero] using
          (forward_coordinates (evol false t)).1)
        (by intro t; simpa only [evol_step, mul_zero, add_zero] using
          (forward_coordinates (evol false t)).2)
        (by intro t; simp)
      exact ht s
    | true =>
      have ht := transfer A G D E
        (by linarith [norm_nonneg G]) (by linarith [norm_nonneg A])
        (by linarith [norm_nonneg E]) (by linarith [norm_nonneg D])
        (fun t => av (evol true t))
        (fun t => av (fun x => (χ x : ℂ) * evol true t x))
        (fun t => av (fun x => (b x : ℂ) * evol true t x))
        (by rw [evol_zero, av_one])
        (by simpa only [evol_zero, mul_one] using av_chi)
        (by simpa only [evol_zero, mul_one] using av_b)
        (by intro t; simpa only [evol_step] using (reverse_coordinates (evol true t)).1)
        (by intro t; simpa only [evol_step] using (reverse_coordinates (evol true t)).2.1)
        (by intro t; simpa only [evol_step] using (reverse_coordinates (evol true t)).2.2)
      exact ht s
  have pair_mean (reverse : Bool) :
      (∑ p : X × X, (((K reverse p.1 p.2 : ℂ) / (n : ℂ)) * w p.1 p.2)) =
        1 + mean reverse := by
    have hav : (∑ p : X × X, (((K reverse p.1 p.2 : ℂ) / (n : ℂ)) * w p.1 p.2)) =
        av ((T reverse).mulVec (fun _ => 1)) := by
      rw [Fintype.sum_prod_type]
      dsimp [av, Matrix.mulVec, dotProduct, T]
      simp_rw [mul_one, div_mul_eq_mul_div, ← (Finset.sum_div (K := ℂ))]
    rw [hav]
    cases reverse with
    | false =>
      have hc := (forward_coordinates (fun _ => 1)).1
      simpa only [av_one, mul_one, av_chi, mul_zero, add_zero, mean, Af, av,
        Bool.false_eq_true, ↓reduceIte] using hc
    | true =>
      have hc := (reverse_coordinates (fun _ => 1)).1
      simpa only [av_one, mul_one, av_chi, av_b, mul_zero, add_zero, mean, A, av,
        ↓reduceIte] using hc
  have pair_bound (a : ℂ) (ha : ‖a‖ ≤ δ) (s : ℕ) :
      ‖(1 + a) ^ s * Complex.exp (-(s : ℂ) * a) - 1‖ ≤
        64 * (s : ℝ) * δ ^ 2 * Real.exp (64 * (s : ℝ) * δ ^ 2) := by
    let q := Complex.exp (-a) * (1 + a)
    have hq : ‖q - 1‖ ≤ 2 * δ ^ 2 := (scalar a ha).2
    have hc := coupled (fun t => q ^ t) (fun _ => 0) (by simp) rfl
      (by
        intro t
        have hid : q ^ (t + 1) - q ^ t = (q - 1) * q ^ t := by rw [pow_succ']; ring
        rw [hid, norm_mul]
        simpa only [mul_zero, add_zero] using
          mul_le_mul_of_nonneg_right hq (norm_nonneg (q ^ t)))
      (by intro t; positivity)
    have hid : (1 + a) ^ s * Complex.exp (-(s : ℂ) * a) = q ^ s := by
      rw [show -(s : ℂ) * a = (s : ℂ) * (-a) by ring, Complex.exp_nat_mul]
      dsimp [q]; rw [mul_pow]; ring
    rw [hid]
    exact (hc s).2.2.trans (envelope s)
  intro reverse path s
  cases path with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    rw [← Fintype.sum_pow (fun p : X × X =>
      ((K reverse p.1 p.2 : ℂ) / (n : ℂ)) * w p.1 p.2) s, pair_mean]
    apply pair_bound
    cases reverse with
    | false => exact hAf
    | true => exact le_trans (le_add_of_nonneg_right (norm_nonneg G)) hAG
  | true =>
    simp only [↓reduceIte]
    rw [path_identification]
    exact path_bound reverse s
#print axioms uniform_marked_moment_bound

end D5.S3.Observer.ProbabilisticClosure.ParityMarkedMoment
