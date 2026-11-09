/- GID: D5/S3/QuadraticForms/ThreeWayBalance
   generality: G
   mirror-B: D5/B/S3/QuadraticForms/ThreeWayBalance
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Three-way balance forces quadratic structure on an abelian group. -/

module

public import D5.S3.QuadraticForms.ParallelogramConstruction
import all D5.S3.QuadraticForms.ParallelogramConstruction
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

/-! Nonnegative three-way balance on arbitrary abelian groups. -/

public section

namespace D5.S3.QuadraticForms.ThreeWayBalance

private theorem bounded_doubling_zero (a : ℕ → ℝ) (C : ℝ)
    (hb : ∀ n, |a n| ≤ C) (hs : ∀ n, |a (n + 1)| = 2 * |a n|) :
    a 0 = 0 := by
  have hg (n : ℕ) : ((n : ℝ) + 1) * |a 0| ≤ |a n| := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hs n]
      push_cast
      nlinarith [abs_nonneg (a 0)]
  by_contra h
  have hp : 0 < |a 0| := abs_pos.mpr h
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |a 0|)
  have hn' : C < (n : ℝ) * |a 0| := (div_lt_iff₀ hp).mp hn
  have hgn := (hg n).trans (hb n)
  nlinarith

theorem nonneg_recurrence_constant (a : ℕ → ℝ)
    (ha : ∀ n, 0 ≤ a n)
    (hr : ∀ n, a (n + 2) + a (n + 1) = 2 * a n) : a 1 = a 0 := by
  have hi (n : ℕ) : a (n + 1) + 2 * a n = a 1 + 2 * a 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := hr n
      convert_to a (n + 2) + 2 * a (n + 1) = a 1 + 2 * a 0
      linarith
  have hb (n : ℕ) : |a (n + 1) - a n| ≤ a 1 + 2 * a 0 := by
    rw [abs_le]
    constructor <;> linarith [hi n, ha n, ha (n + 1)]
  have hs (n : ℕ) : |a (n + 1 + 1) - a (n + 1)| = 2 * |a (n + 1) - a n| := by
    have h : a (n + 1 + 1) - a (n + 1) = -2 * (a (n + 1) - a n) := by
      have h := hr n
      convert_to a (n + 2) - a (n + 1) = -2 * (a (n + 1) - a n)
      linarith
    rw [h, abs_mul]
    norm_num
  have hz := bounded_doubling_zero (fun n => a (n + 1) - a n)
    (a 1 + 2 * a 0) hb hs
  simpa using sub_eq_zero.mp hz

variable {A : Type*} [AddCommGroup A]

private theorem invariant_of_balance (U : A →+ A) (q : A → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) : ∀ y, q (U y) = q y := by
  have hzero : q 0 = 0 := by
    have h := hT 0 0
    simp only [map_zero, add_zero] at h
    linarith
  intro y
  let a : ℕ → ℝ := fun n => q ((U : A → A)^[n] y)
  have hr (n : ℕ) : a (n + 2) + a (n + 1) = 2 * a n := by
    have h := hT 0 ((U : A → A)^[n] y)
    simp only [zero_add, hzero] at h
    have he (n : ℕ) : (U : A → A)^[n + 1] y = U ((U : A → A)^[n] y) :=
      Function.iterate_succ_apply' _ _ _
    change q ((U : A → A)^[n + 2] y) + q ((U : A → A)^[n + 1] y) =
      2 * q ((U : A → A)^[n] y)
    rw [show n + 2 = (n + 1) + 1 by omega, he (n + 1), he n]
    linarith
  simpa [a] using nonneg_recurrence_constant a (fun n => hq _) hr

private theorem invisible_of_balance (U : A →+ A) (q : A → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y)
    (hi : ∀ y, q (U y) = q y) :
    ∀ z y, q (z + (y + U y + U (U y))) = q z := by
  have hzero : q 0 = 0 := by
    have h := hT 0 0
    simp only [map_zero, add_zero] at h
    linarith
  have hp (z y : A) : q (z + y) = q (z + U (U (U y))) := by
    have h := hT z y
    have h' := hT z (U y)
    rw [hi y] at h'
    linarith
  have hc (z y : A) : q (z + (U (U (U y)) - y)) = q z := by
    convert (hp (z - y) y).symm using 1 <;> congr 1 <;> abel
  intro z y
  let d := y + U y + U (U y)
  have hfirst (z : A) : q (z + U d) = q (z + d) := by
    convert hc (z + d) y using 1
    congr 1
    dsimp [d]
    simp only [map_add]
    abel
  have hsecond (z : A) : q (z + U (U d)) = q (z + d) := by
    convert hc (z + d) (y + U y) using 1
    congr 1
    dsimp [d]
    simp only [map_add]
    abel
  have hadd (z : A) : q (z + d) = q z + q d := by
    have h := hT z d
    rw [hfirst, hsecond] at h
    linarith
  have hd : q d = 0 := by
    have h := hadd (-d)
    rw [neg_add_cancel, hzero] at h
    linarith [hq d, hq (-d)]
  simpa only [hd, add_zero] using hadd z

private theorem even_of_doubling (q : A → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hd : ∀ x, q (x + x) + 2 * q (-x) = 6 * q x) :
    ∀ x, q (-x) = q x := by
  intro x
  let v : ℕ → A := fun n => (2 ^ n : ℕ) • x
  let a : ℕ → ℝ := fun n => q (v n)
  let b : ℕ → ℝ := fun n => q (-(v n))
  have hv (n : ℕ) : v (n + 1) = v n + v n := by
    dsimp [v]
    rw [pow_succ, mul_nsmul, two_nsmul]
  have ha (n : ℕ) : a (n + 1) + 2 * b n = 6 * a n := by
    simpa only [a, b, hv] using hd (v n)
  have hb (n : ℕ) : b (n + 1) + 2 * a n = 6 * b n := by
    simpa only [a, b, hv, neg_add, neg_neg] using hd (-(v n))
  have hsum (n : ℕ) : a n + b n = (4 : ℝ) ^ n * (a 0 + b 0) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ]
      linarith [ha n, hb n]
  let c : ℕ → ℝ := fun n => (a n - b n) / (4 : ℝ) ^ n
  have hc (n : ℕ) : |c n| ≤ a 0 + b 0 := by
    dsimp only [c]
    rw [abs_div, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 4) n)]
    apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 4) n)).mpr
    rw [abs_le]
    constructor <;> nlinarith [hsum n, hq (v n), hq (-(v n))]
  have hcs (n : ℕ) : |c (n + 1)| = 2 * |c n| := by
    have hn : (4 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have he : c (n + 1) = 2 * c n := by
      dsimp only [c]
      rw [pow_succ]
      field_simp
      nlinarith [ha n, hb n]
    rw [he, abs_mul]
    norm_num
  have hz := bounded_doubling_zero c (a 0 + b 0) hc hcs
  have he : a 0 = b 0 := sub_eq_zero.mp (by simpa [c] using hz)
  simpa [a, b, v] using he.symm

private theorem parallelogram_of_invisible (U : A →+ A) (q : A → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y)
    (hi : ∀ y, q (U y) = q y)
    (hD : ∀ z y, q (z + (y + U y + U (U y))) = q z) :
    (∀ x, q (-x) = q x) ∧
      (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) := by
  have hzero : q 0 = 0 := by
    have h := hT 0 0
    simp only [map_zero, add_zero] at h
    linarith
  have hd (y : A) : q (y + y) + 2 * q (-y) = 6 * q y := by
    have h := hT y y
    have h₁ : q (y + U y) = q (-y) := by
      calc
        q (y + U y) = q (-U (U y)) := by
          convert hD (-U (U y)) y using 1
          congr 1
          abel
        _ = q (-y) := by
          simpa only [map_neg] using (hi (U (-y))).trans (hi (-y))
    have h₂ : q (y + U (U y)) = q (-y) := by
      calc
        q (y + U (U y)) = q (-U y) := by
          convert hD (-U y) y using 1
          congr 1
          abel
        _ = q (-y) := by simpa only [map_neg] using hi (-y)
    rw [h₁, h₂] at h
    linarith
  have he := even_of_doubling q hq hd
  have hf (x : A) : q (x + x) = 4 * q x := by
    have h := hd x
    rw [he x] at h
    linarith
  let L : A →+ A := U - U.comp U
  have hcomp (x y : A) :
      4 * q x + q (x + L y) + q (x - L y) =
        3 * q (x + y) + 3 * q (x - y) := by
    have h := hT (x + y) (x - y)
    have h₁ : q ((x + y) + (x - y)) = 4 * q x := by
      rw [show (x + y) + (x - y) = x + x by abel]
      exact hf x
    have h₂ : q ((x + y) + U (x - y)) = q (x - L y) := by
      calc
        q ((x + y) + U (x - y)) = q (U ((x + y) + U (x - y))) :=
          (hi _).symm
        _ = q (-(x - L y)) := by
          convert hD (-(x - L y)) x using 1
          congr 1
          dsimp [L]
          simp only [map_add, map_sub]
          abel
        _ = q (x - L y) := he _
    have h₃ : q ((x + y) + U (U (x - y))) = q (x + L y) := by
      calc
        q ((x + y) + U (U (x - y))) =
            q (U (U ((x + y) + U (U (x - y))))) :=
          ((hi _).trans (hi _)).symm
        _ = q (-(x + L y)) := by
          convert hD (-(x + L y)) (x - U x + U (U x) + U y - U (U y)) using 1
          congr 1
          dsimp [L]
          simp only [map_add, map_sub]
          abel
        _ = q (x + L y) := he _
    rw [h₁, h₂, h₃] at h
    linarith
  have hL (y : A) : q (L y) = 3 * q y := by
    have h := hcomp 0 y
    simp only [zero_add, zero_sub, he, hzero] at h
    linarith
  let δ : A → A → ℝ := fun x y => q (x + y) + q (x - y) - 2 * q x - 2 * q y
  have hs (x y : A) : δ x y = δ y x := by
    have hn : q (y - x) = q (x - y) := by
      simpa only [neg_sub] using he (x - y)
    dsimp [δ]
    rw [add_comm y x, hn]
    ring
  have hr (x y : A) : δ x (L y) = 3 * δ x y := by
    dsimp [δ]
    rw [hL]
    linarith [hcomp x y]
  refine ⟨he, ?_⟩
  intro x y
  have hnine : δ (L x) (L y) = 9 * δ x y := by
    rw [hr, hs (L x) y, hr y x, hs y x]
    ring
  have hthree : δ (L x) (L y) = 3 * δ x y := by
    dsimp [δ]
    rw [← map_add, ← map_sub, hL, hL, hL, hL]
    ring
  dsimp [δ] at hnine hthree
  linarith

/-- Universal nonnegative three-way balance forces the visible quadratic structure
on the original additive group. No scalar action on that group is assumed. -/
theorem three_way_quadratic_structure (U : A →+ A) (q : A → ℝ)
    (hq : ∀ x, 0 ≤ q x)
    (hT : ∀ x y, q (x + y) + q (x + U y) + q (x + U (U y)) =
      3 * q x + 3 * q y) :
    (∀ x, q (U x) = q x) ∧
    (∀ z y, q (z + (y + U y + U (U y))) = q z) ∧
    (∀ x, q (-x) = q x) ∧
    (∀ x y, q (x + y) + q (x - y) = 2 * q x + 2 * q y) ∧
    ∃ Q : QuadraticMap ℤ A ℝ, ∀ x, Q x = q x := by
  have hi := invariant_of_balance U q hq hT
  have hD := invisible_of_balance U q hq hT hi
  obtain ⟨he, hp⟩ := parallelogram_of_invisible U q hq hT hi hD
  refine ⟨hi, hD, he, hp, ?_⟩
  let Q : QuadraticMap ℤ A ℝ := TauCeti.QuadraticMap.ofParallelogram
    (smul_right_injective ℝ (by norm_num : (2 : ℕ) ≠ 0))
    (by intro x y; simpa only [two_nsmul, two_mul] using hp x y)
  exact ⟨Q, fun _ => rfl⟩

end D5.S3.QuadraticForms.ThreeWayBalance
