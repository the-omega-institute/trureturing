/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockSectionAlgebra
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:universal-ring-and-floor-proofs)
   anchors: []
   digest: Exact section defects for all golden-integer multipliers; centered sections preserve every contracting multiplier, while additive sections cannot be invariant under a nonrational multiplier. -/

import D5.S1.Scale.Embedding
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

set_option autoImplicit false

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockSectionAlgebra

open D5.S0.Carrier D5.S1.Scale

noncomputable section

abbrev angle : ℝ := -Real.goldenConj

/-- The second REAL embedding of the existing golden-integer ring. -/
def internal : GoldenInt →+* ℝ := embedding.comp conjEquiv.toRingHom

lemma internal_apply (z : GoldenInt) :
    internal z = (z.a : ℝ) - z.b * angle := by
  change embedding (conj z) = _
  rw [embedding_apply, conj_a, conj_b]
  push_cast
  dsimp [angle]
  linear_combination -(z.b : ℝ) * Real.goldenRatio_add_goldenConj

/-- The integer coordinate is chosen by an explicit half-open cut, not by a free hidden field. -/
def select (ρ : ℝ) (n : ℤ) : ℤ := ⌊(n : ℝ) * angle + ρ⌋
def lift (ρ : ℝ) (n : ℤ) : GoldenInt := ⟨select ρ n, n⟩
def residual (ρ : ℝ) (n : ℤ) : ℝ := (n : ℝ) * angle - select ρ n

def projected (u : GoldenInt) (ρ : ℝ) (n : ℤ) : ℤ := (u * lift ρ n).b

def carry (u : GoldenInt) (ρ : ℝ) (n : ℤ) : ℤ :=
  select ρ (projected u ρ n) - (u * lift ρ n).a

@[simp] lemma lift_a (ρ : ℝ) (n : ℤ) : (lift ρ n).a = select ρ n := rfl
@[simp] lemma lift_b (ρ : ℝ) (n : ℤ) : (lift ρ n).b = n := rfl

lemma lift_injective (ρ : ℝ) : Function.Injective (lift ρ) := by
  intro m n h
  exact congrArg GoldenInt.b h

lemma residual_eq (ρ : ℝ) (n : ℤ) :
    residual ρ n = -internal (lift ρ n) := by
  rw [internal_apply]
  simp only [lift_a, lift_b, residual]
  ring

lemma residual_bounds (ρ : ℝ) (n : ℤ) :
    -ρ ≤ residual ρ n ∧ residual ρ n < 1 - ρ := by
  have hlo := Int.floor_le ((n : ℝ) * angle + ρ)
  have hhi := Int.lt_floor_add_one ((n : ℝ) * angle + ρ)
  dsimp [residual, select]
  constructor <;> linarith

/-- Both embeddings have the same integral coordinates; their difference recovers n. -/
theorem lift_two_faces (ρ : ℝ) (n : ℤ) :
    embedding (lift ρ n) - internal (lift ρ n) = Real.sqrt 5 * n := by
  rw [embedding_apply, internal_apply]
  simp only [lift_a, lift_b, angle]
  linear_combination (n : ℝ) * Real.goldenRatio_sub_goldenConj

/-- Exact relifting defect in the existing ring, including n=0 and every real cut offset. -/
theorem relift_defect (u : GoldenInt) (ρ : ℝ) (n : ℤ) :
    lift ρ (projected u ρ n) = u * lift ρ n + (carry u ρ n : GoldenInt) := by
  apply GoldenInt.ext
  · simp only [lift_a, a_add, a_intCast, carry]
    ring
  · simp only [lift_b, b_add, b_intCast, add_zero, projected]

/-- The lost integer is the floor of the contracted residual in the chosen cut. -/
theorem carry_eq_floor (u : GoldenInt) (ρ : ℝ) (n : ℤ) :
    carry u ρ n = ⌊internal u * residual ρ n + ρ⌋ := by
  have hr : (projected u ρ n : ℝ) * angle - ((u * lift ρ n).a : ℝ) =
      internal u * residual ρ n := by
    rw [residual_eq, mul_neg]
    rw [← map_mul, internal_apply]
    dsimp [projected]
    ring
  have hx : (projected u ρ n : ℝ) * angle + ρ =
      ((u * lift ρ n).a : ℝ) + (internal u * residual ρ n + ρ) := by linarith
  unfold carry select
  rw [hx, Int.floor_intCast_add]
  omega

/-- Projection after one multiplication followed by relifting records the same carry. -/
theorem residual_projected (u : GoldenInt) (ρ : ℝ) (n : ℤ) :
    residual ρ (projected u ρ n) =
      internal u * residual ρ n - (carry u ρ n : ℝ) := by
  rw [residual_eq, relift_defect, map_add, map_mul, map_intCast, residual_eq]
  ring

/-- Universal product defect. The multiplier is arbitrary in Z[phi], not just a Fibonacci power. -/
theorem projected_compose (u v : GoldenInt) (ρ : ℝ) (n : ℤ) :
    projected u ρ (projected v ρ n) =
      projected (u * v) ρ n + u.b * carry v ρ n := by
  change (u * lift ρ (projected v ρ n)).b = _
  rw [relift_defect, mul_add, ← mul_assoc, b_add]
  simp only [projected, b_mul, a_intCast, b_intCast, mul_zero, zero_add, add_zero]

/-- Exact order dependence for arbitrary two golden-integer multipliers and a real cut. -/
theorem projected_commutator (u v : GoldenInt) (ρ : ℝ) (n : ℤ) :
    projected u ρ (projected v ρ n) - projected v ρ (projected u ρ n) =
      u.b * carry v ρ n - v.b * carry u ρ n := by
  rw [projected_compose, projected_compose, mul_comm v u]
  ring

/-- The golden irrational orbit never lies on the half-integer cut seam. -/
lemma centered_residual_abs_lt (n : ℤ) : |residual (1 / 2) n| < 1 / 2 := by
  have hb := residual_bounds (1 / 2) n
  have hne : residual (1 / 2) n ≠ -(1 / 2 : ℝ) := by
    intro he
    by_cases hn : n = 0
    · subst n
      norm_num [residual, select] at he
    · have hir : Irrational ((n : ℝ) * angle) :=
        (Real.goldenConj_irrational.neg).intCast_mul hn
      apply hir.ne_rational (2 * select (1 / 2) n - 1) 2
      dsimp [residual] at he
      push_cast
      linarith
  apply abs_lt.mpr
  constructor <;> linarith

/-- Every multiplier contractive in the internal real embedding has zero centered carry. -/
theorem centered_carry_zero (u : GoldenInt) (hu : |internal u| ≤ 1) (n : ℤ) :
    carry u (1 / 2) n = 0 := by
  rw [carry_eq_floor]
  have hprod : |internal u * residual (1 / 2) n| < 1 / 2 := by
    rw [abs_mul]
    calc
      _ ≤ 1 * |residual (1 / 2) n| :=
        mul_le_mul_of_nonneg_right hu (abs_nonneg _)
      _ < 1 / 2 := by simpa using centered_residual_abs_lt n
  have hb := abs_lt.mp hprod
  apply Int.floor_eq_zero_iff.mpr
  constructor <;> linarith

/-- Contractive multiplication preserves the actual selected lift, not only its first output. -/
theorem centered_lift_projected (u : GoldenInt) (hu : |internal u| ≤ 1) (n : ℤ) :
    lift (1 / 2) (projected u (1 / 2) n) = u * lift (1 / 2) n := by
  rw [relift_defect, centered_carry_zero u hu n]
  simp

/-- The same centered section works simultaneously for every internally contractive multiplier. -/
theorem centered_compose (u v : GoldenInt) (hv : |internal v| ≤ 1) (n : ℤ) :
    projected u (1 / 2) (projected v (1 / 2) n) = projected (u * v) (1 / 2) n := by
  rw [projected_compose, centered_carry_zero v hv n]
  simp

theorem centered_commute (u v : GoldenInt)
    (hu : |internal u| ≤ 1) (hv : |internal v| ≤ 1) (n : ℤ) :
    projected u (1 / 2) (projected v (1 / 2) n) =
      projected v (1 / 2) (projected u (1 / 2) n) := by
  rw [centered_compose u v hv, centered_compose v u hu, mul_comm u v]

/-- Products remain in the same contractive family. -/
theorem contractive_mul (u v : GoldenInt)
    (hu : |internal u| ≤ 1) (hv : |internal v| ≤ 1) : |internal (u * v)| ≤ 1 := by
  rw [map_mul, abs_mul]
  calc
    _ ≤ 1 * |internal v| := mul_le_mul_of_nonneg_right hu (abs_nonneg _)
    _ ≤ 1 := by simpa using hv

def run : List GoldenInt → ℤ → ℤ
  | [], n => n
  | u :: us, n => projected u (1 / 2) (run us n)

/-- An arbitrary finite history of contractive multipliers is represented by its ring product. -/
theorem run_lift (us : List GoldenInt)
    (hs : ∀ u ∈ us, |internal u| ≤ 1) (n : ℤ) :
    lift (1 / 2) (run us n) = us.prod * lift (1 / 2) n := by
  revert hs
  induction us with
  | nil => intro hs; simp [run]
  | cons u us ih =>
      intro hs
      have hu : |internal u| ≤ 1 := hs u (by simp)
      have ht : ∀ v ∈ us, |internal v| ≤ 1 := by
        intro v hv
        exact hs v (by simp [hv])
      rw [run, centered_lift_projected u hu, ih ht, List.prod_cons, mul_assoc]

theorem run_eq_projected_product (us : List GoldenInt)
    (hs : ∀ u ∈ us, |internal u| ≤ 1) (n : ℤ) :
    run us n = projected us.prod (1 / 2) n :=
  congrArg GoldenInt.b (run_lift us hs n)

/-- No additive scalar section can also be invariant under one genuinely quadratic multiplier.
This prevents interpreting the centered construction as preserving all ordinary integer arithmetic. -/
theorem no_additive_invariant_section (u : GoldenInt) (hu : u.b ≠ 0)
    (s : ℤ →+ GoldenInt) (hs : ∀ n : ℤ, (s n).b = n) :
    ¬ ∀ n : ℤ, u * s n = s ((u * s n).b) := by
  intro hinv
  have hlin (n : ℤ) : s n = (n : GoldenInt) * s 1 := by
    simpa only [zsmul_eq_mul, mul_one] using (map_zsmul s n (1 : ℤ))
  have hb : (s 1).b = 1 := hs 1
  have he := congrArg GoldenInt.a (hinv 1)
  rw [hlin ((u * s 1).b)] at he
  simp only [a_mul, b_mul, a_intCast, b_intCast, zero_mul, add_zero, hb,
    mul_one] at he
  have hprod : u.b * ((s 1).a ^ 2 + (s 1).a - 1) = 0 := by
    linear_combination -he
  have hroot : (s 1).a ^ 2 + (s 1).a - 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hu
  rcases (show (s 1).a ≤ -2 ∨ (s 1).a = -1 ∨ (s 1).a = 0 ∨ 1 ≤ (s 1).a by omega)
    with h | h | h | h
  · have hp : 0 ≤ ((s 1).a + 2) * ((s 1).a + 1) :=
      mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    nlinarith
  · rw [h] at hroot
    norm_num at hroot
  · rw [h] at hroot
    norm_num at hroot
  · have hp : 0 ≤ ((s 1).a - 1) * (s 1).a := mul_nonneg (by omega) (by omega)
    nlinarith

end
end D5.S3.Observer.GoldenPrimeCircle.GoldenClockSectionAlgebra
