module

public import OmegaBuild.Commands
public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Group.Equiv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Omega original.

Uniform estimates for the fusion of symmetric finite posterior distributions.
The local subadditivity estimate is due to Gu and Polyanskiy, *Uniqueness of BP
fixed point for the Potts model and applications to community detection*,
arXiv:2303.14688v2, Lemma 35 and Appendix D.1, equations (143)--(166).

The proof below uses exact cancellation of the first variation under finite
permutations. A centered sum of squares controls the overlap in the rational
remainder. All simplex coordinates may vanish.
-/

compile_only_with_mathlib

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators Classical

namespace Omega.InformationTheory.PottsFusion

variable {I : Type*} [Fintype I]

/-- The chi-square capacity of a posterior with uniform prior. -/
def posteriorCapacity (p : I → ℝ) : ℝ :=
  (Fintype.card I : ℝ) * ∑ i, p i ^ 2 - 1

/-- The capacity expression for fusion of two fully symmetric posterior orbits.
Division has its usual real convention, including `0 / 0 = 0`. -/
def orbitFusion (p r : I → ℝ) : ℝ :=
  (Fintype.card I : ℝ) ^ 2 *
    (𝔼 σ : Equiv.Perm I,
      (∑ i, (p i * r (σ i)) ^ 2) / (∑ i, p i * r (σ i))) - 1

private lemma card_pos [Nonempty I] : 0 < (Fintype.card I : ℝ) := by
  exact_mod_cast Fintype.card_pos

private lemma coord_le_one (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (i : I) : p i ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ i)

private lemma sum_sq_le_one (p : I → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : (∑ i, p i ^ 2) ≤ 1 := by
  calc
    (∑ i, p i ^ 2) ≤ ∑ i, p i := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one, ← sq] using
        mul_le_mul_of_nonneg_left (coord_le_one p hp hs i) (hp i)
    _ = 1 := hs

private lemma centered_square_sum (p : I → ℝ) (hs : ∑ i, p i = 1) :
    (∑ i, ((Fintype.card I : ℝ) * p i - 1) ^ 2) =
      (Fintype.card I : ℝ) * posteriorCapacity p := by
  calc
    _ = ∑ i, ((Fintype.card I : ℝ) ^ 2 * p i ^ 2 -
        2 * (Fintype.card I : ℝ) * p i + 1) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (Fintype.card I : ℝ) * posteriorCapacity p := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs,
        posteriorCapacity]
      ring

theorem posterior_capacity_nonneg [Nonempty I] (p : I → ℝ)
    (hs : ∑ i, p i = 1) : 0 ≤ posteriorCapacity p := by
  have h := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg ((Fintype.card I : ℝ) * p i - 1))
  rw [centered_square_sum p hs] at h
  exact nonneg_of_mul_nonneg_right h card_pos

private lemma mixed_square_sum (p e : I → ℝ) (c : ℝ)
    (hp : ∑ i, p i = 1) (he : ∑ i, e i = 0) :
    (∑ i, ((Fintype.card I : ℝ) * p i - 1 + c * e i) ^ 2) =
      (Fintype.card I : ℝ) * posteriorCapacity p + c ^ 2 * (∑ i, e i ^ 2) +
        2 * c * (Fintype.card I : ℝ) * (∑ i, p i * e i) := by
  calc
    _ = ∑ i, (((Fintype.card I : ℝ) * p i - 1) ^ 2 +
        c ^ 2 * e i ^ 2 + 2 * c * (Fintype.card I : ℝ) * (p i * e i) -
        2 * c * e i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, centered_square_sum p hp, he, mul_zero, sub_zero]

/-- A centered overlap is controlled by the sum of the two quadratic defects.
This estimate uses no coordinate positivity. -/
private lemma overlap_abs_le [Nonempty I] (p e : I → ℝ)
    (hp : ∑ i, p i = 1) (he : ∑ i, e i = 0) :
    2 * |∑ i, p i * e i| ≤ posteriorCapacity p + (𝔼 i, e i ^ 2) := by
  have hplus := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg ((Fintype.card I : ℝ) * p i - 1 + 1 * e i))
  have hminus := Finset.sum_nonneg (s := Finset.univ)
    (fun i _ => sq_nonneg ((Fintype.card I : ℝ) * p i - 1 + (-1) * e i))
  rw [mixed_square_sum p e 1 hp he] at hplus
  rw [mixed_square_sum p e (-1) hp he] at hminus
  have hmean : (∑ i, e i ^ 2) =
      (Fintype.card I : ℝ) * (𝔼 i, e i ^ 2) :=
    (Fintype.card_mul_expect (fun i => e i ^ 2)).symm
  rw [hmean] at hplus hminus
  have hn : 0 < (Fintype.card I : ℝ) := card_pos
  have hp' : 0 ≤ posteriorCapacity p + (𝔼 i, e i ^ 2) +
      2 * (∑ i, p i * e i) := by
    have hh : 0 ≤ (Fintype.card I : ℝ) *
        (posteriorCapacity p + (𝔼 i, e i ^ 2) + 2 * (∑ i, p i * e i)) := by
      nlinarith [hplus]
    exact nonneg_of_mul_nonneg_right hh hn
  have hm' : 0 ≤ posteriorCapacity p + (𝔼 i, e i ^ 2) -
      2 * (∑ i, p i * e i) := by
    have hh : 0 ≤ (Fintype.card I : ℝ) *
        (posteriorCapacity p + (𝔼 i, e i ^ 2) - 2 * (∑ i, p i * e i)) := by
      nlinarith [hminus]
    exact nonneg_of_mul_nonneg_right hh hn
  rcases le_total 0 (∑ i, p i * e i) with hx | hx
  · rw [abs_of_nonneg hx]
    nlinarith
  · rw [abs_of_nonpos hx]
    nlinarith

private lemma weighted_abs_le (w e : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    {δ : ℝ} (he : ∀ i, |e i| ≤ δ) :
    |∑ i, w i * e i| ≤ δ * ∑ i, w i := by
  calc
    _ ≤ ∑ i, |w i * e i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w i * |e i| := by
      apply Finset.sum_congr rfl
      intro i _
      rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w i * δ := Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (he i) (hw i))
    _ = δ * ∑ i, w i := by rw [← Finset.sum_mul]; ring

/-- An exact rational expansion with an explicit uniform remainder bound. -/
private lemma rational_remainder_bound (S T U x δ B : ℝ)
    (hS1 : S ≤ 1) (hT : |T| ≤ δ)
    (hU0 : 0 ≤ U) (hU1 : U ≤ δ ^ 2)
    (hx : |x| ≤ δ) (hxB : 2 * |x| ≤ B)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) (hB : 0 ≤ B) :
    (S + 2 * T + U) / (1 + x) ≤
      S + 2 * T - S * x + U + 4 * δ * B := by
  have hx0 : 0 ≤ |x| := abs_nonneg x
  have hxlo : -δ ≤ x := (abs_le.mp hx).1
  have hden : 0 < 1 + x := by linarith
  have hδle : δ ≤ 1 := by linarith
  have hxx : S * x ^ 2 ≤ δ * |x| := by
    calc
      S * x ^ 2 ≤ x ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hS1 (sq_nonneg x)
      _ = |x| * |x| := by rw [← sq_abs]; ring
      _ ≤ δ * |x| := mul_le_mul_of_nonneg_right hx hx0
  have htx : -(2 * T * x) ≤ 2 * δ * |x| := by
    have hprod : |T * x| ≤ δ * |x| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hT hx0
    have := neg_le_abs (T * x)
    nlinarith
  have hux : -(U * x) ≤ δ * |x| := by
    have hprod : |U * x| ≤ δ ^ 2 * |x| := by
      rw [abs_mul, abs_of_nonneg hU0]
      exact mul_le_mul_of_nonneg_right hU1 hx0
    have hsq : δ ^ 2 ≤ δ := by
      simpa only [mul_one, ← sq] using mul_le_mul_of_nonneg_left hδle hδ0
    have hmul := mul_le_mul_of_nonneg_right hsq hx0
    have := neg_le_abs (U * x)
    nlinarith
  have hnum : S * x ^ 2 - 2 * T * x - U * x ≤ 2 * δ * B := by
    have hscale := mul_le_mul_of_nonneg_left hxB hδ0
    nlinarith
  have hrest : 2 * δ * B ≤ (4 * δ * B) * (1 + x) := by
    have hdb : 0 ≤ δ * B := mul_nonneg hδ0 hB
    have hhalf : 1 / 2 ≤ 1 + x := by linarith
    nlinarith [mul_nonneg hdb (sub_nonneg.mpr hhalf)]
  apply (div_le_iff₀ hden).2
  nlinarith [hnum.trans hrest]

private lemma expect_perm_apply [Nonempty I] (f : I → ℝ) (i : I) :
    (𝔼 σ : Equiv.Perm I, f (σ i)) = (𝔼 j, f j) := by
  classical
  let a : I → ℝ := fun j => 𝔼 σ : Equiv.Perm I, f (σ j)
  have ha (j : I) : a j = a i := by
    apply Fintype.expect_equiv (Equiv.mulRight (Equiv.swap i j))
      (fun σ : Equiv.Perm I => f (σ j)) (fun σ : Equiv.Perm I => f (σ i))
    intro σ
    change f (σ j) = f (σ ((Equiv.swap i j) i))
    rw [Equiv.swap_apply_left]
  have hsum : (Fintype.card I : ℝ) * a i = ∑ j, f j := by
    calc
      _ = ∑ _j : I, a i := by simp
      _ = ∑ j, a j := Finset.sum_congr rfl (fun j _ => (ha j).symm)
      _ = 𝔼 σ : Equiv.Perm I, ∑ j, f (σ j) := by
        exact (Finset.expect_sum_comm Finset.univ Finset.univ
          (fun (σ : Equiv.Perm I) j => f (σ j))).symm
      _ = 𝔼 _σ : Equiv.Perm I, ∑ j, f j := by
        apply Finset.expect_congr rfl
        intro σ _
        exact Equiv.sum_comp σ f
      _ = ∑ j, f j := Fintype.expect_const _
  apply mul_left_cancel₀ (ne_of_gt (card_pos (I := I)))
  exact hsum.trans (Fintype.card_mul_expect f).symm

private lemma expect_perm_weighted [Nonempty I] (w f : I → ℝ) :
    (𝔼 σ : Equiv.Perm I, ∑ i, w i * f (σ i)) =
      (∑ i, w i) * (𝔼 i, f i) := by
  rw [Finset.expect_sum_comm]
  simp_rw [← Finset.mul_expect, expect_perm_apply]
  rw [Finset.sum_mul]

/-- Uniform local fusion estimate in centered coordinates. The constant depends
only on the input cardinality, and the second posterior enters only through its
maximum centered coordinate and its quadratic energy. -/
theorem permutation_perturbation_bound [Nonempty I] (p e : I → ℝ) (δ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hesum : ∑ i, e i = 0) (he : ∀ i, |e i| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    (Fintype.card I : ℝ) *
        (𝔼 σ : Equiv.Perm I,
          (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) /
            (1 + ∑ i, p i * e (σ i))) - 1 ≤
      (1 + (4 * (Fintype.card I : ℝ) + 1) * δ) *
        (posteriorCapacity p + (𝔼 i, e i ^ 2)) := by
  classical
  let n : ℝ := Fintype.card I
  let S : ℝ := ∑ i, p i ^ 2
  let ε : ℝ := 𝔼 i, e i ^ 2
  let B : ℝ := posteriorCapacity p + ε
  let X : Equiv.Perm I → ℝ := fun σ => ∑ i, p i * e (σ i)
  let T : Equiv.Perm I → ℝ := fun σ => ∑ i, p i ^ 2 * e (σ i)
  let U : Equiv.Perm I → ℝ := fun σ => ∑ i, p i ^ 2 * e (σ i) ^ 2
  have hn : 0 < n := card_pos
  have hS1 : S ≤ 1 := sum_sq_le_one p hp hpsum
  have hε0 : 0 ≤ ε := Finset.expect_nonneg (fun i _ => sq_nonneg (e i))
  have hC0 : 0 ≤ posteriorCapacity p := posterior_capacity_nonneg p hpsum
  have hB : 0 ≤ B := add_nonneg hC0 hε0
  have heSq (i : I) : e i ^ 2 ≤ δ ^ 2 := by
    calc
      e i ^ 2 = |e i| ^ 2 := (sq_abs (e i)).symm
      _ ≤ δ ^ 2 := pow_le_pow_left₀ (abs_nonneg (e i)) (he i) 2
  have hεSq : ε ≤ δ ^ 2 :=
    Finset.expect_le Finset.univ_nonempty (fun i _ => heSq i)
  have hδle1 : δ ≤ 1 := by linarith
  have hδsq : δ ^ 2 ≤ δ := by
    simpa only [mul_one, ← sq] using mul_le_mul_of_nonneg_left hδle1 hδ0
  have hεle : ε ≤ δ := hεSq.trans hδsq
  have hX (σ : Equiv.Perm I) : |X σ| ≤ δ := by
    have := weighted_abs_le p (fun i => e (σ i)) hp (fun i => he (σ i))
    simpa only [hpsum, mul_one] using this
  have hXB (σ : Equiv.Perm I) : 2 * |X σ| ≤ B := by
    have hes : (∑ i, e (σ i)) = 0 := (Equiv.sum_comp σ e).trans hesum
    have hsq : (𝔼 i, e (σ i) ^ 2) = ε := by
      dsimp only [ε]
      rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
      exact congrArg (fun s : ℝ => s / (Fintype.card I : ℝ))
        (Equiv.sum_comp σ (fun i => e i ^ 2))
    simpa only [hsq] using overlap_abs_le p (fun i => e (σ i)) hpsum hes
  have hT (σ : Equiv.Perm I) : |T σ| ≤ δ := by
    have h := weighted_abs_le (fun i => p i ^ 2) (fun i => e (σ i))
      (fun i => sq_nonneg (p i)) (fun i => he (σ i))
    calc
      |T σ| ≤ δ * S := h
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hS1 hδ0
      _ = δ := mul_one _
  have hU0 (σ : Equiv.Perm I) : 0 ≤ U σ :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hU1 (σ : Equiv.Perm I) : U σ ≤ δ ^ 2 := by
    calc
      _ ≤ ∑ i, p i ^ 2 * δ ^ 2 := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (heSq (σ i)) (sq_nonneg (p i)))
      _ = S * δ ^ 2 := by rw [Finset.sum_mul]
      _ ≤ δ ^ 2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hS1 (sq_nonneg δ)
  have hnum (σ : Equiv.Perm I) :
      (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) = S + 2 * T σ + U σ := by
    calc
      _ = ∑ i, (p i ^ 2 + 2 * (p i ^ 2 * e (σ i)) +
          p i ^ 2 * e (σ i) ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, S, T, U]
  have hpoint (σ : Equiv.Perm I) :
      (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) / (1 + X σ) ≤
        S + 2 * T σ - S * X σ + U σ + 4 * δ * B := by
    rw [hnum]
    exact rational_remainder_bound S (T σ) (U σ) (X σ) δ B hS1
      (hT σ) (hU0 σ) (hU1 σ) (hX σ) (hXB σ) hδ0 hδ1 hB
  have heMean : (𝔼 i, e i) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, hesum, zero_div]
  have hXT : (𝔼 σ, X σ) = 0 := by
    dsimp only [X]
    rw [expect_perm_weighted, heMean, mul_zero]
  have hTT : (𝔼 σ, T σ) = 0 := by
    dsimp only [T]
    rw [expect_perm_weighted, heMean, mul_zero]
  have hUT : (𝔼 σ, U σ) = S * ε := by
    exact expect_perm_weighted (fun i => p i ^ 2) (fun i => e i ^ 2)
  have havg :
      (𝔼 σ : Equiv.Perm I,
        (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) / (1 + X σ)) ≤
        S + S * ε + 4 * δ * B := by
    calc
      _ ≤ (𝔼 σ : Equiv.Perm I,
          (S + 2 * T σ - S * X σ + U σ + 4 * δ * B)) :=
        Finset.expect_le_expect (fun σ _ => hpoint σ)
      _ = S + S * ε + 4 * δ * B := by
        simp only [Finset.expect_add_distrib, Finset.expect_sub_distrib,
          ← Finset.mul_expect, Fintype.expect_const, hTT, hXT, hUT,
          mul_zero, add_zero, sub_zero]
  have hscale := mul_le_mul_of_nonneg_left havg hn.le
  have hεC : ε * posteriorCapacity p ≤ δ * B := by
    have h₁ := mul_le_mul_of_nonneg_right hεle hC0
    have h₂ : 0 ≤ δ * ε := mul_nonneg hδ0 hε0
    dsimp only [B]
    nlinarith
  change n * (𝔼 σ : Equiv.Perm I,
      (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) / (1 + X σ)) - 1 ≤
    (1 + (4 * n + 1) * δ) * B
  have hcap : n * S = posteriorCapacity p + 1 := by
    dsimp only [n, S, posteriorCapacity]
    ring
  calc
    _ ≤ n * (S + S * ε + 4 * δ * B) - 1 := sub_le_sub_right hscale 1
    _ = posteriorCapacity p + ε + ε * posteriorCapacity p + 4 * n * δ * B := by
      calc
        _ = (n * S) * (1 + ε) + 4 * n * δ * B - 1 := by ring
        _ = _ := by rw [hcap]; ring
    _ ≤ B + δ * B + 4 * n * δ * B := by
      change posteriorCapacity p + ε + ε * posteriorCapacity p + 4 * n * δ * B ≤
        (posteriorCapacity p + ε) + δ * B + 4 * n * δ * B
      linarith [hεC]
    _ = (1 + (4 * n + 1) * δ) * B := by ring

/-- The exact centered-coordinate normalization of a posterior's capacity. -/
private lemma centered_energy (r : I → ℝ) (hr : ∑ i, r i = 1) :
    (𝔼 i, ((Fintype.card I : ℝ) * r i - 1) ^ 2) = posteriorCapacity r := by
  rw [Fintype.expect_eq_sum_div_card, centered_square_sum r hr]
  by_cases hn : (Fintype.card I : ℝ) = 0
  · have hcard : Fintype.card I = 0 := by exact_mod_cast hn
    haveI : IsEmpty I := Fintype.card_eq_zero_iff.mp hcard
    simp at hr
  · field_simp [hn]

/-- A local estimate for the actual orbit-fusion expression. The simplex
coordinates may vanish; the coordinate bound ensures positivity of the fused
denominator in precisely this local regime. -/
theorem orbit_fusion_le_of_coordinate_bound [Nonempty I]
    (p r : I → ℝ) (δ : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hrsum : ∑ i, r i = 1)
    (hr : ∀ i, |(Fintype.card I : ℝ) * r i - 1| ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1 / 2) :
    orbitFusion p r ≤
      (1 + (4 * (Fintype.card I : ℝ) + 1) * δ) *
        (posteriorCapacity p + posteriorCapacity r) := by
  classical
  let n : ℝ := Fintype.card I
  let e : I → ℝ := fun i => n * r i - 1
  have hn : n ≠ 0 := ne_of_gt (card_pos (I := I))
  have hes : (∑ i, e i) = 0 := by
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, hrsum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, n, sub_self]
  have h := permutation_perturbation_bound p e δ hp hpsum hes hr hδ0 hδ1
  rw [centered_energy r hrsum] at h
  have hrat (σ : Equiv.Perm I) :
      (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) /
          (1 + ∑ i, p i * e (σ i)) =
        n * ((∑ i, (p i * r (σ i)) ^ 2) / (∑ i, p i * r (σ i))) := by
    have hden : (1 + ∑ i, p i * e (σ i)) =
        n * (∑ i, p i * r (σ i)) := by
      calc
        _ = 1 + ∑ i, (n * (p i * r (σ i)) - p i) := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          dsimp only [e]
          ring
        _ = _ := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hpsum]
          ring
    have hnum : (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) =
        n ^ 2 * (∑ i, (p i * r (σ i)) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [e]
      ring
    rw [hden, hnum]
    by_cases hd : (∑ i, p i * r (σ i)) = 0
    · simp [hd]
    · field_simp [hn, hd]
      <;> ring
  have hexpr :
      n * (𝔼 σ : Equiv.Perm I,
        (∑ i, p i ^ 2 * (1 + e (σ i)) ^ 2) /
          (1 + ∑ i, p i * e (σ i))) - 1 = orbitFusion p r := by
    simp_rw [hrat]
    rw [← Finset.mul_expect]
    dsimp only [orbitFusion, n]
    ring
  exact hexpr ▸ h

private lemma square_ratio_le_sum (a : I → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (∑ i, a i ^ 2) / (∑ i, a i) ≤ ∑ i, a i := by
  have hs0 : 0 ≤ ∑ i, a i := Finset.sum_nonneg (fun i _ => ha i)
  have hs2 : (∑ i, a i ^ 2) ≤ (∑ i, a i) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => ha i)
  by_cases hs : (∑ i, a i) = 0
  · simp [hs]
  · apply (div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm hs))).2
    nlinarith

/-- A global capacity bound, including singular overlaps. -/
theorem orbit_fusion_le_card_sub_one [Nonempty I] (p r : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i) (hrsum : ∑ i, r i = 1) :
    orbitFusion p r ≤ (Fintype.card I : ℝ) - 1 := by
  classical
  have hpoint (σ : Equiv.Perm I) :
      (∑ i, (p i * r (σ i)) ^ 2) / (∑ i, p i * r (σ i)) ≤
        ∑ i, p i * r (σ i) :=
    square_ratio_le_sum _ (fun i => mul_nonneg (hp i) (hr (σ i)))
  have havg := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hpoint σ)
  have hrmean : (𝔼 i, r i) = 1 / (Fintype.card I : ℝ) := by
    rw [Fintype.expect_eq_sum_div_card, hrsum]
  rw [expect_perm_weighted, hpsum, one_mul, hrmean] at havg
  have hn : (Fintype.card I : ℝ) ≠ 0 := ne_of_gt (card_pos (I := I))
  have hscaled := mul_le_mul_of_nonneg_left havg
    (sq_nonneg (Fintype.card I : ℝ))
  have hcancel : (Fintype.card I : ℝ) ^ 2 * (1 / (Fintype.card I : ℝ)) =
      (Fintype.card I : ℝ) := by field_simp [hn] <;> ring
  rw [hcancel] at hscaled
  exact sub_le_sub_right hscaled 1

private lemma centered_coord_le (r : I → ℝ) (hr : ∑ i, r i = 1)
    (i : I) : ((Fintype.card I : ℝ) * r i - 1) ^ 2 ≤
      (Fintype.card I : ℝ) * posteriorCapacity r := by
  rw [← centered_square_sum r hr]
  exact Finset.single_le_sum
    (fun (j : I) _ => sq_nonneg ((Fintype.card I : ℝ) * r j - 1))
    (Finset.mem_univ i)

private lemma orbit_fusion_le_of_square_root [Nonempty I]
    (p r : I → ℝ) (t : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i) (hrsum : ∑ i, r i = 1)
    (ht : 0 ≤ t) (htsq : t ^ 2 = posteriorCapacity r) :
    orbitFusion p r ≤
      (1 + 8 * (Fintype.card I : ℝ) ^ 4 * t) *
        (posteriorCapacity p + posteriorCapacity r) := by
  let n : ℝ := Fintype.card I
  have hn : 0 < n := card_pos
  have hn1 : 1 ≤ n := by
    change (1 : ℝ) ≤ (Fintype.card I : ℝ)
    exact_mod_cast (show 1 ≤ Fintype.card I from Fintype.card_pos)
  have hnsq : n ≤ n ^ 2 := by
    simpa only [mul_one, ← sq] using mul_le_mul_of_nonneg_left hn1 hn.le
  have hC0 := posterior_capacity_nonneg p hpsum
  have hR0 := posterior_capacity_nonneg r hrsum
  have hB0 : 0 ≤ posteriorCapacity p + posteriorCapacity r := add_nonneg hC0 hR0
  have hcoord (i : I) : |n * r i - 1| ≤ n * t := by
    have h₁ := centered_coord_le r hrsum i
    change (n * r i - 1) ^ 2 ≤ n * posteriorCapacity r at h₁
    have h₂ : n * t ^ 2 ≤ (n * t) ^ 2 := by
      have hprod := mul_nonneg (sub_nonneg.mpr hn1) (sq_nonneg t)
      have hprod' := mul_nonneg hn.le hprod
      nlinarith
    rw [← htsq] at h₁
    have hnt : 0 ≤ n * t := mul_nonneg hn.le ht
    have ha : 0 ≤ |n * r i - 1| := abs_nonneg _
    apply (sq_le_sq₀ ha hnt).mp
    rw [sq_abs]
    exact h₁.trans h₂
  by_cases hsmall : n * t ≤ 1 / 2
  · have hlocal := orbit_fusion_le_of_coordinate_bound p r (n * t)
      hp hpsum hrsum hcoord (mul_nonneg hn.le ht) hsmall
    have hn2 : 1 ≤ n ^ 2 := hn1.trans hnsq
    have hn4 : n ^ 2 ≤ n ^ 4 := by
      have h := mul_le_mul_of_nonneg_right hn2 (sq_nonneg n)
      nlinarith
    have hK : (4 * n + 1) * n ≤ 8 * n ^ 4 := by nlinarith
    have hKt := mul_le_mul_of_nonneg_right hK ht
    have hfactor : 1 + (4 * n + 1) * (n * t) ≤ 1 + 8 * n ^ 4 * t := by
      nlinarith
    exact hlocal.trans (mul_le_mul_of_nonneg_right hfactor hB0)
  · have hnt : (1 / 2 : ℝ) ≤ n * t := le_of_lt (lt_of_not_ge hsmall)
    have hcube : (1 / 2 : ℝ) ^ 3 ≤ (n * t) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hnt 3
    have hcube' : 1 ≤ 8 * (n * t) ^ 3 := by nlinarith [hcube]
    have hprod : n ≤ (8 * n ^ 4 * t) * posteriorCapacity r := by
      calc
        n ≤ n * (8 * (n * t) ^ 3) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hcube' hn.le
        _ = (8 * n ^ 4 * t) * posteriorCapacity r := by rw [← htsq]; ring
    have hnonneg : 0 ≤ 8 * n ^ 4 * t := by positivity
    have hfinal : n ≤ (1 + 8 * n ^ 4 * t) *
        (posteriorCapacity p + posteriorCapacity r) := by
      have h₁ := mul_le_mul_of_nonneg_left
        (show posteriorCapacity r ≤ posteriorCapacity p + posteriorCapacity r by linarith)
        hnonneg
      nlinarith [hprod]
    have hglobal := orbit_fusion_le_card_sub_one p r hp hpsum hr hrsum
    change orbitFusion p r ≤ (1 + 8 * n ^ 4 * t) *
      (posteriorCapacity p + posteriorCapacity r)
    linarith

/-- Gu--Polyanskiy's FSC estimate with an explicit constant depending only on
the input cardinality. This is the simplex-orbit estimate; channel interpretation is a
separate correspondence. -/
theorem orbit_fusion_local_subadditivity [Nonempty I]
    (p r : I → ℝ) (ε : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hr : ∀ i, 0 ≤ r i) (hrsum : ∑ i, r i = 1)
    (hε : posteriorCapacity r ≤ ε) :
    orbitFusion p r ≤
      (1 + 8 * (Fintype.card I : ℝ) ^ 4 * Real.sqrt ε) *
        (posteriorCapacity p + posteriorCapacity r) := by
  have hR0 := posterior_capacity_nonneg r hrsum
  have h := orbit_fusion_le_of_square_root p r (Real.sqrt (posteriorCapacity r))
    hp hpsum hr hrsum (Real.sqrt_nonneg _) (Real.sq_sqrt hR0)
  have hsqrt := Real.sqrt_le_sqrt hε
  have hK : 0 ≤ 8 * (Fintype.card I : ℝ) ^ 4 := by positivity
  have hfactor := mul_le_mul_of_nonneg_left hsqrt hK
  have hB0 : 0 ≤ posteriorCapacity p + posteriorCapacity r :=
    add_nonneg (posterior_capacity_nonneg p hpsum) hR0
  exact h.trans (mul_le_mul_of_nonneg_right (by linarith) hB0)

/-- Interchanging the two posterior orbits preserves the fusion capacity. -/
theorem orbit_fusion_comm (p r : I → ℝ) : orbitFusion p r = orbitFusion r p := by
  classical
  have hnum (σ : Equiv.Perm I) :
      (∑ i, (p i * r (σ i)) ^ 2) = (∑ i, (r i * p (σ⁻¹ i)) ^ 2) := by
    apply Fintype.sum_equiv σ
      (fun i => (p i * r (σ i)) ^ 2) (fun i => (r i * p (σ⁻¹ i)) ^ 2)
    intro i
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    ring
  have hden (σ : Equiv.Perm I) :
      (∑ i, p i * r (σ i)) = (∑ i, r i * p (σ⁻¹ i)) := by
    apply Fintype.sum_equiv σ
      (fun i => p i * r (σ i)) (fun i => r i * p (σ⁻¹ i))
    intro i
    simp only [Equiv.Perm.coe_inv, Equiv.symm_apply_apply]
    ring
  unfold orbitFusion
  congr 2
  apply Fintype.expect_equiv (Equiv.inv (Equiv.Perm I))
  intro σ
  change (∑ i, (p i * r (σ i)) ^ 2) / (∑ i, p i * r (σ i)) =
    (∑ i, (r i * p (σ⁻¹ i)) ^ 2) / (∑ i, r i * p (σ⁻¹ i))
  rw [hnum, hden]

end Omega.InformationTheory.PottsFusion
