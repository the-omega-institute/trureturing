/- GID: D5/S3/Analytic/JNRRemarkThirteenPositivity
   generality: G
   mirror-B: D5/B/S3/Analytic/JNRRemarkThirteenPositivity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: A weighted sum of squares proves strict positivity of the JNR triple sum. -/

/-
# Positivity of the JNR triple sum

admission_basis: open-problem-resolution (#19039; Proved)
escape_witness: none
Direct frozen dependencies: none (imports are pinned Mathlib only).
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19104

Per-declaration proof_shape:
* Algebra.weighted_sub_sum: bind-only; consumers: Algebra.triple_factor, Algebra.centered_relation.
* Algebra.triple_factor: bind-only; consumers: Algebra.triple_positive.
* Algebra.centered_relation: bind-only; consumers: Algebra.factored_sos.
* Algebra.factored_sos: bind-only; consumers: Algebra.triple_positive.
* Algebra.triple_positive: bind-only; consumers: result.
* result: bind-only; external conjecture settlement #19039.
Each row has escape_witness: none and Direct frozen dependencies: none.
The definitions rho0, S and claim are used by result.
The source's Euclidean three-space is written as EuclideanSpace ℝ (Fin 3),
without an additional type alias; the expressions and quantified conditions of
#19039 are otherwise unchanged. No balance condition is assumed.
All declarations are symbolic finite-sum identities or inequalities, rather than
bounded enumeration, a checker, a numerical reduction or a certified instance;
utility kind none applies to the whole module.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.Combination

/-! Definitions for J. Cork and L. Disney-Hogg, "Locations of JNR skyrmions", arXiv:2505.00075v2, Eq. (3)
(`ρ`) and Appendix A, Remark 13, Eq. (18). Poles `aᵢ` and the point `x_*` lie in `ℝ³`, and `yᵢ = aᵢ − x_*`. -/

noncomputable section
namespace D5.S3.Analytic.JNRRemarkThirteenPositivity


/-- Eq. (3) at `μ = 0`: `ρ(0) = Σᵢ λᵢ² / |x_* − aᵢ|² = Σᵢ λᵢ² / |yᵢ|²`. -/
def rho0 {N : ℕ} (lam : Fin (N + 1) → ℝ) (y : Fin (N + 1) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i, lam i ^ 2 / ‖y i‖ ^ 2

/-- Eq. (18): `S = (1/ρ(0)) Σ_{i,j,k} λᵢ²λⱼ²λₖ² ⟨yⱼ − yᵢ, yⱼ − yₖ⟩ / ((|yᵢ|² + μ²)(|yⱼ|² + μ²)|yⱼ|²|yₖ|²)`. -/
def S {N : ℕ} (lam : Fin (N + 1) → ℝ) (mu : ℝ) (y : Fin (N + 1) → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  (1 / rho0 lam y) * ∑ i, ∑ j, ∑ k,
    lam i ^ 2 * lam j ^ 2 * lam k ^ 2 * inner ℝ (y j - y i) (y j - y k) /
      ((‖y i‖ ^ 2 + mu ^ 2) * (‖y j‖ ^ 2 + mu ^ 2) * ‖y j‖ ^ 2 * ‖y k‖ ^ 2)

/-- Remark 13: "we conjecture that the sum in (18) is positive for any choice of `yᵢ`", for `N + 1 ≥ 2` pairwise
distinct poles, positive weights `λᵢ`, `μ > 0` and `x_*` off the poles. -/
def claim : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (lam : Fin (N + 1) → ℝ) (mu : ℝ) (a : Fin (N + 1) → EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3)),
    (∀ i, 0 < lam i) → 0 < mu → Function.Injective a → (∀ i, x ≠ a i) →
      0 < S lam mu (fun i => a i - x)

end D5.S3.Analytic.JNRRemarkThirteenPositivity

open scoped InnerProductSpace
open Finset

namespace D5.S3.Analytic.JNRRemarkThirteenPositivity
namespace Algebra
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem weighted_sub_sum (c : ι → ℝ) (y : ι → E) (v : E) :
    ∑ i, c i • (v - y i) = (∑ i, c i) • v - ∑ i, c i • y i := by
  simpa using (Finset.sum_smul_const_vsub_eq_sub_weightedVSubOfPoint
    (Finset.univ : Finset ι) c y v (0 : E))

private theorem triple_factor (α β q : ι → ℝ) (y : ι → E) :
    (∑ i, ∑ j, ∑ k, α i * q j * β k * ⟪y j - y i, y j - y k⟫_ℝ) =
      ∑ j, q j * ⟪(∑ i, α i) • y j - ∑ i, α i • y i,
        (∑ k, β k) • y j - ∑ k, β k • y k⟫_ℝ := by
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  rw [← weighted_sub_sum α y (y j), ← weighted_sub_sum β y (y j)]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro k _
  ring

private theorem centered_relation (α β q : ι → ℝ) (y : ι → E) (t : ℝ) (m : E)
    (hrel : ∀ i, β i = α i + t * q i)
    (hm : (∑ i, β i) • m = ∑ i, β i • y i) :
    t • (∑ i, q i • (y i - m)) = (∑ i, α i) • m - ∑ i, α i • y i := by
  have hβ : (∑ i, β i • (y i - m)) = 0 := by
    simpa only [← Finset.sum_neg_distrib, ← smul_neg, neg_sub, hm, sub_self, neg_zero] using
      congrArg Neg.neg (weighted_sub_sum β y m)
  have hx : (∑ i, β i • (y i - m)) =
      (∑ i, α i • (y i - m)) + t • (∑ i, q i • (y i - m)) := by
    simp_rw [hrel, add_smul, mul_smul]
    rw [sum_add_distrib, smul_sum]
  have hα : (∑ i, α i • (y i - m)) =
      (∑ i, α i • y i) - (∑ i, α i) • m := by
    simpa using (Finset.sum_smul_vsub_const_eq_weightedVSubOfPoint_sub
      (Finset.univ : Finset ι) α y m (0 : E))
  rw [hβ, hα] at hx
  apply eq_of_sub_eq_zero
  calc
    _ = ((∑ i, α i • y i) - (∑ i, α i) • m) +
        t • (∑ i, q i • (y i - m)) := by abel
    _ = 0 := hx.symm

private theorem factored_sos (α β q : ι → ℝ) (y : ι → E) (t : ℝ) (m : E)
    (ht : t ≠ 0) (hrel : ∀ i, β i = α i + t * q i)
    (hm : (∑ i, β i) • m = ∑ i, β i • y i) :
    (∑ j, q j * ⟪(∑ i, α i) • y j - ∑ i, α i • y i,
        (∑ k, β k) • y j - ∑ k, β k • y k⟫_ℝ) =
    (∑ i, β i) * ((∑ i, α i) * (∑ i, q i * ‖y i - m‖ ^ 2) +
      ‖(∑ i, α i) • m - ∑ i, α i • y i‖ ^ 2 / t) := by
  let A := ∑ i, α i
  let B := ∑ i, α i • y i
  let C := ∑ i, β i
  let z := A • m - B
  have hz : t • (∑ i, q i • (y i - m)) = z := centered_relation α β q y t m hrel hm
  have hinner : (∑ i, q i * ⟪z, y i - m⟫_ℝ) = ‖z‖ ^ 2 / t := by
    apply (eq_div_iff ht).2
    simp_rw [← real_inner_smul_right]
    rw [← inner_sum, mul_comm, ← real_inner_smul_right, hz, real_inner_self_eq_norm_sq]
  change (∑ j, q j * ⟪A • y j - B, C • y j - ∑ k, β k • y k⟫_ℝ) = _
  have he (j : ι) : ⟪A • y j - B, C • y j - ∑ k, β k • y k⟫_ℝ =
      C * (A * ‖y j - m‖ ^ 2 + ⟪z, y j - m⟫_ℝ) := by
    have hleft : A • y j - B = A • (y j - m) + z := by
      simpa only [z, smul_sub] using (sub_add_sub_cancel (A • y j) (A • m) B).symm
    rw [← hm]
    change ⟪A • y j - B, C • y j - C • m⟫_ℝ = _
    rw [← smul_sub, hleft, real_inner_smul_right, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp_rw [he, mul_add]
  rw [sum_add_distrib]
  calc
    _ = C * A * (∑ j, q j * ‖y j - m‖ ^ 2) + C * (∑ j, q j * ⟪z, y j - m⟫_ℝ) := by
      simp_rw [mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intros <;> ring
    _ = _ := by rw [hinner]; ring

end Algebra
end D5.S3.Analytic.JNRRemarkThirteenPositivity

namespace D5.S3.Analytic.JNRRemarkThirteenPositivity
namespace Algebra
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem triple_positive (α β q : ι → ℝ) (y : ι → E) (t : ℝ)
    (hα : ∀ i, 0 < α i) (hβ : ∀ i, 0 < β i) (hq : ∀ i, 0 < q i)
    (ht : 0 < t) (hrel : ∀ i, β i = α i + t * q i)
    (hne : ∃ i j, y i ≠ y j) :
    0 < (1 / ∑ i, β i) *
      (∑ i, ∑ j, ∑ k, α i * q j * β k * ⟪y j - y i, y j - y k⟫_ℝ) := by
  classical
  obtain ⟨i, j, hij⟩ := hne
  have : Nonempty ι := ⟨i⟩
  let A := ∑ i, α i
  let C := ∑ i, β i
  let D := ∑ i, β i • y i
  let m := C⁻¹ • D
  have hA : 0 < A := sum_pos (fun i _ => hα i) univ_nonempty
  have hC : 0 < C := sum_pos (fun i _ => hβ i) univ_nonempty
  have hm : (∑ i, β i) • m = ∑ i, β i • y i := by
    exact smul_inv_smul₀ (ne_of_gt hC) D
  have hex : ∃ k, y k ≠ m := by
    by_cases hi : y i = m
    · exact ⟨j, fun hj => hij (hi.trans hj.symm)⟩
    · exact ⟨i, hi⟩
  obtain ⟨k, hk⟩ := hex
  have hvar : 0 < ∑ i, q i * ‖y i - m‖ ^ 2 := by
    apply sum_pos' (fun i _ => mul_nonneg (le_of_lt (hq i)) (sq_nonneg _))
    refine ⟨k, mem_univ k, mul_pos (hq k) ?_⟩
    exact sq_pos_of_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hk))
  rw [triple_factor, factored_sos α β q y t m (ne_of_gt ht) hrel hm]
  have hc : (1 / ∑ i, β i) * (∑ i, β i) = 1 :=
    one_div_mul_cancel (ne_of_gt hC)
  rw [← mul_assoc, hc, one_mul]
  exact add_pos_of_pos_of_nonneg (mul_pos hA hvar) (div_nonneg (sq_nonneg _) ht.le)

end Algebra
end D5.S3.Analytic.JNRRemarkThirteenPositivity

namespace D5.S3.Analytic.JNRRemarkThirteenPositivity

theorem result : claim := by
  classical
  intro N hN lam mu a x hlam hmu ha hx
  let y := fun i => a i - x
  let r := fun i => ‖y i‖ ^ 2
  let w := fun i => lam i ^ 2
  let t := mu ^ 2
  let α := fun i => w i / (r i + t)
  let β := fun i => w i / r i
  let q := fun i => w i / (r i * (r i + t))
  have hy (i) : y i ≠ 0 := sub_ne_zero.mpr (Ne.symm (hx i))
  have hr (i) : 0 < r i := sq_pos_of_pos (norm_pos_iff.mpr (hy i))
  have hw (i) : 0 < w i := sq_pos_of_pos (hlam i)
  have ht : 0 < t := sq_pos_of_pos hmu
  have hrt (i) : 0 < r i + t := add_pos (hr i) ht
  have hα (i) : 0 < α i := div_pos (hw i) (hrt i)
  have hβ (i) : 0 < β i := div_pos (hw i) (hr i)
  have hq (i) : 0 < q i := div_pos (hw i) (mul_pos (hr i) (hrt i))
  have hrel (i) : β i = α i + t * q i := by
    dsimp [α, β, q]
    field_simp [ne_of_gt (hr i), ne_of_gt (hrt i)]
  have hne : ∃ i j, y i ≠ y j := by
    let i : Fin (N + 1) := ⟨0, Nat.zero_lt_succ N⟩
    let j : Fin (N + 1) := ⟨1, Nat.lt_succ_of_le hN⟩
    refine ⟨i, j, ?_⟩
    intro h
    have he : a i = a j := (sub_left_inj).mp h
    have hn := congrArg Fin.val (ha he)
    change 0 = 1 at hn
    exact Nat.zero_ne_one hn
  have hp := Algebra.triple_positive α β q y t hα hβ hq ht hrel hne
  have heq : S lam mu y = (1 / ∑ i, β i) *
      (∑ i, ∑ j, ∑ k, α i * q j * β k * ⟪y j - y i, y j - y k⟫_ℝ) := by
    unfold S rho0
    congr 1
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro k _
    dsimp [α, β, q, w, r, t]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  change 0 < S lam mu y
  rwa [heq]

end D5.S3.Analytic.JNRRemarkThirteenPositivity
