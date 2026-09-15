/- GID: D5/S3/Analytic/ChebyshevEndpointCertificate
   generality: G
   mirror-B: D5/B/S3/Analytic/ChebyshevEndpointCertificate
   mirror-E: none(waiver:unbounded-symbolic-endpoint-certificate)
   anchors: []
   digest: A shifted Chebyshev filter converts an actual noisy moment prefix into a dimension-free endpoint certificate. -/

import D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
import Mathlib.Tactic

/-!
# A dimension-free endpoint certificate from actual moments

The inputs are two positive normalized finite spectra and their actual Prony
moments. There is no assumed polynomial certificate or coefficient budget.
The proof constructs the affine Chebyshev filter. Two inductive estimates
supply its quadratic exterior amplification and its raw-moment noise cost.
Their combination is used in the finite-horizon inverse problem in the
existing NS observer theory. No mode separation or fixed dimension is needed.

Chebyshev interval bounds and recurrence are Mathlib prerequisites. The
finite-horizon minimax theorem is an ordinary mathematical consumer, not a
claim made by this Lean declaration. No physical Hamiltonian is identified.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.ChebyshevEndpointCertificate

open Polynomial Polynomial.Chebyshev
open scoped BigOperators
open D5.S3.Analytic.GoldenTomography.FinitePronyHankelReconstruction

/-- The first-difference invariant supplies the n^2 exterior growth.
The intermediate invariant is used in the successor step, not discarded. -/
private theorem exterior_growth (n : ℕ) (z : ℝ) (hz : 1 ≤ z) :
    1 + (n : ℝ) ^ 2 * (z - 1) ≤ (T ℝ (n : ℤ)).eval z := by
  let f : ℕ → ℝ := fun k => (T ℝ (k : ℤ)).eval z
  have hrec (k : ℕ) : f (k + 2) = 2 * z * f (k + 1) - f k := by
    dsimp [f]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, T_add_two,
      eval_sub, eval_mul, eval_ofNat, eval_X]
  have hp : ∀ k : ℕ,
      1 + (k : ℝ) ^ 2 * (z - 1) ≤ f k ∧
      (2 * (k : ℝ) + 1) * (z - 1) ≤ f (k + 1) - f k := by
    intro k
    induction k with
    | zero => simp [f]
    | succ k ih =>
        have hnext : 1 + ((k : ℝ) + 1) ^ 2 * (z - 1) ≤ f (k + 1) := by
          nlinarith [ih.1, ih.2]
        have hone : 1 ≤ f (k + 1) := one_le_eval_T_real _ hz
        constructor
        · simpa only [Nat.cast_succ] using hnext
        · simp only [Nat.cast_succ]
          have hmul := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hone)
          nlinarith [ih.2, hrec k]
  exact (hp n).1

/-- A shifted Chebyshev polynomial's observation error is bounded by an
explicit affine-recurrence cost. The induction applies to the modified
functional f |-> F((alpha*t+beta)*f), so it consumes raw moments directly. -/
private theorem affine_moment_budget (n : ℕ) :
    ∀ (F : (ℝ → ℝ) →ₗ[ℝ] ℝ) (α β ε : ℝ), 0 ≤ ε →
      (∀ k : ℕ, k ≤ n → |F (fun t => t ^ k)| ≤ ε) →
      |F (fun t => (T ℝ (n : ℤ)).eval (α * t + β))| ≤
        ε * (2 * (|α| + |β|) + 1) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro F α β ε hε hm
      let S : ℝ := |α| + |β|
      let Q : ℝ := 2 * S + 1
      have hS : 0 ≤ S := add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hQ : 0 ≤ Q := by dsimp [Q]; positivity
      cases n with
      | zero => simpa using hm 0 (by omega)
      | succ n =>
          cases n with
          | zero =>
              have hf : (fun t : ℝ => α * t + β) =
                  α • (fun t : ℝ => t ^ 1) + β • (fun _ : ℝ => (1 : ℝ)) := by
                ext t
                simp
              have he : F (fun t => α * t + β) =
                  α * F (fun t => t ^ 1) + β * F (fun _ => (1 : ℝ)) := by
                rw [hf, map_add, map_smul, map_smul]
                rfl
              have h0 : |F (fun _ : ℝ => (1 : ℝ))| ≤ ε := by simpa using hm 0 (by omega)
              have h1 := hm 1 (by omega)
              simp only [Nat.cast_one, T_one, eval_X, pow_one]
              rw [he]
              calc
                |α * F (fun t => t ^ 1) + β * F (fun _ => (1 : ℝ))| ≤
                    |α| * |F (fun t => t ^ 1)| + |β| * |F (fun _ => (1 : ℝ))| := by
                  simpa only [abs_mul] using abs_add (α * F (fun t => t ^ 1))
                    (β * F (fun _ => (1 : ℝ)))
                _ ≤ |α| * ε + |β| * ε := add_le_add
                  (mul_le_mul_of_nonneg_left h1 (abs_nonneg _))
                  (mul_le_mul_of_nonneg_left h0 (abs_nonneg _))
                _ ≤ ε * (2 * (|α| + |β|) + 1) := by
                  nlinarith [mul_nonneg hε (abs_nonneg α), mul_nonneg hε (abs_nonneg β)]
          | succ k =>
              let A : (ℝ → ℝ) →ₗ[ℝ] (ℝ → ℝ) :=
                { toFun := fun f t => (α * t + β) * f t
                  map_add' := by intro f g; ext t; simp only [Pi.add_apply]; ring
                  map_smul' := by intro c f; ext t; simp only [Pi.smul_apply, smul_eq_mul]; ring }
              let F' : (ℝ → ℝ) →ₗ[ℝ] ℝ := F.comp A
              have hm' (j : ℕ) (hj : j ≤ k + 1) :
                  |F' (fun t => t ^ j)| ≤ S * ε := by
                have hf : (fun t : ℝ => (α * t + β) * t ^ j) =
                    α • (fun t : ℝ => t ^ (j + 1)) + β • (fun t : ℝ => t ^ j) := by
                  ext t
                  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, pow_succ]
                  ring
                have he : F' (fun t => t ^ j) =
                    α * F (fun t => t ^ (j + 1)) + β * F (fun t => t ^ j) := by
                  change F (fun t => (α * t + β) * t ^ j) = _
                  rw [hf, map_add, map_smul, map_smul]
                  rfl
                rw [he]
                calc
                  |α * F (fun t => t ^ (j + 1)) + β * F (fun t => t ^ j)| ≤
                      |α| * |F (fun t => t ^ (j + 1))| + |β| * |F (fun t => t ^ j)| := by
                    simpa only [abs_mul] using abs_add
                      (α * F (fun t => t ^ (j + 1))) (β * F (fun t => t ^ j))
                  _ ≤ |α| * ε + |β| * ε := add_le_add
                    (mul_le_mul_of_nonneg_left (hm (j + 1) (by omega)) (abs_nonneg _))
                    (mul_le_mul_of_nonneg_left (hm j (by omega)) (abs_nonneg _))
                  _ = S * ε := by dsimp [S]; ring
              have h1 := ih (k + 1) (by omega) F' α β (S * ε)
                (mul_nonneg hS hε) hm'
              have h0 := ih k (by omega) F α β ε hε
                (fun j hj => hm j (by omega))
              have hrec : (fun t : ℝ => (T ℝ ((k + 2 : ℕ) : ℤ)).eval (α * t + β)) =
                  (2 : ℝ) • (fun t => (α * t + β) *
                    (T ℝ ((k + 1 : ℕ) : ℤ)).eval (α * t + β)) -
                    (fun t => (T ℝ (k : ℤ)).eval (α * t + β)) := by
                ext t
                simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, T_add_two,
                  eval_sub, eval_mul, eval_ofNat, eval_X, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
                ring
              change |F (fun t => (T ℝ ((k + 2 : ℕ) : ℤ)).eval (α * t + β))| ≤ ε * Q ^ (k + 2)
              rw [hrec, map_sub, map_smul]
              change |2 * F' (fun t => (T ℝ ((k + 1 : ℕ) : ℤ)).eval (α * t + β)) -
                F (fun t => (T ℝ (k : ℤ)).eval (α * t + β))| ≤ _
              have hbound : |2 * F' (fun t => (T ℝ ((k + 1 : ℕ) : ℤ)).eval (α * t + β)) -
                  F (fun t => (T ℝ (k : ℤ)).eval (α * t + β))| ≤
                    2 * (S * ε * Q ^ (k + 1)) + ε * Q ^ k := by
                calc
                  _ ≤ |2 * F' (fun t => (T ℝ ((k + 1 : ℕ) : ℤ)).eval (α * t + β))| +
                      |F (fun t => (T ℝ (k : ℤ)).eval (α * t + β))| := abs_sub _ _
                  _ ≤ 2 * (S * ε * Q ^ (k + 1)) + ε * Q ^ k := by
                    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
                    exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h0
              have halgebra : ε * Q ^ (k + 2) -
                  (2 * (S * ε * Q ^ (k + 1)) + ε * Q ^ k) =
                    (ε * Q ^ k) * (2 * S) := by
                simp only [pow_succ]
                dsimp [Q]
                ring
              have hpos := mul_nonneg (mul_nonneg hε (pow_nonneg hQ k))
                (show 0 ≤ 2 * S by positivity)
              linarith

/-- Actual noisy raw moments certify an exterior endpoint without a modal
count bound. The interval and noise parameters determine the entire budget.
The polynomial certificate and the n^2 amplification are constructed in the
proof, and the conclusion remains meaningful for colliding or zero-weight modes. -/
theorem noisy_moment_endpoint_certificate
    {r s : ℕ} (x u : Fin r → ℝ) (y v : Fin s → ℝ)
    (i₀ : Fin r) (a b η ε : ℝ) (n : ℕ)
    (ha : 0 ≤ a) (hab : a < b)
    (hx : ∀ i, a ≤ x i) (hy : ∀ j, a ≤ y j ∧ y j ≤ b)
    (hu : ∀ i, 0 ≤ u i) (hv : ∀ j, 0 ≤ v j)
    (hmu : (∑ i, u i) = 1) (hnu : (∑ j, v j) = 1)
    (hη : 0 < η) (hweight : η ≤ u i₀) (houtside : b ≤ x i₀) (hε : 0 ≤ ε)
    (hnoise : ∀ k : ℕ, k ≤ n → |pronyMoment x u k - pronyMoment y v k| ≤ ε) :
    2 * η * (n : ℝ) ^ 2 * (x i₀ - b) ≤
      (b - a) * (2 * (1 - η) + ε * (2 * ((2 + a + b) / (b - a)) + 1) ^ n) := by
  let w : ℝ := b - a
  let α : ℝ := 2 / w
  let β : ℝ := -(a + b) / w
  let R : ℝ → ℝ := fun t => (T ℝ (n : ℤ)).eval (α * t + β)
  let Q : ℝ := 2 * ((2 + a + b) / (b - a)) + 1
  have hw : 0 < w := sub_pos.mpr hab
  have hw0 : w ≠ 0 := ne_of_gt hw
  have hb : 0 ≤ b := ha.trans hab.le
  have hα : 0 ≤ α := div_nonneg (by norm_num) hw.le
  have hβ : β ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by dsimp; linarith) hw.le
  have hS : |α| + |β| = (2 + a + b) / (b - a) := by
    rw [abs_of_nonneg hα, abs_of_nonpos hβ]
    dsimp [α, β, w]
    ring
  have hcoord (t : ℝ) : α * t + β = (2 * t - a - b) / w := by
    dsimp [α, β]
    ring
  have hlow (t : ℝ) (ht : a ≤ t) : -1 ≤ α * t + β := by
    rw [hcoord]
    apply (le_div_iff₀ hw).mpr
    dsimp [w]
    linarith
  have hhigh (t : ℝ) (ht : t ≤ b) : α * t + β ≤ 1 := by
    rw [hcoord]
    apply (div_le_iff₀ hw).mpr
    dsimp [w]
    linarith
  have hpositive (i : Fin r) : 0 ≤ 1 + R (x i) := by
    by_cases h : α * x i + β ≤ 1
    · have hmem := eval_T_real_mem_Icc (n : ℤ) ⟨hlow (x i) (hx i), h⟩
      change 0 ≤ 1 + (T ℝ (n : ℤ)).eval (α * x i + β)
      linarith [hmem.1]
    · have hge := one_le_eval_T_real (n : ℤ) (le_of_not_ge h)
      change 0 ≤ 1 + (T ℝ (n : ℤ)).eval (α * x i + β)
      linarith
  have hcomp (j : Fin s) : R (y j) ≤ 1 :=
    (eval_T_real_mem_Icc (n : ℤ) ⟨hlow (y j) (hy j).1, hhigh (y j) (hy j).2⟩).2
  have hz : 1 ≤ α * x i₀ + β := by
    rw [hcoord]
    apply (le_div_iff₀ hw).mpr
    dsimp [w]
    linarith
  have hgrowth := exterior_growth n (α * x i₀ + β) hz
  have hgeom : w * (α * x i₀ + β - 1) = 2 * (x i₀ - b) := by
    dsimp [α, β]
    field_simp [hw0]
    dsimp [w]
    ring
  have hground : 2 * (n : ℝ) ^ 2 * (x i₀ - b) ≤ w * (R (x i₀) - 1) := by
    have hg := mul_le_mul_of_nonneg_left hgrowth hw.le
    change w * (1 + (n : ℝ) ^ 2 * (α * x i₀ + β - 1)) ≤
      w * R (x i₀) at hg
    nlinarith [congrArg (fun z : ℝ => (n : ℝ) ^ 2 * z) hgeom]
  let F : (ℝ → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => (∑ i, u i * f (x i)) - ∑ j, v j * f (y j)
      map_add' := by
        intro f g
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        ring
      map_smul' := by
        intro c f
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        simp_rw [mul_left_comm _ c, ← Finset.mul_sum]
        ring }
  have hbudget : |F R| ≤ ε * Q ^ n := by
    have h := affine_moment_budget n F α β ε hε
      (fun k hk => by simpa [F, pronyMoment] using hnoise k hk)
    rw [hS] at h
    exact h
  have herror : (∑ i, u i * R (x i)) - (∑ j, v j * R (y j)) ≤ ε * Q ^ n :=
    (le_abs_self (F R)).trans hbudget
  have hmusum : η * (1 + R (x i₀)) ≤ 1 + ∑ i, u i * R (x i) := by
    calc
      η * (1 + R (x i₀)) ≤ u i₀ * (1 + R (x i₀)) :=
        mul_le_mul_of_nonneg_right hweight (hpositive i₀)
      _ ≤ ∑ i, u i * (1 + R (x i)) :=
        Finset.single_le_sum (fun i _ => mul_nonneg (hu i) (hpositive i)) (Finset.mem_univ i₀)
      _ = 1 + ∑ i, u i * R (x i) := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hmu]
  have hnusum : (∑ j, v j * R (y j)) ≤ 1 := by
    calc
      (∑ j, v j * R (y j)) ≤ ∑ j, v j * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hcomp j) (hv j)
      _ = 1 := by simpa using hnu
  have hupper : η * (R (x i₀) - 1) ≤ 2 * (1 - η) + ε * Q ^ n := by
    linarith
  have hfirst := mul_le_mul_of_nonneg_left hground hη.le
  have hlast := mul_le_mul_of_nonneg_left hupper hw.le
  change 2 * η * (n : ℝ) ^ 2 * (x i₀ - b) ≤ w * (2 * (1 - η) + ε * Q ^ n)
  nlinarith

#print axioms noisy_moment_endpoint_certificate

end D5.S3.Analytic.ChebyshevEndpointCertificate
