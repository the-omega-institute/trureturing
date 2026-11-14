/- GID: D5/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers
   generality: G
   mirror-B: D5/B/S3/Combinatorics/PowerSeries/SchulteImplicitQuadrinomialPowers
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Native integer series and every power coefficient in Schulte A262082. -/

/-
proof_shape: native_iff: bind-only; consumer: native_exists_unique.
proof_shape: native_exists_unique: bind-only; consumer: result.
proof_shape: rational_native: bind-only; consumer: coefficient_formula.
proof_shape: transport: bind-only; consumer: lagrange_bridge.
proof_shape: lagrange_bridge: bind-only; consumer: coefficient_formula.
proof_shape: quadrinomial_coeff: bind-only; consumer: coefficient_formula.
proof_shape: coefficient_formula: bind-only; consumer: result.
proof_shape: result: bind-only.
admission_basis: open-problem-resolution; source-qualified issue #30449.
escape_witness: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/30462.
The existing normalized-contraction, Lagrange and A008287 theorems are applied directly.
-/

import D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction
import D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo
import D5.S1.Recurrence.SchulteQuadrinomialAlternatingBinomialExpansion
import Mathlib.RingTheory.PowerSeries.Expand

open PowerSeries
open D5.S1.Recurrence.Invariants.UnitReversionSquareParity
namespace D5.S3.Combinatorics.PowerSeries.SchulteImplicitQuadrinomialPowers
set_option maxHeartbeats 800000

def Native {R : Type*} [CommRing R] (n : ℕ) (P : PowerSeries R) : Prop :=
  P = 1 + X * P ^ n + X ^ 2 * P ^ (2*n) + X ^ 3 * P ^ (3*n)

private noncomputable def step {R : Type*} [CommRing R] (n : ℕ) (P : PowerSeries R) : PowerSeries R :=
  1 + X * (P ^ n + X * P ^ (2*n) + X^2 * P ^ (3*n))

private theorem native_iff {R : Type*} [CommRing R] (n : ℕ) (P : PowerSeries R) :
    Native n P ↔ P = step n P := by
  unfold Native step
  congr 1 <;> ring

private theorem native_exists_unique (n : ℕ) : ∃! P : PowerSeries ℤ, Native n P := by
  have hc {d : ℕ} {f g : PowerSeries ℤ} (h : Agree d f g) :
      Agree (d+1) (step n f) (step n g) := by
    have hx : Agree d (X : PowerSeries ℤ) X := fun _ _ => rfl
    have hx2 : Agree d (X^2 : PowerSeries ℤ) (X^2) := fun _ _ => rfl
    have h2 := agree_mul hx (agree_pow h (2*n))
    have h3 := agree_mul hx2 (agree_pow h (3*n))
    have hs : Agree d (f^n + X*f^(2*n) + X^2*f^(3*n))
        (g^n + X*g^(2*n) + X^2*g^(3*n)) := by
      intro i hi
      simp only [map_add, agree_pow h n i hi, h2 i hi, h3 i hi]
    intro i hi
    simpa only [step, map_add] using
      congrArg (fun t => coeff i (1 : PowerSeries ℤ) + t) (agree_X hs i hi)
  obtain ⟨P,hP0,hP,hunique⟩ :=
    D5.S1.Recurrence.Invariants.PowerSeriesNormalizedContraction.exists_unique_fixed
      (step n) (by intro f _; simp [step]) (fun _ _ _ h => hc h)
  refine ⟨P,(native_iff n P).mpr hP, ?_⟩
  intro Q hQ
  have hQ0 : constantCoeff Q = 1 := by simpa [Native] using congrArg constantCoeff hQ
  exact hunique Q hQ0 ((native_iff n Q).mp hQ)

private theorem rational_native (n : ℕ) (P : PowerSeries ℤ) (hP : Native n P) :
    Native n (map (Int.castRingHom ℚ) P) := by
  unfold Native at *
  have h := congrArg (map (Int.castRingHom ℚ)) hP
  simpa only [map_add, map_mul, map_pow, map_one, map_X] using h

private theorem transport (n m k : ℕ) (hn : n ≠ 0) (P : PowerSeries ℚ) :
    coeff (n*k+m) ((X * expand n hn P)^m) = coeff k (P^m) := by
  rw [mul_pow, ← map_pow, coeff_X_pow_mul, coeff_expand_mul]

private theorem lagrange_bridge (n m k : ℕ) (hn : n ≠ 0) (hm : 1 ≤ m)
    (P : PowerSeries ℚ) (hP : Native n P) :
    ((n*k+m : ℕ) : ℚ) * coeff k (P^m) =
      (m : ℚ) * coeff k ((1+X+X^2+X^3 : PowerSeries ℚ)^(n*k+m)) := by
  let E := expand n hn P
  let U : PowerSeries ℚ := X * E
  let F : PowerSeries ℚ := 1 + X^n + X^(2*n) + X^(3*n)
  have hU0 : constantCoeff U = 0 := by simp [U]
  have hsub : HasSubst U := HasSubst.of_constantCoeff_zero' hU0
  have hE : E = 1 + X^n * E^n + X^(2*n) * E^(2*n) + X^(3*n) * E^(3*n) := by
    have h := congrArg (expand n hn) hP
    simpa only [map_add, map_mul, map_pow, map_one, expand_X, ← pow_mul,
      show n*2 = 2*n by omega, show n*3 = 3*n by omega] using h
  have hUF : U = X * subst U F := by
    have hF : subst U F = 1 + U^n + U^(2*n) + U^(3*n) := by
      simp only [F, subst_add hsub, subst_pow hsub, subst_X hsub]
      rw [← coe_substAlgHom hsub, map_one]
    rw [hF]
    dsimp [U]
    conv_lhs => rw [hE]
    simp only [mul_pow]
  have hF : F = expand n hn (1+X+X^2+X^3 : PowerSeries ℚ) := by
    simp only [F, map_add, map_pow, map_one, expand_X, ← pow_mul]
    simp only [Nat.mul_comm]
  have h := D5.S3.Combinatorics.Nonnesting.NonnestingOneThreeTwoTwo.lagrange_coefficient
    U F hU0 hUF (n*k+m) m hm (by omega)
  rw [show n*k+m-m = n*k by omega, hF, ← map_pow, coeff_expand_mul] at h
  simpa only [U, E, transport] using h

private theorem quadrinomial_coeff (N k : ℕ) (hk : k ≤ 3*N) :
    coeff k ((1+X+X^2+X^3 : PowerSeries ℚ)^N) =
      ∑ j ∈ Finset.range (k+1), (-2 : ℚ)^j * (N.choose j : ℚ) *
        ((3*N-2*j).choose (k-j) : ℚ) := by
  have h := congrArg (fun z : ℤ => (z : ℚ))
    (D5.S1.Recurrence.SchulteQuadrinomialAlternatingBinomialExpansion.result N k hk)
  have hc : coeff k ((1+X+X^2+X^3 : PowerSeries ℚ)^N) =
      (D5.S1.Recurrence.SchulteQuadrinomialAlternatingBinomialExpansion.T N k : ℚ) := by
    let q : Polynomial ℤ := (1+Polynomial.X+Polynomial.X^2+Polynomial.X^3)^N
    have he : map (Int.castRingHom ℚ) (q : PowerSeries ℤ) =
        (1+X+X^2+X^3 : PowerSeries ℚ)^N := by
      simp only [q, Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one,
        Polynomial.coe_X, map_pow, map_add, map_one, map_X]
    rw [← he, coeff_map]
    exact congrArg (Int.castRingHom ℚ) (Polynomial.coeff_coe q k)
  rw [hc]
  exact_mod_cast h

private theorem coefficient_formula (n m k : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m)
    (P : PowerSeries ℤ) (hP : Native n P) :
    ((coeff k (P^m) : ℤ) : ℚ) = (m : ℚ) / (n*k+m : ℕ) *
      ∑ j ∈ Finset.range (k+1), (-2 : ℚ)^j * ((n*k+m).choose j : ℚ) *
        ((3*(n*k+m)-2*j).choose (k-j) : ℚ) := by
  have h := lagrange_bridge n m k (by omega) hm
    (map (Int.castRingHom ℚ) P) (rational_native n P hP)
  rw [quadrinomial_coeff (n*k+m) k (by nlinarith)] at h
  simp only [← map_pow, coeff_map] at h
  have hN : ((n*k+m : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (show n*k+m ≠ 0 by omega)
  apply mul_left_cancel₀ hN
  calc
    _ = (m : ℚ) * _ := h
    _ = _ := by field_simp

theorem result : ∀ n : ℕ, 1 ≤ n →
    (∃! P : PowerSeries ℤ, Native n P) ∧
    ∀ P : PowerSeries ℤ, Native n P → ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ,
      ((coeff k (P^m) : ℤ) : ℚ) = (m : ℚ) / (n*k+m : ℕ) *
        ∑ j ∈ Finset.range (k+1), (-2 : ℚ)^j * ((n*k+m).choose j : ℚ) *
          ((3*(n*k+m)-2*j).choose (k-j) : ℚ) := by
  intro n hn
  exact ⟨native_exists_unique n, fun P hP m hm k => coefficient_formula n m k hn hm P hP⟩
end D5.S3.Combinatorics.PowerSeries.SchulteImplicitQuadrinomialPowers
