/- GID: D5/S3/Arith/Congruence/ConditionalComparison/CappedGainGeometric
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: MIT source transplant: Exact all-height geometric tails. -/

/-
Copyright (c) 2026 Michael Schroeder. MIT License.
Source: three-prime-factors-complete/formal/Erdos7/CappedGainGeometric.lean
Archive, full license, import map and retirement condition:
Library/Arith/schroeder2026noncoverage.md.
Original declaration names and proofs are retained. Utility is none: the
results are symbolic laws on arbitrary finite types, without certified
instances, bounded enumerations, checkers or numerical certificate inputs.
-/

import D5.S3.Arith.Congruence.ConditionalComparison.CappedGainFunctional

/-!
# Exact all-height geometric tails

The infinite scalar comparison is represented by nine finite increments and
one rational affine-tail term. The identities here justify that representation
for every finite actual depth bound, with no exponent cut-off assumption.
-/

namespace Erdos7.CappedGain

theorem beta_sum (p : ℚ) (hp : 1 ≤ p) (D : ℕ) :
    (∑ d ∈ Finset.range D, beta p (d + 1)) = 1 - 1 / p ^ D := by
  have hp0 : p ≠ 0 := by linarith
  induction D with
  | zero => norm_num
  | succ D ih =>
    rw [Finset.sum_range_succ, ih]
    unfold beta
    rw [pow_succ]
    field_simp
    <;> ring

theorem beta_sum_le_one (p : ℚ) (hp : 1 ≤ p) (D : ℕ) :
    (∑ d ∈ Finset.range D, beta p (d + 1)) ≤ 1 := by
  rw [beta_sum p hp D]
  have h : 0 ≤ 1 / p ^ D := by positivity
  linarith

def scalarFiniteGain (p : ℚ) (u : ℕ → ℚ) (K D : ℕ) : ℚ :=
  ∑ d ∈ Finset.range D, beta p (d + 1) * (u (K * (d + 2)) - u (K * (d + 1)))

def scalarGain (p : ℚ) (u : ℕ → ℚ) (a : ℚ) (K : ℕ) : ℚ :=
  scalarFiniteGain p u K 9 + a * K / p ^ 9

theorem affine_increment {u : ℕ → ℚ} {a b : ℚ}
    (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    {K d : ℕ} (hK : 1 ≤ K) (hd : 9 ≤ d) :
    u (K * (d + 2)) - u (K * (d + 1)) = a * K := by
  have h1 : 10 ≤ K * (d + 1) := by
    have h := Nat.mul_le_mul hK (show 10 ≤ d + 1 by omega)
    simpa using h
  have h2 : 10 ≤ K * (d + 2) := h1.trans (Nat.mul_le_mul_left K (by omega))
  rw [htail _ h2, htail _ h1]
  push_cast
  ring

theorem scalar_tail_identity {p : ℚ} (hp : 1 ≤ p)
    {u : ℕ → ℚ} {a b : ℚ} (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    {K D : ℕ} (hK : 1 ≤ K) (hD : 9 ≤ D) :
    scalarFiniteGain p u K D + a * K / p ^ D = scalarGain p u a K := by
  have hp0 : p ≠ 0 := by linarith
  induction D, hD using Nat.le_induction with
  | base => rfl
  | succ D hD ih =>
    have he : scalarFiniteGain p u K (D + 1) = scalarFiniteGain p u K D +
        beta p (D + 1) * (u (K * (D + 2)) - u (K * (D + 1))) := by
      exact Finset.sum_range_succ _ _
    rw [he, affine_increment htail hK hD, ← ih]
    unfold beta
    rw [pow_succ]
    field_simp
    <;> ring

theorem scalarFiniteGain_le {p : ℚ} (hp : 1 ≤ p)
    {u : ℕ → ℚ} {a b : ℚ} (ha : 0 ≤ a)
    (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    {K D : ℕ} (hK : 1 ≤ K) (hD : 9 ≤ D) :
    scalarFiniteGain p u K D ≤ scalarGain p u a K := by
  rw [← scalar_tail_identity hp htail hK hD]
  have h : 0 ≤ a * K / p ^ D := by positivity
  linarith

theorem scalarGain_affine {p : ℚ} (hp : 1 ≤ p)
    {u : ℕ → ℚ} {a b : ℚ} (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    {K : ℕ} (hK : 10 ≤ K) : scalarGain p u a K = a * K := by
  have he : scalarFiniteGain p u K 9 =
      (∑ d ∈ Finset.range 9, beta p (d + 1)) * (a * K) := by
    unfold scalarFiniteGain
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    have h1 : 10 ≤ K * (d + 1) := hK.trans (Nat.le_mul_of_pos_right K (by omega))
    have h2 : 10 ≤ K * (d + 2) := hK.trans (Nat.le_mul_of_pos_right K (by omega))
    rw [htail _ h1, htail _ h2]
    push_cast
    ring
  unfold scalarGain
  rw [he, beta_sum p hp 9]
  ring

variable {ι : Type*} [DecidableEq ι]

/-- Substitute bounds into the positive probability mixture, not separately
into positive and negative increment terms. -/
theorem phi_le_scalar {p r : ℚ} (hp : 1 ≤ p) (hr : 0 ≤ r)
    (hcap : r * beta p 1 ≤ 1) {D K : ℕ} (hD : 9 ≤ D) (hK : 1 ≤ K)
    (depth : ι → ℕ) (F : Finset ι → ℚ) (S : Finset ι)
    {u : ℕ → ℚ} {a b : ℚ} (ha : 0 ≤ a)
    (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    (hbound : ∀ d, d ≤ D → F (depthLe depth d S) ≤ u (K * (d + 1))) :
    phi p r D depth F S ≤ u K + r * scalarGain p u a K := by
  rw [phi_eq_expect D depth F hp hr hcap]
  let R := depthRun p r D hp hr hcap
  have h1 : R.law.expect (fun d ↦ F (depthLe depth d S)) ≤
      R.law.expect (fun d ↦ u (K * ((d : ℕ) + 1))) :=
    R.law.expect_mono (fun d ↦ hbound d (Nat.le_of_lt_succ d.isLt))
  have he : R.law.expect (fun d ↦ u (K * ((d : ℕ) + 1))) =
      u K + r * scalarFiniteGain p u K D := by
    rw [R.expect_eq_abel (fun d ↦ u (K * (d + 1)))]
    simp only [zero_add, mul_one]
    unfold scalarFiniteGain
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hs : R.survival (d + 1) = r * beta p (d + 1) :=
      depthRun_survival_pos hp hr hcap (by omega) (by simpa using Finset.mem_range.mp hd)
    rw [hs]
    ring
  rw [he] at h1
  have h2 := mul_le_mul_of_nonneg_left (scalarFiniteGain_le hp ha htail hK hD) hr
  linarith

def scalarStep (p t : ℚ) (u : ℕ → ℚ) (a : ℚ) (K : ℕ) : ℚ :=
  charge (p - 2) t (K - 1) + max
    (u K + rho (p - 2) t (K - 1) * scalarGain p u a K)
    (u K + scalarGain p u a K / (p - 2 - t) -
      (1 - (p - 2 - t) * rho (p - 2) t (K - 1)))

theorem scalarStep_affine {p t : ℚ} (hp : 3 ≤ p) (ht : t < p - 2)
    {u : ℕ → ℚ} {a b : ℚ} (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    {K : ℕ} (hK : 10 ≤ K) (hKt : t ≤ (K : ℚ) - 1) :
    scalarStep p t u a K =
      (a + (1 + a) / (p - 2 - t)) * K + b - (t + 1) / (p - 2 - t) := by
  have hc : p - 2 - t ≠ 0 := by linarith
  have hr : rho (p - 2) t ((K : ℚ) - 1) = 1 / (p - 2 - t) := by
    simp only [rho, min_eq_left hKt]
  have hq : charge (p - 2) t ((K : ℚ) - 1) = ((K : ℚ) - 1 - t) / (p - 2 - t) := by
    simp only [charge, max_eq_left (sub_nonneg.mpr hKt)]
  unfold scalarStep
  rw [hr, hq, scalarGain_affine (by linarith) htail hK, htail K hK]
  have he : a * K + b + a * K / (p - 2 - t) - (1 - (p - 2 - t) * (1 / (p - 2 - t))) =
      a * K + b + 1 / (p - 2 - t) * (a * K) := by
    field_simp
    <;> ring
  rw [he, max_self]
  ring

theorem lift_le_scalarStep {p t : ℚ} (hp : 3 ≤ p) (ht : t ≤ p - 3)
    {D K : ℕ} (hD : 9 ≤ D) (hK : 1 ≤ K) (depth : ι → ℕ)
    {F : Finset ι → ℚ} (hInc : Increasing F) (S : Finset ι)
    {L : ℚ} (hL : L ≤ (K : ℚ) - 1) {u : ℕ → ℚ} {a b : ℚ}
    (ha : 0 ≤ a) (htail : ∀ K, 10 ≤ K → u K = a * K + b)
    (hbound : ∀ d, d ≤ D → F (depthLe depth d S) ≤ u (K * (d + 1))) :
    lift (p - 2) t (fun T ↦ F (depthLe depth 0 T)) (gain p D depth F) L S ≤
      scalarStep p t u a K := by
  have hc : 0 < p - 2 - t := by linarith
  have hmono := lift_load_monotone (by linarith : t < p - 2)
    (fun T ↦ F (depthLe depth 0 T)) (gain p D depth F)
    (gain_nonneg (by linarith) D depth hInc S) hL
  have h1 := phi_le_scalar (by linarith : 1 ≤ p)
    (rho_pos (by linarith : t < p - 2) ((K : ℚ) - 1)).le
    (admissible_cap hp ht (rho_pos (by linarith) ((K : ℚ) - 1)).le (rho_le (by linarith) _))
    hD hK depth F S ha htail hbound
  have h2 := phi_le_scalar (by linarith : 1 ≤ p)
    (show 0 ≤ 1 / (p - 2 - t) by positivity)
    (admissible_cap hp ht (by positivity) (le_refl _)) hD hK depth F S ha htail hbound
  have h2' : F (depthLe depth 0 S) + gain p D depth F S / (p - 2 - t) -
      (1 - (p - 2 - t) * rho (p - 2) t ((K : ℚ) - 1)) ≤
      u K + scalarGain p u a K / (p - 2 - t) -
      (1 - (p - 2 - t) * rho (p - 2) t ((K : ℚ) - 1)) := by
    dsimp [phi] at h2
    linear_combination h2
  have hm := max_le_max h1 h2'
  unfold lift at hmono ⊢
  dsimp only at hmono
  unfold scalarStep
  dsimp [phi] at hm
  linarith

end Erdos7.CappedGain
