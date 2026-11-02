/- GID: D5/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LinearForests/TwoPathConcentration
   mirror-E: none(waiver:actual-carrier-transport-pending)
   anchors: [D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional]
   utility: none
   digest: The exact signed-Catalan shift-three identity for two odd path factors, with an arbitrary residual factor. -/

import D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset PowerSeries
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion
open D5.S3.Combinatorics.Graph.LinearForests.PathCatalanFunctional
namespace D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration

local instance : DecidableRel (SimpleGraph.hasse ℕ).Adj := Classical.decRel _

def pathSeries (v : ℕ) : PowerSeries ℤ :=
  partition (SimpleGraph.hasse ℕ) (range v) (fun _ => -X)

def catalanIntegerSeries : PowerSeries ℤ := catalanSeries.map (Nat.castRingHom ℤ)

private lemma catalanIntegerSeries_eq : catalanIntegerSeries ^ 2 * X + 1 = catalanIntegerSeries := by
  simpa [catalanIntegerSeries] using congrArg (PowerSeries.map (Nat.castRingHom ℤ))
    catalanSeries_sq_mul_X_add_one

private lemma path_adj (u v : ℕ) :
    (SimpleGraph.hasse ℕ).Adj u v ↔ u + 1 = v ∨ v + 1 = u := by
  simp [SimpleGraph.hasse_adj, ← Order.succ_eq_iff_covBy]

private lemma path_rec (v : ℕ) :
    pathSeries (v + 2) = pathSeries (v + 1) - X * pathSeries v := by
  have he : (range (v + 2)).erase (v + 1) = range (v + 1) := by
    ext x
    simp only [mem_erase, mem_range]
    omega
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1) =
      range v := by
    ext x
    simp only [closedComplement, mem_filter, mem_erase, mem_range, path_adj]
    omega
  simpa [pathSeries, he, hc, sub_eq_add_neg] using
    partition_delete (SimpleGraph.hasse ℕ) (range (v + 2)) (v + 1)
      (by simp) (fun _ => (-X : PowerSeries ℤ))

private lemma path_zero : pathSeries 0 = 1 := by
  simp [pathSeries, partition_empty]

private lemma path_one : pathSeries 1 = 1 - X := by
  have he : (range 1).erase 0 = ∅ := by decide
  have hc : closedComplement (SimpleGraph.hasse ℕ) (range 1) 0 = ∅ := by
    simp [closedComplement]
  have hh := partition_delete (SimpleGraph.hasse ℕ) (range 1) 0
    (by simp) (fun _ => (-X : PowerSeries ℤ))
  rw [he, hc, partition_empty] at hh
  simpa [pathSeries, partition_empty, sub_eq_add_neg] using hh

private lemma path_two : pathSeries 2 = 1 - 2 * X := by
  rw [show 2 = 0 + 2 by omega, path_rec, path_one, path_zero]
  ring

private lemma path_three : pathSeries 3 = 1 - 3 * X + X ^ 2 := by
  rw [show 3 = 1 + 2 by omega, path_rec, path_two, path_one]
  ring

private lemma path_four : pathSeries 4 = 1 - 4 * X + 3 * X ^ 2 := by
  rw [show 4 = 2 + 2 by omega, path_rec, path_three, path_two]
  ring

private lemma path_five : pathSeries 5 = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 := by
  rw [path_rec 3, path_four, path_three]
  ring

private lemma path_six : pathSeries 6 = 1 - 6 * X + 10 * X ^ 2 - 4 * X ^ 3 := by
  rw [path_rec 4, path_five, path_four]
  ring

private lemma path_seven : pathSeries 7 = 1 - 7 * X + 15 * X ^ 2 - 10 * X ^ 3 + X ^ 4 := by
  rw [path_rec 5, path_six, path_five]
  ring

private lemma catalan_ring_forms :
    (1 + X * catalanIntegerSeries ^ 2 - catalanIntegerSeries = 0) ∧ (-1 - X * catalanIntegerSeries ^ 2 + catalanIntegerSeries = 0) := by
  have h : catalanIntegerSeries ^ 2 * X + 1 - catalanIntegerSeries = 0 := sub_eq_zero.mpr catalanIntegerSeries_eq
  constructor
  · convert h using 1 <;> ring
  · have hn : -(catalanIntegerSeries ^ 2 * X + 1 - catalanIntegerSeries) = 0 := by rw [h, neg_zero]
    convert hn using 1 <;> ring

private lemma two_path_series (n k : ℕ) (hn : 3 ≤ n) (hk : 3 ≤ k) :
    (pathSeries n * pathSeries k - pathSeries (n + k - 1) * pathSeries 1) * catalanIntegerSeries =
      X ^ 3 * pathSeries (n - 3) * pathSeries (k - 3) * catalanIntegerSeries := by
  induction hs : n + k using Nat.strong_induction_on generalizing n k with
  | h t ih =>
      subst t
      by_cases hn5 : 5 ≤ n
      · have hn2 : 3 ≤ n - 2 := by omega
        have hn1 : 3 ≤ n - 1 := by omega
        have hsum2 : (n - 2) + k < n + k := by omega
        have hsum1 : (n - 1) + k < n + k := by omega
        have h₂ := ih ((n - 2) + k) hsum2 (n - 2) k hn2 hk rfl
        have h₁ := ih ((n - 1) + k) hsum1 (n - 1) k hn1 hk rfl
        have hna : n - 2 + 2 = n := by omega
        rw [← hna, path_rec (n - 2), hna,
          show n + k - 1 = (n + k - 3) + 2 by omega,
          path_rec (n + k - 3), show n - 3 = (n - 5) + 2 by omega,
          path_rec (n - 5)] at ⊢
        have hi₁ : n - 2 + 1 = n - 1 := by omega
        have hi₂ : n + k - 3 + 1 = n - 1 + k - 1 := by omega
        have hi₃ : n - 5 + 1 = n - 4 := by omega
        have hi₄ : n - 1 - 3 = n - 4 := by omega
        have hi₅ : n - 2 - 3 = n - 5 := by omega
        have hn1pos : 1 ≤ n - 1 + k := by omega
        have hiC : n + k - 3 = n - 2 + k - 1 := by omega
        rw [hi₄] at h₁
        rw [hi₅] at h₂
        rw [hi₁, hi₂, hi₃, hiC] at ⊢
        linear_combination h₁ - X * h₂
      · have hn34 : n = 3 ∨ n = 4 := by omega
        rcases hn34 with rfl | rfl
        · by_cases hk5 : 5 ≤ k
          · have hk2 : 3 ≤ k - 2 := by omega
            have hk1 : 3 ≤ k - 1 := by omega
            have hsum2 : 3 + (k - 2) < 3 + k := by omega
            have hsum1 : 3 + (k - 1) < 3 + k := by omega
            have h₂ := ih (3 + (k - 2)) hsum2 3 (k - 2) (by omega) hk2 rfl
            have h₁ := ih (3 + (k - 1)) hsum1 3 (k - 1) (by omega) hk1 rfl
            have hka : k - 2 + 2 = k := by omega
            rw [← hka, path_rec (k - 2), hka,
              show 3 + k - 1 = k + 2 by omega,
              path_rec k, show k - 3 = (k - 5) + 2 by omega,
              path_rec (k - 5)] at ⊢
            have hi₁ : k - 2 + 1 = k - 1 := by omega
            have hi₂ : k - 1 - 3 = k - 5 + 1 := by omega
            have hi₃ : k - 2 - 3 = k - 5 := by omega
            have hiC₂ : 3 + (k - 2) - 1 = k := by omega
            have hiC₁ : 3 + (k - 1) - 1 = k + 1 := by omega
            rw [hi₃, hiC₂] at h₂
            rw [hi₂, hiC₁] at h₁
            rw [hi₁] at ⊢
            linear_combination h₁ - X * h₂
          · have hk34 : k = 3 ∨ k = 4 := by omega
            rcases hk34 with rfl | rfl
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_three, path_five, path_one, path_zero]
              rcases catalan_ring_forms with ⟨hp, hn⟩
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_three, path_four, path_one, path_six, path_zero]
              rcases catalan_ring_forms with ⟨hp, hn⟩
              ring_nf
        · by_cases hk5 : 5 ≤ k
          · have hk2 : 3 ≤ k - 2 := by omega
            have hk1 : 3 ≤ k - 1 := by omega
            have hsum2 : 4 + (k - 2) < 4 + k := by omega
            have hsum1 : 4 + (k - 1) < 4 + k := by omega
            have h₂ := ih (4 + (k - 2)) hsum2 4 (k - 2) (by omega) hk2 rfl
            have h₁ := ih (4 + (k - 1)) hsum1 4 (k - 1) (by omega) hk1 rfl
            have hka : k - 2 + 2 = k := by omega
            rw [← hka, path_rec (k - 2), hka,
              show 4 + k - 1 = (k + 1) + 2 by omega,
              path_rec (k + 1), show k - 3 = (k - 5) + 2 by omega,
              path_rec (k - 5)] at ⊢
            have hi₁ : k - 2 + 1 = k - 1 := by omega
            have hi₂ : k + 1 + 1 = k + 2 := by omega
            have hi₃ : k - 1 - 3 = k - 5 + 1 := by omega
            have hi₄ : k - 2 - 3 = k - 5 := by omega
            have hiC₁ : 4 + (k - 1) - 1 = k + 2 := by omega
            have hiC₂ : 4 + (k - 2) - 1 = k + 1 := by omega
            rw [hi₄] at h₂
            rw [hiC₂] at h₂
            rw [hiC₁, hi₃] at h₁
            rw [hi₁] at ⊢
            rw [hi₂] at ⊢
            linear_combination h₁ - X * h₂
          · have hk34 : k = 3 ∨ k = 4 := by omega
            rcases hk34 with rfl | rfl
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_four, path_three, path_one, path_six, path_zero]
              rcases catalan_ring_forms with ⟨hp, hn⟩
              ring_nf
            · simp only [Nat.reduceAdd, Nat.reduceSub]
              rw [path_four, path_one, path_seven]
              rcases catalan_ring_forms with ⟨hp, hn⟩
              ring_nf

/-- The exact series law behind the two-path signed-Catalan concentration move.
The factor `R` is arbitrary, so it may be the actual partition series of any
untouched finite residual graph. -/
theorem two_path_series_concentration (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (R : PowerSeries ℤ) :
    (pathSeries (2 * p + 1) * pathSeries (2 * q + 1) * R * catalanIntegerSeries -
      pathSeries (2 * p + 2 * q + 1) * pathSeries 1 * R * catalanIntegerSeries) =
      X ^ 3 * pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R * catalanIntegerSeries := by
  have h := two_path_series (2 * p + 1) (2 * q + 1) (by omega) (by omega)
  have h' := congrArg (fun t : PowerSeries ℤ => t * R) h
  have hp' : 2 * p + 1 - 3 = 2 * p - 2 := by omega
  have hq' : 2 * q + 1 - 3 = 2 * q - 2 := by omega
  have hL : 2 * p + 1 + (2 * q + 1) - 1 = 2 * p + 2 * q + 1 := by omega
  rw [hp', hq'] at h'
  rw [hL] at h'
  convert h' using 1 <;> ring

/-- Exact coefficient application, kept as a transient check of the reusable
series law so the public API remains content-bearing. -/
example (p q m : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hm : 2 * p + 2 * q + 2 ≤ m) (R : PowerSeries ℤ) :
    coeff m (pathSeries (2 * p + 1) * pathSeries (2 * q + 1) * R * catalanIntegerSeries) -
      coeff m (pathSeries (2 * p + 2 * q + 1) * pathSeries 1 * R * catalanIntegerSeries) =
      coeff (m - 3) (pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R * catalanIntegerSeries) := by
  have hs := two_path_series_concentration p q hp hq R
  have hm3 : 3 ≤ m := by omega
  have hc := congrArg (fun F : PowerSeries ℤ => coeff m F) hs
  simp only [map_sub] at hc
  have hcoef := coeff_X_pow_mul'
    (pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R * catalanIntegerSeries) 3 m
  have hcoef' : coeff m (X ^ 3 * pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R * catalanIntegerSeries) =
      if 3 ≤ m then coeff (m - 3) (pathSeries (2 * p - 2) * pathSeries (2 * q - 2) * R * catalanIntegerSeries) else 0 := by
    simpa [mul_assoc] using hcoef
  rw [hcoef', ite_eq_left (show 3 ≤ m by omega)] at hc
  simpa using hc

#print axioms two_path_series_concentration
end D5.S3.Combinatorics.Graph.LinearForests.TwoPathConcentration
