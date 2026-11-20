/- GID: D5/S3/ConceptDynamics/Attribution/EightOutcomeGridSupport
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Attribution/EightOutcomeGridSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The eight-outcome denominator-210 grid needs exactly three regular seed orbits. -/

import D5.S3.Combinatorics.SubsetSpectrum.DigitDiagonalCapacity
import D5.S3.ConceptDynamics.Attribution.PermutationGridSupport
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Sharp support for all permutation-equivariant readouts on the denominator-210 grid. -/

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport

open Finset
open D5.S3.Combinatorics.SubsetSpectrum
open D5.S3.ConceptDynamics.Attribution.PermutationGridSupport

private abbrev Coarse := {p : Fin 8 → ℕ // ∑ i, p i = 210}

private theorem divides_primes (p : ℕ) (prime : p.Prime) (le : p ≤ Fintype.card (Fin 8)) :
    p ∣ 210 := by
  rw [Fintype.card_fin] at le
  have lb := prime.two_le
  have cases : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6 ∨ p = 7 ∨ p = 8 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | decide | exact False.elim ((by decide : ¬ Nat.Prime _) prime)

set_option maxRecDepth 4096 in
private theorem lower {S : Type} [Fintype S] [MulAction (Equiv.Perm (Fin 8)) S]
    (w : S → ℝ) (f : Coarse → S → Fin 8) (law : CalibratingLaw S w f) :
    120960 ≤ Fintype.card S := by
  classical
  obtain ⟨positive, total, invariant, mass, covariance⟩ := law
  let v (s : S) := 210 * w s
  have calibrated (p : Coarse) (i : Fin 8) :
      (∑ s, if f p s = i then v s else 0) = (p.val i : ℝ) := by
    have term (s : S) :
        (if f p s = i then v s else 0) = 210*(if f p s = i then w s else 0) := by
      by_cases h : f p s = i <;> simp [h, v]
    rw [Finset.sum_congr rfl (fun s _ => term s), ← Finset.mul_sum, mass]
    norm_num
    ring
  have free := PrimeCycleSeedFreeness.free_of_prime_divisibility divides_primes v
    (fun s => mul_pos (by norm_num) (positive s)) f calibrated covariance
  have vi (g : Equiv.Perm (Fin 8)) (s : S) : v (g • s) = v s :=
    congrArg (210*·) (invariant g s)
  obtain ⟨r, weight, hcard, hsum, cover⟩ := weighted_orbit_spectrum (I := Fin 8)
    (by decide) free v vi f calibrated covariance
  norm_num [Fintype.card_fin, Nat.factorial] at hcard hsum cover
  by_contra hbound
  have rLe : r ≤ 2 := by omega
  have rTwo : r = 2 := by
    choose d eq using cover
    have inj : Function.Injective d := by
      intro t u same
      apply Fin.ext
      exact_mod_cast ((eq t).symm.trans (same ▸ eq u))
    have cards := Fintype.card_le_of_injective d inj
    simp only [Fintype.card_fun, Fintype.card_fin] at cards
    change 31 ≤ 9 ^ r at cards
    by_contra different
    have rSmall : r ≤ 1 := by omega
    have upper := Nat.pow_le_pow_right (by decide : 0 < 9) rSmall
    omega
  subst r
  have vTotal : ∑ s, v s = 210 := by simp [v, ← Finset.mul_sum, total]
  rw [vTotal] at hsum
  have weights : weight 0 + weight 1 = 15/4 := by
    rw [Fin.sum_univ_two] at hsum
    linarith only [hsum]
  have pairs (t : Fin 31) : ∃ d : Fin 9 × Fin 9,
      (d.1.val : ℝ) * weight 0 + (d.2.val : ℝ) * weight 1 = t.val := by
    obtain ⟨d, eq⟩ := cover t
    refine ⟨(d 0, d 1), ?_⟩
    rwa [Fin.sum_univ_two] at eq
  have bound := DigitDiagonalCapacity.integral_range_le_diagonal_codes (b := 4) (c := 15)
    (k := 8) (by decide) (by decide) (weight 0) (weight 1) (by simpa using weights) pairs
  exact (by decide : ¬ 31 ≤ (Finset.univ.image (DigitDiagonalCapacity.code (k := 8) 4)).card)
    bound


private abbrev Fine := {p : Fin 8 → ℕ // ∑ i, p i = 8 * (8 - 1) * 30}

private def scale (p : Coarse) : Fine :=
  ⟨fun i => 8 * p.val i, by rw [← Finset.mul_sum, p.property]; decide⟩

private theorem divides_fine (d : ℕ) (pos : 0 < d) (le : d ≤ 8) :
    d ∣ 8 * (8 - 1) * 30 := by
  have cases : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 := by
    omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem upper :
    ∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin 8)) S)
      (w : S → ℝ) (f : Coarse → S → Fin 8),
      CalibratingLaw S w f ∧ Fintype.card S ≤ 120960 := by
  obtain ⟨S, hS, hA, w, f, law, bound⟩ :=
    (grid_support_budget_iff (k := 8) (q := 30) (by decide) (by decide) divides_fine 3).mpr
      (by decide)
  obtain ⟨pos, total, inv, mass, cov⟩ := law
  refine ⟨S, hS, hA, w, fun p => f (scale p), ⟨pos, total, inv, ?_, ?_⟩, bound⟩
  · intro p i
    calc
      _ = ((scale p).val i : ℝ) / (↑(8 * (8 - 1) * 30 : ℕ) : ℝ) := mass (scale p) i
      _ = (p.val i : ℝ) / 210 := by
        change ((8 * p.val i : ℕ) : ℝ) / (↑(1680 : ℕ) : ℝ) = _
        push_cast
        ring
  · intro g p s
    exact cov g (scale p) s


/-- A complete eight-outcome grid of denominator 210 needs exactly three regular seed orbits. -/
theorem grid_support_budget_iff (budget : ℕ) :
    (∃ (S : Type) (_ : Fintype S) (_ : MulAction (Equiv.Perm (Fin 8)) S)
      (w : S → ℝ) (f : Coarse → S → Fin 8),
      CalibratingLaw S w f ∧ Fintype.card S ≤ budget) ↔ 120960 ≤ budget := by
  constructor
  · rintro ⟨S, _, _, w, f, law, bound⟩
    exact (lower w f law).trans bound
  · intro bound
    obtain ⟨S, iS, act, w, f, law, h⟩ := upper
    exact ⟨S, iS, act, w, f, law, h.trans bound⟩


end D5.S3.ConceptDynamics.Attribution.EightOutcomeGridSupport
