/- GID: D5/S3/Analytic/Polynomial/HermiteAbsoluteModeThreshold
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/HermiteAbsoluteModeThreshold
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Quadratic threshold of the absolute Hermite mode and uniqueness away from the tie degrees. -/

import D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

/-! The absolute Hermite mode has a quadratic threshold, and its maximum is unique except at the
tie degrees.

admission_basis: escape-witness. proof_shape: content for rises_iff, threshold_iff, unique_or_two,
unique_iff and result. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Analytic.Polynomial.HermiteAbsoluteModeThreshold

open D5.S3.Analytic.Polynomial.HermiteAbsoluteMode
open D5.S3.Analytic.Polynomial.HermiteAbsoluteTieOrders

private theorem rises_iff (n r : ℕ) : rises n r ↔ 2 * r ≤ n ∧ 2 * n ≤ (n - 2 * r) ^ 2 + 5 * (n - 2 * r) + 2 := by
  unfold rises second
  constructor
  · rintro ⟨h2, h4⟩
    refine ⟨h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
    rw [hj] at h4 ⊢
    have : n = j + 2 * r := by omega
    subst this; nlinarith
  · rintro ⟨h2, hF⟩
    refine ⟨h2, ?_⟩
    obtain ⟨j, hj⟩ : ∃ j, n - 2 * r = j := ⟨_, rfl⟩
    rw [hj] at hF ⊢
    have : n = j + 2 * r := by omega
    subst this; nlinarith

private theorem threshold_iff (n j : ℕ) (hj : j % 2 = n % 2) :
    b n ≤ j ↔ 2 * n ≤ j ^ 2 + 5 * j + 2 := by
  have hm := mode_rises n
  have hm2 := hm.1
  unfold b
  rcases Nat.lt_or_ge n j with hnj | hjn
  · constructor
    · intro _; nlinarith
    · intro _; omega
  obtain ⟨r, hr⟩ : ∃ r, n - j = 2 * r := ⟨(n - j) / 2, by omega⟩
  have hjr : j = n - 2 * r := by omega
  constructor
  · intro h
    have hle : r ≤ mode n := by omega
    have := ((rises_iff n r).1 (rises_lower hm hle)).2
    rw [← hjr] at this; exact this
  · intro h
    have := le_mode ((rises_iff n r).2 ⟨by omega, by rw [← hjr]; exact h⟩)
    omega

private theorem unique_or_two (k : ℕ) : (∃! j, IsAbsMax k j) ∨ HasExactlyTwo k := by
  by_cases hT : HasExactlyTwo k
  · exact Or.inr hT
  left
  have hm := (mode_rises k).1
  refine ⟨k - 2 * mode k, (max_iff_weight k _).2 ⟨mode k, hm, rfl, rfl⟩, fun j hj => ?_⟩
  obtain ⟨r, hr, rfl, he⟩ := (max_iff_weight k j).1 hj
  rcases equal_mode_indices k r hr he with h | h
  · rw [h]
  · exfalso
    apply hT
    have heq : weight k r = weight k (r + 1) := by rw [h]; exact he
    have ht := (adjacent_equal k r (by omega)).1 heq
    exact (tie_characterization k).2 ⟨r + 1, by omega, by omega, ht⟩

private theorem unique_iff (k : ℕ) :
    (∃! j, IsAbsMax k j) ↔ ¬ ∃ m, 1 ≤ m ∧ (k : ℤ) = a m := by
  obtain ⟨-, hmono, htie⟩ := HermiteAbsoluteTieOrders.result
  constructor
  · rintro ⟨j, hj, huniq⟩ ⟨m, hm, hk⟩
    have hT : HasExactlyTwo k := (htie k).2 ⟨m, ⟨hm, hk⟩, fun m' ⟨hm', hk'⟩ => by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := hmono m' m hm' h; omega
      · have := hmono m m' hm h; omega⟩
    obtain ⟨u, v, huv, huvs⟩ := hT
    have hu := huniq u ((huvs u).2 (Or.inl rfl))
    have hv := huniq v ((huvs v).2 (Or.inr rfl))
    omega
  · intro hn
    rcases unique_or_two k with h | h
    · exact h
    · obtain ⟨m, ⟨hm, hk⟩, -⟩ := (htie k).1 h
      exact absurd ⟨m, hm, hk⟩ hn

/-- Theorem 3 of Ma and Zhang on OEIS A381524/A381737: `b n ≡ n (mod 2)`, and among `j ≡ n (mod 2)`,
`b n ≤ j` exactly when `j² + 5j + 2 ≥ 2n`, so `b n` is the least such `j`; every degree has either a
unique absolute maximum or exactly two; and the maximum is unique exactly at the degrees that are
not tie degrees `a m = 2m(m+2) + (m+1)(-1)^(m+1)`, `m ≥ 1`. -/
theorem result :
    (∀ n : ℕ, b n % 2 = n % 2 ∧
      ∀ j : ℕ, j % 2 = n % 2 → (b n ≤ j ↔ 2 * n ≤ j ^ 2 + 5 * j + 2)) ∧
    (∀ k : ℕ, (∃! j, IsAbsMax k j) ∨ HasExactlyTwo k) ∧
    (∀ k : ℕ, (∃! j, IsAbsMax k j) ↔ ¬ ∃ m, 1 ≤ m ∧ (k : ℤ) = a m) :=
  ⟨fun n => ⟨by have := (mode_rises n).1; unfold b; omega, threshold_iff n⟩, unique_or_two,
    unique_iff⟩

end D5.S3.Analytic.Polynomial.HermiteAbsoluteModeThreshold
