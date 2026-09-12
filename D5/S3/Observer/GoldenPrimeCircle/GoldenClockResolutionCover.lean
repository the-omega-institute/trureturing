/- GID: D5/S3/Observer/GoldenPrimeCircle/GoldenClockResolutionCover
   generality: G
   mirror-B: none(waiver:new-cross-library-adapter)
   mirror-E: none(waiver:exact-universal-algebra)
   anchors: []
   digest: The golden phase-event cover holds at every nonnegative integer time, with an explicit negative seam in the full lattice. -/

import D5.S3.Observer.GoldenPrimeCircle.GoldenClockLattice

namespace D5.S3.Observer.GoldenPrimeCircle.GoldenClockResolutionCover

open GoldenClockLattice

noncomputable section

lemma coordinate_two (L : ℕ) (e h : ℤ) :
    phaseCoordinate (L + 2) e h = phaseCoordinate L e h / alpha ^ 2 := by
  unfold phaseCoordinate
  rw [signedWidth_two]
  field_simp [signedWidth_ne_zero L, ne_of_gt alpha_pos] <;> ring

lemma coordinate_forward (L : ℕ) (e h : ℤ) :
    phaseCoordinate (L + 1) (e + boundary L) (h + previous L) =
      (1 - phaseCoordinate L e h) / alpha := by
  have hb := boundary_error L
  have hnum : ((e + boundary L : ℤ) : ℝ) * alpha - (h + previous L : ℤ) =
      (e : ℝ) * alpha - h - signedWidth L := by
    push_cast
    linarith
  unfold phaseCoordinate
  rw [hnum, signedWidth_succ]
  field_simp [signedWidth_ne_zero L, ne_of_gt alpha_pos] <;> ring

/-- The missing cut point in an open-interval split has exactly one integer-time location. -/
theorem seam_forces_negative_time (L : ℕ) (e h : ℤ)
    (hs : phaseCoordinate L e h = alpha ^ 2) :
    e = -leading (L + 1) := by
  have he : (e : ℝ) * alpha - h = alpha ^ 2 * signedWidth L :=
    (div_eq_iff (signedWidth_ne_zero L)).mp hs
  have hb := leading_error (L + 1)
  rw [signedWidth_succ] at hb
  have hlin : (((e + leading (L + 1) : ℤ) : ℝ) * alpha) =
      ((h + boundary (L + 1) : ℤ) : ℝ) := by
    push_cast
    nlinarith
  by_contra hne
  have hp : e + leading (L + 1) ≠ 0 := by omega
  exact no_nonzero_clock_period _ hp ⟨h + boundary (L + 1), hlin⟩

/-- The seam is the negative Beatty index -1, not an unexplained numerical anomaly. -/
theorem negative_one_entry (L : ℕ) : entry L (-1) = -leading (L + 1) := by
  have hf : ⌊(-alpha)⌋ = (-1 : ℤ) := by
    apply Int.floor_eq_iff.mpr
    constructor <;> norm_num <;> linarith [alpha_pos, alpha_lt_one]
  unfold entry
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul]
  rw [hf, leading_succ]
  ring

/-- Exact cover away from the negative seam. No unproved digit-successor premise is supplied. -/
theorem resolution_cover_away_from_seam (L : ℕ) (e : ℤ)
    (he : e ≠ -leading (L + 1)) :
    Hits L e ↔ Hits (L + 2) e ∨ Hits (L + 1) (e + boundary L) := by
  constructor
  · rintro ⟨h, hlo, hhi⟩
    rcases lt_trichotomy (phaseCoordinate L e h) (alpha ^ 2) with hlt | heq | hgt
    · left
      refine ⟨h, ?_⟩
      rw [coordinate_two]
      have ha : 0 < alpha ^ 2 := pow_pos alpha_pos _
      constructor
      · exact div_pos hlo ha
      · apply (div_lt_iff₀ ha).2
        simpa using hlt
    · exact (he (seam_forces_negative_time L e h heq)).elim
    · right
      refine ⟨h + previous L, ?_⟩
      rw [coordinate_forward]
      constructor
      · exact div_pos (by linarith) alpha_pos
      · apply (div_lt_iff₀ alpha_pos).2
        nlinarith [alpha_sq_add]
  · rintro (h | h)
    · exact hits_two_steps L e h
    · simpa using hits_preceding_boundary L (e + boundary L) h

/-- Natural-time observation never meets the negative seam. The cover is uniform in L and e. -/
theorem resolution_cover_nonnegative (L : ℕ) (e : ℤ) (he : 0 ≤ e) :
    Hits L e ↔ Hits (L + 2) e ∨ Hits (L + 1) (e + boundary L) := by
  have ha : 0 < leading (L + 1) := by
    unfold leading
    exact_mod_cast (Nat.fib_pos.mpr (show 0 < L + 1 + 3 by omega))
  exact resolution_cover_away_from_seam L e (by omega)

/-- A seam-free finite observation protocol can be refined at every scale by the same law. -/
theorem resolution_cover_nat (L n : ℕ) :
    Hits L n ↔ Hits (L + 2) n ∨ Hits (L + 1) ((n : ℤ) + boundary L) :=
  resolution_cover_nonnegative L n (by positivity)

end
end D5.S3.Observer/GoldenPrimeCircle.GoldenClockResolutionCover
