/- GID: D5/S3/PrimeForms/Splitting/EisensteinCriterion
   generality: G
   mirror-B: D5/B/S3/PrimeForms/Splitting/EisensteinCriterion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The discriminant -3 splitting criterion. For an odd prime p ≠ 3, the field element -3 is a quadratic residue mod p if and only if p ≡ 1 (mod 3). The proof assembles quadratic reciprocity for the Legendre symbol: -3 = (-1)·3, the -1 factor gives χ₄, and reciprocity between p and 3 cancels the sign, leaving a residue condition mod 3 that splits into p ≡ 1 (residue) and p ≡ 2 (non-residue). -/

import Mathlib

namespace D5.S3.PrimeForms.Splitting.EisensteinCriterion

private lemma sq1_zmod3 : IsSquare ((1 : ℕ) : ZMod 3) := ⟨1, by decide⟩

private lemma nsq2_zmod3 : ¬ IsSquare ((2 : ℕ) : ZMod 3) := by decide

/-- **Discriminant `-3` splitting criterion.** For an odd prime `p ≠ 3`, the field element
`-3 : ZMod p` is a quadratic residue (a square in `ZMod p`) if and only if `p ≡ 1 (mod 3)`. This is
the residue half of the Eisenstein splitting law: `-3` is the discriminant of `x² + x + 1`, so its
being a square mod `p` is exactly the condition for `p` to split in the Eisenstein integers, i.e.
`p ≡ 1 (mod 3)`. Both `p ≠ 2` and `p ≠ 3` are needed (`-3 ≡ 1` is a square mod `2` yet `2 ≢ 1 mod 3`;
`-3 ≡ 0` mod `3`).

The proof runs through the Legendre symbol: writing `-3 = (-1)·3`, the `-1` factor contributes
`χ₄ p = (-1)^(p/2)`, and quadratic reciprocity between `p` and `3` cancels that sign, reducing
`(-3 / p) = 1` to `(p / 3) = 1`; casting `p` mod `3` and splitting the two nonzero residues finishes.

Only this residue criterion — the central discriminant-`-3` clause — is recorded here; the dyadic
`2`-adic clause (`3k² + 1` an Eisenstein norm for odd `k`) and the ladder-factory corollary of the
wider result are not covered by this statement. -/
theorem neg_three_isSquare_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    IsSquare (-3 : ZMod p) ↔ p % 3 = 1 := by
  have hp : p.Prime := Fact.out
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  have hmod3 : p % 3 ≠ 0 := by
    intro h
    have hdvd : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (hp.eq_one_or_self_of_dvd 3 hdvd) with h1 | h1
    · norm_num at h1
    · exact hp3 h1.symm
  have key : legendreSym p (-3) = legendreSym 3 (p : ℤ) := by
    have h1 : legendreSym p (-3) = (ZMod.χ₄ (p : ZMod 4) : ℤ) * legendreSym p 3 := by
      rw [show (-3 : ℤ) = (-1) * 3 by ring, legendreSym.mul, legendreSym.at_neg_one hp2]
    have h2 : (ZMod.χ₄ (p : ZMod 4) : ℤ) = (-1) ^ (p / 2) := ZMod.χ₄_eq_neg_one_pow hodd
    have qr : legendreSym 3 (p : ℤ) = (-1) ^ (p / 2 * (3 / 2)) * legendreSym p 3 :=
      legendreSym.quadratic_reciprocity' hp2 (by norm_num)
    rw [h1, h2, qr]
    norm_num
  have hne : ((-3 : ℤ) : ZMod p) ≠ 0 := by
    have h3p : Nat.Prime 3 := by norm_num
    have h3 : ((3 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      rcases (h3p.eq_one_or_self_of_dvd p hdvd) with h1 | h1
      · subst h1; norm_num at hp
      · exact hp3 h1
    push_cast
    simpa using h3
  have hne3 : ((p : ℤ) : ZMod 3) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
    exact hmod3
  rw [show (-3 : ZMod p) = ((-3 : ℤ) : ZMod p) by push_cast; ring,
      ← legendreSym.eq_one_iff p hne, key, legendreSym.eq_one_iff 3 hne3]
  have cast_eq : ((p : ℤ) : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_mod p 3).symm
  rw [cast_eq]
  have hcases : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hcases with hc | hc
  · rw [hc]; exact iff_of_true sq1_zmod3 rfl
  · rw [hc]; exact iff_of_false nsq2_zmod3 (by omega)

end D5.S3.PrimeForms.Splitting.EisensteinCriterion
