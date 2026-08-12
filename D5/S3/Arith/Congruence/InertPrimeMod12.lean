/- GID: D5/S3/Arith/Congruence/InertPrimeMod12
   generality: G
   mirror-B: D5/B/S3/Arith/Congruence/InertPrimeMod12
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Any prime p that is inert in the Eisenstein integers (p ≡ 2 mod 3) and divides (6j)²+1 satisfies p ≡ 5 mod 12. Since p divides a value of the form k²+1, minus one is a square modulo p, forcing p ≡ 1 mod 4; combined with the inert residue p ≡ 2 mod 3 this pins p ≡ 5 mod 12 by the Chinese remainder theorem (the E.48 bad-prime lemma). -/

import Mathlib

namespace D5.S3.Arith.Congruence.InertPrimeMod12

/-- **Bad-prime lemma (E.48).** Any prime `p` that is inert in the Eisenstein integers
(`p % 3 = 2`) and divides `(6 * j) ^ 2 + 1` is congruent to `5` modulo `12`.

Because `p` divides a value of the form `k ^ 2 + 1`, the element `-1` is a square modulo `p`, which
forces `p % 4 = 1`; together with the inert residue `p % 3 = 2` the Chinese remainder theorem pins
`p % 12 = 5`. Only inert prime factors are constrained this way — split factors (`p % 3 = 1`) are
congruent to `1` modulo `12`. -/
theorem inert_prime_dvd_mod_twelve (j p : ℕ) (hp : p.Prime)
    (hdvd : p ∣ (6 * j) ^ 2 + 1) (hinert : p % 3 = 2) :
    p % 12 = 5 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h : (6 * j) ^ 2 + 1 = 2 * (18 * j ^ 2) + 1 := by ring
    rw [h] at hdvd
    omega
  have h0 : (6 * (j : ZMod p)) ^ 2 = -1 := by
    have hz : (((6 * j) ^ 2 + 1 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
    push_cast at hz
    linear_combination hz
  have hsq : IsSquare (-1 : ZMod p) := ⟨6 * (j : ZMod p), by linear_combination -h0⟩
  have h4 : p % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsq
  have hodd : p % 2 = 1 := (hp.eq_two_or_odd).resolve_left hp2
  omega

end D5.S3.Arith.Congruence.InertPrimeMod12
