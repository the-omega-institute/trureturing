/- GID: D5/S3/PrimeForms/ThreeModFourDescent
   generality: G
   mirror-B: D5/B/S3/PrimeForms/ThreeModFourDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A prime three modulo four dividing a sum of two squares divides both bases. -/

import Mathlib.NumberTheory.LegendreSymbol.Basic

/- Provenance: the modular tool is pinned mathlib's
   `ZMod.mod_four_ne_three_of_sq_eq_neg_sq'` (nonzero squares are never
   negatives of each other modulo a prime three mod four); the descent
   statement itself (`q ∣ a ^ 2 + b ^ 2` forces `q ∣ a` and `q ∣ b`) is not
   in pinned mathlib and is proved here by casting into `ZMod q`. -/

namespace D5.S3.PrimeForms.ThreeModFourDescent

/--
Descent at a prime `q ≡ 3 (mod 4)`: if `q` divides `a ^ 2 + b ^ 2`, then `q`
divides both `a` and `b`.  Otherwise, with `b` a unit modulo `q`, the residue
`(a * b⁻¹) ^ 2` would square to `-1` modulo `q`, which is impossible for
`q % 4 = 3`.
-/
theorem prime_dvd_dvd_of_dvd_sq_add_sq (q a b : ℕ) (hq : q.Prime)
    (h3 : q % 4 = 3) (h : q ∣ a ^ 2 + b ^ 2) : q ∣ a ∧ q ∣ b := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hz : (a : ZMod q) ^ 2 + (b : ZMod q) ^ 2 = 0 := by
    have hcast := (ZMod.natCast_eq_zero_iff (a ^ 2 + b ^ 2) q).mpr h
    push_cast at hcast
    exact hcast
  have hb : (b : ZMod q) = 0 := by
    by_contra hb
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (a : ZMod q)) hb
      (by linear_combination hz) h3
  have ha : (a : ZMod q) = 0 := by
    have hsq : (a : ZMod q) ^ 2 = 0 := by
      rw [hb] at hz
      simpa using hz
    exact sq_eq_zero_iff.mp hsq
  exact ⟨(ZMod.natCast_eq_zero_iff a q).mp ha, (ZMod.natCast_eq_zero_iff b q).mp hb⟩

end D5.S3.PrimeForms.ThreeModFourDescent
