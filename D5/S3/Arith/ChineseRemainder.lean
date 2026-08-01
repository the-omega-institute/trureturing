/- GID: D5/S3/Arith/ChineseRemainder
   generality: G
   mirror-B: D5/B/S3/Arith/ChineseRemainder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The natural map modulo coprime factors is bijective. -/

import Mathlib.Data.ZMod.Basic

namespace D5.S3.Arith.ChineseRemainder

/-- The Blueprint atom uses injectivity plus finite counting; Mathlib supplies
the same natural map as a ring equivalence, so its bijectivity is the faithful
assembly of that skeleton (precedent 6.1). -/
theorem chinese_remainder_bijective (m n : ℕ) (h : Nat.Coprime m n) :
    Function.Bijective
      (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff])
        (ZMod m × ZMod n)) :=
  (ZMod.chineseRemainder h).bijective

end D5.S3.Arith.ChineseRemainder
