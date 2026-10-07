/- GID: D5/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits
   generality: G
   mirror-B: D5/B/S1/Words/Palindromes/PeriodDoubling/NonadjacentSignedDigits
   mirror-E: none(waiver:weight-minimal-nonadjacent-signed-digits)
   anchors: []
   utility: none
   digest: Every finite nonadjacent signed binary expansion has minimum signed weight. -/

/-
proof_shape: content (signed_weight_nonadjacent)
escape_witness: List induction forces a zero after each nonzero digit and resolves both signed branches.
admission_basis: escape-witness
Direct frozen dependencies: none; SignedWeight is delivered with this module.
Information-escape registration is paused under CLAUDE.md section 3.9.
-/

import D5.S1.Words.Palindromes.PeriodDoubling.SignedWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Palindromes.PeriodDoubling

/-- Digits are read least significant first; leading zero digits are permitted. -/
theorem signed_weight_nonadjacent (digits : List ℤ)
    (hcoeff : ∀ z ∈ digits, z = -1 ∨ z = 0 ∨ z = 1)
    (hgap : digits.IsChain (fun a b => a = 0 ∨ b = 0)) :
    signedWeight (digits.foldr (fun z acc => z + 2 * acc) 0) =
      (digits.filter (fun z => z != 0)).length := by
  obtain ⟨hzero, hone, hneg, htri, heven, hodd⟩ := signed_weight_arithmetic
  have adjacent (x : ℤ) :
      signedWeight x ≤ signedWeight (x + 1) + 1 ∧
        signedWeight (x + 1) ≤ signedWeight x + 1 := by
    have ha := htri x 1
    have hb := htri (x + 1) (-1)
    have hn := hneg 1
    simp only [hone] at ha hn
    have he : x + 1 + -1 = x := by omega
    rw [he, hn] at hb
    exact ⟨hb, ha⟩
  have low_positive (x : ℤ) : signedWeight (4 * x + 1) = signedWeight x + 1 := by
    have ho := hodd x
    have ha := adjacent x
    have he : 4 * x + 1 = 2 * (2 * x) + 1 := by ring
    rw [he, hodd, heven]
    omega
  have low_negative (x : ℤ) : signedWeight (4 * x - 1) = signedWeight x + 1 := by
    have h := low_positive (-x)
    have he : 4 * (-x) + 1 = -(4 * x - 1) := by ring
    rw [he, hneg, hneg] at h
    exact h
  induction digits with
  | nil => simp [hzero]
  | cons z zs ih =>
    have hz := hcoeff z (by simp)
    have htail : ∀ z ∈ zs, z = -1 ∨ z = 0 ∨ z = 1 := by
      intro z hz
      exact hcoeff z (List.mem_cons_of_mem _ hz)
    have htailgap : zs.IsChain (fun a b => a = 0 ∨ b = 0) := hgap.tail
    have hih := ih htail htailgap
    by_cases hz0 : z = 0
    · subst z
      simpa [heven] using hih
    · cases zs with
      | nil =>
        rcases hz with rfl | h | rfl
        · simpa [hneg, hone] using (show signedWeight (-1) = 1 by rw [hneg, hone])
        · exact (hz0 h).elim
        · simp [hone]
      | cons b bs =>
        have hb : b = 0 := by
          have hpair := (List.isChain_cons_cons.mp hgap).1
          exact hpair.resolve_left hz0
        subst b
        have hval : (z :: 0 :: bs).foldr (fun z acc => z + 2 * acc) 0 =
            z + 4 * bs.foldr (fun z acc => z + 2 * acc) 0 := by
          simp only [List.foldr_cons]
          ring
        have hcount : ((z :: 0 :: bs).filter (fun z => z != 0)).length =
            (bs.filter (fun z => z != 0)).length + 1 := by
          simp [hz0]
        have hi : signedWeight (bs.foldr (fun z acc => z + 2 * acc) 0) =
            (bs.filter (fun z => z != 0)).length := by
          simpa [heven] using hih
        rw [hval, hcount]
        rcases hz with rfl | h | rfl
        · have he : -1 + 4 * bs.foldr (fun z acc => z + 2 * acc) 0 =
              4 * bs.foldr (fun z acc => z + 2 * acc) 0 - 1 := by ring
          rw [he, low_negative, hi]
        · exact (hz0 h).elim
        · have he : 1 + 4 * bs.foldr (fun z acc => z + 2 * acc) 0 =
              4 * bs.foldr (fun z acc => z + 2 * acc) 0 + 1 := by ring
          rw [he, low_positive, hi]

end D5.S1.Words.Palindromes.PeriodDoubling

#print axioms D5.S1.Words.Palindromes.PeriodDoubling.signed_weight_nonadjacent
