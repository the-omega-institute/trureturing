/- GID: D5/S0/Rewriting/GuardedBoxPathAttainment
   generality: G
   mirror-B: D5/B/S0/Rewriting/GuardedBoxPathAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every pair of bounded natural configurations admits a shortest guarded unit word whose length is its coordinate distance. -/

import D5.S0.Rewriting.GuardedBoxPaths
import Mathlib.Data.Int.NatAbs

set_option autoImplicit false

namespace D5.S0.Rewriting.GuardedBoxPathAttainment

open GuardedBoxPaths

/-- Two configurations in a finite capacity box are joined by a successful unit word
whose length is their total absolute coordinate difference and is minimal among all
successful words with those endpoints. -/
theorem exists_shortest_word {P : Type*} [DecidableEq P] [Fintype P]
    (A a b : P → ℕ) (ha : ∀ p, a p ≤ A p) (hb : ∀ p, b p ≤ A p) :
    ∃ w : List (Instruction P), LegalPath A a b w ∧ w.length = distance a b ∧
      ∀ v : List (Instruction P), LegalPath A a b v → w.length ≤ v.length := by
  classical
  have attain : ∀ n (c : P → ℕ), distance c b = n → (∀ p, c p ≤ A p) →
      ∃ w : List (Instruction P), eval A c w = some b ∧ w.length = distance c b := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro c hn hc
      by_cases hcb : c = b
      · subst c
        exact ⟨[], rfl, by simp [distance]⟩
      obtain ⟨p, hp⟩ : ∃ p, c p ≠ b p := Function.ne_iff.mp hcb
      have update_distance (z : ℕ)
          (hz : ((b p : ℤ) - (z : ℤ)).natAbs + 1 =
            ((b p : ℤ) - (c p : ℤ)).natAbs) :
          distance (Function.update c p z) b + 1 = distance c b := by
        have hold := Finset.sum_erase_add Finset.univ
          (fun q => ((b q : ℤ) - (c q : ℤ)).natAbs) (Finset.mem_univ p)
        have hnew := Finset.sum_erase_add Finset.univ
          (fun q => ((b q : ℤ) - (Function.update c p z q : ℤ)).natAbs)
          (Finset.mem_univ p)
        have heq : (∑ q ∈ Finset.univ.erase p,
            ((b q : ℤ) - (Function.update c p z q : ℤ)).natAbs) =
            ∑ q ∈ Finset.univ.erase p, ((b q : ℤ) - (c q : ℤ)).natAbs := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hq)]
        simp only [Function.update_self] at hnew
        unfold distance
        omega
      have next : ∃ (s : Instruction P) (d : P → ℕ),
          step A c s = some d ∧ (∀ q, d q ≤ A q) ∧
          distance d b + 1 = distance c b := by
        rcases lt_or_gt_of_ne hp with hup | hdown
        · let d := Function.update c p (c p + 1)
          have hguard : c p < A p := hup.trans_le (hb p)
          refine ⟨(p, true), d, ?_, ?_, ?_⟩
          · simp [step, hguard, d]
          · intro q
            by_cases hqp : q = p
            · subst q
              simpa [d] using (show c p + 1 ≤ A p by omega)
            · simpa [d, Function.update_of_ne hqp] using hc q
          · apply update_distance
            rw [Int.natAbs_natCast_sub_natCast_of_ge (by omega),
              Int.natAbs_natCast_sub_natCast_of_ge hup.le]
            omega
        · let d := Function.update c p (c p - 1)
          have hguard : 0 < c p := by omega
          refine ⟨(p, false), d, ?_, ?_, ?_⟩
          · simp [step, hguard, d]
          · intro q
            by_cases hqp : q = p
            · subst q
              simpa [d] using (show c p - 1 ≤ A p by have := hc p; omega)
            · simpa [d, Function.update_of_ne hqp] using hc q
          · apply update_distance
            rw [Int.natAbs_natCast_sub_natCast_of_le (by omega),
              Int.natAbs_natCast_sub_natCast_of_le hdown.le]
            omega
      obtain ⟨s, d, hs, hd, hdist⟩ := next
      have hlt : distance d b < n := by omega
      obtain ⟨w, hw, hlen⟩ := ih (distance d b) hlt d rfl hd
      refine ⟨s :: w, ?_, ?_⟩
      · simpa only [eval, hs, Option.bind_some] using hw
      · simp only [List.length_cons, hlen]
        exact hdist
  obtain ⟨w, hw, hlen⟩ := attain (distance a b) a rfl ha
  refine ⟨w, ⟨ha, hw⟩, hlen, ?_⟩
  intro v hv
  rw [hlen]
  exact (path_lower_bound A a b v hv).2.2.1

end D5.S0.Rewriting.GuardedBoxPathAttainment
