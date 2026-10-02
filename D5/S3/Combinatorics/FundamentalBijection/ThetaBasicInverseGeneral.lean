/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicInverseGeneral
   mirror-E: none(waiver:record-interval-reconstruction)
   anchors: [mathlib/module/Mathlib.Data.List.Intervals]
   utility: none
   digest: Record intervals reconstruct a permutation from its inverse cycles. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks
import Mathlib.Data.List.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.ArrowWilfDefs
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
open D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseBlocks

/-- The next marked position, with the end of the word as a sentinel. -/
def nextBoundary (P : ℕ → Prop) [DecidablePred P] (n s : ℕ) : ℕ :=
  if h : s < n then
    Nat.find (show ∃ e, s < e ∧ e ≤ n ∧ (e = n ∨ P e) from
      ⟨n, h, le_refl _, Or.inl rfl⟩)
  else n


/-- Consecutive intervals picked out by a predicate concatenate to the original suffix. -/
theorem filter_interval_partition (p : List ℕ) (P : ℕ → Prop) [DecidablePred P]
    (s : ℕ) (hs : s ≤ p.length) (hstart : s < p.length → P s) :
    ((List.Ico s p.length).filter P).flatMap (fun j =>
      (p.drop j).take (nextBoundary P p.length j - j)) = p.drop s := by
  induction hdist : p.length - s using Nat.strong_induction_on generalizing s with
  | h d ih =>
    by_cases hend : s = p.length
    · subst s
      simp
    · have hsn : s < p.length := by omega
      let e := nextBoundary P p.length s
      have hb : s < nextBoundary P p.length s ∧
          nextBoundary P p.length s ≤ p.length ∧
          (nextBoundary P p.length s = p.length ∨
            P (nextBoundary P p.length s)) ∧
          ∀ j, s < j → j < nextBoundary P p.length s → ¬ P j := by
        unfold nextBoundary
        simp only [dif_pos hsn]
        let Q : ℕ → Prop := fun e => s < e ∧ e ≤ p.length ∧
          (e = p.length ∨ P e)
        have hex : ∃ e, Q e :=
          ⟨p.length, hsn, le_refl _, Or.inl rfl⟩
        have hfind : Q (Nat.find hex) := Nat.find_spec hex
        refine ⟨hfind.1, hfind.2.1, hfind.2.2, ?_⟩
        intro j hsj hjb hjP
        have hmin : Nat.find hex ≤ j :=
          Nat.find_min' hex ⟨hsj, by omega, Or.inr hjP⟩
        omega
      have hse : s < e := hb.1
      have hen : e ≤ p.length := hb.2.1
      have hsplit : List.Ico s p.length =
          s :: (List.Ico (s + 1) e ++ List.Ico e p.length) := by
        rw [List.Ico.eq_cons hsn,
          ← List.Ico.append_consecutive (by omega : s + 1 ≤ e) hen]
      have hmiddle : (List.Ico (s + 1) e).filter P = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro j hj
        obtain ⟨hjl, hjr⟩ := List.Ico.mem.mp hj
        simp [hb.2.2.2 j (by omega) hjr]
      have hfiltered : ((List.Ico s p.length).filter P) =
          s :: ((List.Ico e p.length).filter P) := by
        rw [hsplit]
        simp [hstart hsn, hmiddle]
      have htail : ((List.Ico e p.length).filter P).flatMap (fun j =>
          (p.drop j).take (nextBoundary P p.length j - j)) = p.drop e := by
        by_cases heq : e = p.length
        · simp [heq, List.Ico.self_empty]
        · have heP : P e := hb.2.2.1.resolve_left heq
          apply ih (p.length - e) (by omega) e hen
          · intro _
            exact heP
          · rfl
      rw [hfiltered, List.flatMap_cons, htail]
      change (p.drop s).take (e - s) ++ p.drop e = p.drop s
      simpa only [show s + (e - s) = e by omega] using
        List.drop_take_append_drop p s (e - s)

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverseGeneral
