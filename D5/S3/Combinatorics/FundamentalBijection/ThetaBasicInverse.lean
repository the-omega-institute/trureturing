/- GID: D5/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse
   generality: G
   mirror-B: D5/B/S3/Combinatorics/FundamentalBijection/ThetaBasicInverse
   mirror-E: none(waiver:inverse-bijection-uses-one-line-permutation-data)
   anchors: [mathlib/module/Mathlib.GroupTheory.Perm.Cycle.Concrete]
   utility: none
   digest: Prefix-record dominance and injectivity of record-block rotation. -/

import D5.S3.Combinatorics.FundamentalBijection.ThetaFixedDefs
import Mathlib.GroupTheory.Perm.Cycle.Concrete

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse

local notation "B" =>
  (fun p : List ℕ =>
    List.map (D5.S3.Combinatorics.ArrowWilfDefs.hat p)
      (List.range' 1 (List.length p)))

open D5.S3.Combinatorics.ArrowWilfDefs

/-- The last left-to-right maximum seen at a position dominates the whole prefix.
This identifies the first entry of each record block as its maximum. -/
theorem last_record_bounds_prefix (p : List ℕ) (i : ℕ) (hi : i < p.length) :
    ∀ j ≤ i,
      p.getD j 0 ≤ p.getD (Nat.findGreatest (IsLtrMax p) i) 0 := by
  induction i with
  | zero =>
      intro j hj
      have : j = 0 := by omega
      subst j
      simp
  | succ i ih =>
      have hprev : i < p.length := by omega
      rw [Nat.findGreatest_succ]
      by_cases hrec : IsLtrMax p (i + 1)
      · simp only [if_pos hrec]
        intro j hj
        by_cases hji : j = i + 1
        · subst j
          exact le_refl _
        · exact (hrec j (by omega)).le
      · simp only [if_neg hrec]
        have hnew : p.getD (i + 1) 0 ≤
            p.getD (Nat.findGreatest (IsLtrMax p) i) 0 := by
          by_contra hle
          have hgt : p.getD (Nat.findGreatest (IsLtrMax p) i) 0 <
              p.getD (i + 1) 0 := by omega
          apply hrec
          intro j hj
          exact (ih hprev j (by omega)).trans_lt hgt
        intro j hj
        by_cases hji : j = i + 1
        · subst j
          exact hnew
        · exact ih hprev j (by omega)

/-- Each entry has a distinct successor under record-block rotation. -/
theorem hat_inj_on (p : List ℕ) (hp : p.Nodup) :
    ∀ x ∈ p, ∀ y ∈ p, hat p x = hat p y → x = y := by
  have hzero : IsLtrMax p 0 := by
    intro j hj
    omega
  have hgetidx (i : ℕ) (hi : i < p.length) : p.idxOf (p.getD i 0) = i := by
    rw [List.getD_eq_getElem _ 0 hi]
    simpa using (List.get_idxOf hp ⟨i, hi⟩)
  have htarget (z : ℕ) (hz : z ∈ p) :
      p.idxOf (hat p z) =
        if p.idxOf z + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf z + 1)
        then p.idxOf z + 1 else Nat.findGreatest (IsLtrMax p) (p.idxOf z) := by
    have hzidx : p.idxOf z < p.length := List.idxOf_lt_length_of_mem hz
    unfold hat
    dsimp only
    by_cases hb : p.idxOf z + 1 < p.length ∧ ¬ IsLtrMax p (p.idxOf z + 1)
    · rw [if_pos hb, if_pos hb]
      exact hgetidx _ hb.1
    · rw [if_neg hb, if_neg hb]
      exact hgetidx _ (lt_of_le_of_lt (Nat.findGreatest_le _) hzidx)
  intro x hx y hy hxy
  let i := p.idxOf x
  let j := p.idxOf y
  have hi : i < p.length := List.idxOf_lt_length_of_mem hx
  have hj : j < p.length := List.idxOf_lt_length_of_mem hy
  have hidxeq :
      (if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)
        then i + 1 else Nat.findGreatest (IsLtrMax p) i) =
      (if j + 1 < p.length ∧ ¬ IsLtrMax p (j + 1)
        then j + 1 else Nat.findGreatest (IsLtrMax p) j) := by
    rw [← htarget x hx, ← htarget y hy, hxy]
  have hij : i = j := by
    by_cases hbi : i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)
    · by_cases hbj : j + 1 < p.length ∧ ¬ IsLtrMax p (j + 1)
      · simpa [hbi, hbj] using hidxeq
      · have heq : i + 1 = Nat.findGreatest (IsLtrMax p) j := by
          simpa [hbi, hbj] using hidxeq
        have hr : IsLtrMax p (i + 1) := by
          rw [heq]
          exact Nat.findGreatest_spec (Nat.zero_le j) hzero
        exact (hbi.2 hr).elim
    · by_cases hbj : j + 1 < p.length ∧ ¬ IsLtrMax p (j + 1)
      · have heq : Nat.findGreatest (IsLtrMax p) i = j + 1 := by
          simpa [hbi, hbj] using hidxeq
        have hr : IsLtrMax p (j + 1) := by
          rw [← heq]
          exact Nat.findGreatest_spec (Nat.zero_le i) hzero
        exact (hbj.2 hr).elim
      · have heq : Nat.findGreatest (IsLtrMax p) i =
            Nat.findGreatest (IsLtrMax p) j := by
          simpa [hbi, hbj] using hidxeq
        by_contra hne
        by_cases hlt : i < j
        · have hr : IsLtrMax p (i + 1) := by
            by_contra hnr
            exact hbi ⟨by omega, hnr⟩
          have hlow : i + 1 ≤ Nat.findGreatest (IsLtrMax p) j :=
            Nat.le_findGreatest (by omega) hr
          have hupp := Nat.findGreatest_le (P := IsLtrMax p) i
          omega
        · have hji : j < i := by omega
          have hr : IsLtrMax p (j + 1) := by
            by_contra hnr
            exact hbj ⟨by omega, hnr⟩
          have hlow : j + 1 ≤ Nat.findGreatest (IsLtrMax p) i :=
            Nat.le_findGreatest (by omega) hr
          have hupp := Nat.findGreatest_le (P := IsLtrMax p) j
          omega
  have hgetx : p.getD i 0 = x := by
    rw [List.getD_eq_getElem _ 0 hi]
    exact List.getElem_idxOf hi
  have hgety : p.getD j 0 = y := by
    rw [List.getD_eq_getElem _ 0 hj]
    exact List.getElem_idxOf hj
  calc
    x = p.getD i 0 := hgetx.symm
    _ = p.getD j 0 := by rw [hij]
    _ = y := hgety

end D5.S3.Combinatorics.FundamentalBijection.ThetaBasicInverse
