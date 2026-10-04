/- GID: D5/S1/Words/ClosedRunStarts
   generality: I
   mirror-B: D5/B/S1/Words/ClosedRunStarts
   mirror-E: none(waiver:symbolic-proof-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Scanner legality and declumped starts agree on closed Boolean words. -/

import D5.S0.Tower.DBonacci.Names

open scoped BigOperators

namespace D5.S1.Words.ClosedRunStarts

open D5.S0.Tower.DBonacci.Names

/-- A literal contiguous block of `k` true bits, wholly inside the closed word. -/
def TrueBlock {n : ℕ} (word : Fin n → Bool) (s k : ℕ) : Prop :=
  s + k ≤ n ∧ ∀ j : Fin n, s ≤ j.val → j.val < s + k → word j = true

/-- A block starts a true run when its predecessor, if present, is false. -/
def RunStart {n : ℕ} (word : Fin n → Bool) (k s : ℕ) : Prop :=
  TrueBlock word s k ∧ ∀ j : Fin n, j.val + 1 = s → word j = false

/-- The number of possible starts in a closed length-`n` word. -/
def startPositions (n k : ℕ) : ℕ := n - k + 1

/-- Count run beginnings rather than overlapping windows inside a long run. -/
noncomputable def startCount {n : ℕ} (k : ℕ) (word : Fin n → Bool) : ℕ := by
  classical
  exact ∑ i : Fin (startPositions n k), if RunStart word k i.val then 1 else 0

/-- Literal block avoidance agrees both with the scanner and with absence of run starts. -/
theorem closed_word_run_start_equivalence (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n)
    (word : Fin n → Bool) :
    (DBonacciAdmissible k n word ↔ ∀ s : ℕ, ¬ TrueBlock word s k) ∧
    ((∀ s : ℕ, ¬ TrueBlock word s k) ↔ startCount k word = 0) := by
  classical
  have scanner : ∀ (q maxTrue fuel : ℕ) (w : Fin q → Bool), fuel ≤ maxTrue →
      (runAdmissible maxTrue fuel q w = true ↔
        ¬ TrueBlock w 0 (fuel + 1) ∧ ∀ s : ℕ, ¬ TrueBlock w s (maxTrue + 1)) := by
    intro q
    induction q with
    | zero =>
        intro maxTrue fuel w hfm
        simp [runAdmissible, TrueBlock]
    | succ q ih =>
        intro maxTrue fuel w hfm
        have shift : ∀ s d : ℕ,
            TrueBlock (Fin.tail w) s d ↔ TrueBlock w (s + 1) d := by
          intro s d
          constructor
          · rintro ⟨hlen, hall⟩
            refine ⟨by omega, ?_⟩
            intro j hjlo hjhi
            have hjpos : 0 < j.val := by omega
            let j' : Fin q := ⟨j.val - 1, by omega⟩
            have heq : j'.succ = j := by apply Fin.ext; simp [j']; omega
            rw [← heq]
            exact hall j' (by simp [j']; omega) (by simp [j']; omega)
          · rintro ⟨hlen, hall⟩
            refine ⟨by omega, ?_⟩
            intro j hjlo hjhi
            exact hall j.succ (by simpa using Nat.add_le_add_right hjlo 1)
              (by simp; omega)
        cases hhead : w 0 with
        | false =>
            have prefixBlock : ∀ d : ℕ, 0 < d → ¬ TrueBlock w 0 d := by
              intro d hd hb
              have h := hb.2 0 (by simp) (by simpa using hd)
              simp [hhead] at h
            have tailBlocks :
                (∀ s : ℕ, ¬ TrueBlock w s (maxTrue + 1)) ↔
                (∀ s : ℕ, ¬ TrueBlock (Fin.tail w) s (maxTrue + 1)) := by
              constructor
              · intro h s hb
                exact h (s + 1) ((shift s (maxTrue + 1)).mp hb)
              · intro h s hb
                cases s with
                | zero => exact prefixBlock _ (by omega) hb
                | succ s => exact h s ((shift s (maxTrue + 1)).mpr hb)
            have tailPrefix : (∀ s : ℕ, ¬ TrueBlock (Fin.tail w) s (maxTrue + 1)) →
                ¬ TrueBlock (Fin.tail w) 0 (maxTrue + 1) := fun h => h 0
            cases fuel <;>
              simp only [runAdmissible, hhead, Bool.false_eq_true, ↓reduceIte]
            all_goals
              rw [ih maxTrue maxTrue (Fin.tail w) le_rfl]
              constructor
              · intro h
                exact ⟨prefixBlock _ (by omega), tailBlocks.mpr h.2⟩
              · intro h
                exact ⟨tailPrefix (tailBlocks.mp h.2), tailBlocks.mp h.2⟩
        | true =>
            cases fuel with
            | zero =>
                have hb : TrueBlock w 0 1 := by
                  refine ⟨by omega, ?_⟩
                  intro j hjlo hjhi
                  have hj : j = 0 := by
                    apply Fin.ext
                    change j.val = 0
                    omega
                  simpa [hj] using hhead
                simp [runAdmissible, hhead, hb]
            | succ fuel =>
                have prefixBlock : TrueBlock w 0 (fuel + 1 + 1) ↔
                    TrueBlock (Fin.tail w) 0 (fuel + 1) := by
                  constructor
                  · rintro ⟨hlen, hall⟩
                    refine ⟨by omega, ?_⟩
                    intro j hjlo hjhi
                    exact hall j.succ (by omega) (by simp; omega)
                  · rintro ⟨hlen, hall⟩
                    refine ⟨by omega, ?_⟩
                    intro j hjlo hjhi
                    by_cases hj : j.val = 0
                    · have heq : j = 0 := Fin.ext hj
                      simpa [heq] using hhead
                    · let j' : Fin q := ⟨j.val - 1, by omega⟩
                      have heq : j'.succ = j := by apply Fin.ext; simp [j']; omega
                      rw [← heq]
                      exact hall j' (by omega) (by simp [j']; omega)
                have firstBlock : TrueBlock w 0 (maxTrue + 1) →
                    TrueBlock w 0 (fuel + 1 + 1) := by
                  rintro ⟨hlen, hall⟩
                  refine ⟨by omega, ?_⟩
                  intro j hjlo hjhi
                  exact hall j hjlo (by omega)
                simp only [runAdmissible, hhead, ↓reduceIte]
                rw [ih maxTrue fuel (Fin.tail w) (by omega)]
                constructor
                · rintro ⟨hp, ht⟩
                  refine ⟨fun hb => hp (prefixBlock.mp hb), ?_⟩
                  intro s hb
                  cases s with
                  | zero => exact hp (prefixBlock.mp (firstBlock hb))
                  | succ s => exact ht s ((shift s (maxTrue + 1)).mpr hb)
                · rintro ⟨hp, ht⟩
                  refine ⟨fun hb => hp (prefixBlock.mpr hb), ?_⟩
                  intro s hb
                  exact ht (s + 1) ((shift s (maxTrue + 1)).mp hb)
  constructor
  · obtain ⟨maxTrue, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    change runAdmissible maxTrue maxTrue n word = true ↔ _
    rw [scanner n maxTrue maxTrue word le_rfl]
    exact ⟨fun h => h.2, fun h => ⟨h 0, h⟩⟩
  · have zeroCount : startCount k word = 0 ↔
        ∀ i : Fin (startPositions n k), ¬ RunStart word k i.val := by
      simp [startCount]
    rw [zeroCount]
    constructor
    · intro h i hs
      exact h i.val hs.1
    · intro h s hb
      have existsBlock : ∃ t : ℕ, TrueBlock word t k := ⟨s, hb⟩
      let t := Nat.find existsBlock
      have ht : TrueBlock word t k := Nat.find_spec existsBlock
      have hlen := ht.1
      have htbound : t < startPositions n k := by
        simp only [startPositions]
        omega
      apply h ⟨t, htbound⟩
      change RunStart word k t
      refine ⟨ht, ?_⟩
      intro j hj
      cases hbit : word j with
      | false => rfl
      | true =>
          have prev : TrueBlock word j.val k := by
            refine ⟨by omega, ?_⟩
            intro a halo hahi
            by_cases ha : a.val = j.val
            · have heq : a = j := Fin.ext ha
              simpa [heq] using hbit
            · exact ht.2 a (by omega) (by omega)
          exact False.elim ((Nat.find_min existsBlock (by omega : j.val < t)) prev)

end D5.S1.Words.ClosedRunStarts
