/- GID: D5/S3/Arith/CounterSequences/KimberlingA371279
   generality: I
   mirror-B: D5/B/S3/Arith/CounterSequences/KimberlingA371279
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: First-retention cumulative generation covers every positive rational at most one. -/

import Mathlib.Data.Rat.Defs
import Mathlib.Data.List.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.CounterSequences.KimberlingA371279

/-- A left-to-right scan retaining the first occurrence of every value. -/
def firstRetentionAux : List ℚ → List ℚ → List ℚ
  | _, [] => []
  | seen, x :: xs =>
      if x ∈ seen then firstRetentionAux seen xs
      else x :: firstRetentionAux (x :: seen) xs

/-- The source's first-occurrence operation. -/
def firstRetention (xs : List ℚ) : List ℚ := firstRetentionAux [] xs

theorem firstRetentionAux_mem_iff (seen xs : List ℚ) (x : ℚ) :
    x ∈ firstRetentionAux seen xs ↔ x ∈ xs ∧ x ∉ seen := by
  induction xs generalizing seen with
  | nil => simp [firstRetentionAux]
  | cons a xs ih =>
      by_cases ha : a ∈ seen
      · simp [firstRetentionAux, ha, ih]
      · simp only [firstRetentionAux, if_neg ha, List.mem_cons, ih]
        constructor
        · intro h
          rcases h with h | h
          · exact ⟨Or.inl rfl, by simpa [h] using ha⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · rintro ⟨hmem, hseen⟩
          rcases hmem with rfl | hmem
          · exact Or.inl rfl
          · exact Or.inr ⟨hmem, by simpa using hseen⟩

theorem firstRetention_mem_iff (xs : List ℚ) (x : ℚ) :
    x ∈ firstRetention xs ↔ x ∈ xs := by
  simpa [firstRetention] using firstRetentionAux_mem_iff ([] : List ℚ) xs x

theorem firstRetention_nodup (xs : List ℚ) : (firstRetention xs).Nodup := by
  unfold firstRetention
  induction xs with
  | nil => simp [firstRetentionAux]
  | cons a xs ih =>
      by_cases ha : a ∈ ([] : List ℚ)
      · simp [firstRetentionAux, ha, ih]
      · simp only [firstRetentionAux, if_neg ha]
        apply List.nodup_cons.mpr
        refine ⟨?_, ih⟩
        intro h
        rw [firstRetentionAux_mem_iff] at h
        exact h.2 (by simp)

/-- The complete ordered pair list, with the outer index first. -/
def pairList (xs : List ℚ) : List ℚ :=
  xs.flatMap (fun x => xs.map (fun y => x / (1 + y)))

theorem pairList_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ pairList xs ↔ ∃ x ∈ xs, ∃ y ∈ xs, z = x / (1 + y) := by
  simp [pairList, List.mem_flatMap]

/-- New values are first-retained among the pair list, while the old prefix is untouched. -/
def freshTail (xs : List ℚ) : List ℚ :=
  firstRetention ((pairList xs).filter (fun z => z ∉ xs))

def nextList (xs : List ℚ) : List ℚ := xs ++ freshTail xs

theorem freshTail_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ freshTail xs ↔ z ∈ pairList xs ∧ z ∉ xs := by
  simp [freshTail, firstRetention_mem_iff]

theorem nextList_mem_iff (xs : List ℚ) (z : ℚ) :
    z ∈ nextList xs ↔ z ∈ xs ∨ ∃ x ∈ xs, ∃ y ∈ xs, z = x / (1 + y) := by
  rw [nextList, List.mem_append, freshTail_mem_iff, pairList_mem_iff]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr ⟨h, by
        intro hz
        rcases h with ⟨x, hx, y, hy, rfl⟩
        exact hz⟩

theorem freshTail_nodup (xs : List ℚ) : (freshTail xs).Nodup := by
  exact firstRetention_nodup _

theorem nextList_nodup {xs : List ℚ} (hxs : xs.Nodup) : (nextList xs).Nodup := by
  apply List.Nodup.append hxs (freshTail_nodup xs)
  intro z hzxs hzfresh
  exact (freshTail_mem_iff xs z).mp hzfresh |>.2 hzxs

theorem nextList_prefix (xs : List ℚ) : xs <+: nextList xs := by
  exact ⟨freshTail xs, rfl⟩

/-- The cumulative lists `U₁, U₂, ...`, represented with `cumulative 0 = U₁`. -/
def cumulative : ℕ → List ℚ
  | 0 => [1]
  | n + 1 => nextList (cumulative n)

theorem cumulative_nodup (n : ℕ) : (cumulative n).Nodup := by
  induction n with
  | zero => simp [cumulative]
  | succ n ih => exact nextList_nodup ih

theorem cumulative_prefix (n : ℕ) : cumulative n <+: cumulative (n + 1) := by
  simpa [cumulative] using nextList_prefix (cumulative n)

theorem cumulative_mono {m n : ℕ} (hmn : m ≤ n) :
    ∀ z ∈ cumulative m, z ∈ cumulative n := by
  induction n, hmn using Nat.le_induction with
  | base => exact fun z hz => hz
  | succ n hmn ih =>
      intro z hz
      exact (cumulative_prefix n).mem hz |>.trans (ih z)

theorem cumulative_one_mem (n : ℕ) : (1 : ℚ) ∈ cumulative n := by
  exact cumulative_mono (Nat.zero_le n) 1 (by simp [cumulative])

theorem coverage_q : ∀ q p : ℕ, 1 ≤ p → p ≤ q →
    ((p : ℚ) / (q : ℚ)) ∈ cumulative q := by
  intro q
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro p hp hpq
      by_cases hpeq : p = q
      · subst q
        simpa [div_self (by exact_mod_cast hp.ne')]
          using cumulative_one_mem p
      have hpq' : p < q := by omega
      by_cases hdiag : 2 * p ≤ q
      · have hd : 1 ≤ q - p := by omega
        have hlt : q - p < q := by omega
        have hpd : p ≤ q - p := by omega
        have ht := ih (q - p) hlt p hp hpd
        have ht' : ((p : ℚ) / ((q - p : ℕ) : ℚ)) ∈ cumulative q :=
          cumulative_mono (by omega) ht
        have hpair : (p : ℚ) / (q : ℚ) =
            ((p : ℚ) / ((q - p : ℕ) : ℚ)) /
              (1 + (p : ℚ) / ((q - p : ℕ) : ℚ)) := by
          have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : 0 < q)
          have hdq : ((q - p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : 0 < q - p)
          field_simp [hq, hdq]
          ring
        rw [hpair]
        exact (nextList_mem_iff (cumulative q) _).mpr
          (Or.inr ⟨_, ht', _, ht', rfl⟩)
      · have ha : 1 ≤ q - p := by omega
        have hlt : p < q := hpq'
        have hat := ih p hlt (q - p) ha (by omega)
        have hat' : ((q - p : ℕ) : ℚ) / (p : ℚ) ∈ cumulative q :=
          cumulative_mono (by omega) hat
        have hone : (1 : ℚ) ∈ cumulative q := cumulative_one_mem q
        have hpair : (p : ℚ) / (q : ℚ) =
            (1 : ℚ) / (1 + ((q - p : ℕ) : ℚ) / (p : ℚ)) := by
          have hq : (q : ℚ) ≠ 0 := by exact_mod_cast (by omega : 0 < q)
          have hpq0 : (p : ℚ) ≠ 0 := by exact_mod_cast (by omega : 0 < p)
          field_simp [hq, hpq0]
          ring
        rw [hpair]
        exact (nextList_mem_iff (cumulative q) _).mpr
          (Or.inr ⟨1, hone, _, hat', rfl⟩)

/-- Every rational in `(0,1]` occurs in the exact first-retention cumulative run. -/
theorem every_rational_interval (r : ℚ) (hr : 0 < r) (hr1 : r ≤ 1) :
    r ∈ cumulative r.den := by
  have hnum : 0 < r.num := Rat.num_pos.mpr hr
  have hden : 0 < r.den := r.den_pos
  have hfrac : (r.num : ℚ) / (r.den : ℚ) ≤ 1 := by
    simpa [r.num_div_den] using hr1
  have hnumdenQ : (r.num : ℚ) ≤ (r.den : ℚ) := by
    exact (div_le_iff₀ (by exact_mod_cast hden)).mp hfrac
  have hnumden : r.num ≤ (r.den : ℤ) := by exact_mod_cast hnumdenQ
  let p : ℕ := r.num.natAbs
  have hpcast : (p : ℤ) = r.num := by
    simpa [p] using (Int.natAbs_of_nonneg (le_of_lt hnum))
  have hp : 1 ≤ p := by
    exact_mod_cast hnum
  have hpq : p ≤ r.den := by
    exact_mod_cast hnumden
  have h := coverage_q r.den p hp hpq
  simpa [hpcast, p, Rat.num_div_den] using h

end D5.S3.Arith.CounterSequences.KimberlingA371279
