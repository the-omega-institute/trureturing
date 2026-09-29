/- GID: D5/S3/Combinatorics/ArrowWilfCharacterization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/ArrowWilfCharacterization
   mirror-E: none(waiver:structural-characterization-of-the-two-arrow-patterns)
   anchors: [mathlib/module/Mathlib.Data.List.Nodup]
   utility: none
   digest: The two arrow patterns are characterized by ordered pairs around fixed points of the Foata map. -/

import D5.S3.Combinatorics.ArrowWilfDefs
import Mathlib.Data.List.Nodup
import Lean.Elab.Tactic.Omega

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.ArrowWilfCharacterization

open D5.S3.Combinatorics.ArrowWilfDefs

/-- An occurrence of `(12; 3 -> 3)` is an increasing pair below a fixed point. -/
theorem contains_twelve_iff (p : List ℕ) :
    Contains [1, 2] [(3, 3)] 3 p ↔
      ∃ a b f : ℕ, a < b ∧ b < f ∧ a ∈ p ∧ b ∈ p ∧ f ∈ p ∧
        [a, b].Sublist p ∧ hat p f = f := by
  constructor
  · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
    refine ⟨x 1, x 2, x 3, hxlt 1 (by omega) (by omega),
      hxlt 2 (by omega) (by omega), hxmem 1 (by omega) (by omega),
      hxmem 2 (by omega) (by omega), hxmem 3 (by omega) (by omega), ?_, ?_⟩
    · simpa using hxsub
    · exact hxhat (3, 3) (by simp)
  · rintro ⟨a, b, f, hab, hbf, ha, hb, hf, hsub, hhat⟩
    let x : ℕ → ℕ := fun i => if i = 1 then a else if i = 2 then b else f
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · intro i hi hik
      have hi_cases : i = 1 ∨ i = 2 := by omega
      rcases hi_cases with rfl | rfl <;> simp [x, hab, hbf]
    · intro i hi hik
      have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi_cases with rfl | rfl | rfl <;> simp [x, ha, hb, hf]
    · simpa [x] using hsub
    · intro bc hbc
      simp only [List.mem_singleton] at hbc
      subst bc
      simpa [x] using hhat

/-- An occurrence of `(23; 1 -> 1)` is an increasing pair above a fixed point. -/
theorem contains_twenty_three_iff (p : List ℕ) :
    Contains [2, 3] [(1, 1)] 3 p ↔
      ∃ f a b : ℕ, f < a ∧ a < b ∧ f ∈ p ∧ a ∈ p ∧ b ∈ p ∧
        [a, b].Sublist p ∧ hat p f = f := by
  constructor
  · rintro ⟨x, hxlt, hxmem, hxsub, hxhat⟩
    refine ⟨x 1, x 2, x 3, hxlt 1 (by omega) (by omega),
      hxlt 2 (by omega) (by omega), hxmem 1 (by omega) (by omega),
      hxmem 2 (by omega) (by omega), hxmem 3 (by omega) (by omega), ?_, ?_⟩
    · simpa using hxsub
    · exact hxhat (1, 1) (by simp)
  · rintro ⟨f, a, b, hfa, hab, hf, ha, hb, hsub, hhat⟩
    let x : ℕ → ℕ := fun i => if i = 1 then f else if i = 2 then a else b
    refine ⟨x, ?_, ?_, ?_, ?_⟩
    · intro i hi hik
      have hi_cases : i = 1 ∨ i = 2 := by omega
      rcases hi_cases with rfl | rfl <;> simp [x, hfa, hab]
    · intro i hi hik
      have hi_cases : i = 1 ∨ i = 2 ∨ i = 3 := by omega
      rcases hi_cases with rfl | rfl | rfl <;> simp [x, hf, ha, hb]
    · simpa [x] using hsub
    · intro bc hbc
      simp only [List.mem_singleton] at hbc
      subst bc
      simpa [x] using hhat

/-- On a duplicate-free word, `hat` fixes an entry exactly when that entry starts a singleton
    left-to-right-maximum block. -/
theorem hat_fixed_iff {p : List ℕ} (hp : p.Nodup) {f : ℕ} (hf : f ∈ p) :
    hat p f = f ↔
      IsLtrMax p (p.idxOf f) ∧
        (p.idxOf f + 1 = p.length ∨ f < p.getD (p.idxOf f + 1) 0) := by
  let i := p.idxOf f
  have hi : i < p.length := List.idxOf_lt_length_of_mem hf
  have hget : p.getD i 0 = f := by
    rw [List.getD_eq_getElem (l := p) 0 hi, List.getElem_idxOf hi]
  change hat p f = f ↔ IsLtrMax p i ∧
    (i + 1 = p.length ∨ f < p.getD (i + 1) 0)
  constructor
  · intro hfixed
    have hbranch : ¬ (i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)) := by
      intro hbad
      have hnext : p.getD (i + 1) 0 = f := by
        simpa [hat, i, hbad] using hfixed
      have heq : (i + 1 : ℕ) = i := by
        have hsame := hnext.trans hget.symm
        rw [List.getD_eq_getElem (l := p) 0 hbad.1,
          List.getD_eq_getElem (l := p) 0 hi] at hsame
        exact hp.getElem_inj_iff.mp hsame
      omega
    have hgreatest_value : p.getD (Nat.findGreatest (IsLtrMax p) i) 0 = f := by
      simpa [hat, i, hbranch] using hfixed
    have hg_le : Nat.findGreatest (IsLtrMax p) i ≤ i := Nat.findGreatest_le i
    have hg_lt : Nat.findGreatest (IsLtrMax p) i < p.length := lt_of_le_of_lt hg_le hi
    have hg_eq : Nat.findGreatest (IsLtrMax p) i = i := by
      have hsame := hgreatest_value.trans hget.symm
      rw [List.getD_eq_getElem (l := p) 0 hg_lt,
        List.getD_eq_getElem (l := p) 0 hi] at hsame
      exact hp.getElem_inj_iff.mp hsame
    have hltr : IsLtrMax p i := by
      by_cases hi0 : i = 0
      · subst i
        intro j hj
        omega
      · exact Nat.findGreatest_of_ne_zero hg_eq hi0
    refine ⟨hltr, ?_⟩
    by_cases hend : i + 1 = p.length
    · exact Or.inl hend
    · right
      have hnext_lt : i + 1 < p.length := by omega
      have hnext_ltr : IsLtrMax p (i + 1) := by
        by_contra hn
        exact hbranch ⟨hnext_lt, hn⟩
      have hstep := hnext_ltr i (by omega)
      rw [hget] at hstep
      exact hstep
  · rintro ⟨hltr, hend | hnext⟩
    · have hnot : ¬ (i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)) := by omega
      change (if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1) then
        p.getD (i + 1) 0 else p.getD (Nat.findGreatest (IsLtrMax p) i) 0) = f
      rw [if_neg hnot, Nat.findGreatest_eq hltr, hget]
    · have hnext_ltr : IsLtrMax p (i + 1) := by
        intro j hj
        by_cases hji : j = i
        · subst j
          rw [hget]
          exact hnext
        · apply lt_trans (hltr j (by omega))
          rw [hget]
          exact hnext
      have hnot : ¬ (i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1)) := by simp [hnext_ltr]
      change (if i + 1 < p.length ∧ ¬ IsLtrMax p (i + 1) then
        p.getD (i + 1) 0 else p.getD (Nat.findGreatest (IsLtrMax p) i) 0) = f
      rw [if_neg hnot, Nat.findGreatest_eq hltr, hget]

/-- Two distinct members of a duplicate-free word occur in one of the two possible orders. -/
theorem pair_sublist_total {α : Type*} [DecidableEq α] {p : List α} (hp : p.Nodup)
    {a b : α} (hab : a ≠ b) (ha : a ∈ p) (hb : b ∈ p) :
    [a, b].Sublist p ∨ [b, a].Sublist p := by
  induction p with
  | nil => simp at ha
  | cons x p ih =>
      have hp' := hp.of_cons
      by_cases hxa : x = a
      · subst x
        have hbp : b ∈ p := by simpa [hab.symm] using hb
        left
        exact (List.singleton_sublist.mpr hbp).cons_cons a
      · by_cases hxb : x = b
        · subst x
          have hap : a ∈ p := by simpa [hab] using ha
          right
          exact (List.singleton_sublist.mpr hap).cons_cons b
        · have hap : a ∈ p := by simpa [Ne.symm hxa] using ha
          have hbp : b ∈ p := by simpa [Ne.symm hxb] using hb
          rcases ih hp' hap hbp with h | h
          · exact Or.inl (h.cons x)
          · exact Or.inr (h.cons x)

/-- Opposite strict orders of two distinct entries cannot both be sublists of a duplicate-free word. -/
theorem pair_sublist_asymm {α : Type*} [DecidableEq α] {p : List α} (hp : p.Nodup)
    {a b : α} (hab : a ≠ b) : ¬ ([a, b].Sublist p ∧ [b, a].Sublist p) := by
  induction p with
  | nil => simp
  | cons x p ih =>
      intro h
      rcases h with ⟨habp, hbap⟩
      have hp' := hp.of_cons
      by_cases hxa : x = a
      · subst x
        have hamem : a ∈ p := by
          have hdrop : [b, a].Sublist p := hbap.of_cons_of_ne hab.symm
          exact hdrop.subset (by simp)
        exact hp.notMem hamem
      · by_cases hxb : x = b
        · subst x
          have hdrop : [a, b].Sublist p := habp.of_cons_of_ne hab
          have hbmem : b ∈ p := hdrop.subset (by simp)
          exact hp.notMem hbmem
        · have habp' : [a, b].Sublist p := habp.of_cons_of_ne (Ne.symm hxa)
          have hbap' : [b, a].Sublist p := hbap.of_cons_of_ne (Ne.symm hxb)
          exact ih hp' ⟨habp', hbap'⟩

/-- Avoiding `(12; 3 -> 3)` means that all entries below each fixed point are decreasing. -/
theorem avoids_twelve_iff {p : List ℕ} (hp : p.Nodup) :
    ¬ Contains [1, 2] [(3, 3)] 3 p ↔
      ∀ f ∈ p, hat p f = f → ∀ a b : ℕ,
        a < b → b < f → a ∈ p → b ∈ p → [b, a].Sublist p := by
  rw [contains_twelve_iff]
  constructor
  · intro h f hfmem hfix a b hab hbf ha hb
    rcases pair_sublist_total hp (Nat.ne_of_lt hab) ha hb with habp | hbap
    · exact (h ⟨a, b, f, hab, hbf, ha, hb, hfmem, habp, hfix⟩).elim
    · exact hbap
  · intro h hcontains
    rcases hcontains with ⟨a, b, f, hab, hbf, ha, hb, hf, habp, hfix⟩
    have hbap := h f hf hfix a b hab hbf ha hb
    exact pair_sublist_asymm hp (Nat.ne_of_lt hab) ⟨habp, hbap⟩

/-- Avoiding `(23; 1 -> 1)` means that all entries above each fixed point are decreasing. -/
theorem avoids_twenty_three_iff {p : List ℕ} (hp : p.Nodup) :
    ¬ Contains [2, 3] [(1, 1)] 3 p ↔
      ∀ f ∈ p, hat p f = f → ∀ a b : ℕ,
        f < a → a < b → a ∈ p → b ∈ p → [b, a].Sublist p := by
  rw [contains_twenty_three_iff]
  constructor
  · intro h f hfmem hfix a b hfa hab ha hb
    rcases pair_sublist_total hp (Nat.ne_of_lt hab) ha hb with habp | hbap
    · exact (h ⟨f, a, b, hfa, hab, hfmem, ha, hb, habp, hfix⟩).elim
    · exact hbap
  · intro h hcontains
    rcases hcontains with ⟨f, a, b, hfa, hab, hf, ha, hb, habp, hfix⟩
    have hbap := h f hf hfix a b hfa hab ha hb
    exact pair_sublist_asymm hp (Nat.ne_of_lt hab) ⟨habp, hbap⟩

end D5.S3.Combinatorics.ArrowWilfCharacterization
