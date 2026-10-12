/- GID: D5/S3/Combinatorics/Games/DivisorNimGrundy
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Games/DivisorNimGrundy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The multiset game and its well-founded Sprague--Grundy recursion. -/

import D5.S0.Certificates.Games.CrimGrundyRefutation
import Mathlib.Data.Multiset.FinsetOps
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Finset.PImage
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.WellFounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Games.DivisorNimGrundy

abbrev Position := Multiset ℕ

def Positive (P : Position) : Prop := ∀ h ∈ P, 0 < h

def dividesAll (d : ℕ) (P : Position) : Prop := ∀ h ∈ P, d ∣ h

def successor (P : Position) (h d : ℕ) : Position :=
  P.erase h + if h - d = 0 then 0 else {h - d}

def legal (P : Position) (h d : ℕ) : Prop :=
  0 < d ∧ d ≤ h ∧ dividesAll d (P.erase h)

noncomputable def moves (P : Position) : Finset Position := by
  classical
  exact P.toFinset.biUnion (fun h =>
    ((Finset.Icc 1 h).filter (fun d => legal P h d)).image (successor P h))

theorem successor_sum_lt (P : Position) {h d : ℕ} (hd : legal P h d)
    (hh : h ∈ P) : (successor P h d).sum < P.sum := by
  have hs : h + (P.erase h).sum = P.sum := by
    simpa using (Multiset.sum_map_erase (f := id) hh)
  have hpos : 0 < h := lt_of_lt_of_le hd.1 hd.2.1
  have hdpos := hd.1
  have hdle := hd.2.1
  by_cases hz : h - d = 0
  · simp only [successor, hz, if_true, Multiset.sum_add, Multiset.sum_zero]
    omega
  · simp only [successor, hz, if_false, Multiset.sum_add, Multiset.sum_singleton]
    omega

open D5.S0.Certificates.Games.CrimGrundyRefutation (mex mex_spec)

noncomputable def grundy : Position → ℕ :=
  (measure Multiset.sum).wf.fix
    (fun P rec =>
      mex ((moves P).attach.image (fun q =>
        rec q.1 (by
          have hq : q.1 ∈ moves P := q.2
          simp only [moves, Finset.mem_biUnion, Finset.mem_image,
            Finset.mem_filter] at hq
          rcases hq with ⟨h, hh, d, hd, hsucc⟩
          rw [← hsucc]
          exact successor_sum_lt P hd.2 (Multiset.mem_toFinset.mp hh)))))

theorem move_sum_lt {P Q : Position} (hq : Q ∈ moves P) : Q.sum < P.sum := by
  classical
  simp only [moves, Finset.mem_biUnion, Finset.mem_image, Finset.mem_filter] at hq
  rcases hq with ⟨h, hh, d, hd, rfl⟩
  exact successor_sum_lt P hd.2 (Multiset.mem_toFinset.mp hh)

theorem grundy_eq (P : Position) :
    grundy P = mex ((moves P).image grundy) := by
  classical
  rw [grundy, WellFounded.fix_eq]
  congr 1
  ext n
  simp only [Finset.mem_image, Finset.mem_attach]
  constructor
  · rintro ⟨q, _, hq⟩
    exact ⟨q.1, q.2, hq⟩
  · rintro ⟨q, hq, hn⟩
    exact ⟨⟨q, hq⟩, by simp, hn⟩

theorem grundy_not_follower (P : Position) : grundy P ∉ (moves P).image grundy := by
  rw [grundy_eq]
  exact (mex_spec _).1

theorem follower_mem_of_lt (P : Position) {n : ℕ} (hn : n < grundy P) :
    n ∈ (moves P).image grundy := by
  rw [grundy_eq] at hn
  exact (mex_spec _).2 n hn

theorem mex_le_card (s : Finset ℕ) : mex s ≤ s.card := by
  have hsub : Finset.range (mex s) ⊆ s := by
    intro n hn
    exact (mex_spec s).2 n (Finset.mem_range.mp hn)
  simpa only [Finset.card_range] using Finset.card_le_card hsub

/-- Only distinct exceptional values are counted beyond the initial interval. -/
theorem mex_counting (s E : Finset ℕ) (B : ℕ)
    (hcover : ∀ n ∈ s, n ≤ B ∨ n ∈ E) : mex s ≤ B + E.card + 1 := by
  have hsub : s ⊆ Finset.range (B + 1) ∪ E := by
    intro n hn
    rcases hcover n hn with h | h
    · exact Finset.mem_union_left E (Finset.mem_range.mpr (by omega))
    · exact Finset.mem_union_right _ h
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simp only [Finset.card_range] at hc
  exact (mex_le_card s).trans (by omega)

/-- Exceptional followers contribute at most their number of distinct boards. -/
theorem grundy_counting (P : Position) (E : Finset Position) (B : ℕ)
    (hcover : ∀ Q ∈ moves P, grundy Q ≤ B ∨ Q ∈ E) :
    grundy P ≤ B + E.card + 1 := by
  classical
  rw [grundy_eq]
  have h := mex_counting ((moves P).image grundy) (E.image grundy) B (by
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨Q, hQ, rfl⟩
    rcases hcover Q hQ with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_image.mpr ⟨Q, h, rfl⟩))
  have hc := Finset.card_image_le (s := E) (f := grundy)
  omega

theorem grundy_le_of_followers (P : Position) (B : ℕ)
    (hbound : ∀ Q ∈ moves P, grundy Q ≤ B) : grundy P ≤ B + 1 := by
  simpa using grundy_counting P ∅ B (fun Q hQ => Or.inl (hbound Q hQ))

theorem grundy_zero_iff (P : Position) :
    grundy P = 0 ↔ ∀ Q ∈ moves P, grundy Q ≠ 0 := by
  classical
  constructor
  · intro h Q hQ hz
    apply grundy_not_follower P
    exact Finset.mem_image.mpr ⟨Q, hQ, hz.trans h.symm⟩
  · intro h
    by_contra hn
    have hpos : 0 < grundy P := Nat.pos_of_ne_zero hn
    rcases Finset.mem_image.mp (follower_mem_of_lt P hpos) with ⟨Q, hQ, hz⟩
    exact h Q hQ hz

def claim : Prop :=
  ∀ P : Position, Positive P → P ≠ 0 →
    ∀ m ∈ P, (∀ h ∈ P, m ≤ h) → grundy P ≤ 2 * m

end D5.S3.Combinatorics.Games.DivisorNimGrundy
