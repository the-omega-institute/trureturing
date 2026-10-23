/- GID: D5/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Transportation/FerrersIntegerRectanglePaths
   mirror-E: none(waiver:finite-count-paths)
   anchors: []
   utility: none
   digest: Nested legal neighborhoods admit finite integer rectangle paths with fixed margins. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators

namespace D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths

variable {R C : Type*} [Fintype R] [Fintype C] [LinearOrder R] [DecidableEq C]

/-- The table is zero outside the allowed row-column relation. -/
def Supported (E : R → C → Prop) (P : R → C → ℕ) : Prop :=
  ∀ i j, ¬ E i j → P i j = 0

/-- Both complete finite marginal sums agree. -/
def SameMargins (P Q : R → C → ℕ) : Prop :=
  (∀ i, (∑ j, P i j) = ∑ j, Q i j) ∧
  (∀ j, (∑ i, P i j) = ∑ i, Q i j)

private def transfer {A : Type*} [DecidableEq A] (f : A → ℕ) (j k : A) : A → ℕ :=
  fun c => if c = j then f c - 1 else if c = k then f c + 1 else f c

/-- Transfer one count from each diagonal donor to the two opposite corners. -/
def unitSwap (P : R → C → ℕ) (i l : R) (j k : C) : R → C → ℕ :=
  fun a => if a = i then transfer (P a) j k
    else if a = l then transfer (P a) k j else P a

/-- A genuine unit rectangle transfer with distinct endpoints, legal corners and positive donors. -/
def RectangleStep (E : R → C → Prop) (P P' : R → C → ℕ) : Prop :=
  ∃ i l j k, i ≠ l ∧ j ≠ k ∧ E i j ∧ E i k ∧ E l j ∧ E l k ∧
    0 < P i j ∧ 0 < P l k ∧ P' = unitSwap P i l j k

private def excess (P Q : R → C → ℕ) : ℕ := ∑ i, ∑ j, (P i j - Q i j)

private theorem transfer_sum {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → ℕ) (j k : A) (hjk : j ≠ k) (hj : 0 < f j) :
    (∑ a, transfer f j k a) = ∑ a, f a := by
  have h (a : A) : transfer f j k a + (if a = j then 1 else 0) =
      f a + (if a = k then 1 else 0) := by
    by_cases ha : a = j
    · subst a; simp [transfer, hjk]; omega
    · by_cases hb : a = k
      · subst a; simp [transfer, ha]
      · simp [transfer, ha, hb]
  have hs := congrArg (fun f : A → ℕ => ∑ a, f a) (funext h)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  omega

private theorem transfer_excess_le {A : Type*} [Fintype A] [DecidableEq A]
    (f g : A → ℕ) (j k : A) (hjk : j ≠ k) (hj : g j < f j) :
    (∑ a, (transfer f j k a - g a)) ≤ ∑ a, (f a - g a) := by
  have h (a : A) : (transfer f j k a - g a) + (if a = j then 1 else 0) ≤
      (f a - g a) + (if a = k then 1 else 0) := by
    by_cases ha : a = j
    · subst a; simp [transfer, hjk]; omega
    · by_cases hb : a = k
      · subst a; simp [transfer, ha]; omega
      · simp [transfer, ha, hb]
  have hs := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => h a)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  omega

private theorem transfer_excess_lt {A : Type*} [Fintype A] [DecidableEq A]
    (f g : A → ℕ) (j k : A) (hj : g j < f j)
    (hk : f k < g k) :
    (∑ a, (transfer f j k a - g a)) < ∑ a, (f a - g a) := by
  have h (a : A) : (transfer f j k a - g a) + (if a = j then 1 else 0) =
      f a - g a := by
    by_cases ha : a = j
    · subst a; simp [transfer]; omega
    · by_cases hb : a = k
      · subst a; simp [transfer, ha]; omega
      · simp [transfer, ha, hb]
  have hs := congrArg (fun f : A → ℕ => ∑ a, f a) (funext h)
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hs
  omega

private theorem exists_surplus {A : Type*} [Fintype A] (f g : A → ℕ)
    (hs : (∑ a, f a) = ∑ a, g a) {k : A} (hk : f k < g k) :
    ∃ j, g j < f j := by
  by_contra h
  push Not at h
  have hl := Finset.sum_lt_sum (fun a (_ : a ∈ (Finset.univ : Finset A)) => h a)
    ⟨k, Finset.mem_univ _, hk⟩
  omega

private theorem swap_invariants (E : R → C → Prop) (P Q : R → C → ℕ)
    (hP : Supported E P) (hm : SameMargins P Q)
    (i l : R) (j k : C) (hil : i ≠ l) (hjk : j ≠ k)
    (eij : E i j) (eik : E i k) (elj : E l j) (elk : E l k)
    (hij : 0 < P i j) (hlk : 0 < P l k) :
    Supported E (unitSwap P i l j k) ∧ SameMargins (unitSwap P i l j k) Q := by
  have hli : l ≠ i := Ne.symm hil
  have hkj : k ≠ j := Ne.symm hjk
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = i
    · subst a
      have hb : b ≠ j := fun h => hab (h ▸ eij)
      have hc : b ≠ k := fun h => hab (h ▸ eik)
      simp [unitSwap, transfer, hb, hc, hP i b hab]
    · by_cases hc : a = l
      · subst a
        have hb : b ≠ j := fun h => hab (h ▸ elj)
        have hd : b ≠ k := fun h => hab (h ▸ elk)
        simp [unitSwap, transfer, hli, hb, hd, hP l b hab]
      · simpa [unitSwap, ha, hc] using hP a b hab
  · intro a
    by_cases ha : a = i
    · subst a; simpa [unitSwap] using (transfer_sum (P i) j k hjk hij).trans (hm.1 i)
    · by_cases hb : a = l
      · subst a; simpa [unitSwap, hli] using (transfer_sum (P l) k j hkj hlk).trans (hm.1 l)
      · simpa [unitSwap, ha, hb] using hm.1 a
  · intro b
    by_cases hb : b = j
    · subst b
      have hcol : (fun a => unitSwap P i l j k a j) = transfer (fun a => P a j) i l := by
        funext a
        by_cases ha : a = i <;> by_cases hc : a = l <;>
          simp_all [unitSwap, transfer]
      simpa only [hcol] using (transfer_sum (fun a => P a j) i l hil hij).trans (hm.2 j)
    · by_cases hc : b = k
      · subst b
        have hcol : (fun a => unitSwap P i l j k a k) = transfer (fun a => P a k) l i := by
          funext a
          by_cases ha : a = i <;> by_cases hd : a = l <;>
            simp_all [unitSwap, transfer]
        simpa only [hcol] using (transfer_sum (fun a => P a k) l i hli hlk).trans (hm.2 k)
      · have hcol : (fun a => unitSwap P i l j k a b) = fun a => P a b := by
          funext a
          by_cases ha : a = i <;> by_cases hd : a = l <;>
            simp_all [unitSwap, transfer]
        simpa only [hcol] using hm.2 b

private theorem repair_step (E : R → C → Prop)
    (nested : ∀ i l, i ≤ l → ∀ j, E i j → E l j)
    (P Q : R → C → ℕ) (hP : Supported E P) (hQ : Supported E Q)
    (hm : SameMargins P Q) (hne : P ≠ Q) :
    ∃ P', RectangleStep E P P' ∧ Supported E P' ∧ SameMargins P' Q ∧
      excess P' Q < excess P Q := by
  classical
  let bad := Finset.univ.filter (fun i => P i ≠ Q i)
  have hbad : bad.Nonempty := by
    by_contra h
    have hall : ∀ i, P i = Q i := by
      intro i
      by_contra hi
      exact h ⟨i, by simp [bad, hi]⟩
    exact hne (funext hall)
  let i := bad.min' hbad
  have hib : i ∈ bad := Finset.min'_mem bad hbad
  have hidef : P i ≠ Q i := (Finset.mem_filter.mp hib).2
  have earlier (l : R) (hl : l < i) : P l = Q l := by
    by_contra h
    have hlb : l ∈ bad := by simp [bad, h]
    have := Finset.min'_le bad l hlb
    exact (not_le_of_gt hl) this
  have deficit : ∃ k, P i k < Q i k := by
    have hdiff : ∃ k, P i k ≠ Q i k := by
      by_contra h; push Not at h; exact hidef (funext h)
    obtain ⟨k, hk⟩ := hdiff
    rcases lt_or_gt_of_ne hk with hk | hk
    · exact ⟨k, hk⟩
    · exact exists_surplus (Q i) (P i) (hm.1 i).symm hk
  obtain ⟨k, hk⟩ := deficit
  obtain ⟨j, hj⟩ := exists_surplus (P i) (Q i) (hm.1 i) hk
  obtain ⟨l, hl⟩ := exists_surplus (fun a => P a k) (fun a => Q a k) (hm.2 k) hk
  have hil : i < l := by
    rcases lt_trichotomy l i with h | h | h
    · have heq := congrFun (earlier l h) k; omega
    · subst l; omega
    · exact h
  have hjk : j ≠ k := by intro h; subst j; omega
  have hij : 0 < P i j := by omega
  have hlk : 0 < P l k := by omega
  have eij : E i j := by by_contra h; have := hP i j h; omega
  have eik : E i k := by by_contra h; have := hQ i k h; omega
  have elk : E l k := by by_contra h; have := hP l k h; omega
  have elj : E l j := nested i l (le_of_lt hil) j eij
  refine ⟨unitSwap P i l j k, ⟨i, l, j, k, ne_of_lt hil, hjk, eij, eik, elj, elk,
    hij, hlk, rfl⟩, ?_⟩
  obtain ⟨hs, hm'⟩ := swap_invariants E P Q hP hm i l j k (ne_of_lt hil) hjk
    eij eik elj elk hij hlk
  refine ⟨hs, hm', ?_⟩
  apply Finset.sum_lt_sum
  · intro a ha
    by_cases hai : a = i
    · subst a
      simpa [unitSwap] using le_of_lt (transfer_excess_lt (P i) (Q i) j k hj hk)
    · by_cases hal : a = l
      · subst a
        simpa [unitSwap, Ne.symm (ne_of_lt hil)] using
          transfer_excess_le (P l) (Q l) k j (Ne.symm hjk) hl
      · simp [unitSwap, hai, hal]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    simpa [unitSwap] using transfer_excess_lt (P i) (Q i) j k hj hk

/-- Natural tables with nested legal row neighborhoods and the same margins are
connected by finitely many legal unit transfers. Every intermediate table keeps
the original support restriction and both target margins, including zero margins. -/
theorem ferrers_integer_rectangle_connected (E : R → C → Prop)
    (nested : ∀ i l, i ≤ l → ∀ j, E i j → E l j)
    (P Q : R → C → ℕ) (hP : Supported E P) (hQ : Supported E Q)
    (hm : SameMargins P Q) :
    Relation.ReflTransGen
      (fun A B => RectangleStep E A B ∧ Supported E B ∧ SameMargins B Q) P Q := by
  have hmain : ∀ n, ∀ A : R → C → ℕ, excess A Q = n →
      Supported E A → SameMargins A Q →
      Relation.ReflTransGen
        (fun A B => RectangleStep E A B ∧ Supported E B ∧ SameMargins B Q) A Q := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A hn hA hmA
      by_cases heq : A = Q
      · subst A; exact .refl
      obtain ⟨B, hstep, hB, hmB, hlt⟩ := repair_step E nested A Q hA hQ hmA heq
      have htail := ih (excess B Q) (by omega) B rfl hB hmB
      exact (Relation.ReflTransGen.single ⟨hstep, hB, hmB⟩).trans htail
  exact hmain (excess P Q) P rfl hP hm

end D5.S3.Combinatorics.Transportation.FerrersIntegerRectanglePaths
