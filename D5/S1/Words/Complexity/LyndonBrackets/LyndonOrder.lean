/- GID: D5/S1/Words/Complexity/LyndonBrackets/LyndonOrder
   generality: G
   mirror-B: D5/B/S1/Words/Complexity/LyndonBrackets/LyndonOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Algebra.MonoidAlgebra.Support]
   utility: none
   digest: Lyndon words are ordered by their proper suffixes and admit Lyndon concatenation. -/

import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder

variable {A : Type*} [LinearOrder A]

/-- A nonempty word strictly smaller than each of its nontrivial rotations. -/
def IsLyndon (w : List A) : Prop :=
  w ≠ [] ∧ ∀ u v : List A, u ≠ [] → v ≠ [] → w = u ++ v → w < v ++ u

private theorem list_lt_self_append (u : List A) {v : List A} (hv : v ≠ []) :
    u < u ++ v := by
  change List.Lex (· < ·) u (u ++ v)
  induction u with
  | nil =>
      cases v with
      | nil => exact (hv rfl).elim
      | cons a v => exact List.Lex.nil
  | cons a u ih => exact List.Lex.cons ih

private theorem append_left_lt_iff (p x y : List A) :
    p ++ x < p ++ y ↔ x < y := by
  change List.Lex (· < ·) (p ++ x) (p ++ y) ↔ List.Lex (· < ·) x y
  induction p with
  | nil => simp
  | cons a p ih =>
      simpa only [List.cons_append, List.lex_cons_iff] using ih

private theorem lex_append_of_lex_of_length_eq {u x : List A}
    (hux : u < x) (hlen : u.length = x.length) (v y : List A) :
    u ++ v < x ++ y := by
  change List.Lex (· < ·) u x at hux
  change List.Lex (· < ·) (u ++ v) (x ++ y)
  induction hux with
  | nil => simp at hlen
  | rel h => exact List.Lex.rel h
  | cons h ih =>
      exact List.Lex.cons (ih (Nat.succ.inj hlen))

private theorem prefix_of_lt_of_lt_append {v w u : List A}
    (hvw : v < w) (hw : w < v ++ u) : ∃ t, w = v ++ t := by
  induction v generalizing w with
  | nil => exact ⟨w, by simp⟩
  | cons a v ih =>
      cases w with
      | nil => simp at hvw
      | cons b w =>
          have hab : a = b := le_antisymm
            (List.head_le_of_lt hvw) (List.head_le_of_lt hw)
          subst b
          have hvw' : v < w := List.lex_cons_iff.mp hvw
          have hw' : w < v ++ u := by
            change List.Lex (· < ·) (a :: w) ((a :: v) ++ u) at hw
            exact List.lex_cons_iff.mp hw
          rcases ih hvw' hw' with ⟨t, rfl⟩
          exact ⟨t, by simp⟩

/-- The rotation definition of a Lyndon word is equivalent to strict comparison
with every nonempty proper suffix. -/
theorem isLyndon_iff_lt_suffix (w : List A) :
    IsLyndon w ↔
      w ≠ [] ∧ ∀ v : List A, v ≠ [] → v <:+ w → v ≠ w → w < v := by
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    intro v hv ⟨u, huv⟩ hvw
    have hu : u ≠ [] := by
      intro hu
      apply hvw
      simpa [hu] using huv
    have hrot : w < v ++ u := hw.2 u v hu hv huv.symm
    by_contra hn
    have hvltw : v < w := lt_of_le_of_ne (le_of_not_gt hn) hvw
    rcases prefix_of_lt_of_lt_append hvltw hrot with ⟨t, hwt⟩
    have ht : t ≠ [] := by
      intro ht
      apply hvw
      simpa [hwt, ht]
    have htu : t < u := by
      apply (append_left_lt_iff v t u).mp
      simpa only [hwt] using hrot
    have hlen : t.length = u.length := by
      have h₁ := congrArg List.length huv
      have h₂ := congrArg List.length hwt
      simp only [List.length_append] at h₁ h₂
      omega
    have hback : t ++ v < w := by
      rw [← huv]
      exact lex_append_of_lex_of_length_eq htu hlen v v
    have hforward : w < t ++ v := hw.2 v t hv ht hwt
    exact lt_asymm hforward hback
  · rintro ⟨hwne, hsuffix⟩
    refine ⟨hwne, ?_⟩
    intro u v hu hv huv
    have hvSuffix : v <:+ w := ⟨u, huv.symm⟩
    have hvw : v ≠ w := by
      intro heq
      have hlen := congrArg List.length huv
      simp only [heq, List.length_append] at hlen
      have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
      omega
    exact (hsuffix v hv hvSuffix hvw).trans (list_lt_self_append v hu)

private theorem append_right_lt_of_lt_of_length_ge {u v : List A}
    (huv : u < v) (hlen : v.length ≤ u.length) (z : List A) :
    u ++ z < v ++ z := by
  change List.Lex (· < ·) u v at huv
  change List.Lex (· < ·) (u ++ z) (v ++ z)
  induction huv with
  | nil => simp at hlen
  | rel h => exact List.Lex.rel h
  | cons h ih => exact List.Lex.cons (ih (Nat.le_of_succ_le_succ hlen))

private theorem append_lt_of_lt_of_not_prefix {u v : List A}
    (huv : u < v) (hn : ¬u <+: v) (z : List A) : u ++ z < v := by
  change List.Lex (· < ·) u v at huv
  induction huv with
  | nil => exact (hn List.nil_prefix).elim
  | rel h => exact List.Lex.rel h
  | @cons a u v h ih =>
      apply List.Lex.cons
      apply ih
      intro hp
      rcases hp with ⟨q, hq⟩
      exact hn ⟨q, by simpa using congrArg (List.cons a) hq⟩

private theorem append_lt_right_of_lt_of_lyndon {u v : List A}
    (hu : u ≠ []) (huv : u < v) (hv : IsLyndon v) : u ++ v < v := by
  by_cases hp : u <+: v
  · rcases hp with ⟨z, rfl⟩
    have hz : z ≠ [] := by
      intro hz
      simp [hz] at huv
    apply (append_left_lt_iff u (u ++ z) z).mpr
    exact ((isLyndon_iff_lt_suffix (u ++ z)).mp hv).2 z hz
      ⟨u, rfl⟩ (by
        intro h
        have hlen := congrArg List.length h
        simp only [List.length_append] at hlen
        have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
        omega)
  · exact append_lt_of_lt_of_not_prefix huv hp v

/-- Concatenating two Lyndon words in increasing lexicographic order is Lyndon. -/
theorem isLyndon_append {u v : List A} (hu : IsLyndon u) (hv : IsLyndon v)
    (huv : u < v) : IsLyndon (u ++ v) := by
  apply (isLyndon_iff_lt_suffix (u ++ v)).mpr
  refine ⟨by simp [hu.1, hv.1], ?_⟩
  intro t ht htw htwne
  have huvltv : u ++ v < v := append_lt_right_of_lt_of_lyndon hu.1 huv hv
  have hvSuffix : v <:+ u ++ v := List.suffix_append u v
  rcases List.suffix_or_suffix_of_suffix htw hvSuffix with htv | hvt
  · rcases eq_or_ne t v with rfl | htvne
    · exact huvltv
    · exact huvltv.trans_le
        (((isLyndon_iff_lt_suffix v).mp hv).2 t ht htv htvne).le
  · rcases hvt with ⟨s, hst⟩
    subst t
    by_cases hs : s = []
    · subst s
      simpa only [List.nil_append] using huvltv
    · rcases htw with ⟨x, hxt⟩
      have hx : x ≠ [] := by
        intro hx
        apply htwne
        simpa [hx] using hxt
      have hxu : x ++ s = u := by
        apply List.append_left_injective v
        simpa only [List.append_assoc] using hxt
      have hsSuffix : s <:+ u := ⟨x, hxu⟩
      have hsu : s ≠ u := by
        intro h
        have hlen := congrArg List.length hxu
        simp only [h, List.length_append] at hlen
        have hxpos : 0 < x.length := List.length_pos_of_ne_nil hx
        omega
      have hus : u < s := ((isLyndon_iff_lt_suffix u).mp hu).2 s hs hsSuffix hsu
      exact append_right_lt_of_lt_of_length_ge hus hsSuffix.length_le v

theorem exists_lyndon_suffix_cut (w : List A) (hw : 2 ≤ w.length) :
    ∃ i : ℕ, 0 < i ∧ i < w.length ∧ IsLyndon (w.drop i) := by
  have hwne : w ≠ [] := by
    intro h
    simp [h] at hw
  refine ⟨w.length - 1, by omega, by omega, ?_⟩
  rw [List.drop_length_sub_one hwne]
  refine ⟨by simp, ?_⟩
  intro u v hu hv huv
  have hlen := congrArg List.length huv
  simp only [List.length_singleton, List.length_append] at hlen
  have huPos : 0 < u.length := List.length_pos_of_ne_nil hu
  have hvPos : 0 < v.length := List.length_pos_of_ne_nil hv
  omega


end D5.S1.Words.Complexity.LyndonBrackets.LyndonOrder
