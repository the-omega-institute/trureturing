/- GID: D5/S3/Combinatorics/Permutation/Verkama62Local
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Permutation/Verkama62Local
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Terminal 3412 patterns obstruct northeast double ears after at most one cheap insertion. -/

import D5.S1.Words.Patterns.DerangementRatioNonconvergence
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FinCases

/-! Local order arguments for northeast ears in permutation diagrams. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Permutation.Verkama62Local

open D5.S1.Words.Patterns.DerangementRatioNonconvergence (Contains)

/-- The classical pattern 351624, with zero-based values. -/
def pattern : Equiv.Perm (Fin 6) where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide
  right_inv := by decide

/-- A terminal 3412: its second point is topmost and its fourth is rightmost. -/
structure Terminal {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) where
  a : Fin n
  b : Fin n
  c : Fin n
  d : Fin n
  ha : a ∈ S
  hb : b ∈ S
  hc : c ∈ S
  hd : d ∈ S
  hab : a < b
  hbc : b < c
  hcd : c < d
  hval₁ : π c < π d
  hval₂ : π d < π a
  hval₃ : π a < π b
  rightmost : ∀ i ∈ S, i ≤ d
  topmost : ∀ i ∈ S, π i ≤ π b

/-- In a fresh terminal pattern, the last three points and largest three values are fixed. -/
structure Fresh {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n))
    extends Terminal π S where
  right : ∀ i ∈ S, i ≤ b ∨ i = c ∨ i = d
  top : ∀ i ∈ S, π i ≤ π d ∨ i = a ∨ i = b

/-- The order geometry of a northeast two-vertex ear, in the original coordinates. -/
structure Double {n : ℕ} (π : Equiv.Perm (Fin n)) (S : Finset (Fin n)) where
  u : Fin n
  v : Fin n
  x : Fin n
  y : Fin n
  hx : x ∈ S
  hy : y ∈ S
  hu : u ∉ S
  hv : v ∉ S
  hxy : x ≠ y
  hux : u < x
  hxv : x < v
  hvy : π v < π y
  hyu : π y < π u
  old_left : ∀ i ∈ S, i ≠ x → i < u
  old_below : ∀ i ∈ S, i ≠ y → π i < π v

/-- Every northeast double ear produces a fresh terminal 3412. -/
def Double.fresh {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (e : Double π S) : Fresh π (insert e.u (insert e.v S)) where
  a := e.y
  b := e.u
  c := e.x
  d := e.v
  ha := by simp [e.hy]
  hb := by simp
  hc := by simp [e.hx]
  hd := by simp
  hab := e.old_left e.y e.hy e.hxy.symm
  hbc := e.hux
  hcd := e.hxv
  hval₁ := e.old_below e.x e.hx e.hxy
  hval₂ := e.hvy
  hval₃ := e.hyu
  rightmost := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact (e.hux.trans e.hxv).le
    · exact le_rfl
    · by_cases h : i = e.x
      · exact h ▸ e.hxv.le
      · exact ((e.old_left i hi h).trans (e.hux.trans e.hxv)).le
  topmost := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact le_rfl
    · exact (e.hvy.trans e.hyu).le
    · by_cases h : i = e.y
      · exact h ▸ e.hyu.le
      · exact ((e.old_below i hi h).trans (e.hvy.trans e.hyu)).le
  right := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact Or.inl le_rfl
    · exact Or.inr (Or.inr rfl)
    · by_cases h : i = e.x
      · exact Or.inr (Or.inl h)
      · exact Or.inl (e.old_left i hi h).le
  top := by
    intro i hi
    simp only [Finset.mem_insert] at hi
    rcases hi with rfl | rfl | hi
    · exact Or.inr (Or.inr rfl)
    · exact Or.inl le_rfl
    · by_cases h : i = e.y
      · exact Or.inr (Or.inl h)
      · exact Or.inl (e.old_below i hi h).le

set_option maxHeartbeats 1200000 in
private theorem realize {n : ℕ} (π : Equiv.Perm (Fin n))
    (a b c d e f : Fin n)
    (hab : a < b) (hbc : b < c) (hcd : c < d) (hde : d < e) (hef : e < f)
    (hce : π c < π e) (hea : π e < π a) (haf : π a < π f)
    (hfb : π f < π b) (hbd : π b < π d) : Contains pattern π := by
  let positions : Fin 6 ↪o Fin n := OrderEmbedding.ofStrictMono ![a, b, c, d, e, f] (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i <;> simpa)
  refine ⟨positions, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pattern, positions, OrderEmbedding.ofStrictMono] <;> omega

/-- A terminal 3412 immediately followed by a northeast double ear forces 351624. -/
theorem Terminal.forces {n : ℕ} {π : Equiv.Perm (Fin n)} {S : Finset (Fin n)}
    (t : Terminal π S) (e : Double π S) : Contains pattern π := by
  have hd : t.d = e.x := by
    apply le_antisymm
    · by_cases h : t.d = e.x
      · exact h.le
      · exact ((e.old_left t.d t.hd h).trans e.hux).le
    · exact t.rightmost e.x e.hx
  have hb : t.b = e.y := by
    apply π.injective
    apply le_antisymm
    · by_cases h : t.b = e.y
      · exact (congrArg π h).le
      · exact ((e.old_below t.b t.hb h).trans e.hvy).le
    · exact t.topmost e.y e.hy
  have hcx : t.c ≠ e.x := by rw [← hd]; exact ne_of_lt t.hcd
  have hay : t.a ≠ e.y := by rw [← hb]; exact ne_of_lt t.hab
  exact realize π t.a t.b t.c e.u t.d e.v
    t.hab t.hbc (e.old_left t.c t.hc hcx) (hd ▸ e.hux) (hd ▸ e.hxv)
    t.hval₁ t.hval₂ (e.old_below t.a t.ha hay) (hb ▸ e.hvy) (hb ▸ e.hyu)

end D5.S3.Combinatorics.Permutation.Verkama62Local
