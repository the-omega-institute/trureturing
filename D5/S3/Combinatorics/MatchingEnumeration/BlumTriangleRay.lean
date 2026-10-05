/- GID: D5/S3/Combinatorics/MatchingEnumeration/BlumTriangleRay
   generality: G
   mirror-B: D5/B/S3/Combinatorics/MatchingEnumeration/BlumTriangleRay
   mirror-E: none(waiver:discrete-halfplane-separation)
   anchors: [mathlib/module/Mathlib.Data.ZMod.Basic, mathlib/module/Mathlib.Algebra.CharP.Two]
   utility: none
   digest: A discrete ray potential separates boundary endpoints of left-half graph chains. -/

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two
import D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleGeometry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRay

open BlumTriangleDefs Finset

set_option maxHeartbeats 12000000 in
-- The finite edge-incidence cases and cut reindexing share one elaboration budget.
/-- Mod-two ray counts give a potential constant along edges disjoint from a left-half
chain. Its axis values are the prefix sums of the chain's boundary divergence. -/
theorem left_ray_potential (k : ℕ) (w : Vertex (4 * k) → Vertex (4 * k) → ZMod 2)
    (hsymm : ∀ u v, w u v = w v u)
    (hsupport : ∀ u v, ¬ Adj u v → w u v = 0)
    (hleft : ∀ u v, w u v ≠ 0 → u.1.2.val ≤ 4 * k - 1 ∧ v.1.2.val ≤ 4 * k - 1)
    (hdiv : ∀ u, u.1.2.val < 4 * k - 1 → ∑ v, w u v = 0) :
    ∃ F : Vertex (4 * k) → ZMod 2,
      (∀ u z, Adj u z → u.1.2.val ≤ 4 * k - 1 → z.1.2.val ≤ 4 * k - 1 →
        (∀ v, w u v = 0) → (∀ v, w z v = 0) → F u = F z) ∧
      ∀ u, u.1.2.val = 4 * k - 1 →
        F u = ∑ v, if v.1.1.val ≤ u.1.1.val then ∑ z, w v z else 0 := by
  classical
  let V := Vertex (4 * k)
  let ray : V → V → V → Prop := fun u s t =>
    s.1.1.val ≤ u.1.1.val ∧ u.1.1.val < t.1.1.val ∧
      min s.1.2.val t.1.2.val < u.1.2.val
  let F : V → ZMod 2 := fun u => ∑ s, ∑ t,
    if Step s t then w s t * (if ray u s t then 1 else 0) else 0
  have disjoint (s t : V) : ¬ (Step s t ∧ Step t s) := by
    rintro ⟨hst, hts⟩
    rcases hst with ⟨hr, hx | hx⟩ | ⟨he, ⟨hr, hx⟩ | ⟨hr, hx⟩⟩
    all_goals rcases hts with ⟨hr', hx' | hx'⟩ | ⟨he', ⟨hr', hx'⟩ | ⟨hr', hx'⟩⟩
    all_goals omega
  have split (s t : V) :
      w s t = (if Step s t then w s t else 0) +
        (if Step t s then w s t else 0) := by
    by_cases hst : Step s t
    · have hts : ¬ Step t s := fun h => disjoint s t ⟨hst, h⟩
      simp [hst, hts]
    · by_cases hts : Step t s
      · simp [hst, hts]
      · have hz := hsupport s t (by exact fun h => h.elim hst hts)
        simp [hst, hts, hz]
  have cut_sum (I : V → ZMod 2) :
      (∑ s, I s * ∑ t, w s t) =
        ∑ s, ∑ t, if Step s t then w s t * (I s + I t) else 0 := by
    let A := ∑ s, ∑ t, if Step s t then I s * w s t else 0
    let B := ∑ s, ∑ t, if Step t s then I s * w s t else 0
    let D := ∑ s, ∑ t, if Step s t then I t * w s t else 0
    have start : (∑ s, I s * ∑ t, w s t) = A + B := by
      simp only [mul_sum]
      dsimp [A, B]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro s _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t _
      rw [split s t, mul_add]
      by_cases hst : Step s t <;> by_cases hts : Step t s <;>
        simp [hst, hts, CharTwo.add_self_eq_zero]
    have reverse : B = D := by
      dsimp [B, D]
      rw [sum_comm]
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro t _
      rw [hsymm t s]
    rw [start, reverse]
    dsimp [A, D]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro s _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    split_ifs <;> ring
  have incidence (u z s t : V) (huz : Step u z) (hst : Step s t)
      (hsu : s ≠ u) (hsz : s ≠ z) (htu : t ≠ u) (htz : t ≠ z) :
      ((if ray u s t then 1 else 0) : ZMod 2) +
        (if ray z s t then 1 else 0) =
      (if u.1.1.val < s.1.1.val ∧ s.1.1.val ≤ z.1.1.val ∧
          s.1.2.val < min u.1.2.val z.1.2.val then 1 else 0) +
        (if u.1.1.val < t.1.1.val ∧ t.1.1.val ≤ z.1.1.val ∧
          t.1.2.val < min u.1.2.val z.1.2.val then 1 else 0) := by
    have ne_coord (v v' : V) (h : v ≠ v') :
        ¬ (v.1.1.val = v'.1.1.val ∧ v.1.2.val = v'.1.2.val) := by
      intro he
      apply h
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      · exact he.1
      · exact he.2
    have hsu' := ne_coord s u hsu
    have hsz' := ne_coord s z hsz
    have htu' := ne_coord t u htu
    have htz' := ne_coord t z htz
    have hu := u.2
    have hz := z.2
    have hs := s.2
    have ht := t.2
    dsimp [ray]
    simp only [lt_min_iff, min_lt_iff]
    rcases huz with ⟨hr, hx | hx⟩ | ⟨he, ⟨hr, hx⟩ | ⟨hr, hx⟩⟩
    all_goals rcases hst with ⟨hr', hx' | hx'⟩ | ⟨he', ⟨hr', hx'⟩ | ⟨hr', hx'⟩⟩
    all_goals split_ifs <;> simp only [CharTwo.add_self_eq_zero, add_zero, zero_add] <;>
      omega
  have constant_step (u z : V) (huz : Step u z)
      (hu : u.1.2.val ≤ 4 * k - 1) (hz : z.1.2.val ≤ 4 * k - 1)
      (hwu : ∀ v, w u v = 0) (hwz : ∀ v, w z v = 0) : F u = F z := by
    let I : V → ZMod 2 := fun v =>
      if u.1.1.val < v.1.1.val ∧ v.1.1.val ≤ z.1.1.val ∧
        v.1.2.val < min u.1.2.val z.1.2.val then 1 else 0
    have ray_cut : F u + F z =
        ∑ s, ∑ t, if Step s t then w s t * (I s + I t) else 0 := by
      dsimp [F]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro s _
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro t _
      by_cases hst : Step s t
      · rw [if_pos hst, if_pos hst, if_pos hst, ← mul_add]
        by_cases hw : w s t = 0
        · simp [hw]
        · have hsu : s ≠ u := fun h => hw (h ▸ hwu t)
          have hsz : s ≠ z := fun h => hw (h ▸ hwz t)
          have htu : t ≠ u := by
            intro h
            apply hw
            rw [h, hsymm, hwu]
          have htz : t ≠ z := by
            intro h
            apply hw
            rw [h, hsymm, hwz]
          rw [incidence u z s t huz hst hsu hsz htu htz]
      · simp [hst]
    have cut_zero : (∑ s, I s * ∑ t, w s t) = 0 := by
      apply sum_eq_zero
      intro s _
      dsimp [I]
      split_ifs with hs
      · have hsleft : s.1.2.val < 4 * k - 1 := by
          have hl := (lt_min_iff.mp hs.2.2).1
          omega
        rw [hdiv s hsleft, mul_zero]
      · exact zero_mul _
    apply CharTwo.add_eq_zero.mp
    exact ray_cut.trans ((cut_sum I).symm.trans cut_zero)
  refine ⟨F, ?_, ?_⟩
  · intro u z hadj hu hz hwu hwz
    rcases hadj with hadj | hadj
    · exact constant_step u z hadj hu hz hwu hwz
    · exact (constant_step z u hadj hz hu hwz hwu).symm
  · intro u hu
    let I : V → ZMod 2 := fun v => if v.1.1.val ≤ u.1.1.val then 1 else 0
    have axis_ray : F u =
        ∑ s, ∑ t, if Step s t then w s t * (I s + I t) else 0 := by
      apply sum_congr rfl
      intro s _
      apply sum_congr rfl
      intro t _
      by_cases hst : Step s t
      · rw [if_pos hst, if_pos hst]
        by_cases hw : w s t = 0
        · simp [hw]
        · have hl := hleft s t hw
          have hs := s.2
          have ht := t.2
          have hrs := s.1.1.isLt
          have hm : min s.1.2.val t.1.2.val < 4 * k - 1 := by
            rcases hst with ⟨hr, hx | hx⟩ | ⟨he, ⟨hr, hx⟩ | ⟨hr, hx⟩⟩
            all_goals simp only [min_lt_iff]
            all_goals omega
          have hr : s.1.1.val ≤ t.1.1.val := by
            rcases hst with ⟨hr, _⟩ | ⟨_, ⟨hr, _⟩ | ⟨hr, _⟩⟩ <;> omega
          congr 1
          dsimp [ray, I]
          rw [hu]
          simp only [hm, and_true]
          split_ifs <;> simp only [CharTwo.add_self_eq_zero, add_zero, zero_add] <;>
            omega
      · simp [hst]
    rw [axis_ray, ← cut_sum]
    apply sum_congr rfl
    intro v _
    dsimp [I]
    split_ifs <;> simp

end D5.S3.Combinatorics.MatchingEnumeration.BlumTriangleRay
