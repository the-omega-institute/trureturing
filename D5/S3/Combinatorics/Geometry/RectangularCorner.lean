/- GID: D5/S3/Combinatorics/Geometry/RectangularCorner
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/RectangularCorner
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Consecutive global minima correspond to strict global corners in finite rectangles. -/

import Mathlib.Order.UpperLower.Closure
import Mathlib.Order.Minimal
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Geometry.RectangularCorner

abbrev Point (m n : ℕ) := Fin m × Fin n

def LocalMin {m n : ℕ} (I : Set (Point m n)) (a u : Point m n) : Prop :=
  Minimal (· ∈ I) u ∧ u ≤ a

def Adjacent {m n : ℕ} (I : Set (Point m n)) (a u v : Point m n) : Prop :=
  LocalMin I a u ∧ LocalMin I a v ∧ u.1 < v.1 ∧
  ∀ w, LocalMin I a w → ¬ (u.1 < w.1 ∧ w.1 < v.1)

def Corner {m n : ℕ} (I : Set (Point m n)) (a b : Point m n) : Prop :=
  Maximal (· ∈ (lowerClosure I : Set (Point m n)) \ I) b ∧
  b.1 < a.1 ∧ b.2 < a.2

/-- Consecutive minima produce the exact strict rectangular corner. -/
theorem adjacent_gives_corner {m n : ℕ} {I : Set (Point m n)}
    (hI : I.OrdConnected) {a u v b : Point m n} (ha : a ∈ I)
    (huv : Adjacent I a u v)
    (hr : b.1.val + 1 = v.1.val) (hs : b.2.val + 1 = u.2.val) :
    Corner I a b := by
  rcases huv with ⟨⟨hu, hua⟩, ⟨hv, hva⟩, huv, hadj⟩
  have hvu : v.2 < u.2 := by
    by_contra h
    have hle : u ≤ v := ⟨le_of_lt huv, le_of_not_gt h⟩
    have hh := hv.2 hu.1 hle
    have hrow := hh.1
    exact (not_le_of_gt huv) hrow
  have hba : b ≤ a := by
    constructor
    · have hh := hva.1
      change b.1.val ≤ a.1.val
      change v.1.val ≤ a.1.val at hh
      omega
    · have hh := hua.2
      change b.2.val ≤ a.2.val
      change u.2.val ≤ a.2.val at hh
      omega
  have hnone : ∀ x ∈ I, ¬ x ≤ b := by
    intro x hx hxb
    obtain ⟨w, hwx, hw⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ I) x hx
    have hwb : w ≤ b := hwx.trans hxb
    have hwa : w ≤ a := hwb.trans hba
    have hwu : ¬ w.1 ≤ u.1 := by
      intro hh
      have hle : w ≤ u := by
        constructor
        · exact hh
        · have hc := hwb.2
          change w.2.val ≤ b.2.val at hc
          change w.2.val ≤ u.2.val
          omega
      have hh := hu.2 hw.1 hle
      have hc := hh.2
      have hc' := hwb.2
      change u.2.val ≤ w.2.val at hc
      change w.2.val ≤ b.2.val at hc'
      omega
    have hwv : w.1 < v.1 := by
      have hc := hwb.1
      change w.1.val ≤ b.1.val at hc
      change w.1.val < v.1.val
      omega
    exact hadj w ⟨hw, hwa⟩ ⟨lt_of_not_ge hwu, hwv⟩
  refine ⟨⟨⟨⟨a, ha, hba⟩, fun hb ↦ hnone b hb le_rfl⟩, ?_⟩, ?_, ?_⟩
  · intro x hx hbx
    obtain ⟨z, hz, hxz⟩ := hx.1
    have hxr : x.1 ≤ b.1 := by
      by_contra h
      have hvx : v ≤ x := by
        constructor
        · change v.1.val ≤ x.1.val
          have hh : b.1 < x.1 := lt_of_not_ge h
          change b.1.val < x.1.val at hh
          omega
        · have hh := hbx.2
          change b.2.val ≤ x.2.val at hh
          change v.2.val < u.2.val at hvu
          change v.2.val ≤ x.2.val
          omega
      exact hx.2 (hI.out hv.1 hz ⟨hvx, hxz⟩)
    have hxc : x.2 ≤ b.2 := by
      by_contra h
      have hux : u ≤ x := by
        constructor
        · have hh := hbx.1
          change b.1.val ≤ x.1.val at hh
          change u.1.val < v.1.val at huv
          change u.1.val ≤ x.1.val
          omega
        · have hh : b.2 < x.2 := lt_of_not_ge h
          change b.2.val < x.2.val at hh
          change u.2.val ≤ x.2.val
          omega
      exact hx.2 (hI.out hu.1 hz ⟨hux, hxz⟩)
    exact ⟨hxr, hxc⟩
  · have hh := hva.1
    change v.1.val ≤ a.1.val at hh
    change b.1.val < a.1.val
    omega
  · have hh := hua.2
    change u.2.val ≤ a.2.val at hh
    change b.2.val < a.2.val
    omega

/-- The two immediate successors of a strict corner recover consecutive minima. -/
theorem corner_gives_adjacent {m n : ℕ} {I : Set (Point m n)}
    (hI : I.OrdConnected) {a b : Point m n} (ha : a ∈ I)
    (hb : Corner I a b) :
    ∃ u v, Adjacent I a u v ∧
      b.1.val + 1 = v.1.val ∧ b.2.val + 1 = u.2.val := by
  rcases hb with ⟨hb, hbr, hbc⟩
  let r : Fin m := ⟨b.1.val + 1, by have hh := a.1.isLt; change b.1.val < a.1.val at hbr; omega⟩
  let s : Fin n := ⟨b.2.val + 1, by have hh := a.2.isLt; change b.2.val < a.2.val at hbc; omega⟩
  let x : Point m n := (r, b.2)
  let y : Point m n := (b.1, s)
  have hxa : x ≤ a := by
    constructor
    · change b.1.val + 1 ≤ a.1.val
      change b.1.val < a.1.val at hbr
      omega
    · exact le_of_lt hbc
  have hya : y ≤ a := by
    constructor
    · exact le_of_lt hbr
    · change b.2.val + 1 ≤ a.2.val
      change b.2.val < a.2.val at hbc
      omega
  have hbx : b ≤ x := by
    constructor
    · change b.1.val ≤ b.1.val + 1
      omega
    · exact le_rfl
  have hby : b ≤ y := by
    constructor
    · exact le_rfl
    · change b.2.val ≤ b.2.val + 1
      omega
  have hxI : x ∈ I := by
    by_contra hx
    have hh := hb.2 (show x ∈ (lowerClosure I : Set (Point m n)) \ I from ⟨⟨a, ha, hxa⟩, hx⟩) hbx
    have hr := hh.1
    change b.1.val + 1 ≤ b.1.val at hr
    omega
  have hyI : y ∈ I := by
    by_contra hy
    have hh := hb.2 (show y ∈ (lowerClosure I : Set (Point m n)) \ I from ⟨⟨a, ha, hya⟩, hy⟩) hby
    have hs := hh.2
    change b.2.val + 1 ≤ b.2.val at hs
    omega
  obtain ⟨u, huy, hu⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ I) y hyI
  obtain ⟨v, hvx, hv⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ I) x hxI
  have hua := huy.trans hya
  have hva := hvx.trans hxa
  have hba : b ≤ a := ⟨le_of_lt hbr, le_of_lt hbc⟩
  have hs : b.2.val + 1 = u.2.val := by
    have hle := huy.2
    change u.2.val ≤ b.2.val + 1 at hle
    have hn : ¬ u.2 ≤ b.2 := by
      intro hh
      exact hb.1.2 (hI.out hu.1 ha ⟨⟨huy.1, hh⟩, hba⟩)
    change ¬ u.2.val ≤ b.2.val at hn
    omega
  have hr : b.1.val + 1 = v.1.val := by
    have hle := hvx.1
    change v.1.val ≤ b.1.val + 1 at hle
    have hn : ¬ v.1 ≤ b.1 := by
      intro hh
      exact hb.1.2 (hI.out hv.1 ha ⟨⟨hh, hvx.2⟩, hba⟩)
    change ¬ v.1.val ≤ b.1.val at hn
    omega
  have huv : u.1 < v.1 := by
    have hh := huy.1
    change u.1.val ≤ b.1.val at hh
    change u.1.val < v.1.val
    omega
  refine ⟨u, v, ⟨⟨hu, hua⟩, ⟨hv, hva⟩, huv, ?_⟩, hr, hs⟩
  intro w hw hbetween
  have hwu : w.2 < u.2 := by
    by_contra hn
    have hh := hw.1.2 hu.1 (show u ≤ w from ⟨le_of_lt hbetween.1, le_of_not_gt hn⟩)
    exact (not_le_of_gt hbetween.1) hh.1
  have hwb : w ≤ b := by
    constructor
    · have hh := hbetween.2
      change w.1.val < v.1.val at hh
      change w.1.val ≤ b.1.val
      omega
    · change w.2.val < u.2.val at hwu
      change w.2.val ≤ b.2.val
      omega
  exact hb.1.2 (hI.out hw.1.1 ha ⟨hwb, hba⟩)

open Classical in
/-- Exact strict-corner count for every finite rectangle and order-convex subset. -/
theorem rectangular_corner_card (m n : ℕ) (I : Set (Point m n))
    (hI : I.OrdConnected) (a : Point m n) (ha : a ∈ I) :
    (Finset.univ.filter (Corner I a)).card + 1 =
      (Finset.univ.filter (LocalMin I a)).card := by
  classical
  let S : Finset (Point m n) := Finset.univ.filter (LocalMin I a)
  let B : Finset (Point m n) := Finset.univ.filter (Corner I a)
  have memS (u : Point m n) : u ∈ S ↔ LocalMin I a u := by simp [S]
  have memB (b : Point m n) : b ∈ B ↔ Corner I a b := by simp [B]
  have rowinj : ∀ u, LocalMin I a u → ∀ v, LocalMin I a v → u.1 = v.1 → u = v := by
    intro u hu v hv he
    rcases le_total u.2 v.2 with h | h
    · exact hv.1.eq_of_le hu.1.1 ⟨he.le, h⟩
    · exact hu.1.eq_of_ge hv.1.1 ⟨he.ge, h⟩
  obtain ⟨w, hwa, hw⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ I) a ha
  obtain ⟨z, hz⟩ := exists_minimalFor_of_wellFoundedLT (LocalMin I a)
    (fun x : Point m n ↦ x.1) ⟨w, hw, hwa⟩
  have hzS : z ∈ S := (memS z).2 hz.1
  have unique_predecessor : ∀ {u u' v}, Adjacent I a u v → Adjacent I a u' v → u = u' := by
    intro u u' v h h'
    apply rowinj u h.1 u' h'.1
    apply le_antisymm
    · by_contra hn
      exact h'.2.2.2 u h.1 ⟨lt_of_not_ge hn, h.2.2.1⟩
    · by_contra hn
      exact h.2.2.2 u' h'.1 ⟨lt_of_not_ge hn, h'.2.2.1⟩
  have pairs : ∀ b ∈ B, ∃ u v, Adjacent I a u v ∧
      b.1.val + 1 = v.1.val ∧ b.2.val + 1 = u.2.val := by
    intro b hb
    exact corner_gives_adjacent hI ha ((memB b).1 hb)
  choose U V hUV hR hC using pairs
  have maps : ∀ b (hb : b ∈ B), V b hb ∈ S.erase z := by
    intro b hb
    apply Finset.mem_erase.mpr
    refine ⟨?_, (memS _).2 (hUV b hb).2.1⟩
    intro he
    have hh := hz.le (hUV b hb).1
    rw [← he] at hh
    exact (not_le_of_gt (hUV b hb).2.2.1) hh
  have injective : ∀ b (hb : b ∈ B) b' (hb' : b' ∈ B),
      V b hb = V b' hb' → b = b' := by
    intro b hb b' hb' he
    have hu : U b hb = U b' hb' := by
      apply unique_predecessor (hUV b hb)
      simpa [he] using hUV b' hb'
    apply Prod.ext
    · apply Fin.ext
      have h1 := hR b hb
      have h2 := hR b' hb'
      rw [he] at h1
      omega
    · apply Fin.ext
      have h1 := hC b hb
      have h2 := hC b' hb'
      rw [hu] at h1
      omega
  have surjective : ∀ v ∈ S.erase z, ∃ b, ∃ hb : b ∈ B, V b hb = v := by
    intro v hv
    obtain ⟨hvz, hvS⟩ := Finset.mem_erase.mp hv
    have hvL := (memS v).1 hvS
    have hzv : z.1 < v.1 := by
      apply lt_of_le_of_ne (hz.le hvL)
      intro he
      exact hvz (rowinj v hvL z hz.1 he.symm)
    obtain ⟨u, hu⟩ := exists_maximalFor_of_wellFoundedGT
      (fun u : Point m n ↦ LocalMin I a u ∧ u.1 < v.1)
      (fun u : Point m n ↦ u.1) ⟨z, hz.1, hzv⟩
    have huv : Adjacent I a u v := by
      refine ⟨hu.1.1, hvL, hu.1.2, ?_⟩
      intro w hw hh
      exact (not_le_of_gt hh.1) (hu.2 ⟨hw, hh.2⟩ (le_of_lt hh.1))
    have hvu : v.2 < u.2 := by
      by_contra hn
      have hh := hvL.1.2 hu.1.1.1.1 (show u ≤ v from ⟨le_of_lt hu.1.2, le_of_not_gt hn⟩)
      exact (not_le_of_gt hu.1.2) hh.1
    have hvpos : 0 < v.1.val := by
      have hh := hu.1.2
      change u.1.val < v.1.val at hh
      omega
    have hupos : 0 < u.2.val := by
      change v.2.val < u.2.val at hvu
      omega
    let b : Point m n :=
      (⟨v.1.val - 1, by have hh := v.1.isLt; omega⟩,
       ⟨u.2.val - 1, by have hh := u.2.isLt; omega⟩)
    have hr : b.1.val + 1 = v.1.val := by change v.1.val - 1 + 1 = v.1.val; omega
    have hs : b.2.val + 1 = u.2.val := by change u.2.val - 1 + 1 = u.2.val; omega
    have hb : b ∈ B := (memB b).2 (adjacent_gives_corner hI ha huv hr hs)
    refine ⟨b, hb, ?_⟩
    apply rowinj _ (hUV b hb).2.1 v hvL
    apply Fin.ext
    have hh := hR b hb
    omega
  have hcard : B.card = (S.erase z).card := Finset.card_bij V maps injective surjective
  change B.card + 1 = S.card
  rw [hcard]
  exact Finset.card_erase_add_one hzS

#print axioms adjacent_gives_corner
#print axioms corner_gives_adjacent
#print axioms rectangular_corner_card

end D5.S3.Combinatorics.Geometry.RectangularCorner
