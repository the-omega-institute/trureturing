/- GID: D5/S1/Dynamics/Shadowing/ReturnDistanceSupport
   generality: G
   mirror-B: D5/B/S1/Dynamics/Shadowing/ReturnDistanceSupport
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Repair of integer return-distance supports by separated intervals of unit gaps. -/

import Mathlib.Data.Int.Interval
import Mathlib.Tactic

/-! Integer supports repaired without choosing an enumeration. -/

namespace D5.S1.Dynamics.Shadowing

/-- Consecutive members of a support, including the strict order of its endpoints. -/
def SupportAdjacent (P : Set ℤ) (p q : ℤ) : Prop :=
  p ∈ P ∧ q ∈ P ∧ p < q ∧ ∀ t, p < t → t < q → t ∉ P

/-- Fill the middle of each illegal original gap, without enumerating the support. -/
def gapInsertions (D P : Set ℤ) (h : ℤ) : Set ℤ :=
  {t | ∃ p q, SupportAdjacent P p q ∧ q - p ∉ D ∧ p + h ≤ t ∧ t ≤ q - h}

def repairedSupport (D P : Set ℤ) (h : ℤ) : Set ℤ := P ∪ gapInsertions D P h

/-- Every new point is separated from every original point by at least h. -/
theorem insertion_separated {D P : Set ℤ} {h t s : ℤ}
    (ht : t ∈ gapInsertions D P h) (hs : s ∈ P) : t ≤ s - h ∨ s + h ≤ t := by
  obtain ⟨p, q, hpq, _, hpt, htq⟩ := ht
  by_cases hsp : s ≤ p
  · right; omega
  · left
    have hqs : q ≤ s := by
      by_contra! hsq
      exact hpq.2.2.2 s (by omega) hsq hs
    omega

/-- Short original gaps remain untouched; every long repaired gap has edge distances h
and internal distances one. The statement includes finite and unbounded supports. -/
theorem repaired_support_legal {D P : Set ℤ} {h : ℤ} (hpos : 0 < h)
    (hone : 1 ∈ D) (hh : h ∈ D)
    (hshort : ∀ p q, SupportAdjacent P p q → q - p ≤ 2 * h → q - p ∈ D) :
    ∀ x y, SupportAdjacent (repairedSupport D P h) x y → y - x ∈ D := by
  intro x y hxy
  have hxlt := hxy.2.2.1
  have hnone := hxy.2.2.2
  rcases hxy.1 with hx | hx <;> rcases hxy.2.1 with hy | hy
  · have hbase : SupportAdjacent P x y :=
      ⟨hx, hy, hxlt, fun t hxt hty ht => hnone t hxt hty (Or.inl ht)⟩
    by_contra hbad
    have hlong : 2 * h < y - x := by
      by_contra! hle
      exact hbad (hshort x y hbase hle)
    exact hnone (x + h) (by omega) (by omega)
      (Or.inr ⟨x, y, hbase, hbad, le_rfl, by omega⟩)
  · obtain ⟨p, q, hpq, hbad, hpy, hyq⟩ := hy
    have hxp : x ≤ p := by
      by_contra! hpx
      exact hpq.2.2.2 x hpx (by omega) hx
    have hxe : x = p := by
      by_contra hne
      exact hnone p (by omega) (by omega) (Or.inl hpq.1)
    have hye : y = p + h := by
      by_contra hne
      exact hnone (p + h) (by omega) (by omega)
        (Or.inr ⟨p, q, hpq, hbad, le_rfl, by omega⟩)
    simpa [hxe, hye] using hh
  · obtain ⟨p, q, hpq, hbad, hpx, hxq⟩ := hx
    have hqy : q ≤ y := by
      by_contra! hyq
      exact hpq.2.2.2 y (by omega) hyq hy
    have hye : y = q := by
      by_contra hne
      exact hnone q (by omega) (by omega) (Or.inl hpq.2.1)
    have hxe : x = q - h := by
      by_contra hne
      exact hnone (q - h) (by omega) (by omega)
        (Or.inr ⟨p, q, hpq, hbad, by omega, le_rfl⟩)
    simpa [hxe, hye] using hh
  · obtain ⟨p, q, hpq, hbad, hpx, hxq⟩ := hx
    have hyq : y ≤ q - h := by
      rcases insertion_separated hy hpq.2.1 with hl | hr
      · exact hl
      · exact (hnone q (by omega) (by omega) (Or.inl hpq.2.1)).elim
    have hunit : y - x = 1 := by
      by_contra hne
      exact hnone (x + 1) (by omega) (by omega)
        (Or.inr ⟨p, q, hpq, hbad, by omega, by omega⟩)
    simpa [hunit] using hone

/-- A radius-r window containing an original point cannot contain any insertion. -/
theorem repaired_window_eq {D P : Set ℤ} {h r i : ℤ} (hh : 2 * r < h)
    (hs : ∃ s ∈ P, i - r ≤ s ∧ s ≤ i + r) :
    ∀ t, i - r ≤ t → t ≤ i + r → (t ∈ repairedSupport D P h ↔ t ∈ P) := by
  obtain ⟨s, hs, hsl, hsu⟩ := hs
  intro t htl htu
  constructor
  · rintro (ht | ht)
    · exact ht
    · rcases insertion_separated ht hs with hl | hu <;> omega
  · exact Or.inl

/-- Keeping only one interval of a legal support creates no new consecutive pair. -/
theorem truncated_support_legal {D P : Set ℤ} {l u : ℤ}
    (hlegal : ∀ p q, SupportAdjacent P p q → u - l ≥ q - p → q - p ∈ D) :
    ∀ p q, SupportAdjacent (P ∩ Set.Icc l u) p q → q - p ∈ D := by
  intro p q hpq
  obtain ⟨hpl, hpu⟩ := hpq.1.2
  obtain ⟨hql, hqu⟩ := hpq.2.1.2
  apply hlegal p q
  · refine ⟨hpq.1.1, hpq.2.1.1, hpq.2.2.1, ?_⟩
    intro t hpt htq ht
    exact hpq.2.2.2 t hpt htq ⟨ht, by
      constructor <;> omega⟩
  · omega

#print axioms repaired_support_legal
#print axioms repaired_window_eq

end D5.S1.Dynamics.Shadowing
