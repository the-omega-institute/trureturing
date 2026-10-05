/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeGapStability
   generality: G
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeGapStability
   mirror-E: none(waiver:finite-cut-perturbation)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Trimming empty intervals controls maximal gaps under finite-cut perturbations. -/

import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

/-- Maximal adjacent intervals exist and vary by at most twice the two-sided cut error.
No distinctness, matching bijection, or preservation of cut order is required. -/
theorem finite_cut_gap_stability (S T : Finset ℝ) {delta : ℝ}
    (hS0 : 0 ∈ S) (hS1 : 1 ∈ S) (hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1)
    (hT0 : 0 ∈ T) (hT1 : 1 ∈ T) (hT : ∀ x ∈ T, 0 ≤ x ∧ x ≤ 1)
    (hST : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ delta)
    (hTS : ∀ y ∈ T, ∃ x ∈ S, |y - x| ≤ delta) :
    ∃ a b c d : ℝ,
      a ∈ S ∧ b ∈ S ∧ a < b ∧ (∀ x ∈ S, x ≤ a ∨ b ≤ x) ∧
      (∀ u ∈ S, ∀ v ∈ S, u < v → (∀ x ∈ S, x ≤ u ∨ v ≤ x) → v - u ≤ b - a) ∧
      c ∈ T ∧ d ∈ T ∧ c < d ∧ (∀ x ∈ T, x ≤ c ∨ d ≤ x) ∧
      (∀ u ∈ T, ∀ v ∈ T, u < v → (∀ x ∈ T, x ≤ u ∨ v ≤ x) → v - u ≤ d - c) ∧
      |(b - a) - (d - c)| ≤ 2 * delta := by
  classical
  have select (U : Finset ℝ) (hU0 : 0 ∈ U) (hU1 : 1 ∈ U)
      : ∃ a b : ℝ, a ∈ U ∧ b ∈ U ∧ a < b ∧ (∀ x ∈ U, x ≤ a ∨ b ≤ x) ∧
        (∀ u ∈ U, ∀ v ∈ U, u < v →
          (∀ x ∈ U, x ≤ u ∨ v ≤ x) → v - u ≤ b - a) := by
    let V := U.filter fun x => 0 < x
    have hV : V.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨hU1, by norm_num⟩⟩
    let b := V.min' hV
    have hb : b ∈ V := Finset.min'_mem _ _
    have hcuts : ∀ x ∈ U, x ≤ 0 ∨ b ≤ x := by
      intro x hx
      by_cases h : x ≤ 0
      · exact Or.inl h
      · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge h⟩))
    let P := (U ×ˢ U).filter fun p =>
      p.1 < p.2 ∧ ∀ x ∈ U, x ≤ p.1 ∨ p.2 ≤ x
    have hP : P.Nonempty := ⟨(0, b), Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hU0, (Finset.mem_filter.mp hb).1⟩,
        (Finset.mem_filter.mp hb).2, hcuts⟩⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image P (fun p => p.2 - p.1) hP
    have hm := Finset.mem_filter.mp hp
    have hm' := Finset.mem_product.mp hm.1
    refine ⟨p.1, p.2, hm'.1, hm'.2, hm.2.1, hm.2.2, ?_⟩
    intro u hu v hv huv hgap
    exact hmax (u, v) (Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hu, hv⟩, huv, hgap⟩)
  obtain ⟨a, b, ha, hb, hab, hgapS, hmaxS⟩ := select S hS0 hS1
  obtain ⟨c, d, hc, hd, hcd, hgapT, hmaxT⟩ := select T hT0 hT1
  have transfer (U V : Finset ℝ) (hV0 : 0 ∈ V) (hV1 : 1 ∈ V)
      (hU : ∀ x ∈ U, 0 ≤ x ∧ x ≤ 1)
      (hclose : ∀ y ∈ V, ∃ x ∈ U, |y - x| ≤ delta)
      (l r p q : ℝ) (hl : l ∈ U) (hr : r ∈ U) (hlr : l < r)
      (hgap : ∀ x ∈ U, x ≤ l ∨ r ≤ x) (hpq : p < q)
      (hmax : ∀ u ∈ V, ∀ v ∈ V, u < v →
        (∀ x ∈ V, x ≤ u ∨ v ≤ x) → v - u ≤ q - p) :
      r - l ≤ q - p + 2 * delta := by
    by_cases hshort : r - l ≤ 2 * delta
    · linarith
    have hwide : 2 * delta < r - l := lt_of_not_ge hshort
    let z := (l + r) / 2
    have hz0 : 0 ≤ z := by dsimp [z]; linarith [(hU l hl).1, (hU r hr).1]
    have hz1 : z < 1 := by dsimp [z]; linarith [(hU r hr).2]
    have htrim : ∀ y ∈ V, y ≤ l + delta ∨ r - delta ≤ y := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hclose y hy
      have hdist := abs_le.mp hxy
      rcases hgap x hx with hx | hx
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    let L := V.filter fun y => y ≤ z
    let R := V.filter fun y => z < y
    have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hV0, hz0⟩⟩
    have hR : R.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨hV1, hz1⟩⟩
    let u := L.max' hL
    let v := R.min' hR
    have huL : u ∈ L := Finset.max'_mem _ _
    have hvR : v ∈ R := Finset.min'_mem _ _
    have hu : u ∈ V := (Finset.mem_filter.mp huL).1
    have hv : v ∈ V := (Finset.mem_filter.mp hvR).1
    have huz : u ≤ z := (Finset.mem_filter.mp huL).2
    have hzv : z < v := (Finset.mem_filter.mp hvR).2
    have hule : u ≤ l + delta := by
      rcases htrim u hu with h | h
      · exact h
      · dsimp [z] at huz; linarith
    have hvge : r - delta ≤ v := by
      rcases htrim v hv with h | h
      · dsimp [z] at hzv; linarith
      · exact h
    have hgapV : ∀ x ∈ V, x ≤ u ∨ v ≤ x := by
      intro x hx
      by_cases h : x ≤ z
      · exact Or.inl (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨hx, h⟩))
      · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨hx, lt_of_not_ge h⟩))
    have hbound := hmax u hu v hv (huz.trans_lt hzv) hgapV
    linarith
  refine ⟨a, b, c, d, ha, hb, hab, hgapS, hmaxS, hc, hd, hcd, hgapT, hmaxT, ?_⟩
  rw [abs_le]
  constructor
  · have h := transfer T S hS0 hS1 hT hST c d a b hc hd hcd hgapT hab hmaxS
    linarith
  · have h := transfer S T hT0 hT1 hS hTS a b c d ha hb hab hgapS hcd hmaxT
    linarith

end D5.S1.Words.KAbelianLagrange
