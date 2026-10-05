/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrangeExponentEstimate
   generality: I
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrangeExponentEstimate
   mirror-E: none(waiver:stationary-cut-exponent-estimate)
   anchors: []
   utility: none
   digest: A uniform cut separation controls actual exponents by stationary maximal gaps. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeGapStability
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeIntervalPower
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeConfinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs
open scoped ENNReal

/-- One stationary maximal interval controls all sufficiently small return displacements.
The separation is chosen uniformly from the nonzero cuts; the actual exponent supremum
is bounded and attained, rather than replaced by a geometric definition. -/
theorem kabelian_critical_exponent_formula {alpha : ℝ}
    (h0 : 0 ≤ alpha) (h1 : alpha < 1) (hirr : Irrational alpha)
    {k : ℕ} (hk : 2 ≤ k) :
    let S := insert 1 (insert 0
      (((Finset.Icc 1 (k - 1)).image (fun j : ℕ => Int.fract ((j : ℝ) * alpha))) ∪
        ((Finset.Icc 1 (k - 1)).image (fun j : ℕ => 1 - Int.fract ((j : ℝ) * alpha)))))
    ∃ a b eta : ℝ, a ∈ S ∧ b ∈ S ∧ a < b ∧
      (∀ x ∈ S, x ≤ a ∨ b ≤ x) ∧
      (∀ u ∈ S, ∀ v ∈ S, u < v →
        (∀ x ∈ S, x ≤ u ∨ v ≤ x) → v - u ≤ b - a) ∧
      0 < eta ∧ (∀ m : ℕ, k ≤ m →
        |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)| < eta →
        |(ae k alpha m : ℝ) - (b - a) /
          (|(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|)| ≤ 2) ∧
      ac k alpha = ENNReal.ofReal (b - a) * Filter.limsup
        (fun m : ℕ => ENNReal.ofReal (1 / ((m : ℝ) *
          |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|))) Filter.atTop := by
  classical
  let J := Finset.Icc 1 (k - 1)
  let f (j : ℕ) := Int.fract ((j : ℝ) * alpha)
  let cut (j : ℕ) := 1 - f j
  let C := J.image f ∪ J.image cut
  let S := insert 1 (insert 0 C)
  change ∃ a b eta : ℝ, a ∈ S ∧ b ∈ S ∧ a < b ∧ _
  have hf (j : ℕ) (hj : j ∈ J) : 0 < f j ∧ f j < 1 := by
    have hj0 : j ≠ 0 := by have := (Finset.mem_Icc.mp hj).1; omega
    exact ⟨Int.fract_pos.mpr ((hirr.natCast_mul hj0).ne_int _), Int.fract_lt_one _⟩
  have hC : ∀ x ∈ C, 0 < x ∧ x < 1 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hf j hj
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have hh := hf j hj
      dsimp [cut]; constructor <;> linarith
  have hCne : C.Nonempty := by
    refine ⟨f 1, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨1, ?_, rfl⟩)⟩
    exact Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  let eta := C.min' hCne
  have heta : 0 < eta := (hC _ (Finset.min'_mem _ _)).1
  have hmargin (j : ℕ) (hj : j ∈ J) : eta ≤ f j ∧ eta ≤ 1 - f j := by
    exact ⟨Finset.min'_le _ _ (Finset.mem_union_left _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩)),
      Finset.min'_le _ _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨j, hj, rfl⟩))⟩
  have hS0 : 0 ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hS1 : 1 ∈ S := Finset.mem_insert_self _ _
  have hS : ∀ x ∈ S, 0 ≤ x ∧ x ≤ 1 := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    exact ⟨(hC x hx).1.le, (hC x hx).2.le⟩
  have hself : ∀ x ∈ S, ∃ y ∈ S, |x - y| ≤ (0 : ℝ) := by
    intro x hx; exact ⟨x, hx, by simp⟩
  obtain ⟨a, b, _, _, ha, hb, hab, hgap, hmax, _⟩ :=
    finite_cut_gap_stability S S hS0 hS1 hS hS0 hS1 hS hself hself
  have hestimate : ∀ m : ℕ, k ≤ m →
      |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)| < eta →
      |(ae k alpha m : ℝ) - (b - a) /
        (|(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|)| ≤ 2 := by
    intro m hmk hsmall
    have hm : 0 < m := by omega
    let t := (m : ℝ) * alpha
    let c : ℤ := round t
    let d := t - (c : ℝ)
    let delta := |d|
    change delta < eta at hsmall
    have hd0 : 0 < delta := abs_pos.mpr
      (sub_ne_zero.mpr ((hirr.natCast_mul (Nat.ne_of_gt hm)).ne_int c))
    have hdhalf : delta ≤ 1 / 2 := abs_sub_round t
    have hd : -delta ≤ d ∧ d ≤ delta := abs_le.mp (le_refl delta)
    let A := min (0 : ℝ) (-d)
    let B := max (0 : ℝ) (-d)
    have hA : A ≤ 0 := min_le_left _ _
    have hB : 0 ≤ B := le_max_left _ _
    have hAB : B - A = delta := by
      rcases le_total 0 d with hdpos | hdneg
      · simp only [A, B, min_eq_right (neg_nonpos.mpr hdpos),
          max_eq_left (neg_nonpos.mpr hdpos), delta, abs_of_nonneg hdpos]
        ring
      · simp only [A, B, min_eq_left (neg_nonneg.mpr hdneg),
          max_eq_right (neg_nonneg.mpr hdneg), delta, abs_of_nonpos hdneg]
        ring
    have hzero : A ≤ (0 : ℝ) ∧ (0 : ℝ) ≤ B := ⟨hA, hB⟩
    have hshift : A ≤ -d ∧ -d ≤ B := ⟨min_le_right _ _, le_max_right _ _⟩
    let T := insert 1 (insert 0
      ((Finset.range k).image cut ∪ (Finset.range k).image (fun j => cut (m - j))))
    have hT0 : 0 ∈ T := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hT1 : 1 ∈ T := Finset.mem_insert_self _ _
    have hT : ∀ x ∈ T, 0 ≤ x ∧ x ≤ 1 := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · norm_num
      rcases Finset.mem_insert.mp hx with rfl | hx
      · norm_num
      rcases Finset.mem_union.mp hx with hx | hx
      all_goals
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        dsimp [cut, f]
        constructor <;> linarith [Int.fract_nonneg ((j : ℝ) * alpha),
          Int.fract_lt_one ((j : ℝ) * alpha),
          Int.fract_nonneg (((m - j : ℕ) : ℝ) * alpha),
          Int.fract_lt_one (((m - j : ℕ) : ℝ) * alpha)]
    have hneg (r : ℕ) (hr : 0 < r) : cut r = Int.fract (-((r : ℝ) * alpha)) := by
      exact (Int.fract_neg (ne_of_gt
        (Int.fract_pos.mpr ((hirr.natCast_mul (Nat.ne_of_gt hr)).ne_int _)))).symm
    have hmove (j : ℕ) (hj : j ∈ J) : cut (m - j) = f j - d := by
      have hjm : j ≤ m := ((Finset.mem_Icc.mp hj).2).trans (by omega)
      have hpos : 0 < m - j := by have := (Finset.mem_Icc.mp hj).2; omega
      have hmar := hmargin j hj
      have hunit : 0 ≤ f j - d ∧ f j - d < 1 := by constructor <;> linarith
      rw [hneg _ hpos]
      have heq : -(((m - j : ℕ) : ℝ) * alpha) =
          (f j - d) + ((⌊(j : ℝ) * alpha⌋ - c : ℤ) : ℝ) := by
        dsimp [f, d, t]
        rw [Nat.cast_sub hjm, Int.fract]
        push_cast
        ring
      rw [heq, Int.fract_add_intCast, Int.fract_eq_self.mpr hunit]
    have hcentral : cut m = if d < 0 then -d else 1 - d := by
      rw [hneg m hm]
      have heq : -((m : ℝ) * alpha) = -d + ((-c : ℤ) : ℝ) := by
        dsimp [d, t]; push_cast; ring
      rw [heq, Int.fract_add_intCast]
      split_ifs with h
      · exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
      · have hdpos : 0 < d := by
          have hdne : d ≠ 0 := abs_pos.mp hd0
          exact lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hdne)
        have he : Int.fract (-d + 1) = -d + 1 :=
          Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
        rw [Int.fract_add_one] at he
        linarith
    have hprefix (j : ℕ) (hj : j < k) : cut j ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)))
    have hsuffix (j : ℕ) (hj : j < k) : cut (m - j) ∈ T :=
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)))
    have hST : ∀ x ∈ S, ∃ y ∈ T, A ≤ y - x ∧ y - x ≤ B := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨1, hT1, by simpa using hzero⟩
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨0, hT0, by simpa using hzero⟩
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        refine ⟨cut (m - j), hsuffix j (by have := (Finset.mem_Icc.mp hj).2; omega), ?_⟩
        rw [hmove j hj, sub_sub_cancel_left]
        exact hshift
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨cut j, hprefix j (by have := (Finset.mem_Icc.mp hj).2; omega),
          by simpa using hzero⟩
    have hTS : ∀ y ∈ T, ∃ x ∈ S, A ≤ y - x ∧ y - x ≤ B := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨1, hS1, by simpa using hzero⟩
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact ⟨0, hS0, by simpa using hzero⟩
      rcases Finset.mem_union.mp hy with hy | hy
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        by_cases hz : j = 0
        · subst j; exact ⟨1, hS1, by simpa [cut, f] using hzero⟩
        have hjJ : j ∈ J := Finset.mem_Icc.mpr
          ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩
        refine ⟨cut j, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hjJ, rfl⟩))), ?_⟩
        simpa using hzero
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        by_cases hz : j = 0
        · subst j
          simp only [Nat.sub_zero]
          by_cases hn : d < 0
          · refine ⟨0, hS0, ?_⟩
            rw [hcentral, if_pos hn, sub_zero]
            exact hshift
          · refine ⟨1, hS1, ?_⟩
            rw [hcentral, if_neg hn, sub_sub_cancel_left]
            exact hshift
        have hjJ : j ∈ J := Finset.mem_Icc.mpr
          ⟨by omega, by have := Finset.mem_range.mp hj; omega⟩
        refine ⟨f j, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hjJ, rfl⟩))), ?_⟩
        rw [hmove j hjJ, sub_sub_cancel_left]
        exact hshift
    have hSTabs : ∀ x ∈ S, ∃ y ∈ T, |x - y| ≤ delta := by
      intro x hx
      obtain ⟨y, hy, hxy⟩ := hST x hx
      refine ⟨y, hy, abs_le.mpr ?_⟩
      constructor <;> linarith
    have hTSabs : ∀ y ∈ T, ∃ x ∈ S, |y - x| ≤ delta := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := hTS y hy
      refine ⟨x, hx, abs_le.mpr ?_⟩
      constructor <;> linarith
    obtain ⟨_, _, l, r, _, _, _, _, _, hl, hr, hlr, hgapT, hmaxT, _⟩ :=
      finite_cut_gap_stability S T hS0 hS1 hS hT0 hT1 hT hSTabs hTSabs
    have transfer (U V : Finset ℝ) (hV0 : 0 ∈ V) (hV1 : 1 ∈ V)
        (hU : ∀ x ∈ U, 0 ≤ x ∧ x ≤ 1) (s z : ℝ) (hs : s ≤ 0) (hz : 0 ≤ z)
        (hclose : ∀ y ∈ V, ∃ x ∈ U, s ≤ y - x ∧ y - x ≤ z)
        (p q l r : ℝ) (hp : p ∈ U) (hq : q ∈ U) (hpq : p < q)
        (hgap : ∀ x ∈ U, x ≤ p ∨ q ≤ x) (hlr : l < r)
        (hmax : ∀ x ∈ V, ∀ y ∈ V, x < y →
          (∀ t ∈ V, t ≤ x ∨ y ≤ t) → y - x ≤ r - l) :
        q - p ≤ r - l + (z - s) := by
      by_cases hshort : q - p ≤ z - s
      · linarith
      have hwide : z - s < q - p := lt_of_not_ge hshort
      let mid := (p + z + q + s) / 2
      have hmid0 : 0 ≤ mid := by dsimp [mid]; linarith [(hU p hp).1]
      have hmid1 : mid < 1 := by dsimp [mid]; linarith [(hU q hq).2]
      have htrim : ∀ y ∈ V, y ≤ p + z ∨ q + s ≤ y := by
        intro y hy
        obtain ⟨x, hx, hxy⟩ := hclose y hy
        rcases hgap x hx with h | h
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      let L := V.filter fun x => x ≤ mid
      let R := V.filter fun x => mid < x
      have hL : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hV0, hmid0⟩⟩
      have hR : R.Nonempty := ⟨1, Finset.mem_filter.mpr ⟨hV1, hmid1⟩⟩
      let x := L.max' hL
      let y := R.min' hR
      have hx := Finset.mem_filter.mp (show x ∈ L from Finset.max'_mem _ _)
      have hy := Finset.mem_filter.mp (show y ∈ R from Finset.min'_mem _ _)
      have hxl : x ≤ p + z := by
        rcases htrim x hx.1 with h | h
        · exact h
        · dsimp [mid] at hx; linarith [hx.2]
      have hyr : q + s ≤ y := by
        rcases htrim y hy.1 with h | h
        · dsimp [mid] at hy; linarith [hy.2]
        · exact h
      have hgapV : ∀ t ∈ V, t ≤ x ∨ y ≤ t := by
        intro t ht
        by_cases h : t ≤ mid
        · exact Or.inl (Finset.le_max' _ _ (Finset.mem_filter.mpr ⟨ht, h⟩))
        · exact Or.inr (Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨ht, lt_of_not_ge h⟩))
      have hlen := hmax x hx.1 y hy.1 (hx.2.trans_lt hy.2) hgapV
      linarith
    have hdist : |(b - a) - (r - l)| ≤ delta := by
      have hforward := transfer S T hT0 hT1 hS A B hA hB hTS
        a b l r ha hb hab hgap hlr hmaxT
      have hreverseClose : ∀ x ∈ S, ∃ y ∈ T, -B ≤ x - y ∧ x - y ≤ -A := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hST x hx
        exact ⟨y, hy, by constructor <;> linarith⟩
      have hbackward := transfer T S hS0 hS1 hT (-B) (-A)
        (neg_nonpos.mpr hB) (neg_nonneg.mpr hA) hreverseClose
        l r a b hl hr hlr hgapT hab hmax
      rw [abs_le]
      constructor <;> linarith
    have hcutmem (q : ℕ) (hq : 0 < q) (hqm : q ≤ m)
        (hqk : q ≤ k - 1 ∨ m - (k - 1) ≤ q) : cut q ∈ T := by
      rcases hqk with hqk | hqk
      · exact hprefix q (by omega)
      · have hj : m - q < k := by omega
        simpa only [Nat.sub_sub_self hqm] using hsuffix (m - q) hj
    have hends (x : ℝ) (hx : x ∈ T) : x = 0 ∨ x = 1 ∨
        ∃ q : ℕ, 0 < q ∧ q ≤ m ∧
          (q ≤ k - 1 ∨ m - (k - 1) ≤ q) ∧ x = cut q := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (Or.inl rfl)
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inl rfl
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        by_cases hz : j = 0
        · subst j; exact Or.inr (Or.inl (by simp [cut, f]))
        have hjk : j < k := Finset.mem_range.mp hj
        exact Or.inr (Or.inr ⟨j, by omega, by omega, Or.inl (by omega), rfl⟩)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
        have hjk : j < k := Finset.mem_range.mp hj
        exact Or.inr (Or.inr ⟨m - j, by omega, Nat.sub_le _ _,
          Or.inr (by omega), rfl⟩)
    let E := ⌈(r - l) / delta⌉₊
    have hEpos : 0 < E := Nat.one_le_ceil_iff.mpr (div_pos (sub_pos.mpr hlr) hd0)
    have hEspan : ((E - 1 : ℕ) : ℝ) * delta < r - l := by
      apply (lt_div_iff₀ hd0).mp
      exact Nat.lt_ceil.mp (show E - 1 < E by omega)
    have hEp : E ∈ {e : ℕ | ∃ start, IsKAbelianPower alpha k m e start} := by
      apply kabelian_power_in_cut_interval h0 h1 hirr (hT l hl).1 hlr (hT r hr).2
        (show k - 1 ≤ m by omega) hEpos c
      · intro q hq hqm hqk
        exact hgapT (cut q) (hcutmem q hq hqm hqk)
      · exact hEspan
    have hupper (e : ℕ) (he : e ∈ {e : ℕ | ∃ start,
        IsKAbelianPower alpha k m e start}) : e ≤ E := by
      by_cases he0 : e = 0
      · subst e; exact Nat.zero_le _
      obtain ⟨start, hp⟩ := he
      obtain ⟨p, q, hp0, hpq, hq1, hpend, hqend, hpqcut, _, hspan⟩ :=
        kabelian_power_cut_confinement h0 h1 (show 1 ≤ k by omega)
          (show k - 1 ≤ m by omega) (Nat.pos_of_ne_zero he0) hp
      have hpmem : p ∈ T := by
        rcases hpend with rfl | ⟨j, hj, hjm, hjk, rfl⟩
        · exact hT0
        · exact hcutmem j hj hjm hjk
      have hqmem : q ∈ T := by
        rcases hqend with rfl | ⟨j, hj, hjm, hjk, rfl⟩
        · exact hT1
        · exact hcutmem j hj hjm hjk
      have hcuts : ∀ x ∈ T, x ≤ p ∨ q ≤ x := by
        intro x hx
        rcases hends x hx with rfl | rfl | ⟨j, hj, hjm, hjk, rfl⟩
        · exact Or.inl hp0
        · exact Or.inr hq1
        · exact hpqcut j hj hjm hjk
      have hw := hmaxT p hpmem q hqmem hpq hcuts
      have hh : ((e - 1 : ℕ) : ℝ) < (r - l) / delta :=
        (lt_div_iff₀ hd0).mpr (hspan.trans_le hw)
      have hlt : e - 1 < E := Nat.lt_ceil.mpr hh
      omega
    have hsup : ae k alpha m = E := by
      rw [ae, if_neg (Nat.ne_of_gt hm)]
      exact le_antisymm (csSup_le ⟨E, hEp⟩ hupper) (le_csSup ⟨E, hupper⟩ hEp)
    have hround : |(E : ℝ) - (r - l) / delta| ≤ 1 :=
      Nat.abs_ceil_sub_le (div_nonneg (sub_nonneg.mpr hlr.le) hd0.le)
    have hgeom : |(r - l) / delta - (b - a) / delta| ≤ 1 := by
      rw [← sub_div, abs_div, abs_of_pos hd0]
      apply (div_le_iff₀ hd0).mpr
      simpa only [abs_sub_comm, one_mul] using hdist
    change |(ae k alpha m : ℝ) - (b - a) / delta| ≤ 2
    rw [hsup]
    calc
      |(E : ℝ) - (b - a) / delta| ≤
          |(E : ℝ) - (r - l) / delta| + |(r - l) / delta - (b - a) / delta| :=
        abs_sub_le _ _ _
      _ ≤ 2 := by linarith
  refine ⟨a, b, eta, ha, hb, hab, hgap, hmax, heta, hestimate, ?_⟩
  let G := b - a
  have hG0 : 0 < G := sub_pos.mpr hab
  have hG1 : G ≤ 1 := by dsimp [G]; linarith [(hS a ha).1, (hS b hb).2]
  let C0 := max (2 : ℝ) (1 / eta + 1)
  have hC0 : 0 ≤ C0 := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  have hglobal (m : ℕ) (hmk : k ≤ m) :
      |(ae k alpha m : ℝ) - G /
        (|(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|)| ≤ C0 := by
    let t := (m : ℝ) * alpha
    let delta := |t - (round t : ℝ)|
    have hm : 0 < m := by omega
    have hd0 : 0 < delta := abs_pos.mpr
      (sub_ne_zero.mpr ((hirr.natCast_mul (Nat.ne_of_gt hm)).ne_int _))
    by_cases hsmall : delta < eta
    · exact (hestimate m hmk hsmall).trans (le_max_left _ _)
    have hlarge : eta ≤ delta := le_of_not_gt hsmall
    let P : Set ℕ := {e | ∃ start, IsKAbelianPower alpha k m e start}
    have hP : P.Nonempty := by
      refine ⟨1, 0, ?_⟩
      intro i j hi hj
      have hi0 : i = 0 := by omega
      have hj0 : j = 0 := by omega
      subst i; subst j
      intro z _ _; rfl
    have hupper (e : ℕ) (he : e ∈ P) : e ≤ ⌈1 / delta⌉₊ := by
      by_cases he0 : e = 0
      · subst e; exact Nat.zero_le _
      obtain ⟨start, hp⟩ := he
      obtain ⟨c, _, hspan⟩ := kabelian_power_phase_span h0 h1
        (show 1 ≤ k by omega) (Nat.pos_of_ne_zero he0) hp
      have hnear : delta ≤ |t - c| := round_le t c
      have hh : (e : ℝ) * delta < 1 :=
        (mul_le_mul_of_nonneg_left hnear (Nat.cast_nonneg e)).trans_lt hspan
      exact (Nat.lt_ceil.mpr ((lt_div_iff₀ hd0).mpr hh)).le
    have hae : (ae k alpha m : ℝ) ≤ 1 / delta + 1 := by
      have hh : ae k alpha m ≤ ⌈1 / delta⌉₊ := by
        rw [ae, if_neg (Nat.ne_of_gt hm)]
        exact csSup_le hP hupper
      exact (Nat.cast_le.mpr hh).trans
        (Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 / delta)).le
    have hinv : 1 / delta ≤ 1 / eta := one_div_le_one_div_of_le heta hlarge
    have hgapquot : G / delta ≤ 1 / eta :=
      (div_le_div_of_nonneg_right hG1 hd0.le).trans hinv
    have hquot0 : 0 ≤ G / delta := div_nonneg hG0.le hd0.le
    have hmaxbound : 1 / eta + 1 ≤ C0 := le_max_right _ _
    rw [abs_le]
    have hae0 : (0 : ℝ) ≤ (ae k alpha m : ℝ) := Nat.cast_nonneg _
    constructor <;> linarith
  let u (m : ℕ) : ℝ≥0∞ := (ae k alpha m : ℝ≥0∞) / (m : ℝ≥0∞)
  let coeff (m : ℕ) := ENNReal.ofReal (1 / ((m : ℝ) *
    |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|))
  let v (m : ℕ) := ENNReal.ofReal G * coeff m
  let err (m : ℕ) := ENNReal.ofReal (C0 / (m : ℝ))
  have herr : Filter.Tendsto err Filter.atTop (nhds 0) := by
    simpa only [err, Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_const_div_atTop_nhds_zero_nat C0)
  have hsandwich : ∀ᶠ m : ℕ in Filter.atTop,
      u m ≤ v m + err m ∧ v m ≤ u m + err m := by
    refine Filter.eventually_atTop.mpr ⟨k, ?_⟩
    intro m hmk
    have hm : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
    let delta := |(m : ℝ) * alpha - (round ((m : ℝ) * alpha) : ℝ)|
    have hd0 : 0 < delta := abs_pos.mpr
      (sub_ne_zero.mpr ((hirr.natCast_mul (show m ≠ 0 by omega)).ne_int _))
    have hreal : |(ae k alpha m : ℝ) / (m : ℝ) -
        G * (1 / ((m : ℝ) * delta))| ≤ C0 / (m : ℝ) := by
      have h := div_le_div_of_nonneg_right (hglobal m hmk) hm.le
      have heq : G * (1 / ((m : ℝ) * delta)) = (G / delta) / (m : ℝ) := by
        field_simp
      rw [heq, ← sub_div, abs_div, abs_of_pos hm]
      exact h
    have hu : ENNReal.ofReal ((ae k alpha m : ℝ) / (m : ℝ)) = u m := by
      simp only [u, ENNReal.ofReal_div_of_pos hm, ENNReal.ofReal_natCast]
    have hv : ENNReal.ofReal (G * (1 / ((m : ℝ) * delta))) = v m :=
      ENNReal.ofReal_mul hG0.le
    have he0 : 0 ≤ C0 / (m : ℝ) := div_nonneg hC0 hm.le
    have hv0 : 0 ≤ G * (1 / ((m : ℝ) * delta)) := by positivity
    have hu0 : 0 ≤ (ae k alpha m : ℝ) / (m : ℝ) := by positivity
    have hbounds := abs_le.mp hreal
    constructor
    · rw [← hu, ← hv, ← ENNReal.ofReal_add hv0 he0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rw [← hu, ← hv, ← ENNReal.ofReal_add hu0 he0]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  have hlim : Filter.limsup u Filter.atTop = Filter.limsup v Filter.atTop := by
    apply le_antisymm
    · have h := Filter.limsup_le_limsup (hsandwich.mono fun _ h => h.1)
      change Filter.limsup u Filter.atTop ≤ Filter.limsup (v + err) Filter.atTop at h
      rw [ENNReal.limsup_add_of_right_tendsto_zero herr] at h
      exact h
    · have h := Filter.limsup_le_limsup (hsandwich.mono fun _ h => h.2)
      change Filter.limsup v Filter.atTop ≤ Filter.limsup (u + err) Filter.atTop at h
      rw [ENNReal.limsup_add_of_right_tendsto_zero herr] at h
      exact h
  have hmono : Monotone (fun x : ℝ≥0∞ => ENNReal.ofReal G * x) :=
    fun _ _ h => by simpa only [mul_comm] using mul_le_mul_left h (ENNReal.ofReal G)
  have hmap : Filter.limsup v Filter.atTop =
      ENNReal.ofReal G * Filter.limsup coeff Filter.atTop :=
    (hmono.map_limsSup_of_continuousAt (F := Filter.atTop.map coeff)
      (ENNReal.continuous_const_mul ENNReal.ofReal_ne_top).continuousAt).symm
  exact hlim.trans hmap

end D5.S1.Words.KAbelianLagrange
