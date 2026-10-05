/- GID: D5/S1/Words/KAbelianLagrange/KAbelianLagrange
   generality: I
   mirror-B: D5/B/S1/Words/KAbelianLagrange/KAbelianLagrange
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: The k-abelian Lagrange spectrum contains the ray above six over two k minus one. -/

import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeExponentEstimate
import D5.S1.Words.KAbelianLagrange.KAbelianLagrangeContinuous

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.KAbelianLagrange

open KAbelianLagrangeDefs GenContFract
open scoped ENNReal

set_option maxHeartbeats 1000000 in
-- Budget for the combined two-digit cylinder estimates and finite-cut classification.
/-- The half-line question of Peltomäki and Whiteland has an affirmative answer. -/
theorem result : KAbelianLagrangeDefs.claim := by
  classical
  intro k hk
  let n := k - 1
  let r : ℝ := 2 * (n : ℝ)
  let D := 2 * n + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hD : 0 < (D : ℝ) := by dsimp [D]; positivity
  have hD1 : 1 ≤ (D : ℝ) := by exact_mod_cast (show 1 ≤ D by dsimp [D]; omega)
  have hr : 0 < r := by dsimp [r]; exact mul_pos (by norm_num) (by exact_mod_cast hn)
  have hDr : (D : ℝ) = r + 1 := by dsimp [D, r]; push_cast; ring
  let c : ℝ := 1 / (D : ℝ)
  have hc : 0 < c := one_div_pos.mpr hD
  have hrc : 1 - r * c = c := by
    dsimp [c]
    rw [hDr]
    field_simp [ne_of_gt (by linarith : 0 < r + 1)]
    ring
  refine ⟨6 / (D : ℝ), ?_⟩
  intro t ht
  have ht6 : 6 * c < t := by simpa only [Set.mem_Ioi, c, mul_one_div] using ht
  have ht0 : 0 < t := lt_trans (by positivity) ht6
  let epsilon := min (c / 2) ((t / 6 - c) / (2 * r))
  have heps : 0 < epsilon := lt_min (by positivity)
    (div_pos (by linarith) (by positivity))
  have hepsc : epsilon ≤ c / 2 := min_le_left _ _
  have hepsr : r * epsilon ≤ (t / 6 - c) / 2 := by
    have h := min_le_right (c / 2) ((t / 6 - c) / (2 * r))
    have h' := (le_div_iff₀ (mul_pos (by norm_num) hr)).mp h
    dsimp [epsilon]
    linarith
  let l := c - epsilon
  have hl : 0 < l := by dsimp [l]; linarith
  have hlc : l ≤ c := by dsimp [l]; linarith
  let clip (x : ℝ) := max l (min c x)
  have hclip (x : ℝ) : l ≤ clip x ∧ clip x ≤ c := by
    exact ⟨le_max_left _ _, max_le hlc (min_le_left _ _)⟩
  have hden (x : ℝ) : c ≤ 1 - r * clip x ∧ 1 - r * clip x < t / 6 := by
    have h := hclip x
    have hlow := mul_le_mul_of_nonneg_left h.1 hr.le
    have hhigh := mul_le_mul_of_nonneg_left h.2 hr.le
    dsimp [l] at hlow
    constructor <;> nlinarith
  let F (x : ℝ) := t / (1 - r * clip x)
  have hF : Continuous F := by
    apply continuous_const.div
      (continuous_const.sub (continuous_const.mul
        (continuous_const.max (continuous_const.min continuous_id))))
    intro x
    exact ne_of_gt (hc.trans_le (hden x).1)
  obtain ⟨B, hB⟩ := exists_nat_gt (t / c)
  have hbound (x : ℝ) : 6 < F x ∧ F x ≤ (B : ℝ) := by
    have hd := hc.trans_le (hden x).1
    constructor
    · apply (lt_div_iff₀ hd).mpr
      have h := (hden x).2
      linarith
    · exact (div_le_div_of_nonneg_left ht0.le hc (hden x).1).trans hB.le
  obtain ⟨L, hL⟩ := exists_nat_gt (max 1 (1 / epsilon))
  have hL1 : 1 < (L : ℝ) := lt_of_le_of_lt (le_max_left _ _) hL
  have hLpos : 0 < L := by exact_mod_cast (show (0 : ℝ) < (L : ℝ) by linarith)
  have hLeps : 1 / (L : ℝ) < epsilon := by
    have h := lt_of_le_of_lt (le_max_right _ _) hL
    apply (div_lt_iff₀ (by linarith : 0 < (L : ℝ))).mpr
    have h' := (div_lt_iff₀ heps).mp h
    linarith
  let seed := [D, L]
  have hseed : ∀ a ∈ seed, 0 < a ∧ a ≤ max D L := by
    intro a ha
    simp only [seed, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · exact ⟨by dsimp [D]; omega, le_max_left _ _⟩
    · exact ⟨hLpos, le_max_right _ _⟩
  obtain ⟨alpha, hirr, ha0, ha1, hs, _, hlim⟩ :=
    continuous_feedback_realization seed (max D L) B hseed F hF hbound
  have hs0 : (GenContFract.of alpha).s.get? 0 = some ⟨1, (D : ℝ)⟩ := by
    simpa [seed] using hs 0 (by simp [seed])
  have hs1 : (GenContFract.of alpha).s.get? 1 = some ⟨1, (L : ℝ)⟩ := by
    simpa [seed] using hs 1 (by simp [seed])
  obtain ⟨P, hP, hPb⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hs0
  obtain ⟨Q, hQ, hQb⟩ := IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some hs1
  have hPunit := IntFractPair.nth_stream_fr_nonneg_lt_one hP
  have hQunit := IntFractPair.nth_stream_fr_nonneg_lt_one hQ
  obtain ⟨P0, hP0, _, hstep0⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hP
  have hP0eq : P0 = IntFractPair.of alpha :=
    Option.some.inj (hP0.symm.trans (IntFractPair.stream_zero alpha))
  subst P0
  have haf : Int.fract alpha = alpha := Int.fract_eq_self.mpr ⟨ha0.le, ha1⟩
  have hPf : Int.fract alpha⁻¹ = P.fr := by
    simpa only [IntFractPair.of, haf] using congrArg IntFractPair.fr hstep0
  have hPfloor : (⌊alpha⁻¹⌋ : ℝ) = (D : ℝ) := by
    have h := congrArg (fun p : IntFractPair ℝ => (p.b : ℝ)) hstep0
    simpa only [IntFractPair.of, haf] using h.trans hPb
  have hainv : alpha⁻¹ = (D : ℝ) + P.fr := by
    rw [← hPf, ← hPfloor, Int.floor_add_fract]
  have haeq : alpha = 1 / ((D : ℝ) + P.fr) := by rw [← hainv]; simp
  obtain ⟨P', hP', hPne, hstep⟩ := IntFractPair.succ_nth_stream_eq_some_iff.mp hQ
  have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
  subst P'
  have hPfpos : 0 < P.fr := lt_of_le_of_ne hPunit.1 hPne.symm
  have hQf : Int.fract P.fr⁻¹ = Q.fr := congrArg IntFractPair.fr hstep
  have hQfloor : (⌊P.fr⁻¹⌋ : ℝ) = (L : ℝ) :=
    (congrArg (fun p : IntFractPair ℝ => (p.b : ℝ)) hstep).trans hQb
  have hPinv : P.fr⁻¹ = (L : ℝ) + Q.fr := by
    rw [← hQf, ← hQfloor, Int.floor_add_fract]
  have hPeq : P.fr = 1 / ((L : ℝ) + Q.fr) := by rw [← hPinv]; simp
  have hPbound : P.fr ≤ 1 / (L : ℝ) := by
    rw [hPeq]
    exact one_div_le_one_div_of_le (by linarith) (by linarith [hQunit.1])
  have hac : alpha ≤ c := by
    rw [haeq]
    exact one_div_le_one_div_of_le hD (by linarith [hPunit.1])
  have hclose : c - alpha ≤ P.fr := by
    have heq : c - alpha = P.fr / ((D : ℝ) * ((D : ℝ) + P.fr)) := by
      rw [haeq]
      dsimp [c]
      field_simp [ne_of_gt hD, ne_of_gt (add_pos_of_pos_of_nonneg hD hPunit.1)]
      ring
    rw [heq]
    exact div_le_self hPunit.1 (by nlinarith)
  have hla : l ≤ alpha := by
    have h := hclose.trans_lt (hPbound.trans_lt hLeps)
    dsimp [l]
    linarith
  have hclipa : clip alpha = alpha := by
    dsimp [clip]
    rw [min_eq_right hac, max_eq_right hla]
  have hFa : F alpha = t / (1 - r * alpha) := by dsimp [F]; rw [hclipa]
  obtain ⟨a, b, eta, ha, hb, hab, hgap, hmax, _, _, hformula⟩ :=
    kabelian_critical_exponent_formula ha0.le ha1 hirr hk
  let S := insert 1 (insert 0
    (((Finset.Icc 1 n).image (fun j : ℕ => Int.fract ((j : ℝ) * alpha))) ∪
      ((Finset.Icc 1 n).image (fun j : ℕ => 1 - Int.fract ((j : ℝ) * alpha)))))
  change a ∈ S at ha
  change b ∈ S at hb
  change ∀ x ∈ S, x ≤ a ∨ b ≤ x at hgap
  change ∀ u ∈ S, ∀ v ∈ S, u < v →
    (∀ x ∈ S, x ≤ u ∨ v ≤ x) → v - u ≤ b - a at hmax
  have hna : (n : ℝ) * alpha < 1 / 2 := by
    have hDalpha : (D : ℝ) * alpha ≤ 1 := by
      simpa only [mul_comm] using (le_div_iff₀ hD).mp hac
    rw [hDr] at hDalpha
    dsimp [r] at hDalpha
    nlinarith only [hDalpha, ha0]
  have hf (j : ℕ) (hj : j ≤ n) : Int.fract ((j : ℝ) * alpha) = (j : ℝ) * alpha := by
    apply Int.fract_eq_self.mpr
    exact ⟨mul_nonneg (Nat.cast_nonneg _) ha0.le,
      (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hj) ha0.le).trans_lt
        (hna.trans (by norm_num))⟩
  have hSmem (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n) :
      (j : ℝ) * alpha ∈ S ∧ 1 - (j : ℝ) * alpha ∈ S := by
    have hm := Finset.mem_Icc.mpr hj
    constructor
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, hm, hf j hj.2⟩
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_insert_of_mem
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, hm, by rw [hf j hj.2]⟩
  have hS0 : 0 ∈ S := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hS1 : 1 ∈ S := Finset.mem_insert_self _ _
  have hSends (x : ℝ) (hx : x ∈ S) : x = 0 ∨ x = 1 ∨
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ n ∧ (x = (j : ℝ) * alpha ∨ x = 1 - (j : ℝ) * alpha) := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inr (Or.inl rfl)
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Or.inl rfl
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_Icc.mp hj
      exact Or.inr (Or.inr ⟨j, h.1, h.2, Or.inl (hf j h.2)⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      have h := Finset.mem_Icc.mp hj
      exact Or.inr (Or.inr ⟨j, h.1, h.2, Or.inr (by rw [hf j h.2])⟩)
  have hSunit (x : ℝ) (hx : x ∈ S) : 0 ≤ x ∧ x ≤ 1 := by
    rcases hSends x hx with rfl | rfl | ⟨j, hj1, hjn, rfl | rfl⟩
    · norm_num
    · norm_num
    all_goals
      have hpos := mul_nonneg (Nat.cast_nonneg j) ha0.le
      have hbound := (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjn) ha0.le)
      constructor <;> linarith only [hpos, hbound, hna]
  let left := (n : ℝ) * alpha
  let right := 1 - (n : ℝ) * alpha
  have hcentral : ∀ x ∈ S, x ≤ left ∨ right ≤ x := by
    intro x hx
    rcases hSends x hx with rfl | rfl | ⟨j, hj1, hjn, rfl | rfl⟩
    · exact Or.inl (by dsimp [left]; positivity)
    · exact Or.inr (by dsimp [right]; exact sub_le_self _ (by positivity))
    · exact Or.inl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjn) ha0.le)
    · exact Or.inr (sub_le_sub_left
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hjn) ha0.le) 1)
  have hcentralWidth : right - left = 1 - r * alpha := by dsimp [left, right, r]; ring
  have hsmallgap : alpha ≤ 1 - r * alpha := by
    have h := (le_div_iff₀ hD).mp hac
    rw [hDr] at h
    nlinarith only [h]
  have hupper (p q : ℝ) (hp : p ∈ S) (hq : q ∈ S) (hpq : p < q)
      (hcuts : ∀ x ∈ S, x ≤ p ∨ q ≤ x) : q - p ≤ 1 - r * alpha := by
    have hnext (x : ℝ) (hx : x ∈ S) (hpx : p < x) : q ≤ x := by
      rcases hcuts x hx with h | h
      · linarith
      · exact h
    rcases hSends p hp with rfl | rfl | ⟨j, hj1, hjn, hp | hp⟩
    · have hnxt := hnext alpha (by simpa using (hSmem 1 ⟨le_rfl, hn⟩).1) ha0
      linarith
    · linarith [(hSunit q hq).2]
    · subst p
      by_cases hjlt : j < n
      · have hnxt := hnext (((j + 1 : ℕ) : ℝ) * alpha) (by
          exact (hSmem (j + 1) ⟨by omega, by omega⟩).1) (by
          push_cast; nlinarith)
        push_cast at hnxt
        linarith
      · have hj : j = n := by omega
        subst j
        have hnxt := hnext right (hSmem n ⟨hn, le_rfl⟩).2 (by
          dsimp [right]; linarith only [hna])
        dsimp [right] at hnxt
        dsimp [r]
        linarith
    · subst p
      by_cases hjlt : 1 < j
      · have hnxt := hnext (1 - ((j - 1 : ℕ) : ℝ) * alpha)
          (hSmem (j - 1) ⟨by omega, by omega⟩).2 (by
            rw [Nat.cast_sub (by omega : 1 ≤ j)]; push_cast; nlinarith)
        rw [Nat.cast_sub (by omega : 1 ≤ j)] at hnxt
        push_cast at hnxt
        linarith
      · have hj : j = 1 := by omega
        subst j
        have hnxt := hnext 1 hS1 (by norm_num; linarith)
        norm_num at hpq ⊢
        linarith
  have hgapvalue : b - a = 1 - r * alpha := by
    apply le_antisymm (hupper a b ha hb hab hgap)
    have hm := hSmem n ⟨hn, le_rfl⟩
    have hlt : left < right := by dsimp [left, right]; linarith only [hna]
    simpa only [hcentralWidth] using hmax left hm.1 right hm.2 hlt hcentral
  have hacvalue : ac k alpha = ENNReal.ofReal t := by
    have hd : 0 < 1 - r * alpha := by
      have h := (hden alpha).1
      rw [hclipa] at h
      exact hc.trans_le h
    rw [hformula, hgapvalue, hlim, hFa, ← ENNReal.ofReal_mul hd.le]
    congr 1
    field_simp [ne_of_gt hd]
  refine ⟨alpha, hirr, ha0, ha1, ?_, ?_⟩
  · rw [hacvalue]; exact ENNReal.ofReal_ne_top
  · rw [hacvalue, ENNReal.toReal_ofReal ht0.le]

end D5.S1.Words.KAbelianLagrange
