/- GID: D5/S3/Estimation/DecisionRisk/CARApproximateRecovery
   generality: G
   mirror-B: D5/B/S3/Estimation/DecisionRisk/CARApproximateRecovery
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Construct common approximate CAR recovery with signed pair budgets. -/

import D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators ENNReal
open D5.S3.Divergence.ClassicalDPI
open D5.S3.Estimation.DecisionRisk.DescentDefectBounds
open D5.S3.Estimation.SequentialDecisionRisk.FiniteDeficiencyRiskTransfer
open D5.S3.TotalVariation.Pinsker D5.S3.TotalVariation.Metric
namespace D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
/-- All nonempty subsets of the finite state space, including zero-weight outputs. -/
abbrev Block (A : Type*) := {s : Finset A // s.Nonempty}
/-- The CAR probability row of a state under a block profile. -/
def row {A : Type*} [DecidableEq A] (w : Block A → ℝ) (i : A) (B : Block A) : ℝ :=
  if i ∈ B.1 then w B else 0
/-- The total weight of blocks containing both states. -/
def pair {A : Type*} [DecidableEq A] [Fintype A] (w : Block A → ℝ) (i j : A) : ℝ :=
  ∑ B, if i ∈ B.1 ∧ j ∈ B.1 then w B else 0

/-- A single approximate CAR garbling admits a common reverse with the signed pair budget. -/
theorem result {A : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    (w v : Block A → ℝ) (hw : ∀ B, 0 ≤ w B) (hv : ∀ C, 0 ≤ v C)
    (hwrow : ∀ i, ∑ B, row w i B = 1) (hvrow : ∀ i, ∑ C, row v i C = 1)
    (H : FiniteMarkovKernel (Block A) (Block A)) :
    let ε := fun i => totalVariation (channelOutput H.1 (row w i)) (row v i)
    let Δ := fun i j => pair v i j - pair w i j
    let b := fun i => (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, (Δ i j + ε i + ε j)
    let εmax := Finset.univ.sup' Finset.univ_nonempty ε
    let η := Finset.univ.sup' Finset.univ_nonempty
      (fun ij : A × A => if ij.1 = ij.2 then (0 : ℝ) else |Δ ij.1 ij.2|)
    let bmax := Finset.univ.sup' Finset.univ_nonempty b
    ∃ R : FiniteMarkovKernel (Block A) (Block A),
      (∀ i j, 0 ≤ Δ i j + ε i + ε j) ∧
      (∀ i, totalVariation (channelOutput R.1 (row v i)) (row w i) ≤ b i) ∧
      finiteDeficiency (row w) (row v) ≤ ENNReal.ofReal (min 1 bmax) ∧
      min 1 bmax ≤ min 1 (((Fintype.card A : ℝ) - 1) * η / 2 +
        ((Fintype.card A : ℝ) - 1) * εmax) ∧
      ((∀ i, ε i = 0) → ∀ B C, 0 < v C →
        R.1 C B = if B.1 ⊆ C.1 then
          (B.1.card : ℝ) * (w B * H.1 B C) / ((C.1.card : ℝ) * v C) else 0) := by
  classical
  dsimp only
  let W := row w
  let V := row v
  let F := fun i B C => W i B * H.1 B C
  let Q := fun i C => ∑ B, F i B C
  let ε := fun i => totalVariation (Q i) (V i)
  let Δ := fun i j => pair v i j - pair w i j
  let b := fun i => (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, (Δ i j + ε i + ε j)
  have hW (i B) : 0 ≤ W i B := by dsimp only [W, row]; split_ifs; exact hw B; exact le_rfl
  have hV (i C) : 0 ≤ V i C := by dsimp only [V, row]; split_ifs; exact hv C; exact le_rfl
  have hF (i B C) : 0 ≤ F i B C := mul_nonneg (hW i B) (H.2.1 B C)
  have hQ (i C) : 0 ≤ Q i C := Finset.sum_nonneg fun B _ => hF i B C
  have hFrow (i B) : ∑ C, F i B C = W i B := by
    dsimp only [F]; rw [← Finset.mul_sum, H.2.2, mul_one]
  have hQsum (i) : ∑ C, Q i C = 1 := by
    dsimp only [Q]; rw [Finset.sum_comm]; simp_rw [hFrow]; exact hwrow i
  have hε (i) : 0 ≤ ε i := total_variation_nonneg _ _
  let a := fun i C => if 0 < Q i C then min 1 (V i C / Q i C) else 1
  let t := fun i B C => a i C * F i B C
  have ha (i C) : 0 ≤ a i C ∧ a i C ≤ 1 := by
    dsimp only [a]; split_ifs with h
    · exact ⟨le_min (by norm_num) (div_nonneg (hV i C) (hQ i C)), min_le_left _ _⟩
    · exact ⟨by norm_num, le_rfl⟩
  have ht (i B C) : 0 ≤ t i B C := mul_nonneg (ha i C).1 (hF i B C)
  have htF (i B C) : t i B C ≤ F i B C := by
    exact (mul_le_mul_of_nonneg_right (ha i C).2 (hF i B C)).trans_eq (one_mul _)
  have htcol (i C) : ∑ B, t i B C = min (Q i C) (V i C) := by
    change (∑ B, a i C * F i B C) = _
    rw [← Finset.mul_sum]
    change a i C * Q i C = _
    by_cases h : 0 < Q i C
    · dsimp only [a]; rw [if_pos h, min_mul_of_nonneg _ _ h.le, one_mul,
        div_mul_cancel₀ _ (ne_of_gt h)]
    · have hz : Q i C = 0 := le_antisymm (le_of_not_gt h) (hQ i C)
      simp [hz, hV i C]
  let u := fun i B => W i B - ∑ C, t i B C
  let z := fun i C => V i C - ∑ B, t i B C
  have hu (i B) : 0 ≤ u i B := by
    apply sub_nonneg.mpr
    calc (∑ C, t i B C) ≤ ∑ C, F i B C := Finset.sum_le_sum fun C _ => htF i B C
      _ = W i B := hFrow i B
  have hz (i C) : 0 ≤ z i C := by
    dsimp only [z]; rw [htcol]; exact sub_nonneg.mpr (min_le_right _ _)
  have hmass (i) : (∑ B, u i B) = ε i ∧ (∑ C, z i C) = ε i := by
    have hs : (∑ C, min (Q i C) (V i C)) = 1 - ε i := by
      have hab : ∀ C, |Q i C - V i C| = Q i C + V i C - 2 * min (Q i C) (V i C) := by
        intro C; rcases le_total (Q i C) (V i C) with h | h
        · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
        · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
      have he : ε i = (1 / 2 : ℝ) * (2 - 2 * ∑ C, min (Q i C) (V i C)) := by
        dsimp only [ε, totalVariation]
        simp_rw [hab]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          hQsum, hvrow]; ring
      linarith only [he]
    constructor
    · dsimp only [u]; rw [Finset.sum_sub_distrib, hwrow, Finset.sum_comm]
      simp_rw [htcol]; linarith only [hs]
    · dsimp only [z]; rw [Finset.sum_sub_distrib, hvrow]; simp_rw [htcol]; linarith only [hs]
  let g := fun i B C => if 0 < ε i then t i B C + u i B * z i C / ε i else t i B C
  clear_value (g_def : g = fun i B C => if 0 < ε i then
    t i B C + u i B * z i C / ε i else t i B C)
  have hg (i B C) : 0 ≤ g i B C := by
    simp only [g_def]; split_ifs with h
    · exact add_nonneg (ht i B C) (div_nonneg (mul_nonneg (hu i B) (hz i C)) h.le)
    · exact ht i B C
  have htg (i B C) : t i B C ≤ g i B C := by
    simp only [g_def]; split_ifs with h
    · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg (hu i B) (hz i C)) h.le)
    · exact le_rfl
  have hzero (i) (he : ε i = 0) : (∀ B, u i B = 0) ∧ (∀ C, z i C = 0) := by
    constructor
    · intro B; exact (Finset.sum_eq_zero_iff_of_nonneg (fun B _ => hu i B)).mp
        ((hmass i).1.trans he) B (Finset.mem_univ _)
    · intro C; exact (Finset.sum_eq_zero_iff_of_nonneg (fun C _ => hz i C)).mp
        ((hmass i).2.trans he) C (Finset.mem_univ _)
  have hgrow (i B) : ∑ C, g i B C = W i B := by
    by_cases h : 0 < ε i
    · simp only [g_def, if_pos h, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.mul_sum, (hmass i).2, mul_div_cancel_right₀ _ (ne_of_gt h)]
      dsimp only [u]; ring
    · have he : ε i = 0 := le_antisymm (le_of_not_gt h) (hε i)
      simp only [g_def, if_neg h]
      have hh := (hzero i he).1 B; dsimp only [u] at hh; linarith only [hh]
  have hgcol (i C) : ∑ B, g i B C = V i C := by
    by_cases h : 0 < ε i
    · simp only [g_def, if_pos h, Finset.sum_add_distrib, ← Finset.sum_div,
        ← Finset.sum_mul, (hmass i).1, mul_div_cancel_left₀ _ (ne_of_gt h)]
      dsimp only [z]; ring
    · have he : ε i = 0 := le_antisymm (le_of_not_gt h) (hε i)
      simp only [g_def, if_neg h]
      have hh := (hzero i he).2 C; dsimp only [z] at hh; linarith only [hh]
  have hgB (i B C) (hi : i ∉ B.1) : g i B C = 0 := by
    have he : (∑ C, g i B C) = 0 := by rw [hgrow]; exact if_neg hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun C _ => hg i B C)).mp he C (Finset.mem_univ _)
  have hgC (i B C) (hi : i ∉ C.1) : g i B C = 0 := by
    have he : (∑ B, g i B C) = 0 := by rw [hgcol]; exact if_neg hi
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun B _ => hg i B C)).mp he B (Finset.mem_univ _)
  let O := fun i j => ∑ B, ∑ C, min (g i B C) (g j B C)
  have hOverlap (i j) : pair w i j - ε i - ε j ≤ O i j := by
    have hpoint (B C) : min (F i B C) (F j B C) -
        (F i B C - t i B C) - (F j B C - t j B C) ≤ min (g i B C) (g j B C) := by
      apply le_min
      · linarith only [min_le_left (F i B C) (F j B C), htF j B C, htg i B C]
      · linarith only [min_le_right (F i B C) (F j B C), htF i B C, htg j B C]
    have hmin : (∑ B, ∑ C, min (F i B C) (F j B C)) = pair w i j := by
      apply Finset.sum_congr rfl
      intro B _
      by_cases hi : i ∈ B.1 <;> by_cases hj : j ∈ B.1
      · simp only [F, W, row, min_self, hi, hj, and_self, ite_true]
        rw [← Finset.mul_sum, H.2.2, mul_one]
      · simp [F, W, row, hi, hj, mul_nonneg (hw B) (H.2.1 B _)]
      · simp [F, W, row, hi, hj, mul_nonneg (hw B) (H.2.1 B _)]
      · simp [F, W, row, hi, hj]
    have hdel (i) : (∑ B, ∑ C, (F i B C - t i B C)) = ε i := by
      calc
        _ = ∑ B, (W i B - ∑ C, t i B C) := by
          apply Finset.sum_congr rfl
          intro B _; rw [Finset.sum_sub_distrib, hFrow]
        _ = ε i := (hmass i).1
    have hh := Finset.sum_le_sum (fun B (_ : B ∈ Finset.univ) =>
      Finset.sum_le_sum (fun C (_ : C ∈ Finset.univ) => hpoint B C))
    have hleft : (∑ B, ∑ C, (min (F i B C) (F j B C) -
        (F i B C - t i B C) - (F j B C - t j B C))) = pair w i j - ε i - ε j := by
      rw [show (∑ B, ∑ C, (min (F i B C) (F j B C) - (F i B C - t i B C) -
        (F j B C - t j B C))) = (∑ B, ∑ C, min (F i B C) (F j B C)) -
        (∑ B, ∑ C, (F i B C - t i B C)) - (∑ B, ∑ C, (F j B C - t j B C)) by
          simp only [Finset.sum_sub_distrib]]
      rw [hmin, hdel, hdel]
    rw [hleft] at hh
    exact hh
  let d := fun i j C => (1 / 2 : ℝ) * ∑ B, |g i B C - g j B C|
  let D := fun i j => ∑ C, if i ∈ C.1 ∧ j ∈ C.1 then d i j C else 0
  have hd (i j C) : 0 ≤ d i j C := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun B _ => abs_nonneg _)
  have hD (i j) : D i j = pair v i j - O i j := by
    have hc (C) : (if i ∈ C.1 ∧ j ∈ C.1 then d i j C else 0) =
        (if i ∈ C.1 ∧ j ∈ C.1 then v C else 0) - ∑ B, min (g i B C) (g j B C) := by
      by_cases hi : i ∈ C.1 <;> by_cases hj : j ∈ C.1
      · simp only [hi, hj, and_self, ite_true]
        have ha (B) : |g i B C - g j B C| = g i B C + g j B C - 2 * min (g i B C) (g j B C) := by
          rcases le_total (g i B C) (g j B C) with h | h
          · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
          · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
        dsimp only [d]; simp_rw [ha]
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          hgcol, hgcol]
        simp only [V, row, if_pos hi, if_pos hj]; ring
      · simp [hi, hj, hgC j _ C hj, hg i _ C]
      · simp [hi, hj, hgC i _ C hi, hg j _ C]
      · simp [hi, hj, hgC i _ C hi, hgC j _ C hj]
    dsimp only [D]; simp_rw [hc]; rw [Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  have hDnonneg (i j) : 0 ≤ D i j := by
    apply Finset.sum_nonneg; intro C _; split_ifs
    · exact hd i j C
    · exact le_rfl
  have hbudget (i j) : D i j ≤ Δ i j + ε i + ε j := by
    rw [hD]; dsimp only [Δ]; linarith only [hOverlap i j]
  have hbudget0 (i j) : 0 ≤ Δ i j + ε i + ε j := (hDnonneg i j).trans (hbudget i j)
  let B₀ : Block A := ⟨{Classical.choice (inferInstance : Nonempty A)}, Finset.singleton_nonempty _⟩
  let R := fun C B => if 0 < v C then
    (∑ j ∈ C.1, g j B C) / ((C.1.card : ℝ) * v C)
    else if B = B₀ then 1 else 0
  have hcard (C : Block A) : 0 < (C.1.card : ℝ) := by exact_mod_cast C.2.card_pos
  have hR : IsRowStochastic R := by
    constructor
    · intro C B; dsimp only [R]; split_ifs with h
      · exact div_nonneg (Finset.sum_nonneg fun j _ => hg j B C)
          (mul_nonneg (hcard C).le (hv C))
      · norm_num
      · exact le_rfl
    · intro C; dsimp only [R]; by_cases h : 0 < v C
      · simp only [if_pos h, ← Finset.sum_div]
        rw [Finset.sum_comm]; simp_rw [hgcol]
        have he : (∑ j ∈ C.1, V j C) = (C.1.card : ℝ) * v C := by
          simp [V, row]
        rw [he, div_self (ne_of_gt (mul_pos (hcard C) h))]
      · simp [h]
  have hscale (i B C) : V i C * R C B =
      if i ∈ C.1 then (∑ j ∈ C.1, g j B C) / (C.1.card : ℝ) else 0 := by
    by_cases hi : i ∈ C.1
    · simp only [V, row, if_pos hi]
      by_cases h : 0 < v C
      · dsimp only [R]; rw [if_pos h]
        rw [← mul_div_assoc, mul_comm (C.1.card : ℝ) (v C),
          mul_div_mul_left _ _ (ne_of_gt h)]
      · have hv0 : v C = 0 := le_antisymm (le_of_not_gt h) (hv C)
        have hg0 (j) (hj : j ∈ C.1) : g j B C = 0 := by
          have he : (∑ B, g j B C) = 0 := by rw [hgcol]; simp [V, row, hj, hv0]
          exact (Finset.sum_eq_zero_iff_of_nonneg (fun B _ => hg j B C)).mp he B (Finset.mem_univ _)
        simp [hv0, Finset.sum_eq_zero hg0]
    · simp [V, row, hi]
  have hcolbound (i C) :
      (1 / 2 : ℝ) * (∑ B, |V i C * R C B - g i B C|) ≤
      (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i,
        (if i ∈ C.1 ∧ j ∈ C.1 then d i j C else 0) := by
    by_cases hi : i ∈ C.1
    · have he (B) : V i C * R C B - g i B C =
          (∑ j ∈ C.1, (g j B C - g i B C)) / (C.1.card : ℝ) := by
        rw [hscale, if_pos hi, Finset.sum_sub_distrib]
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [sub_div, mul_div_cancel_left₀ _ (ne_of_gt (hcard C))]
      have hm : (1 / 2 : ℝ) * (∑ B, |V i C * R C B - g i B C|) ≤
          (∑ j ∈ C.1, d i j C) / (C.1.card : ℝ) := by
        calc
          _ ≤ (1 / 2 : ℝ) * ∑ B, (∑ j ∈ C.1, |g j B C - g i B C|) / (C.1.card : ℝ) := by
            apply mul_le_mul_of_nonneg_left _ (by norm_num)
            apply Finset.sum_le_sum; intro B _
            rw [he, abs_div, abs_of_pos (hcard C)]
            exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (hcard C).le
          _ = (∑ j ∈ C.1, d i j C) / (C.1.card : ℝ) := by
            rw [← Finset.sum_div, Finset.sum_comm]
            simp only [d, abs_sub_comm, ← Finset.mul_sum]; ring
      have he' : (∑ j ∈ C.1, d i j C) / (C.1.card : ℝ) =
          ∑ j ∈ Finset.univ.erase i,
            (if i ∈ C.1 ∧ j ∈ C.1 then d i j C / (C.1.card : ℝ) else 0) := by
        rw [Finset.sum_div]
        have hz : d i i C = 0 := by simp [d]
        rw [← Finset.sum_erase_add _ _ hi, hz, zero_div, add_zero]
        apply Finset.sum_subset_zero_on_sdiff
        · intro j hj; exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, Finset.mem_univ _⟩
        · intro j hjs
          obtain ⟨hj, hj'⟩ := Finset.mem_sdiff.mp hjs
          have hn : j ∉ C.1 := by
            intro h; exact hj' (Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hj).1, h⟩)
          simp [hn]
        · intro j hj
          simp [hi, (Finset.mem_erase.mp hj).2]
      rw [he'] at hm
      refine hm.trans ?_
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum; intro j hj
      by_cases hjC : j ∈ C.1
      · simp only [hi, hjC, and_self, ite_true]
        have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
        have hc2 : (2 : ℝ) ≤ (C.1.card : ℝ) := by
          have hc2n : 2 ≤ C.1.card := by
            have hh : ({i, j} : Finset A) ⊆ C.1 := by simp [Finset.insert_subset_iff, hi, hjC]
            simpa [hij] using Finset.card_le_card hh
          exact_mod_cast hc2n
        apply (div_le_iff₀ (hcard C)).mpr
        nlinarith only [mul_nonneg (hd i j C) (sub_nonneg.mpr hc2)]
      · simp [hjC]
    · simp [V, row, hi, hgC i _ C hi]
  have herror (i) : totalVariation (channelOutput R (V i)) (W i) ≤ b i := by
    have he (B) : channelOutput R (V i) B - W i B =
        ∑ C, (V i C * R C B - g i B C) := by
      rw [Finset.sum_sub_distrib, hgrow]; rfl
    calc
      totalVariation (channelOutput R (V i)) (W i) ≤
          (1 / 2 : ℝ) * ∑ B, ∑ C, |V i C * R C B - g i B C| := by
        unfold totalVariation
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum; intro B _
        rw [he]; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ C, (1 / 2 : ℝ) * ∑ B, |V i C * R C B - g i B C| := by
        rw [Finset.sum_comm, Finset.mul_sum]
      _ ≤ ∑ C, (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i,
          (if i ∈ C.1 ∧ j ∈ C.1 then d i j C else 0) := Finset.sum_le_sum fun C _ => hcolbound i C
      _ = (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, D i j := by
        rw [← Finset.mul_sum, Finset.sum_comm]
      _ ≤ b i := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Finset.sum_le_sum fun j _ => hbudget i j
  let RK : FiniteMarkovKernel (Block A) (Block A) := ⟨R, hR⟩
  let εmax := Finset.univ.sup' Finset.univ_nonempty ε
  let η := Finset.univ.sup' Finset.univ_nonempty
    (fun ij : A × A => if ij.1 = ij.2 then (0 : ℝ) else |Δ ij.1 ij.2|)
  let bmax := Finset.univ.sup' Finset.univ_nonempty b
  have hmax (i) : b i ≤ bmax := Finset.le_sup' b (Finset.mem_univ i)
  have hεmax (i) : ε i ≤ εmax := Finset.le_sup' ε (Finset.mem_univ i)
  have hΔmax (i j) (hij : i ≠ j) : Δ i j ≤ η := by
    apply (le_abs_self _).trans
    have hh := Finset.le_sup' (fun ij : A × A => if ij.1 = ij.2 then (0 : ℝ) else |Δ ij.1 ij.2|)
      (Finset.mem_univ (i,j))
    simpa [hij] using hh
  have hn : 1 ≤ Fintype.card A := Fintype.card_pos_iff.mpr inferInstance
  have hcoarse : bmax ≤ ((Fintype.card A : ℝ) - 1) * η / 2 +
      ((Fintype.card A : ℝ) - 1) * εmax := by
    apply Finset.sup'_le
    intro i _
    calc
      b i ≤ (1 / 2 : ℝ) * ∑ j ∈ Finset.univ.erase i, (η + εmax + εmax) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum; intro j hj
        linarith only [hΔmax i j (Ne.symm (Finset.mem_erase.mp hj).1), hεmax i, hεmax j]
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i),
          Finset.card_univ, Nat.cast_sub hn, Nat.cast_one]
        ring
  have hRlaw (i) : (∀ B, 0 ≤ channelOutput R (V i) B) ∧ ∑ B, channelOutput R (V i) B = 1 := by
    constructor
    · intro B; exact Finset.sum_nonneg fun C _ => mul_nonneg (hV i C) (hR.1 C B)
    · unfold channelOutput; rw [Finset.sum_comm]
      simp_rw [← Finset.mul_sum, hR.2, mul_one]; exact hvrow i
  have hdef : finiteDeficiency W V ≤ ENNReal.ofReal (min 1 bmax) := by
    apply (iInf_le _ RK).trans
    apply ENNReal.ofReal_le_ofReal
    apply Finset.sup'_le
    intro i _
    rw [total_variation_comm]
    exact le_min (total_variation_le_one _ _ (hRlaw i) ⟨hW i, hwrow i⟩) ((herror i).trans (hmax i))
  refine ⟨RK, hbudget0, herror, hdef, min_le_min_left _ hcoarse, ?_⟩
  intro he B C hvc
  have hgF (i B C) : g i B C = F i B C := by
    have hzε : ε i = 0 := he i
    have hdel : (∑ C, (F i B C - t i B C)) = 0 := by
      rw [Finset.sum_sub_distrib, hFrow]
      exact (hzero i hzε).1 B
    have ht' : F i B C - t i B C = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun C _ => sub_nonneg.mpr (htF i B C))).mp hdel C (Finset.mem_univ _)
    simp only [g_def, hzε, lt_self_iff_false, if_false]
    linarith only [ht']
  have hsupp (i) (hiB : i ∈ B.1) (hiC : i ∉ C.1) : w B * H.1 B C = 0 := by
    have hh := hgC i B C hiC
    rw [hgF] at hh
    simpa only [F, W, row, if_pos hiB] using hh
  change R C B = _
  dsimp only [R]; rw [if_pos hvc]
  by_cases hBC : B.1 ⊆ C.1
  · rw [if_pos hBC]
    congr 1
    simp_rw [hgF]
    change (∑ j ∈ C.1, (if j ∈ B.1 then w B else 0) * H.1 B C) = _
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBC, Finset.sum_const, nsmul_eq_mul]
  · rw [if_neg hBC]
    obtain ⟨i, hiB, hiC⟩ := Finset.not_subset.mp hBC
    have hh := hsupp i hiB hiC
    simp only [hgF, F, W, row, ite_mul, zero_mul, hh, ite_self, Finset.sum_const_zero, zero_div]

#print axioms Block
#print axioms row
#print axioms pair
#print axioms result
end D5.S3.Estimation.DecisionRisk.CARApproximateRecovery
