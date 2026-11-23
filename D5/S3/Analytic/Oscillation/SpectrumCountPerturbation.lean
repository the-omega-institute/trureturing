/- GID: D5/S3/Analytic/Oscillation/SpectrumCountPerturbation
   generality: G
   mirror-B: D5/B/S3/Analytic/Oscillation/SpectrumCountPerturbation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Separated perturbation intervals preserve the count of a spectrum up to a crossing. -/

import D5.S3.Analytic.Oscillation.OrdinateCounting

/-! Local perturbations of positive injective spectra with bounded sublevel counts. -/

set_option autoImplicit false

noncomputable section

open Finset Set
open D5.S3.Analytic.Oscillation.OrdinateCounting

namespace D5.S3.Analytic.Oscillation.SpectrumCountPerturbation

private theorem exists_radius (S : Spectrum) (j : S.index) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 3 ∧ r < S.gamma j ∧
      ∀ i, i ≠ j → 3 * r ≤ |S.gamma i - S.gamma j| := by
  classical
  let shifts := (S.cut (S.gamma j + 1)).erase j
  let gaps := insert (1 : ℝ) (shifts.image (fun i => |S.gamma i - S.gamma j|))
  have hne : gaps.Nonempty := ⟨1, mem_insert_self _ _⟩
  let d := gaps.min' hne
  have d_pos : 0 < d := by
    have hd : d ∈ gaps := min'_mem gaps hne
    rcases mem_insert.mp hd with h | h
    · rw [h]
      exact zero_lt_one
    · obtain ⟨i, hi, heq⟩ := mem_image.mp h
      rw [← heq]
      exact abs_pos.mpr (sub_ne_zero.mpr (fun e => (ne_of_mem_erase hi) (S.gamma_injective e)))
  have d_le_one : d ≤ 1 := min'_le gaps _ (mem_insert_self _ _)
  let r := min d (S.gamma j) / 3
  have r_pos : 0 < r := div_pos (lt_min d_pos (S.gamma_pos j)) (by norm_num)
  have hr (i : S.index) (hi : i ≠ j) : d ≤ |S.gamma i - S.gamma j| := by
    by_cases h : S.gamma i ≤ S.gamma j + 1
    · have hmem : i ∈ shifts := mem_erase.mpr ⟨hi, by simpa [Spectrum.cut] using h⟩
      exact min'_le gaps _ (mem_insert_of_mem (mem_image_of_mem _ hmem))
    · have hdist : 1 ≤ |S.gamma i - S.gamma j| :=
        (by linarith [le_of_lt (lt_of_not_ge h)] : 1 ≤ S.gamma i - S.gamma j).trans (le_abs_self _)
      exact d_le_one.trans hdist
  have hrd : 3 * r ≤ d := by
    dsimp [r]
    linarith only [min_le_left d (S.gamma j)]
  refine ⟨r, r_pos, by linarith, ?_, fun i hi => hrd.trans (hr i hi)⟩
  dsimp [r]
  linarith only [min_le_right d (S.gamma j), S.gamma_pos j]

private theorem counts_differ_at_crossing (S S' : Spectrum) (r : S.index → ℝ)
    (e : S.index ≃ S'.index)
    (hweight : ∀ j, S'.mult (e j) = S.mult j)
    (hclose : ∀ j, |S'.gamma (e j) - S.gamma j| ≤ r j)
    (hsep : ∀ i j, S.gamma i < S.gamma j →
      S.gamma i + r i < S.gamma j - r j) (T : ℝ) :
    S'.N T = S.N T ∨ ∃ j, T ∈ Ico (S.gamma j - r j) (S.gamma j + r j) ∧
      (S'.N T + S.mult j = S.N T ∨ S.N T + S.mult j = S'.N T) := by
  classical
  let A := (S'.cut T).map e.symm.toEmbedding
  let B := S.cut T
  have hA (j : S.index) : j ∈ A ↔ S'.gamma (e j) ≤ T := by
    simp [A, Spectrum.cut]
  have hB (j : S.index) : j ∈ B ↔ S.gamma j ≤ T := by
    simp [B, Spectrum.cut]
  have hsum : (∑ i ∈ A, S.mult i) = S'.N T := by
    unfold A Spectrum.N
    rw [sum_map]
    exact sum_congr rfl (fun i _ => by simpa using (hweight (e.symm i)).symm)
  change S'.N T = (∑ j ∈ B, S.mult j) ∨ _
  by_cases hAB : A = B
  · exact Or.inl (hsum.symm.trans (congrArg (fun t => ∑ j ∈ t, S.mult j) hAB))
  obtain ⟨j, hj⟩ : ∃ j, ¬ (j ∈ A ↔ j ∈ B) := by
    by_contra! h
    exact hAB (Finset.ext h)
  have hcross (i : S.index) (hi : ¬ (i ∈ A ↔ i ∈ B)) :
      T ∈ Ico (S.gamma i - r i) (S.gamma i + r i) := by
    rw [hA, hB] at hi
    have hnear := abs_le.mp (hclose i)
    rcases le_or_gt (S.gamma i) T with h | h
    · have h' : T < S'.gamma (e i) := lt_of_not_ge (fun hz => hi (iff_of_true hz h))
      exact ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
    · have h' : S'.gamma (e i) ≤ T := le_of_not_gt
        (fun hz => hi (iff_of_false (not_le.mpr hz) (not_le.mpr h)))
      exact ⟨by linarith [hnear.1], by linarith [hnear.2]⟩
  have hjT := hcross j hj
  have hsame (i : S.index) (hij : i ≠ j) : i ∈ A ↔ i ∈ B := by
    by_contra hi
    have hiT := hcross i hi
    rcases lt_or_gt_of_ne (fun h => hij (S.gamma_injective h)) with h | h
    · exact (not_lt_of_ge (hjT.1.trans (le_of_lt hiT.2))) (hsep i j h)
    · exact (not_lt_of_ge (hiT.1.trans (le_of_lt hjT.2))) (hsep j i h)
  have herase : A.erase j = B.erase j := by
    ext i
    simp only [mem_erase]
    exact and_congr_right (hsame i)
  right
  refine ⟨j, hjT, ?_⟩
  by_cases ha : j ∈ A
  · have hb : j ∉ B := fun hb => hj (iff_of_true ha hb)
    right
    change (∑ i ∈ B, S.mult i) + S.mult j = S'.N T
    rw [← erase_eq_of_notMem hb, ← herase, sum_erase_add _ _ ha]
    exact hsum
  · have hb : j ∈ B := by by_contra h; exact hj (iff_of_false ha h)
    left
    change S'.N T + S.mult j = ∑ i ∈ B, S.mult i
    rw [← hsum, ← erase_eq_of_notMem ha, herase, sum_erase_add _ _ hb]

/-- One radius family protects all positive ordinates, their order, and their counts. -/
theorem exists_ordered_count_perturbations (S : Spectrum) :
    ∃ r : S.index → ℝ, (∀ j, 0 < r j ∧ r j ≤ 1 / 3 ∧ r j < S.gamma j) ∧
      (∀ i j, S.gamma i < S.gamma j → S.gamma i + r i < S.gamma j - r j) ∧
      ∀ g' : S.index → ℝ, (∀ j, |g' j - S.gamma j| ≤ r j) →
        ∃ (S' : Spectrum) (e : S.index ≃ S'.index),
          (∀ j, S'.gamma (e j) = g' j ∧ S'.mult (e j) = S.mult j) ∧
          (∀ i j, g' i < g' j ↔ S.gamma i < S.gamma j) ∧
          ∀ T, S'.N T = S.N T ∨ ∃ j, T ∈ Ico (S.gamma j - r j) (S.gamma j + r j) ∧
            (S'.N T + S.mult j = S.N T ∨ S.N T + S.mult j = S'.N T) := by
  classical
  choose r hr using exists_radius S
  have hsep (i j : S.index) (h : S.gamma i < S.gamma j) :
      S.gamma i + r i < S.gamma j - r j := by
    have hn : i ≠ j := fun he => h.ne (congrArg S.gamma he)
    have hi := (hr i).2.2.2 j hn.symm
    have hj := (hr j).2.2.2 i hn
    rw [abs_of_pos (sub_pos.mpr h)] at hi
    rw [abs_of_neg (sub_neg.mpr h)] at hj
    linarith
  refine ⟨r, fun j => ⟨(hr j).1, (hr j).2.1, (hr j).2.2.1⟩, hsep, fun g' hnear => ?_⟩
  have hbox (j : S.index) := abs_le.mp (hnear j)
  have hforward (i j : S.index) (h : S.gamma i < S.gamma j) : g' i < g' j := by
    linarith [(hbox i).2, (hbox j).1, hsep i j h]
  have horder (i j : S.index) : g' i < g' j ↔ S.gamma i < S.gamma j := by
    refine ⟨fun h => ?_, hforward i j⟩
    rcases lt_trichotomy (S.gamma i) (S.gamma j) with hg | hg | hg
    · exact hg
    · exact (h.ne (congrArg g' (S.gamma_injective hg))).elim
    · exact (h.not_gt (hforward j i hg)).elim
  let S' : Spectrum :=
    { index := S.index
      gamma := g'
      mult := S.mult
      gamma_pos := fun j => by linarith [(hr j).2.2.1, (hbox j).1]
      gamma_injective := by
        intro i j hij
        apply S.gamma_injective
        contrapose! hij
        rcases lt_or_gt_of_ne hij with hh | hh
        · exact (hforward i j hh).ne
        · exact (hforward j i hh).ne'
      mult_pos := S.mult_pos
      finite_le := fun T => (S.finite_le (T + 1)).subset (by
        intro j hj
        change g' j ≤ T at hj
        change S.gamma j ≤ T + 1
        linarith [(hbox j).1, (hr j).2.1]) }
  exact ⟨S', Equiv.refl _, fun _ => ⟨rfl, rfl⟩, horder,
    counts_differ_at_crossing S S' r (Equiv.refl _) (fun _ => rfl) hnear hsep⟩

#print axioms exists_ordered_count_perturbations

end D5.S3.Analytic.Oscillation.SpectrumCountPerturbation
