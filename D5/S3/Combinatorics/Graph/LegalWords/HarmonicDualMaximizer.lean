/- GID: D5/S3/Combinatorics/Graph/LegalWords/HarmonicDualMaximizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/LegalWords/HarmonicDualMaximizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Clique]
   utility: none
   digest: Parallel independent-set flips constrain positive stationary harmonic-dual masses. -/

import D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped BigOperators symmDiff
open Finset
open D5.S3.StatisticalMechanics.HardCore.IndependentPartitionDeletion

namespace D5.S3.Combinatorics.Graph.LegalWords.HarmonicDualMaximizer

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (H : SimpleGraph V) [DecidableRel H.Adj]

private noncomputable def flipTerm (ν : Finset V → ℝ) (S : Finset V) (j : V) : ℝ :=
  if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
    (ν (S ∆ {j}) / (ν S + ν (S ∆ {j}))) ^ 2 else 0

/-- The derivative load, indexed by all legal single-coordinate flips. -/
noncomputable def coordinateLoad (ν : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ j : V, flipTerm H ν S j

/-- Each independent-set edge is counted once, from its endpoint lacking the added vertex. -/
noncomputable def harmonicDual (ν : Finset V → ℝ) : ℝ :=
  ∑ S ∈ configurations H univ, ∑ i : V,
    if i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V) then
      ν S * ν (insert i S) / (ν S + ν (insert i S)) else 0

/-- Square-root regularization on the actual independent configurations. -/
noncomputable def regularizedDual (ε : ℝ) (ν : Finset V → ℝ) : ℝ :=
  harmonicDual H ν + ε * ∑ S ∈ configurations H univ, Real.sqrt (ν S)

omit [Fintype V] [DecidableRel H.Adj] in
private theorem independent_insert (S : Finset V) (i : V) :
    H.IsIndepSet (↑(insert i S) : Set V) ↔
      H.IsIndepSet (S : Set V) ∧ ∀ j ∈ S, ¬ H.Adj i j := by
  simp only [SimpleGraph.isIndepSet_iff, coe_insert, Set.pairwise_insert]
  constructor
  · rintro ⟨hS, h⟩
    refine ⟨hS, fun j hj => ?_⟩
    by_cases hij : i = j
    · subst j; exact H.irrefl
    · exact (h j hj hij).1
  · rintro ⟨hS, h⟩
    exact ⟨hS, fun j hj _ => ⟨h j hj, fun e => h j hj e.symm⟩⟩

omit [Fintype V] in
private theorem flip_insert (S : Finset V) {i j : V} (hij : j ≠ i) :
    (insert i S) ∆ {j} = insert i (S ∆ {j}) := by
  ext k
  simp only [mem_symmDiff, mem_insert, mem_singleton]
  by_cases hk : k = i
  · subst k; simp [Ne.symm hij]
  · simp only [hk, false_or]

omit [Fintype V] in
private theorem flip_absent (S : Finset V) {i : V} (hi : i ∉ S) :
    S ∆ {i} = insert i S := by
  rw [Finset.symmDiff_eq_union (Finset.disjoint_singleton_right.mpr hi), union_singleton]

omit [Fintype V] [DecidableRel H.Adj] in
/-- Deletions stay paired; the only lost flips are legal additions adjacent to the inserted site. -/
private theorem paired_flip (S : Finset V) {i j : V}
    (hS : H.IsIndepSet (↑(insert i S) : Set V)) (hij : j ≠ i) :
    H.IsIndepSet (↑((insert i S) ∆ {j}) : Set V) ↔
      H.IsIndepSet (↑(S ∆ {j}) : Set V) ∧ ¬ H.Adj i j := by
  rw [flip_insert S hij, independent_insert]
  have hbase := (independent_insert H S i).mp hS
  constructor
  · rintro ⟨hT, h⟩
    refine ⟨hT, ?_⟩
    by_cases hj : j ∈ S
    · exact hbase.2 j hj
    · exact h j (by simp [mem_symmDiff, hj])
  · rintro ⟨hT, hn⟩
    refine ⟨hT, fun k hk => ?_⟩
    rcases mem_symmDiff.mp hk with hk | hk
    · exact hbase.2 k hk.1
    · have : k = j := mem_singleton.mp hk.1
      subst k; exact hn

private theorem share_mono {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 < x) (hy : 0 < y) (hr : y / x ≤ b / a) :
    (y / (b + y)) ^ 2 ≤ (x / (a + x)) ^ 2 := by
  apply pow_le_pow_left₀ (by positivity)
  apply (div_le_div_iff₀ (by positivity : 0 < b+y) (by positivity : 0 < a+x)).mpr
  have := (div_le_div_iff₀ hx ha).mp hr
  nlinarith

private theorem share_quarter {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
    (b / (a+b)) ^ 2 ≤ (1:ℝ)/4 := by
  have h : b / (a+b) ≤ 1/2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  calc
    _ ≤ (1/2:ℝ)^2 := pow_le_pow_left₀ (by positivity) h 2
    _ = _ := by norm_num

omit [Fintype V] in
private theorem flipTerm_nonneg (ν : Finset V → ℝ) (S : Finset V) (j : V) :
    0 ≤ flipTerm H ν S j := by
  unfold flipTerm
  split <;> positivity

private theorem load_difference (ν : Finset V → ℝ)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (S : Finset V) (i : V) (hi : i ∉ S)
    (hS : H.IsIndepSet (↑(insert i S) : Set V)) :
    coordinateLoad H ν (insert i S) - coordinateLoad H ν S =
      (ν S - ν (insert i S)) / (ν S + ν (insert i S)) +
        ∑ j ∈ univ.erase i, (flipTerm H ν (insert i S) j - flipTerm H ν S j) := by
  have hbase := (independent_insert H S i).mp hS
  have hf : (insert i S) ∆ {i} = S := by
    rw [← flip_absent S hi, symmDiff_symmDiff_cancel_right]
  have he : flipTerm H ν (insert i S) i - flipTerm H ν S i =
      (ν S - ν (insert i S)) / (ν S + ν (insert i S)) := by
    simp only [flipTerm, hf, flip_absent S hi, if_pos hS, if_pos hbase.1]
    have hden : ν S + ν (insert i S) ≠ 0 := ne_of_gt (add_pos (hp S hbase.1) (hp _ hS))
    rw [add_comm (ν (insert i S))]
    field_simp
    <;> ring
  unfold coordinateLoad
  rw [← sum_sub_distrib, ← sum_erase_add _ _ (mem_univ i), he]
  exact add_comm _ _

private theorem stationary_load_mono (ν : Finset V → ℝ) {ε τ : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hs : ∀ S : Finset V, H.IsIndepSet (S : Set V) →
      coordinateLoad H ν S + ε / (2 * Real.sqrt (ν S)) = τ)
    {A B : Finset V} (hA : H.IsIndepSet (A : Set V)) (hB : H.IsIndepSet (B : Set V))
    (hab : ν A ≤ ν B) : coordinateLoad H ν A ≤ coordinateLoad H ν B := by
  have hAp := hp A hA
  have hBp := hp B hB
  have hr := div_le_div_of_nonneg_left hε
    (by positivity : 0 < 2 * Real.sqrt (ν A))
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hab) (by norm_num : (0:ℝ) ≤ 2))
  linarith [hs A hA, hs B hB]

private theorem maximum_ratio_le_one (ν : Finset V → ℝ) {ε τ : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hs : ∀ S : Finset V, H.IsIndepSet (S : Set V) →
      coordinateLoad H ν S + ε / (2 * Real.sqrt (ν S)) = τ)
    (i : V) : ∀ S : Finset V, i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
      ν (insert i S) ≤ ν S := by
  classical
  let D := (univ : Finset (Finset V)).filter fun S : Finset V => i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V)
  have hD : D.Nonempty := ⟨∅, by simp [D, SimpleGraph.IsIndepSet, Set.Pairwise]⟩
  obtain ⟨S, hSD, hmax⟩ := D.exists_max_image (fun S => ν (insert i S) / ν S) hD
  have hSi := (mem_filter.mp hSD).2
  have hbase := (independent_insert H S i).mp hSi.2
  have hbound : ν (insert i S) ≤ ν S := by
    by_contra hn
    have hlt : ν S < ν (insert i S) := lt_of_not_ge hn
    have hsum : (∑ j ∈ univ.erase i,
        (flipTerm H ν (insert i S) j - flipTerm H ν S j)) ≤ 0 := by
      apply sum_nonpos
      intro j hj
      apply sub_nonpos.mpr
      have hij := (mem_erase.mp hj).1
      by_cases hc : H.IsIndepSet (↑((insert i S) ∆ {j}) : Set V)
      · have ht := ((paired_flip H S hSi.2 hij).mp hc).1
        have htD : S ∆ {j} ∈ D := by
          simp only [D, mem_filter, mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · simp [mem_symmDiff, hSi.1, Ne.symm hij]
          · rwa [← flip_insert S hij]
        have hr := hmax (S ∆ {j}) htD
        rw [← flip_insert S hij] at hr
        simp only [flipTerm, if_pos hc, if_pos ht]
        exact share_mono (hp _ hbase.1) (hp _ hSi.2) (hp _ ht) (hp _ hc) hr
      · simp only [flipTerm, if_neg hc]
        exact flipTerm_nonneg H ν S j
    have hd := load_difference H ν hp S i hSi.1 hSi.2
    have hm := stationary_load_mono H ν hε hp hs hbase.1 hSi.2 hlt.le
    have hneg : (ν S - ν (insert i S)) / (ν S + ν (insert i S)) < 0 :=
      div_neg_of_neg_of_pos (sub_neg.mpr hlt) (add_pos (hp _ hbase.1) (hp _ hSi.2))
    linarith
  intro T hi hT
  have hTb := (independent_insert H T i).mp hT
  have hr := hmax T (mem_filter.mpr ⟨mem_univ _, hi, hT⟩)
  have hR : ν (insert i S) / ν S ≤ 1 := (div_le_one (hp _ hbase.1)).mpr hbound
  exact (div_le_one (hp _ hTb.1)).mp (hr.trans hR)

/-- Positive square-root stationary masses decrease on every legal addition, but by no more
than the factor determined by the degree of the added site in the base graph. -/
theorem stationary_ratio_bounds (ν : Finset V → ℝ) {ε τ : ℝ} (hε : 0 ≤ ε)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hs : ∀ S : Finset V, H.IsIndepSet (S : Set V) →
      coordinateLoad H ν S + ε / (2 * Real.sqrt (ν S)) = τ)
    (i : V) (T : Finset V) (hi : i ∉ T)
    (hT : H.IsIndepSet (↑(insert i T) : Set V)) :
    (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) ≤ ν (insert i T) / ν T ∧
      ν (insert i T) / ν T ≤ 1 := by
  classical
  have hmono := maximum_ratio_le_one H ν hε hp hs
  have hTb := (independent_insert H T i).mp hT
  refine ⟨?_, (div_le_one (hp _ hTb.1)).mpr (hmono i T hi hT)⟩
  let D := (univ : Finset (Finset V)).filter fun S : Finset V => i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V)
  have hTD : T ∈ D := mem_filter.mpr ⟨mem_univ _, hi, hT⟩
  obtain ⟨S, hSD, hmin⟩ := D.exists_min_image (fun S => ν (insert i S) / ν S) ⟨T, hTD⟩
  have hSi := (mem_filter.mp hSD).2
  have hbase := (independent_insert H S i).mp hSi.2
  have hsum : -(H.degree i : ℝ)/4 ≤ ∑ j ∈ univ.erase i,
      (flipTerm H ν (insert i S) j - flipTerm H ν S j) := by
    have hpoint : ∀ j ∈ univ.erase i,
        -(if H.Adj i j then (1:ℝ)/4 else 0) ≤
          flipTerm H ν (insert i S) j - flipTerm H ν S j := by
      intro j hj
      have hij := (mem_erase.mp hj).1
      by_cases hc : H.IsIndepSet (↑((insert i S) ∆ {j}) : Set V)
      · obtain ⟨ht, hn⟩ := (paired_flip H S hSi.2 hij).mp hc
        have htD : S ∆ {j} ∈ D := by
          simp only [D, mem_filter, mem_univ, true_and]
          refine ⟨?_, ?_⟩
          · simp [mem_symmDiff, hSi.1, Ne.symm hij]
          · rwa [← flip_insert S hij]
        have hr := hmin (S ∆ {j}) htD
        rw [← flip_insert S hij] at hr
        have hr' : ν (S ∆ {j}) / ν ((insert i S) ∆ {j}) ≤ ν S / ν (insert i S) := by
          apply (div_le_div_iff₀ (hp _ hc) (hp _ hSi.2)).mpr
          have := (div_le_div_iff₀ (hp _ hbase.1) (hp _ ht)).mp hr
          nlinarith
        have hshare := share_mono (hp _ hSi.2) (hp _ hbase.1) (hp _ hc) (hp _ ht) hr'
        simp only [flipTerm, if_pos ht, if_pos hc, if_neg hn, neg_zero]
        linarith
      · by_cases ht : H.IsIndepSet (↑(S ∆ {j}) : Set V)
        · have hn : H.Adj i j := by
            by_contra hn
            exact hc ((paired_flip H S hSi.2 hij).mpr ⟨ht, hn⟩)
          have hjS : j ∉ S := fun hjS => hbase.2 j hjS hn
          have hjind : H.IsIndepSet (↑(insert j S) : Set V) := by
            rwa [flip_absent S hjS] at ht
          have hq := share_quarter (hp _ hbase.1) (hp _ hjind) (hmono j S hjS hjind)
          simp only [flipTerm, if_neg hc, if_pos ht, if_pos hn, zero_sub,
            flip_absent S hjS, if_pos hjind]
          linarith
        · simp only [flipTerm, if_neg hc, if_neg ht, sub_self]
          split <;> norm_num
    have he : ∑ j ∈ univ.erase i, -(if H.Adj i j then (1:ℝ)/4 else 0) =
        -(H.degree i : ℝ)/4 := by
      have hz : (if H.Adj i i then (1:ℝ)/4 else 0) = 0 := by simp
      rw [sum_neg_distrib, sum_erase_eq_sub (mem_univ i), hz, sub_zero]
      rw [← sum_filter]
      simp [← H.neighborFinset_eq_filter, H.card_neighborFinset_eq_degree]
      <;> ring
    rw [← he]
    exact sum_le_sum hpoint
  have hd := load_difference H ν hp S i hSi.1 hSi.2
  have hm := stationary_load_mono H ν hε hp hs hSi.2 hbase.1
    (hmono i S hSi.1 hSi.2)
  have hbound : (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) ≤
      ν (insert i S) / ν S := by
    have hpos := hp S hbase.1
    have hpos' := hp (insert i S) hSi.2
    have hg : (0:ℝ) ≤ H.degree i := Nat.cast_nonneg _
    have hfrac : (ν S - ν (insert i S)) / (ν S + ν (insert i S)) ≤ (H.degree i : ℝ)/4 := by
      linarith
    have hc := (div_le_iff₀ (add_pos hpos hpos')).mp hfrac
    apply (div_le_div_iff₀ (by positivity : (0:ℝ) < 4 + (H.degree i : ℝ)) hpos).mpr
    nlinarith
  exact hbound.trans (hmin T hTD)

#print axioms stationary_ratio_bounds

end D5.S3.Combinatorics.Graph.LegalWords.HarmonicDualMaximizer
