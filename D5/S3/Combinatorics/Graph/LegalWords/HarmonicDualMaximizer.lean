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

/-- Half the directed legal-flip sum counts each independent-set edge once. -/
noncomputable def harmonicDual (ν : Finset V → ℝ) : ℝ :=
  (∑ S ∈ configurations H univ, ∑ i : V,
    if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
      ν S * ν (S ∆ {i}) / (ν S + ν (S ∆ {i})) else 0) / 2

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
    ring
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
  let D := (univ : Finset (Finset V)).filter fun S : Finset V =>
    i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V)
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
  let D := (univ : Finset (Finset V)).filter fun S : Finset V =>
    i ∉ S ∧ H.IsIndepSet (↑(insert i S) : Set V)
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
          simp only [flipTerm, if_neg hc, if_pos hn, zero_sub,
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
      ring
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

/-- Probability vectors extended by zero outside the independent configurations. -/
def probabilities : Set (Finset V → ℝ) :=
  {ν | ν ∈ stdSimplex ℝ (Finset V) ∧
    ∀ S : Finset V, ¬ H.IsIndepSet (S : Set V) → ν S = 0}

private theorem harmonic_le_left {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a*b/(a+b) ≤ a := by
  by_cases hd : a+b = 0
  · simpa [hd] using ha
  · apply (div_le_iff₀ (lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hd))).mpr
    nlinarith [sq_nonneg a]

omit [Fintype V] [DecidableEq V] in
private theorem harmonic_continuous (S T : Finset V) :
    ContinuousOn (fun ν : Finset V → ℝ => ν S * ν T / (ν S + ν T))
      {ν | ∀ U, 0 ≤ ν U} := by
  intro ν hν
  by_cases hd : ν S + ν T = 0
  · have hS : ν S = 0 := by have := hν S; have := hν T; linarith
    change Filter.Tendsto _ _ (nhds (ν S * ν T / (ν S + ν T)))
    simp only [hS, zero_mul, zero_div]
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (show Filter.Tendsto (fun μ : Finset V → ℝ => μ S) _ (nhds 0) from
        hS ▸ (continuous_apply S).continuousWithinAt)
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      exact div_nonneg (mul_nonneg (hμ S) (hμ T)) (add_nonneg (hμ S) (hμ T))
    · filter_upwards [self_mem_nhdsWithin] with μ hμ
      exact harmonic_le_left (hμ S) (hμ T)
  · exact ((continuous_apply S).mul (continuous_apply T)).continuousWithinAt.div
      ((continuous_apply S).add (continuous_apply T)).continuousWithinAt hd

private theorem harmonic_mono_left {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : a ≤ c) : a*b/(a+b) ≤ c*b/(c+b) := by
  obtain rfl | hb := hb.eq_or_lt
  · simp
  apply (div_le_div_iff₀ (by positivity : 0 < a+b) (by linarith : 0 < c+b)).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sq_nonneg b)]

private theorem harmonic_scale (a b c : ℝ) :
    (c*a)*(c*b)/(c*a+c*b) = c*(a*b/(a+b)) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hab : a+b = 0
  · simp [← mul_add, hab]
  rw [← mul_add]
  field_simp

private theorem regularized_continuous (ε : ℝ) :
    ContinuousOn (regularizedDual H ε) (probabilities H) := by
  apply ContinuousOn.add
  · apply ContinuousOn.div_const
    apply continuousOn_finsetSum
    intro S hS
    apply continuousOn_finsetSum
    intro i hi
    by_cases h : H.IsIndepSet (↑(S ∆ {i}) : Set V)
    · simpa only [if_pos h] using (harmonic_continuous S (S ∆ {i})).mono
        (fun ν hν => hν.1.1)
    · simpa only [if_neg h] using (continuousOn_const : ContinuousOn
        (fun _ : Finset V → ℝ => (0:ℝ)) (probabilities H))
  · exact continuousOn_const.mul (continuousOn_finsetSum _ fun S _ =>
      (Real.continuous_sqrt.comp (continuous_apply S)).continuousOn)

omit [DecidableEq V] [DecidableRel H.Adj] in
private theorem probabilities_compact : IsCompact (probabilities H) := by
  have hz : IsClosed {ν : Finset V → ℝ | ∀ S : Finset V,
      ¬ H.IsIndepSet (S : Set V) → ν S = 0} := by
    simp_rw [Set.ofPred_forall]
    exact isClosed_iInter fun S => isClosed_iInter fun _ =>
      isClosed_eq (continuous_apply S) continuous_const
  exact (isCompact_stdSimplex ℝ (Finset V)).inter_right hz

omit [DecidableEq V] [DecidableRel H.Adj] in
private theorem probabilities_nonempty : (probabilities H).Nonempty := by
  classical
  refine ⟨Pi.single ∅ 1, single_mem_stdSimplex ℝ ∅, ?_⟩
  intro S hS
  have hn : S ≠ ∅ := by
    intro he
    subst S
    exact hS (by simp [SimpleGraph.IsIndepSet, Set.Pairwise])
  simp [Ne.symm hn]

private theorem dual_scale_lower (ν μ : Finset V → ℝ) (c : ℝ)
    (hν : ∀ S, 0 ≤ ν S) (hμ : ∀ S, c * ν S ≤ μ S) (hc : 0 ≤ c) :
    c * harmonicDual H ν ≤ harmonicDual H μ := by
  unfold harmonicDual
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [mul_sum]
  apply sum_le_sum
  intro S hS
  rw [mul_sum]
  apply sum_le_sum
  intro j hj
  by_cases h : H.IsIndepSet (↑(S ∆ {j}) : Set V)
  · simp only [if_pos h]
    rw [← harmonic_scale]
    have hpS := mul_nonneg hc (hν S)
    have hpT := mul_nonneg hc (hν (S ∆ {j}))
    calc
      _ ≤ μ S * (c * ν (S ∆ {j})) / (μ S + c * ν (S ∆ {j})) :=
        harmonic_mono_left hpS hpT (hμ S)
      _ ≤ _ := by
        simpa only [mul_comm, add_comm] using
          harmonic_mono_left hpT (hpS.trans (hμ S)) (hμ (S ∆ {j}))
  · simp only [if_neg h, mul_zero, le_refl]

private theorem regularized_maximum_positive (ε : ℝ) (hε : 0 < ε)
    (ν : Finset V → ℝ) (hν : ν ∈ probabilities H)
    (hmax : IsMaxOn (regularizedDual H ε) (probabilities H) ν) :
    ∀ A : Finset V, H.IsIndepSet (A : Set V) → 0 < ν A := by
  intro A hA
  by_contra hn
  have hz : ν A = 0 := le_antisymm (le_of_not_gt hn) (hν.1.1 A)
  obtain ⟨r, hr, hrJ⟩ := exists_pos_mul_lt hε (|regularizedDual H ε ν| + ε + 1)
  have hr1 : r < 1 := by
    have : ε*r < ε := by nlinarith [abs_nonneg (regularizedDual H ε ν)]
    nlinarith
  have hrJ' : regularizedDual H ε ν * r < ε := by
    have := le_abs_self (regularizedDual H ε ν)
    nlinarith
  let t := r^2
  have ht : 0 < t := sq_pos_of_pos hr
  have ht1 : t < 1 := by dsimp [t]; nlinarith
  let μ : Finset V → ℝ := fun S => (1-t)*ν S + if S = A then t else 0
  have hμ : μ ∈ probabilities H := by
    refine ⟨⟨fun S => add_nonneg (mul_nonneg (by linarith) (hν.1.1 S))
      (by split <;> positivity), ?_⟩, ?_⟩
    · dsimp [μ]
      rw [sum_add_distrib, ← mul_sum, hν.1.2]
      simp
    · intro S hS
      have hne : S ≠ A := fun he => hS (he ▸ hA)
      simp [μ, hν.2 S hS, hne]
  have hμlower (S : Finset V) : (1-t)*ν S ≤ μ S := by
    dsimp [μ]
    split <;> linarith
  have hφ := dual_scale_lower H ν μ (1-t) hν.1.1 hμlower (by linarith)
  have hroot : (1-t) * (∑ S ∈ configurations H univ, Real.sqrt (ν S)) + r ≤
      ∑ S ∈ configurations H univ, Real.sqrt (μ S) := by
    have hAK : A ∈ configurations H univ := by simp [configurations, hA]
    rw [← sum_erase_add _ (fun S => Real.sqrt (μ S)) hAK,
      ← sum_erase_add _ (fun S => Real.sqrt (ν S)) hAK]
    have hμA : μ A = t := by simp [μ, hz]
    rw [hμA, hz, Real.sqrt_zero, add_zero]
    have hrt : Real.sqrt t = r := by simpa [t] using Real.sqrt_sq hr.le
    rw [hrt, mul_sum]
    apply add_le_add _ le_rfl
    apply sum_le_sum
    intro S hS
    have hne := (mem_erase.mp hS).1
    have hscale_root : 1-t ≤ Real.sqrt (1-t) := by
      apply (Real.le_sqrt (by linarith) (by linarith)).mpr
      nlinarith
    calc
      _ ≤ Real.sqrt (1-t) * Real.sqrt (ν S) :=
        mul_le_mul_of_nonneg_right hscale_root (Real.sqrt_nonneg _)
      _ = _ := by simp [μ, hne, Real.sqrt_mul (by linarith : 0 ≤ 1-t)]
  have hJ : (1-t) * regularizedDual H ε ν + ε*r ≤ regularizedDual H ε μ := by
    unfold regularizedDual
    nlinarith [mul_le_mul_of_nonneg_left hroot hε.le]
  have hm : regularizedDual H ε μ ≤ regularizedDual H ε ν := hmax hμ
  have hstrict : regularizedDual H ε ν < (1-t)*regularizedDual H ε ν + ε*r := by
    have := mul_pos hr (sub_pos.mpr hrJ')
    dsimp [t]
    nlinarith
  linarith

private theorem flip_sum (f : Finset V → Finset V → ℝ) (i : V) :
    (∑ S ∈ configurations H univ, if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
      f S (S ∆ {i}) else 0) =
    ∑ S ∈ configurations H univ, if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
      f (S ∆ {i}) S else 0 := by
  classical
  rw [← sum_filter, ← sum_filter]
  have hm (S : Finset V) :
      S ∈ (configurations H univ).filter (fun S : Finset V => H.IsIndepSet (↑(S ∆ {i}) : Set V)) ↔
        H.IsIndepSet (S : Set V) ∧ H.IsIndepSet (↑(S ∆ {i}) : Set V) := by
    simp [configurations]
  refine sum_bij (fun S _ => S ∆ {i}) ?_ ?_ ?_ ?_
  · intro S hS
    rw [hm, symmDiff_symmDiff_cancel_right]
    exact (hm S).mp hS |>.symm
  · intro S hS T hT he
    simpa only [symmDiff_symmDiff_cancel_right] using congrArg (fun U => U ∆ {i}) he
  · intro S hS
    refine ⟨S ∆ {i}, ?_, symmDiff_symmDiff_cancel_right _ _⟩
    rw [hm, symmDiff_symmDiff_cancel_right]
    exact (hm S).mp hS |>.symm
  · intro S hS
    simp only [symmDiff_symmDiff_cancel_right]

private theorem flipped_load_sum (ν w : Finset V → ℝ) : (∑ S ∈ configurations H univ, ∑ j : V,
    if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
      w (S ∆ {j}) * (ν S / (ν S + ν (S ∆ {j})))^2 else 0) =
    ∑ S ∈ configurations H univ, w S * coordinateLoad H ν S := by
  simp_rw [coordinateLoad, mul_sum, flipTerm, mul_ite, mul_zero]
  conv_lhs => rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro j _
  convert flip_sum H (fun S T => w T * (ν S / (ν S + ν T))^2) j using 1
  apply sum_congr rfl
  intro S hS
  rw [add_comm (ν (S ∆ {j}))]

private theorem regularized_derivative (ε : ℝ) (ν w : Finset V → ℝ)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S) :
    HasDerivAt (fun t : ℝ => regularizedDual H ε (fun S => ν S + t*w S))
      (∑ S ∈ configurations H univ,
        w S * (coordinateLoad H ν S + ε / (2 * Real.sqrt (ν S)))) 0 := by
  have hd (S : Finset V) : HasDerivAt (fun t : ℝ => ν S + t*w S) (w S) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const (w S)).const_add (ν S)
  have hterm (S : Finset V) (hS : S ∈ configurations H univ) (j : V) :
      HasDerivAt (fun t : ℝ => if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
        (ν S+t*w S)*(ν (S ∆ {j})+t*w (S ∆ {j})) /
        (ν S+t*w S+(ν (S ∆ {j})+t*w (S ∆ {j}))) else 0)
      (if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
        w S * (ν (S ∆ {j}) / (ν S + ν (S ∆ {j})))^2 +
        w (S ∆ {j}) * (ν S / (ν S + ν (S ∆ {j})))^2 else 0) 0 := by
    have hSi : H.IsIndepSet (S : Set V) := by simpa [configurations] using hS
    by_cases hT : H.IsIndepSet (↑(S ∆ {j}) : Set V)
    · simp only [if_pos hT]
      have hz : ν S + ν (S ∆ {j}) ≠ 0 := ne_of_gt (add_pos (hp _ hSi) (hp _ hT))
      apply (((hd S).mul (hd (S ∆ {j}))).div
        ((hd S).add (hd (S ∆ {j}))) (by simpa using hz)).congr_deriv
      simp only [Pi.add_apply, Pi.mul_apply, zero_mul, add_zero, div_pow]
      field_simp [hz]
      ring
    · simpa only [if_neg hT] using hasDerivAt_const (0:ℝ) (0:ℝ)
  have hφ := (HasDerivAt.sum (u := configurations H univ) fun S hS =>
    HasDerivAt.sum (u := (univ : Finset V)) fun j _ => hterm S hS j).div_const 2
  have hR := HasDerivAt.sum (u := configurations H univ) (fun S hS => (hd S).sqrt (by
    have hSi : H.IsIndepSet (S : Set V) := by simpa [configurations] using hS
    simpa using ne_of_gt (hp S hSi)))
  have hsflip := flipped_load_sum H ν w
  have htotal := hφ.add (hR.const_mul ε)
  simp only [Finset.sum_apply] at htotal
  change HasDerivAt (fun t : ℝ => regularizedDual H ε (fun S => ν S + t*w S)) _ 0 at htotal
  apply htotal.congr_deriv
  simp only [zero_mul, add_zero]
  have hsplit (S : Finset V) (j : V) :
        (if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
          w S * (ν (S ∆ {j}) / (ν S + ν (S ∆ {j})))^2 +
          w (S ∆ {j}) * (ν S / (ν S + ν (S ∆ {j})))^2 else 0) =
        w S * flipTerm H ν S j +
          (if H.IsIndepSet (↑(S ∆ {j}) : Set V) then
            w (S ∆ {j}) * (ν S / (ν S + ν (S ∆ {j})))^2 else 0) := by
      unfold flipTerm
      split <;> simp_all
  simp_rw [hsplit, sum_add_distrib]
  rw [hsflip]
  simp only [coordinateLoad, mul_add, mul_sum, sum_add_distrib]
  rw [← mul_sum]
  ring_nf
  simp only [mul_sum, mul_assoc]

private theorem regularized_stationary (ε : ℝ) (ν : Finset V → ℝ)
    (hν : ν ∈ probabilities H)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hmax : IsMaxOn (regularizedDual H ε) (probabilities H) ν) :
    ∃ τ : ℝ, ∀ S : Finset V, H.IsIndepSet (S : Set V) →
      coordinateLoad H ν S + ε / (2 * Real.sqrt (ν S)) = τ := by
  classical
  refine ⟨coordinateLoad H ν ∅ + ε / (2 * Real.sqrt (ν ∅)), ?_⟩
  intro A hA
  let w : Finset V → ℝ := fun S => (if S = A then 1 else 0) - (if S = ∅ then 1 else 0)
  have hwsum : ∑ S, w S = 0 := by simp [w, sum_sub_distrib]
  have hw (S : Finset V) (hS : ¬ H.IsIndepSet (S : Set V)) : w S = 0 := by
    have hne : S ≠ A := fun he => hS (he ▸ hA)
    have hne' : S ≠ ∅ := by
      intro he; subst S; exact hS (by simp [SimpleGraph.IsIndepSet, Set.Pairwise])
    simp [w, hne, hne']
  have hevent : ∀ᶠ t : ℝ in nhds 0, (fun S => ν S+t*w S) ∈ probabilities H := by
    have he : ∀ S, ∀ᶠ t : ℝ in nhds 0, 0 ≤ ν S+t*w S := by
      intro S
      by_cases hS : H.IsIndepSet (S : Set V)
      · have hc : ContinuousAt (fun t : ℝ => ν S+t*w S) 0 := by fun_prop
        exact (continuousAt_const.eventually_lt hc (by simpa using hp S hS)).mono (fun _ h => h.le)
      · exact Filter.Eventually.of_forall fun t => by simp [hν.2 S hS, hw S hS]
    filter_upwards [Filter.eventually_all.mpr he] with t ht
    refine ⟨⟨ht, ?_⟩, ?_⟩
    · simp only [sum_add_distrib, ← mul_sum, hν.1.2, hwsum, mul_zero, add_zero]
    · intro S hS; simp [hν.2 S hS, hw S hS]
  have hlocal : IsLocalMax (fun t : ℝ => regularizedDual H ε (fun S => ν S+t*w S)) 0 := by
    filter_upwards [hevent] with t ht
    simpa using hmax ht
  have hz := hlocal.hasDerivAt_eq_zero (regularized_derivative H ε ν w hp)
  have hAK : A ∈ configurations H univ := by simp [configurations, hA]
  have hEK : (∅ : Finset V) ∈ configurations H univ := by
    simp [configurations, SimpleGraph.IsIndepSet, Set.Pairwise]
  simpa [w, sub_mul, sum_sub_distrib, hAK, hEK, sub_eq_zero] using hz

/-- A square-root regularized harmonic dual has a positive maximizing probability vector,
and all its legal addition ratios satisfy the base-degree bounds. -/
theorem regularized_maximum (ε : ℝ) (hε : 0 < ε) :
    ∃ ν ∈ probabilities H, IsMaxOn (regularizedDual H ε) (probabilities H) ν ∧
      (∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S) ∧
      ∀ (i : V) (S : Finset V), i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
        (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) ≤ ν (insert i S) / ν S ∧
        ν (insert i S) / ν S ≤ 1 := by
  obtain ⟨ν, hν, hmax⟩ := (probabilities_compact H).exists_isMaxOn
    (probabilities_nonempty H) (regularized_continuous H ε)
  have hp := regularized_maximum_positive H ε hε ν hν hmax
  obtain ⟨τ, hs⟩ := regularized_stationary H ε ν hν hp hmax
  exact ⟨ν, hν, hmax, hp, fun i S hi hS => stationary_ratio_bounds H ν hε.le hp hs i S hi hS⟩


private def ratioDomain : Set (Finset V → ℝ) :=
  {ν | ν ∈ probabilities H ∧ ∀ (i : V) (S : Finset V),
    i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
      (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) * ν S ≤ ν (insert i S) ∧
      ν (insert i S) ≤ ν S}

private theorem ratioDomain_compact : IsCompact (ratioDomain H) := by
  have hc : IsClosed {ν : Finset V → ℝ | ∀ (i : V) (S : Finset V),
      i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
        (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) * ν S ≤ ν (insert i S) ∧
        ν (insert i S) ≤ ν S} := by
    simp_rw [Set.ofPred_forall]
    refine isClosed_iInter fun i => isClosed_iInter fun S =>
      isClosed_iInter fun _ => isClosed_iInter fun _ => ?_
    exact (isClosed_le (continuous_const.mul (continuous_apply S))
      (continuous_apply (insert i S))).inter
      (isClosed_le (continuous_apply (insert i S)) (continuous_apply S))
  exact (probabilities_compact H).inter_right hc

private theorem regularized_in_ratioDomain (ε : ℝ) (hε : 0 < ε) :
    ∃ ν ∈ ratioDomain H, IsMaxOn (regularizedDual H ε) (probabilities H) ν := by
  obtain ⟨ν, hν, hm, hp, hr⟩ := regularized_maximum H ε hε
  refine ⟨ν, ⟨hν, ?_⟩, hm⟩
  intro i S hi hS
  have hpos := hp S ((independent_insert H S i).mp hS).1
  exact ⟨(le_div_iff₀ hpos).mp (hr i S hi hS).1,
    (div_le_one hpos).mp (hr i S hi hS).2⟩

private theorem ratioDomain_positive (hd : ∀ i : V, H.degree i ≤ 3)
    (ν : Finset V → ℝ) (hν : ν ∈ ratioDomain H) :
    ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S := by
  have hupper : ∀ S : Finset V, H.IsIndepSet (S : Set V) → ν S ≤ ν ∅ := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact fun _ => le_rfl
    | @insert i S hi ih =>
      intro hS
      exact (hν.2 i S hi hS).2.trans (ih ((independent_insert H S i).mp hS).1)
  have hzero : 0 < ν ∅ := by
    by_contra hn
    have hz : ν ∅ = 0 := le_antisymm (le_of_not_gt hn) (hν.1.1.1 ∅)
    have hall : ∀ S, ν S = 0 := by
      intro S
      by_cases hS : H.IsIndepSet (S : Set V)
      · exact le_antisymm (hz ▸ hupper S hS) (hν.1.1.1 S)
      · exact hν.1.2 S hS
    have hs := hν.1.1.2
    simp only [hall, sum_const_zero] at hs
    norm_num at hs
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun _ => hzero
  | @insert i S hi ih =>
    intro hS
    have hg : (H.degree i : ℝ) ≤ 3 := by exact_mod_cast hd i
    have hl : 0 < (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) :=
      div_pos (by linarith) (by positivity)
    exact (mul_pos hl (ih ((independent_insert H S i).mp hS).1)).trans_le (hν.2 i S hi hS).1

private theorem regularizer_bound (ν : Finset V → ℝ) (hν : ν ∈ probabilities H) :
    ∑ S ∈ configurations H univ, Real.sqrt (ν S) ≤ (configurations H univ).card := by
  calc
    _ ≤ ∑ _S ∈ configurations H univ, (1 : ℝ) := by
      apply sum_le_sum
      intro S hS
      simpa using Real.sqrt_le_sqrt (mem_Icc_of_mem_stdSimplex hν.1 S).2
    _ = _ := by simp

/-- Base graphs of degree at most three have a positive unregularized maximizer obeying
all degree-dependent legal-addition ratios. -/
private theorem positive_maximum (hd : ∀ i : V, H.degree i ≤ 3) :
    ∃ ν ∈ probabilities H, IsMaxOn (harmonicDual H) (probabilities H) ν ∧
      (∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S) ∧
      ∀ (i : V) (S : Finset V), i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
        (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) ≤ ν (insert i S) / ν S ∧
        ν (insert i S) / ν S ≤ 1 := by
  obtain ⟨ρ, hρ, _⟩ := regularized_in_ratioDomain H 1 (by norm_num)
  have hc : ContinuousOn (harmonicDual H) (ratioDomain H) := by
    have hc := (regularized_continuous H 0).mono
      (show ratioDomain H ⊆ probabilities H from fun _ h => h.1)
    have hz : regularizedDual H 0 = harmonicDual H := by
      funext μ
      simp [regularizedDual]
    rwa [hz] at hc
  obtain ⟨ν, hν, hmax⟩ := (ratioDomain_compact H).exists_isMaxOn ⟨ρ, hρ⟩ hc
  have hp := ratioDomain_positive H hd ν hν
  refine ⟨ν, hν.1, ?_, hp, ?_⟩
  · intro μ hμ
    change harmonicDual H μ ≤ harmonicDual H ν
    apply le_of_forall_pos_le_add
    intro δ hδ
    obtain ⟨ε, hε, hsmall⟩ := exists_pos_mul_lt hδ ((configurations H univ).card : ℝ)
    obtain ⟨ρ, hρ, hr⟩ := regularized_in_ratioDomain H ε hε
    have hreg := regularizer_bound H ρ hρ.1
    have hnonneg : 0 ≤ ∑ S ∈ configurations H univ, Real.sqrt (μ S) :=
      sum_nonneg fun _ _ => Real.sqrt_nonneg _
    have hm : regularizedDual H ε μ ≤ regularizedDual H ε ρ := hr hμ
    have hφ : harmonicDual H ρ ≤ harmonicDual H ν := hmax hρ
    have hregmul := mul_le_mul_of_nonneg_left hreg hε.le
    have hposit := mul_nonneg hε.le hnonneg
    unfold regularizedDual at hm
    nlinarith
  · intro i S hi hS
    have hpos := hp S ((independent_insert H S i).mp hS).1
    exact ⟨(le_div_iff₀ hpos).mpr (hν.2 i S hi hS).1,
      (div_le_one hpos).mpr (hν.2 i S hi hS).2⟩


private theorem harmonic_support {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x*y/(x+y) ≤ x*(b/(a+b))^2 + y*(a/(a+b))^2 ∧
      (x*y/(x+y) = x*(b/(a+b))^2 + y*(a/(a+b))^2 ↔ x*b = y*a) := by
  by_cases hz : x+y = 0
  · have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by linarith
    simp [hx0, hy0]
  have hab : a+b ≠ 0 := ne_of_gt (add_pos ha hb)
  have hp : 0 < (x+y)*(a+b)^2 :=
    mul_pos (lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)) (sq_pos_of_pos (add_pos ha hb))
  have hid : x*(b/(a+b))^2 + y*(a/(a+b))^2 - x*y/(x+y) =
      (x*b-y*a)^2 / ((x+y)*(a+b)^2) := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · have := div_nonneg (sq_nonneg (x*b-y*a)) hp.le
    linarith
  · constructor
    · intro he
      by_contra hn
      have := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hn)) hp
      linarith
    · intro he
      rw [sub_eq_zero.mpr he, zero_pow (by norm_num : 2 ≠ 0), zero_div] at hid
      linarith

private theorem weighted_edge_sum (ν μ : Finset V → ℝ) :
    (∑ S ∈ configurations H univ, ∑ i : V,
      if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
        μ S * (ν (S ∆ {i}) / (ν S + ν (S ∆ {i})))^2 +
        μ (S ∆ {i}) * (ν S / (ν S + ν (S ∆ {i})))^2 else 0) =
      2 * ∑ S ∈ configurations H univ, μ S * coordinateLoad H ν S := by
  have hs (S : Finset V) (i : V) :
      (if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
        μ S * (ν (S ∆ {i}) / (ν S + ν (S ∆ {i})))^2 +
        μ (S ∆ {i}) * (ν S / (ν S + ν (S ∆ {i})))^2 else 0) =
      μ S * flipTerm H ν S i +
        (if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
          μ (S ∆ {i}) * (ν S / (ν S + ν (S ∆ {i})))^2 else 0) := by
    unfold flipTerm
    split <;> simp_all
  simp_rw [hs, sum_add_distrib]
  rw [flipped_load_sum H ν μ]
  simp only [coordinateLoad, mul_sum]
  ring_nf
  simp only [sum_mul]

private theorem probability_sum (ν : Finset V → ℝ) (hν : ν ∈ probabilities H) :
    ∑ S ∈ configurations H univ, ν S = 1 := by
  rw [show (∑ S ∈ configurations H univ, ν S) = ∑ S, ν S from ?_]
  · exact hν.1.2
  · apply sum_subset (subset_univ _)
    intro S hS hn
    exact hν.2 S (by simpa [configurations] using hn)

private theorem harmonic_euler (ν : Finset V → ℝ)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S) :
    harmonicDual H ν = ∑ S ∈ configurations H univ, ν S * coordinateLoad H ν S := by
  have he : (∑ S ∈ configurations H univ, ∑ i : V,
      if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
        ν S * ν (S ∆ {i}) / (ν S + ν (S ∆ {i})) else 0) =
      2 * ∑ S ∈ configurations H univ, ν S * coordinateLoad H ν S := by
    rw [← weighted_edge_sum H ν ν]
    apply sum_congr rfl
    intro S hS
    have hSi : H.IsIndepSet (S : Set V) := by simpa [configurations] using hS
    apply sum_congr rfl
    intro i hi
    by_cases hT : H.IsIndepSet (↑(S ∆ {i}) : Set V)
    · simp only [if_pos hT]
      exact (harmonic_support (hp S hSi) (hp _ hT) (hp S hSi).le (hp _ hT).le).2.mpr (mul_comm _ _)
    · simp only [if_neg hT]
  unfold harmonicDual
  rw [he]
  ring

private theorem maximum_edge_ratio (ν μ : Finset V → ℝ)
    (hν : ν ∈ probabilities H) (hμ : μ ∈ probabilities H)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hνmax : IsMaxOn (harmonicDual H) (probabilities H) ν)
    (hμmax : IsMaxOn (harmonicDual H) (probabilities H) μ) :
    ∀ (S : Finset V) (i : V), H.IsIndepSet (S : Set V) →
      H.IsIndepSet (↑(S ∆ {i}) : Set V) → μ S * ν (S ∆ {i}) = μ (S ∆ {i}) * ν S := by
  have hreg : IsMaxOn (regularizedDual H 0) (probabilities H) ν := by
    have hz : regularizedDual H 0 = harmonicDual H := by
      funext ρ
      simp [regularizedDual]
    rwa [hz]
  obtain ⟨τ, hs⟩ := regularized_stationary H 0 ν hν hp hreg
  simp only [zero_div, add_zero] at hs
  have hw (ρ : Finset V → ℝ) (hρ : ρ ∈ probabilities H) :
      (∑ S ∈ configurations H univ, ρ S * coordinateLoad H ν S) = τ := by
    calc
      _ = ∑ S ∈ configurations H univ, ρ S * τ := by
        apply sum_congr rfl
        intro S hS
        rw [hs S (by simpa [configurations] using hS)]
      _ = τ := by rw [← sum_mul, probability_sum H ρ hρ, one_mul]
  have heq : harmonicDual H μ = τ := by
    have he := harmonic_euler H ν hp
    rw [hw ν hν] at he
    exact le_antisymm ((hνmax hμ).trans he.le) (he.ge.trans (hμmax hν))
  let f (S : Finset V) (i : V) : ℝ :=
    if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
      μ S * (ν (S ∆ {i}) / (ν S + ν (S ∆ {i})))^2 +
      μ (S ∆ {i}) * (ν S / (ν S + ν (S ∆ {i})))^2 -
      μ S * μ (S ∆ {i}) / (μ S + μ (S ∆ {i})) else 0
  have hf : ∀ S ∈ configurations H univ, ∀ i : V, 0 ≤ f S i := by
    intro S hS i
    have hSi : H.IsIndepSet (S : Set V) := by simpa [configurations] using hS
    dsimp [f]
    split
    · rename_i hT
      exact sub_nonneg.mpr (harmonic_support (hp _ hSi) (hp _ hT) (hμ.1.1 _) (hμ.1.1 _)).1
    · exact le_rfl
  have hsum : (∑ S ∈ configurations H univ, ∑ i : V, f S i) = 0 := by
    have hsplit (S : Finset V) (i : V) : f S i =
        (if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
          μ S * (ν (S ∆ {i}) / (ν S + ν (S ∆ {i})))^2 +
          μ (S ∆ {i}) * (ν S / (ν S + ν (S ∆ {i})))^2 else 0) -
        (if H.IsIndepSet (↑(S ∆ {i}) : Set V) then
          μ S * μ (S ∆ {i}) / (μ S + μ (S ∆ {i})) else 0) := by
      dsimp [f]; split <;> simp_all
    simp_rw [hsplit, sum_sub_distrib]
    rw [weighted_edge_sum H ν μ, hw μ hμ]
    have hφ := heq
    unfold harmonicDual at hφ
    linarith
  intro S i hS hT
  have hSK : S ∈ configurations H univ := by simp [configurations, hS]
  have hout : (∑ j : V, f S j) = 0 :=
    (sum_eq_zero_iff_of_nonneg (fun T hT => sum_nonneg (fun j _ => hf T hT j))).mp hsum S hSK
  have hfi : f S i = 0 := (sum_eq_zero_iff_of_nonneg (fun j _ => hf S hSK j)).mp hout i (mem_univ _)
  simp only [f, if_pos hT, sub_eq_zero] at hfi
  exact (harmonic_support (hp _ hS) (hp _ hT) (hμ.1.1 _) (hμ.1.1 _)).2.mp hfi.symm

/-- A positive harmonic-dual maximum determines every other maximum by edge equality. -/
private theorem maximum_unique (ν μ : Finset V → ℝ)
    (hν : ν ∈ probabilities H) (hμ : μ ∈ probabilities H)
    (hp : ∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S)
    (hνmax : IsMaxOn (harmonicDual H) (probabilities H) ν)
    (hμmax : IsMaxOn (harmonicDual H) (probabilities H) μ) : μ = ν := by
  have hr := maximum_edge_ratio H ν μ hν hμ hp hνmax hμmax
  have he : H.IsIndepSet (↑(∅ : Finset V) : Set V) := by
    simp [SimpleGraph.IsIndepSet, Set.Pairwise]
  have hp0 := hp ∅ he
  have hcross : ∀ S : Finset V, μ S * ν ∅ = ν S * μ ∅ := by
    intro S
    by_cases hS : H.IsIndepSet (S : Set V)
    · induction S using Finset.induction_on with
      | empty => ring
      | @insert i S hi ih =>
        have hSi := ((independent_insert H S i).mp hS).1
        have hstep := hr S i hSi (by rwa [flip_absent S hi])
        rw [flip_absent S hi] at hstep
        have hind := ih hSi
        have hpos := hp S hSi
        have hA := congrArg (fun x : ℝ => x * ν ∅) hstep
        have hB := congrArg (fun x : ℝ => x * ν (insert i S)) hind
        have hc : ν S * (μ (insert i S) * ν ∅ - ν (insert i S) * μ ∅) = 0 := by
          nlinarith [hA, hB]
        exact sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left (ne_of_gt hpos))
    · rw [hν.2 S hS, hμ.2 S hS]
      ring
  have h0 : ν ∅ = μ ∅ := by
    have hs := congrArg (fun f : Finset V → ℝ => ∑ S, f S) (funext hcross)
    simpa only [← sum_mul, hν.1.2, hμ.1.2, one_mul] using hs
  funext S
  have hh := hcross S
  rw [← h0] at hh
  exact mul_right_cancel₀ (ne_of_gt hp0) hh

/-- Degree at most three gives a unique harmonic-dual maximizing probability,
with full support and the degree-dependent legal-addition bounds. -/
theorem unique_positive_maximum (hd : ∀ i : V, H.degree i ≤ 3) :
    ∃ ν ∈ probabilities H, IsMaxOn (harmonicDual H) (probabilities H) ν ∧
      (∀ S : Finset V, H.IsIndepSet (S : Set V) → 0 < ν S) ∧
      (∀ (i : V) (S : Finset V), i ∉ S → H.IsIndepSet (↑(insert i S) : Set V) →
        (4 - (H.degree i : ℝ)) / (4 + (H.degree i : ℝ)) ≤ ν (insert i S) / ν S ∧
        ν (insert i S) / ν S ≤ 1) ∧
      ∀ μ ∈ probabilities H, IsMaxOn (harmonicDual H) (probabilities H) μ → μ = ν := by
  obtain ⟨ν, hν, hm, hp, hr⟩ := positive_maximum H hd
  exact ⟨ν, hν, hm, hp, hr, fun μ hμ hmax => maximum_unique H ν μ hν hμ hp hm hmax⟩

#print axioms stationary_ratio_bounds
#print axioms regularized_maximum
#print axioms positive_maximum
#print axioms unique_positive_maximum

end D5.S3.Combinatorics.Graph.LegalWords.HarmonicDualMaximizer
