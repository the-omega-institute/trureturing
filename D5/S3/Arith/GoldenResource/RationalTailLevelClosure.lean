/- GID: D5/S3/Arith/GoldenResource/RationalTailLevelClosure
   generality: G
   mirror-B: D5/B/S3/Arith/GoldenResource/RationalTailLevelClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact rational tail filling gives sharp sublevel closures and nonclosed positive finite-state levels. -/
import D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

set_option autoImplicit false

namespace D5.S3.Arith.GoldenResource.RationalTailLevelClosure

open Set Filter
open scoped Topology BigOperators
open D5.S3.Analytic.WeightedCapacity.DyadicTailFilling (X B)
open D5.S3.Arith.GoldenResource.RationalCapacityTailRealization

/-- The finite capacity states with a prescribed real value of their rational reading. -/
noncomputable def level (g A : ℕ → ℕ) (c : ℝ) : Set (B A) :=
  {u | (weightedRead g u : ℝ) = c}

/-- The image of a finite-state level in the full coordinate product. -/
noncomputable def ambientLevel (g A : ℕ → ℕ) (c : ℝ) : Set (X A) :=
  Subtype.val '' level g A c

set_option maxHeartbeats 800000 in
/-- Exact rational tail filling makes nonnegative rational level closures equal to sublevels
in both coordinate carriers, makes positive rational levels nonempty and nonclosed, and leaves
only the zero state at level zero and no finite states at negative or irrational levels. -/
theorem rational_tail_level_closure (g A : ℕ → ℕ) (hg : ∀ n, 0 < g n) :
    (FillsRationalTails g A →
      (∀ c : ℚ, 0 ≤ c →
        closure (ambientLevel g A c) = {x | weightedTotal g x ≤ ENNReal.ofReal c} ∧
        closure (level g A c) = {u | (weightedRead g u : ℝ) ≤ c}) ∧
      (∀ c : ℚ, 0 < c → (level g A c).Nonempty ∧
        ¬ IsClosed (ambientLevel g A c) ∧ ¬ IsClosed (level g A c))) ∧
    (∀ c : ℝ, (c < 0 ∨ ¬ ∃ q : ℚ, (q : ℝ) = c) →
      level g A c = ∅ ∧ closure (level g A c) = ∅ ∧ closure (ambientLevel g A c) = ∅) ∧
    level g A 0 = {u | ∀ n, (u.val n : ℕ) = 0} ∧
    {x : X A | weightedTotal g x = 0} = {x | ∀ n, (x n : ℕ) = 0} := by
  classical
  let p (x : X A) (N : ℕ) : ℚ :=
    ∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℚ) / g n
  have hpcast (x : X A) (N : ℕ) : (p x N : ℝ) =
      ∑ n ∈ Finset.range (N + 1), ((x n : ℕ) : ℝ) / g n := by
    simp only [p, Rat.cast_sum, Rat.cast_div, Rat.cast_natCast]
  have hread (u : B A) (s : Finset ℕ) (hs : u.property.toFinset ⊆ s) :
      weightedRead g u = ∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n := by
    apply Finset.sum_subset hs
    intro n _ hn
    have hz : (u.val n : ℕ) = 0 := by simpa using hn
    simp [hz]
  have hprefix (u : B A) (s : Finset ℕ) :
      (∑ n ∈ s, ((u.val n : ℕ) : ℚ) / g n) ≤ weightedRead g u := by
    rw [hread u (s ∪ u.property.toFinset) Finset.subset_union_right]
    exact Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (by
      intros; positivity)
  have hsub (x : X A) (c : ℝ) (hc : 0 ≤ c) :
      weightedTotal g x ≤ ENNReal.ofReal c ↔ ∀ N, (p x N : ℝ) ≤ c := by
    unfold weightedTotal
    simp only [← hpcast, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hc]
  have hupper (c : ℚ) (hc : 0 ≤ c) :
      closure (ambientLevel g A c) ⊆ {x | weightedTotal g x ≤ ENNReal.ofReal c} := by
    intro x hx
    apply (hsub x c (by exact_mod_cast hc)).mpr
    intro N
    have hcont : Continuous (fun y : X A => (p y N : ℝ)) := by
      simp only [hpcast]
      apply continuous_finsetSum
      intro n _
      exact ((continuous_of_discreteTopology : Continuous (fun z : Fin (A n + 1) =>
        ((z : ℕ) : ℝ))).comp (continuous_apply n)).div_const _
    apply closure_minimal (t := {y : X A | (p y N : ℝ) ≤ c}) ?_
      (isClosed_le hcont continuous_const) hx
    rintro y ⟨u, hu, rfl⟩
    exact (show (p u.val N : ℝ) ≤ (weightedRead g u : ℝ) by
      exact_mod_cast hprefix u (Finset.range (N + 1))).trans_eq hu
  have hcomplete (hfill : FillsRationalTails g A) (c : ℚ) (hc : 0 ≤ c)
      (x : X A) (hx : weightedTotal g x ≤ ENNReal.ofReal c) (N : ℕ) :
      ∃ u : B A, (∀ n, n ≤ N → u.val n = x n) ∧ weightedRead g u = c := by
    have hpc : p x N ≤ c := by
      exact_mod_cast (hsub x c (by exact_mod_cast hc)).mp hx N
    obtain ⟨w, hwN, hwq⟩ := hfill (c - p x N) (sub_nonneg.mpr hpc) N
    let u : X A := fun n => if n ≤ N then x n else w.val n
    let s := Finset.range (N + 1) ∪ w.property.toFinset
    have hus : Function.support (fun n => (u n : ℕ)) ⊆ (s : Set ℕ) := by
      intro n hn
      by_cases hnN : n ≤ N
      · exact Finset.mem_union_left _ (Finset.mem_range.mpr (by omega))
      · apply Finset.mem_union_right
        have hne : (w.val n : ℕ) ≠ 0 := by simpa [u, hnN] using hn
        simpa using hne
    let ub : B A := ⟨u, s.finite_toSet.subset hus⟩
    refine ⟨ub, ?_, ?_⟩
    · intro n hn
      simp [ub, u, hn]
    · have hpre : (∑ n ∈ s, if n ≤ N then ((x n : ℕ) : ℚ) / g n else 0) =
          p x N := by
        calc
          _ = ∑ n ∈ Finset.range (N + 1),
              if n ≤ N then ((x n : ℕ) : ℚ) / g n else 0 := by
            symm
            apply Finset.sum_subset Finset.subset_union_left
            intro n _ hn
            simp only [Finset.mem_range, not_lt] at hn
            simp [show ¬ n ≤ N by omega]
          _ = p x N := by
            apply Finset.sum_congr rfl
            intro n hn
            simp [show n ≤ N by simpa [Finset.mem_range] using hn]
      have hsum : weightedRead g ub = p x N + weightedRead g w := by
        rw [hread ub s (by intro n hn; exact hus (by simpa using hn)),
          hread w s Finset.subset_union_right, ← hpre, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro n _
        by_cases hn : n ≤ N
        · simp [ub, u, hn, hwN n hn]
        · simp [ub, u, hn]
      rw [hsum, hwq]
      ring
  have hambient (hfill : FillsRationalTails g A) (c : ℚ) (hc : 0 ≤ c) :
      closure (ambientLevel g A c) = {x | weightedTotal g x ≤ ENNReal.ofReal c} := by
    apply subset_antisymm (hupper c hc)
    intro x hx
    apply mem_closure_iff.mpr
    intro o ho hxo
    have hon := ho.mem_nhds hxo
    rw [nhds_pi, Filter.mem_pi'] at hon
    obtain ⟨I, t, ht, hto⟩ := hon
    obtain ⟨u, huN, huq⟩ := hcomplete hfill c hc x hx (I.sup id)
    refine ⟨u.val, hto ?_, u, ?_, rfl⟩
    · intro n hn
      rw [huN n (Finset.le_sup (f := id) hn)]
      exact mem_of_mem_nhds (ht n)
    · change (weightedRead g u : ℝ) = c
      exact_mod_cast huq
  have hnonneg (u : B A) : 0 ≤ weightedRead g u := by
    unfold weightedRead
    exact Finset.sum_nonneg (by intros; positivity)
  have hfinite (u : B A) :
      weightedTotal g u.val = ENNReal.ofReal (weightedRead g u) := by
    apply le_antisymm
    · apply (hsub u.val (weightedRead g u) (by exact_mod_cast hnonneg u)).mpr
      intro N
      exact_mod_cast hprefix u (Finset.range (N + 1))
    · let N := u.property.toFinset.sup id
      have hs : u.property.toFinset ⊆ Finset.range (N + 1) := by
        intro n hn
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hn))
      have hp : p u.val N = weightedRead g u := (hread u _ hs).symm
      rw [← hp, hpcast]
      exact le_iSup (fun N => ENNReal.ofReal
        (∑ n ∈ Finset.range (N + 1), ((u.val n : ℕ) : ℝ) / g n)) N
  have hclosure (hfill : FillsRationalTails g A) (c : ℚ) (hc : 0 ≤ c) :
      closure (ambientLevel g A c) = {x | weightedTotal g x ≤ ENNReal.ofReal c} ∧
      closure (level g A c) = {u | (weightedRead g u : ℝ) ≤ c} := by
    refine ⟨hambient hfill c hc, ?_⟩
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    change Subtype.val ⁻¹' closure (ambientLevel g A c) = _
    rw [hambient hfill c hc]
    ext u
    change weightedTotal g u.val ≤ ENNReal.ofReal c ↔ (weightedRead g u : ℝ) ≤ c
    rw [hfinite u, ENNReal.ofReal_le_ofReal_iff (by exact_mod_cast hc)]
  constructor
  · intro hfill
    refine ⟨hclosure hfill, ?_⟩
    intro c hc
    obtain ⟨u, _, hu⟩ := hfill c hc.le 0
    let z : B A := ⟨fun n => ⟨0, Nat.zero_lt_succ _⟩, by simp [Function.support]⟩
    have hzread : weightedRead g z = 0 := by simp [weightedRead, z]
    have hzambient : z.val ∈ closure (ambientLevel g A c) := by
      rw [(hclosure hfill c hc.le).1]
      change weightedTotal g z.val ≤ ENNReal.ofReal c
      simp [hfinite z, hzread]
    have hzrelative : z ∈ closure (level g A c) := by
      rw [(hclosure hfill c hc.le).2]
      change (weightedRead g z : ℝ) ≤ c
      simpa [hzread] using (show (0 : ℝ) ≤ c by exact_mod_cast hc.le)
    have hznot : z ∉ level g A c := by
      intro hz
      have he : (0 : ℚ) = c := by simpa [level, hzread] using hz
      exact (ne_of_gt hc) he.symm
    refine ⟨⟨u, by change (weightedRead g u : ℝ) = c; exact_mod_cast hu⟩, ?_, ?_⟩
    · intro hclosed
      rw [hclosed.closure_eq] at hzambient
      obtain ⟨v, hv, hvz⟩ := hzambient
      have he : v = z := Subtype.ext hvz
      exact hznot (he ▸ hv)
    · intro hclosed
      rw [hclosed.closure_eq] at hzrelative
      exact hznot hzrelative
  · sorry

#print axioms rational_tail_level_closure

end D5.S3.Arith.GoldenResource.RationalTailLevelClosure
