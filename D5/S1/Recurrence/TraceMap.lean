/- GID: D5/S1/Recurrence/TraceMap
   generality: I
   mirror-B: D5/B/S1/Recurrence/TraceMap
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Per-axis admissible-word partial sums satisfy the closed golden trace-map recursion. -/

import Mathlib

/- Provenance: top-bit decomposition of admissible words (using the top bit
   forces its neighbour empty) over pinned mathlib finite-set algebra
   (`Finset.sum_union`, `Finset.sum_image`, `Finset.prod_insert`), combined
   with the golden Fibonacci power recurrence exported by pinned mathlib
   (`Real.goldenRatio_sq`, `Real.goldenConj_sq`, `Real.exp_add`). -/

namespace D5.S1.Recurrence.TraceMap

open Real

/-! ### Admissible words of bounded bit depth

An admissible word of bit depth `K` selects a set of bits among
`0, …, K - 1` with no two consecutive bits selected.  Bit `i` encodes the
Zeckendorf index `i + 1`, so depth `K` ranges over Zeckendorf indices
`1, …, K`. -/

/-- Admissible words of bit depth `K`: subsets of `Finset.range K` with no
two consecutive bits. -/
def admissibleWords (K : ℕ) : Finset (Finset ℕ) :=
  (Finset.range K).powerset.filter fun s => ∀ i ∈ s, i + 1 ∉ s

/-- The weighted sum over admissible words of depth `K`, each word weighted
by the product of its bit weights. -/
noncomputable def wordSum (w : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ s ∈ admissibleWords K, ∏ i ∈ s, w i

private theorem mem_admissibleWords {K : ℕ} {s : Finset ℕ} :
    s ∈ admissibleWords K ↔ s ⊆ Finset.range K ∧ ∀ i ∈ s, i + 1 ∉ s := by
  simp [admissibleWords]

private theorem not_top_mem {K : ℕ} {s : Finset ℕ}
    (hs : s ∈ admissibleWords K) : K + 1 ∉ s := fun h => by
  have := Finset.mem_range.mp ((mem_admissibleWords.mp hs).1 h)
  omega

/-- Top-bit decomposition of the admissible words of depth `K + 2`: the words
avoiding the top bit are the words of depth `K + 1`, and the words using the
top bit force bit `K` empty, leaving a word of depth `K`. -/
private theorem admissibleWords_succ_succ (K : ℕ) :
    admissibleWords (K + 2)
      = admissibleWords (K + 1) ∪ (admissibleWords K).image (insert (K + 1)) := by
  ext s
  rw [Finset.mem_union, Finset.mem_image]
  constructor
  · intro hs
    obtain ⟨hsub, hadj⟩ := mem_admissibleWords.mp hs
    by_cases htop : K + 1 ∈ s
    · refine Or.inr ⟨s.erase (K + 1), mem_admissibleWords.mpr ⟨?_, ?_⟩,
        Finset.insert_erase htop⟩
      · intro i hi
        have hne : i ≠ K + 1 := Finset.ne_of_mem_erase hi
        have hmem : i ∈ s := Finset.mem_of_mem_erase hi
        have hlt : i < K + 2 := Finset.mem_range.mp (hsub hmem)
        have hK : i ≠ K := by
          rintro rfl
          exact hadj i hmem htop
        exact Finset.mem_range.mpr (by omega)
      · intro i hi hcon
        exact hadj i (Finset.mem_of_mem_erase hi) (Finset.mem_of_mem_erase hcon)
    · refine Or.inl (mem_admissibleWords.mpr ⟨fun i hi => ?_, hadj⟩)
      have hlt : i < K + 2 := Finset.mem_range.mp (hsub hi)
      have hne : i ≠ K + 1 := fun h => htop (h ▸ hi)
      exact Finset.mem_range.mpr (by omega)
  · rintro (hs | ⟨t, ht, rfl⟩)
    · obtain ⟨hsub, hadj⟩ := mem_admissibleWords.mp hs
      refine mem_admissibleWords.mpr ⟨fun i hi => ?_, hadj⟩
      have := Finset.mem_range.mp (hsub hi)
      exact Finset.mem_range.mpr (by omega)
    · obtain ⟨hsub, hadj⟩ := mem_admissibleWords.mp ht
      refine mem_admissibleWords.mpr ⟨?_, ?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · exact Finset.mem_range.mpr (by omega)
        · have := Finset.mem_range.mp (hsub hi')
          exact Finset.mem_range.mpr (by omega)
      · intro i hi hcon
        rcases Finset.mem_insert.mp hi with rfl | hi'
        · rcases Finset.mem_insert.mp hcon with h | h
          · omega
          · have := Finset.mem_range.mp (hsub h)
            omega
        · rcases Finset.mem_insert.mp hcon with h | h
          · have := Finset.mem_range.mp (hsub hi')
            omega
          · exact hadj i hi' h

private theorem disjoint_top_split (K : ℕ) :
    Disjoint (admissibleWords (K + 1)) ((admissibleWords K).image (insert (K + 1))) := by
  rw [Finset.disjoint_left]
  intro s hs him
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp him
  have hmem : K + 1 ∈ insert (K + 1) t := Finset.mem_insert_self _ _
  have := Finset.mem_range.mp ((mem_admissibleWords.mp hs).1 hmem)
  omega

/-- Closed recursion of the weighted admissible-word sums: the depth-`(K + 2)`
sum splits along the top bit, whose use forces its neighbour empty. -/
theorem wordSum_succ_succ (w : ℕ → ℝ) (K : ℕ) :
    wordSum w (K + 2) = wordSum w (K + 1) + w (K + 1) * wordSum w K := by
  have hinj : ∀ s ∈ admissibleWords K, ∀ t ∈ admissibleWords K,
      insert (K + 1) s = insert (K + 1) t → s = t := by
    intro s hs t ht hst
    calc s = (insert (K + 1) s).erase (K + 1) :=
          (Finset.erase_insert (not_top_mem hs)).symm
      _ = (insert (K + 1) t).erase (K + 1) := by rw [hst]
      _ = t := Finset.erase_insert (not_top_mem ht)
  unfold wordSum
  rw [admissibleWords_succ_succ, Finset.sum_union (disjoint_top_split K),
    Finset.sum_image hinj]
  congr 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s hs => Finset.prod_insert (not_top_mem hs)

/-! ### Golden per-axis weights

The weight of the Zeckendorf index `k` reads the expansion face at `x`
against the golden ratio power `k + 1` and the contraction face at `y`
against the golden conjugate power `k + 1`. -/

/-- The per-axis weight of the Zeckendorf index `k` at the face pair
`(x, y)`. -/
noncomputable def axisWeight (x y : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-(x * goldenRatio ^ (k + 1)) + y * goldenConj ^ (k + 1))

/-- The per-axis partial sum of bit depth `K`: admissible words on Zeckendorf
indices `1, …, K`, each index weighted by its per-axis weight. -/
noncomputable def tracePartial (x y : ℝ) (K : ℕ) : ℝ :=
  wordSum (fun i => axisWeight x y (i + 1)) K

/-- The per-axis weights are multiplicative along consecutive indices because
both golden exponents satisfy the Fibonacci power recurrence. -/
theorem axisWeight_succ_succ (x y : ℝ) (k : ℕ) :
    axisWeight x y (k + 2) = axisWeight x y (k + 1) * axisWeight x y k := by
  unfold axisWeight
  rw [← Real.exp_add]
  congr 1
  have hφ : goldenRatio ^ (k + 2 + 1)
      = goldenRatio ^ (k + 1 + 1) + goldenRatio ^ (k + 1) := by
    calc goldenRatio ^ (k + 2 + 1) = goldenRatio ^ (k + 1) * goldenRatio ^ 2 := by
          ring
      _ = goldenRatio ^ (k + 1) * (goldenRatio + 1) := by rw [goldenRatio_sq]
      _ = goldenRatio ^ (k + 1 + 1) + goldenRatio ^ (k + 1) := by ring
  have hψ : goldenConj ^ (k + 2 + 1)
      = goldenConj ^ (k + 1 + 1) + goldenConj ^ (k + 1) := by
    calc goldenConj ^ (k + 2 + 1) = goldenConj ^ (k + 1) * goldenConj ^ 2 := by
          ring
      _ = goldenConj ^ (k + 1) * (goldenConj + 1) := by rw [goldenConj_sq]
      _ = goldenConj ^ (k + 1 + 1) + goldenConj ^ (k + 1) := by ring
  rw [hφ, hψ]
  ring

/-! ### The closed trace-map recursion -/

/-- The per-axis trace map of the source atom: the partial sums and the
weights satisfy the closed recursion pair.  The depth-`(K + 2)` partial sum
closes through the two previous depths via the top-bit weight — using the top
bit forces its neighbour empty — and the top-bit weight itself is the product
of the two preceding weights, because the golden exponents satisfy the
Fibonacci recurrence. -/
theorem trace_map_recursion (x y : ℝ) (K : ℕ) :
    tracePartial x y (K + 2)
        = tracePartial x y (K + 1) + axisWeight x y (K + 2) * tracePartial x y K ∧
      axisWeight x y (K + 2) = axisWeight x y (K + 1) * axisWeight x y K :=
  ⟨wordSum_succ_succ (fun i => axisWeight x y (i + 1)) K,
    axisWeight_succ_succ x y K⟩

end D5.S1.Recurrence.TraceMap
