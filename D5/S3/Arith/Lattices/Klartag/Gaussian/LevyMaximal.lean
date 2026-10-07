/- GID: D5/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/Gaussian/LevyMaximal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Gaussian moments, independence and operator norm tails. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Tail.PaddedTail

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Finset
open scoped ENNReal NNReal

/-- **The reflection step.**  If `R` preserves `P`, fixes `E`, and pulls `F` back to `G`, and
`F ∪ G` covers `E`, then `P E ≤ 2 · P (E ∩ F)`.

This is the entire content of the reflection principle, with no probability theory in it. -/
theorem measure_le_two_mul_of_reflection
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E F G : Set Ω} {R : Ω → Ω}
    (hPR : MeasurePreserving R P P)
    (hE : R ⁻¹' E = E) (hFG : R ⁻¹' F = G) (hcover : E ⊆ F ∪ G)
    (hEm : MeasurableSet E) (hFm : MeasurableSet F) :
    P E ≤ 2 * P (E ∩ F) := by
  have hpre : R ⁻¹' (E ∩ F) = E ∩ G := by rw [Set.preimage_inter, hE, hFG]
  have h1 : P (E ∩ G) = P (E ∩ F) := by
    calc P (E ∩ G) = P (R ⁻¹' (E ∩ F)) := by rw [hpre]
      _ = (P.map R) (E ∩ F) := (Measure.map_apply hPR.measurable (hEm.inter hFm)).symm
      _ = P (E ∩ F) := by rw [hPR.map_eq]
  have h2 : E ⊆ (E ∩ F) ∪ (E ∩ G) := by
    intro ω hω
    rcases hcover hω with h | h
    · exact Or.inl ⟨hω, h⟩
    · exact Or.inr ⟨hω, h⟩
  calc P E ≤ P ((E ∩ F) ∪ (E ∩ G)) := measure_mono h2
    _ ≤ P (E ∩ F) + P (E ∩ G) := measure_union_le _ _
    _ = 2 * P (E ∩ F) := by rw [h1, two_mul]

/-- **First-passage decomposition plus reflection.**  `E k` is `{τ = k}`, a disjoint family;
`R k` is the reflection attached to time `k`; `target` absorbs every `E k ∩ F k`.  Then the
hitting event has measure at most `2 · P target`.

Both `hlevy` (here) and `hsym` (`Padding.lean`) are instances of this one lemma. -/
theorem measure_le_two_mul_of_reflection_family
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {E F G : ℕ → Set Ω} {target : Set Ω} {R : ℕ → Ω → Ω}
    (hEm : ∀ k, MeasurableSet (E k)) (hFm : ∀ k, MeasurableSet (F k))
    (hdisj : ∀ j k, j ≠ k → Disjoint (E j) (E k))
    (hPR : ∀ k, MeasurePreserving (R k) P P)
    (hEinv : ∀ k, R k ⁻¹' E k = E k)
    (hFGk : ∀ k, R k ⁻¹' F k = G k)
    (hcover : ∀ k, E k ⊆ F k ∪ G k)
    (hsub : ∀ k, k ≤ N → E k ∩ F k ⊆ target) :
    P (⋃ k ∈ Finset.range (N + 1), E k) ≤ 2 * P target := by
  have hpd : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint E :=
    fun j _ k _ hjk => hdisj j k hjk
  have hpd' : (↑(Finset.range (N + 1)) : Set ℕ).PairwiseDisjoint (fun k => E k ∩ F k) :=
    fun j _ k _ hjk => (hdisj j k hjk).mono inter_subset_left inter_subset_left
  rw [measure_biUnion_finset hpd (fun k _ => hEm k)]
  have hstep : ∀ k ∈ Finset.range (N + 1), P (E k) ≤ 2 * P (E k ∩ F k) := by
    intro k _
    exact measure_le_two_mul_of_reflection (hPR k) (hEinv k) (hFGk k) (hcover k) (hEm k) (hFm k)
  calc ∑ k ∈ Finset.range (N + 1), P (E k)
      ≤ ∑ k ∈ Finset.range (N + 1), 2 * P (E k ∩ F k) := Finset.sum_le_sum hstep
    _ = 2 * ∑ k ∈ Finset.range (N + 1), P (E k ∩ F k) := by rw [Finset.mul_sum]
    _ = 2 * P (⋃ k ∈ Finset.range (N + 1), (E k ∩ F k)) := by
        rw [measure_biUnion_finset hpd' (fun k _ => (hEm k).inter (hFm k))]
    _ ≤ 2 * P target := by
        have hsubset : (⋃ k ∈ Finset.range (N + 1), (E k ∩ F k)) ⊆ target :=
          iUnion₂_subset (fun k hk => hsub k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)))
        gcongr

/-- Flip the sign of the coordinates satisfying `p`. -/
def flipCoords {ι : Type*} (p : ι → Prop) [DecidablePred p] (ω : ι → ℝ) : ι → ℝ :=
  fun i => if p i then -(ω i) else ω i

/-- A product of symmetric laws is invariant under flipping any set of coordinates. -/
theorem measurePreserving_flipCoords {ι : Type*} [Fintype ι] {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : MeasurePreserving (fun x : ℝ => -x) μ μ)
    (p : ι → Prop) [DecidablePred p] :
    MeasurePreserving (flipCoords p) (Measure.pi fun _ : ι => μ) (Measure.pi fun _ : ι => μ) := by
  have h : ∀ i : ι, MeasurePreserving (fun x : ℝ => if p i then -x else x) μ μ := by
    intro i
    by_cases hpi : p i
    · simpa [hpi] using hμ
    · have hid : (fun x : ℝ => if p i then -x else x) = id := by funext x; simp [hpi]
      rw [hid]
      exact MeasurePreserving.id μ
  exact measurePreserving_pi (fun _ : ι => μ) (fun _ : ι => μ) h

/-- `walkSum k ω = ∑_{i < k} ω i`, the partial sums of the coordinate increments. -/
def walkSum {N : ℕ} (k : ℕ) (ω : Fin N → ℝ) : ℝ := ∑ i : Fin N, if (i : ℕ) < k then ω i else 0

theorem measurable_walkSum {N k : ℕ} : Measurable (walkSum (N := N) k) := by
  unfold walkSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  by_cases h : (i : ℕ) < k
  · simpa [h] using (measurable_pi_apply i)
  · simp [h]

/-- `walkSum N` is the total sum. -/
theorem walkSum_total {N : ℕ} (ω : Fin N → ℝ) : walkSum N ω = ∑ i : Fin N, ω i := by
  unfold walkSum
  exact Finset.sum_congr rfl (fun i _ => by simp [i.is_lt])

/-- The reflection attached to time `k`: flip every increment of index `≥ k`. -/
def flipTail (N k : ℕ) : (Fin N → ℝ) → (Fin N → ℝ) :=
  flipCoords (fun i : Fin N => k ≤ (i : ℕ))

/-- `flipTail k` does not move the partial sums up to time `k`. -/
theorem walkSum_flipTail_le {N k j : ℕ} (hjk : j ≤ k) (ω : Fin N → ℝ) :
    walkSum j (flipTail N k ω) = walkSum j ω := by
  unfold walkSum flipTail flipCoords
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : (i : ℕ) < j
  · have : ¬ (k ≤ (i : ℕ)) := by omega
    simp [h, this]
  · simp [h]

/-- `flipTail k` reflects the increment from `k` to `N`. -/
theorem walkSum_flipTail_total {N k : ℕ} (ω : Fin N → ℝ) :
    walkSum N (flipTail N k ω) + walkSum N ω = 2 * walkSum k ω := by
  rw [walkSum_total, walkSum_total]
  unfold walkSum flipTail flipCoords
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : k ≤ (i : ℕ)
  · have : ¬ ((i : ℕ) < k) := by omega
    simp [h, this]
  · have : (i : ℕ) < k := by omega
    simp [h, this]; ring

/-- The reflected tail increment is the negative of the original. -/
theorem tail_flipTail {N k : ℕ} (ω : Fin N → ℝ) :
    walkSum N (flipTail N k ω) - walkSum k (flipTail N k ω)
      = -(walkSum N ω - walkSum k ω) := by
  have h1 : walkSum k (flipTail N k ω) = walkSum k ω := walkSum_flipTail_le (le_refl k) ω
  have h2 := walkSum_flipTail_total (N := N) (k := k) ω
  rw [h1]
  linarith

variable {N : ℕ} {μ : Measure ℝ}

/-- `{τ = k}`: the walk first reaches `r` at time `k`. -/
def firstHit (N : ℕ) (r : ℝ) (k : ℕ) : Set (Fin N → ℝ) :=
  {ω | r ≤ walkSum k ω ∧ ∀ j < k, ¬ (r ≤ walkSum j ω)}

theorem measurableSet_firstHit (N : ℕ) (r : ℝ) (k : ℕ) :
    MeasurableSet (firstHit N r k) := by
  have h1 : MeasurableSet {ω : Fin N → ℝ | r ≤ walkSum k ω} :=
    measurableSet_le measurable_const measurable_walkSum
  have h2 : MeasurableSet
      (⋂ j ∈ Finset.range k, {ω : Fin N → ℝ | ¬ (r ≤ walkSum j ω)}) :=
    MeasurableSet.biInter (Finset.range k).countable_toSet
      (fun j _ => (measurableSet_le measurable_const measurable_walkSum).compl)
  have heq : firstHit N r k = {ω : Fin N → ℝ | r ≤ walkSum k ω}
      ∩ ⋂ j ∈ Finset.range k, {ω : Fin N → ℝ | ¬ (r ≤ walkSum j ω)} := by
    ext ω
    simp [firstHit, Finset.mem_range]
  rw [heq]
  exact h1.inter h2

theorem firstHit_disjoint (N : ℕ) (r : ℝ) {j k : ℕ} (hjk : j ≠ k) :
    Disjoint (firstHit N r j) (firstHit N r k) := by
  rw [Set.disjoint_left]
  intro ω hj hk
  rcases lt_or_gt_of_ne hjk with h | h
  · exact hk.2 j h hj.1
  · exact hj.2 k h hk.1

/-- **First-passage decomposition**, for an arbitrary family of predicates: the events
"`p` first holds at time `k`", `k ≤ N`, partition `{∃ k ≤ N, p k x}`.  Used for both `hlevy`
(here) and `hsym` (`Padding.lean`). -/
theorem biUnion_firstIdx {α : Type*} (p : ℕ → α → Prop) (N : ℕ) :
    (⋃ k ∈ Finset.range (N + 1), {x | p k x ∧ ∀ j < k, ¬ p j x}) = {x | ∃ k ≤ N, p k x} := by
  classical
  ext x
  simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨k, hk, hk1, -⟩
    exact ⟨k, Nat.lt_succ_iff.mp hk, hk1⟩
  · rintro ⟨k, hk, hk1⟩
    have hex : ∃ m, p m x := ⟨k, hk1⟩
    refine ⟨Nat.find hex, ?_, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
    have hle : Nat.find hex ≤ k := Nat.find_le hk1
    omega

theorem biUnion_firstHit (N : ℕ) (r : ℝ) :
    (⋃ k ∈ Finset.range (N + 1), firstHit N r k) = {ω : Fin N → ℝ | ∃ k ≤ N, r ≤ walkSum k ω} :=
  biUnion_firstIdx (fun k ω => r ≤ walkSum k ω) N

theorem levy_maximal [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving (fun x : ℝ => -x) μ μ) (N : ℕ) (r : ℝ) :
    (Measure.pi fun _ : Fin N => μ) {ω | ∃ k ≤ N, r ≤ walkSum k ω}
      ≤ 2 * (Measure.pi fun _ : Fin N => μ) {ω | r ≤ walkSum N ω} := by
  classical
  set P : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => μ with hP
  set F : ℕ → Set (Fin N → ℝ) := fun k => {ω | 0 ≤ walkSum N ω - walkSum k ω} with hF
  set G : ℕ → Set (Fin N → ℝ) := fun k => {ω | walkSum N ω - walkSum k ω ≤ 0} with hG
  have hFm : ∀ k, MeasurableSet (F k) := fun k =>
    measurableSet_le measurable_const (measurable_walkSum.sub measurable_walkSum)
  have hPR : ∀ k, MeasurePreserving (flipTail N k) P P := fun k =>
    measurePreserving_flipCoords hμ _
  have hEinv : ∀ k, flipTail N k ⁻¹' firstHit N r k = firstHit N r k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, firstHit, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j hj => ?_⟩
      · rwa [walkSum_flipTail_le (le_refl k) ω] at h1
      · have hj2 := h2 j hj
        rwa [walkSum_flipTail_le hj.le ω] at hj2
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j hj => ?_⟩
      · rw [walkSum_flipTail_le (le_refl k) ω]; exact h1
      · rw [walkSum_flipTail_le hj.le ω]; exact h2 j hj
  have hFGk : ∀ k, flipTail N k ⁻¹' F k = G k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, hF, hG, Set.mem_ofPred_eq, tail_flipTail ω]
    constructor <;> intro h <;> linarith
  have hcover : ∀ k, firstHit N r k ⊆ F k ∪ G k := by
    intro k ω _
    rcases le_total 0 (walkSum N ω - walkSum k ω) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hsub : ∀ k, k ≤ N → firstHit N r k ∩ F k ⊆ {ω : Fin N → ℝ | r ≤ walkSum N ω} := by
    rintro k - ω ⟨⟨h1, -⟩, h2⟩
    simp only [hF, Set.mem_ofPred_eq] at h2
    simp only [Set.mem_ofPred_eq]
    linarith
  have := measure_le_two_mul_of_reflection_family (P := P) (N := N)
    (E := firstHit N r) (F := F) (G := G) (target := {ω : Fin N → ℝ | r ≤ walkSum N ω})
    (R := flipTail N)
    (measurableSet_firstHit N r) hFm (fun j k h => firstHit_disjoint N r h) hPR hEinv hFGk
    hcover hsub
  rwa [biUnion_firstHit N r] at this

end D5.S3.Arith.Lattices.Klartag
