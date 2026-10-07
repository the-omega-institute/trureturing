/- GID: D5/S3/Arith/Lattices/Klartag/State/Padding
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/Klartag/State/Padding
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Symmetric matrix state invariants and padded driving laws. -/

/- Copyright 2026 Lean FRO, LLC. Licensed under Apache-2.0.
   Source: mlgraham/lean-eval-klartag-submission, commit
   270b3358a135f64a6688636660c07772e8db0173.
   Attribution and full license: Library/QuadraticForms/klartag2025packing.md. -/

import D5.S3.Arith.Lattices.Klartag.Gaussian.LevyMaximal

namespace D5.S3.Arith.Lattices.Klartag

open MeasureTheory
open Set
open Finset
open scoped ENNReal NNReal

section Padding

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {N : ℕ}

/-- The accumulated padding `P_k = ∑_{i<k} c_i(ω₁)·η_i`. -/
def padSum (c : ℕ → Ω₁ → ℝ) (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) : ℝ :=
  ∑ i : Fin N, if (i : ℕ) < k then c i ω.1 * ω.2 i else 0

/-- The padded process `S̃_k = (M_k − M₀) + P_k`. -/
def paddedProc (M : ℕ → Ω₁ → ℝ) (M₀ : ℝ) (c : ℕ → Ω₁ → ℝ) (k : ℕ)
    (ω : Ω₁ × (Fin N → ℝ)) : ℝ := (M k ω.1 - M₀) + padSum c k ω

/-- Negate every padding coordinate, leaving the chain alone. -/
def negPad (N : ℕ) : Ω₁ × (Fin N → ℝ) → Ω₁ × (Fin N → ℝ) :=
  Prod.map id (flipTail N 0)

theorem flipTail_zero_apply (N : ℕ) (ω : Fin N → ℝ) (i : Fin N) :
    flipTail N 0 ω i = -(ω i) := by
  simp [flipTail, flipCoords]

omit [MeasurableSpace Ω₁] in
theorem negPad_fst [MeasurableSpace Ω₁] (N : ℕ) (ω : Ω₁ × (Fin N → ℝ)) :
    (negPad N ω).1 = ω.1 := rfl

omit [MeasurableSpace Ω₁] in
theorem negPad_snd [MeasurableSpace Ω₁] (N : ℕ) (ω : Ω₁ × (Fin N → ℝ)) (i : Fin N) :
    (negPad N ω).2 i = -(ω.2 i) := flipTail_zero_apply N ω.2 i

/-- The accumulated padding is odd in the padding coordinates. -/
theorem padSum_negPad (c : ℕ → Ω₁ → ℝ) (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) :
    padSum c k (negPad N ω) = -(padSum c k ω) := by
  have key : padSum c k (negPad N ω)
      = ∑ i : Fin N, -(if (i : ℕ) < k then c i ω.1 * ω.2 i else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (i : ℕ) < k
    · simp [h, negPad_fst, negPad_snd]
    · simp [h]
  rw [key]
  simp [padSum]

/-- `negPad` is measure preserving when the padding law is symmetric. -/
theorem measurePreserving_negPad {P₁ : Measure Ω₁} {ν : Measure ℝ}
    [SFinite P₁] [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν) (N : ℕ) :
    MeasurePreserving (negPad (Ω₁ := Ω₁) N)
      (P₁.prod (Measure.pi fun _ : Fin N => ν)) (P₁.prod (Measure.pi fun _ : Fin N => ν)) :=
  (MeasurePreserving.id P₁).prod (measurePreserving_flipCoords hν _)

theorem measurable_padSum {c : ℕ → Ω₁ → ℝ} (hc : ∀ i, Measurable (c i)) (k : ℕ) :
    Measurable (padSum (N := N) c k) := by
  unfold padSum
  refine Finset.measurable_sum _ (fun i _ => ?_)
  by_cases h : (i : ℕ) < k
  · simp only [h, ite_true]
    exact ((hc i).comp measurable_fst).mul (((measurable_pi_apply i)).comp measurable_snd)
  · simp only [h, ite_false]
    exact measurable_const

/-- `{∃ k ≤ N, M_k ≤ 0}` — the chain reaches the boundary. Depends only on the chain. -/
def hitSet (M : ℕ → Ω₁ → ℝ) (N : ℕ) : Set (Ω₁ × (Fin N → ℝ)) := {ω | ∃ k ≤ N, M k ω.1 ≤ 0}

/-- `{∃ k ≤ N, S̃_k ≤ −M₀}` — the padded process reaches `−M₀`. -/
def levSet (M : ℕ → Ω₁ → ℝ) (M₀ : ℝ) (c : ℕ → Ω₁ → ℝ) (N : ℕ) : Set (Ω₁ × (Fin N → ℝ)) :=
  {ω | ∃ k ≤ N, paddedProc M M₀ c k ω ≤ -M₀}

/-- **`hsym`: the padded process reaches `−M₀` with at least half the probability that the chain
reaches the boundary.**

`P(∃ k ≤ N, M_k ≤ 0) ≤ 2 · P(∃ k ≤ N, S̃_k ≤ −M₀)`.

This is the first of the two factors of 2 in `padded_increment_tail`'s constant 4.  It needs only
that the padding law is symmetric; the chain `M` is completely arbitrary. -/
theorem hsym_of_symmetric {P₁ : Measure Ω₁} {ν : Measure ℝ}
    [IsProbabilityMeasure P₁] [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    (M₀ : ℝ) (N : ℕ) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      ≤ 2 * (P₁.prod (Measure.pi fun _ : Fin N => ν)) (levSet M M₀ c N) := by
  classical
  set P : Measure (Ω₁ × (Fin N → ℝ)) := P₁.prod (Measure.pi fun _ : Fin N => ν) with hP
  set E : ℕ → Set (Ω₁ × (Fin N → ℝ)) :=
    fun k => {ω | M k ω.1 ≤ 0 ∧ ∀ j < k, ¬ (M j ω.1 ≤ 0)} with hE
  set F : ℕ → Set (Ω₁ × (Fin N → ℝ)) := fun k => {ω | padSum c k ω ≤ 0} with hF
  set G : ℕ → Set (Ω₁ × (Fin N → ℝ)) := fun k => {ω | 0 ≤ padSum c k ω} with hG

  have hMm : ∀ k : ℕ, MeasurableSet {ω : Ω₁ × (Fin N → ℝ) | M k ω.1 ≤ 0} := fun k =>
    measurableSet_le ((hM k).comp measurable_fst) measurable_const
  have hEm : ∀ k : ℕ, MeasurableSet (E k) := by
    intro k
    have h2 : MeasurableSet
        (⋂ j ∈ Finset.range k, {ω : Ω₁ × (Fin N → ℝ) | ¬ (M j ω.1 ≤ 0)}) :=
      MeasurableSet.biInter (Finset.range k).countable_toSet (fun j _ => (hMm j).compl)
    have heq : E k = {ω : Ω₁ × (Fin N → ℝ) | M k ω.1 ≤ 0}
        ∩ ⋂ j ∈ Finset.range k, {ω : Ω₁ × (Fin N → ℝ) | ¬ (M j ω.1 ≤ 0)} := by
      ext ω
      simp [hE, Finset.mem_range]
    rw [heq]
    exact (hMm k).inter h2
  have hFm : ∀ k : ℕ, MeasurableSet (F k) := fun k =>
    measurableSet_le (measurable_padSum hc k) measurable_const

  have hdisj : ∀ j k : ℕ, j ≠ k → Disjoint (E j) (E k) := by
    intro j k hjk
    rw [Set.disjoint_left]
    intro ω hj hk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact hk.2 j h hj.1
    · exact hj.2 k h hk.1

  have hPR : ∀ _k : ℕ, MeasurePreserving (negPad (Ω₁ := Ω₁) N) P P := fun _ =>
    measurePreserving_negPad hν N
  have hEinv : ∀ k : ℕ, negPad (Ω₁ := Ω₁) N ⁻¹' E k = E k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, hE, Set.mem_ofPred_eq, negPad_fst]
  have hFGk : ∀ k : ℕ, negPad (Ω₁ := Ω₁) N ⁻¹' F k = G k := by
    intro k
    ext ω
    simp only [Set.mem_preimage, hF, hG, Set.mem_ofPred_eq, padSum_negPad c k ω]
    constructor <;> intro h <;> linarith
  have hcover : ∀ k : ℕ, E k ⊆ F k ∪ G k := by
    intro k ω _
    rcases le_total (padSum c k ω) 0 with h | h
    · exact Or.inl h
    · exact Or.inr h

  have hsub : ∀ k : ℕ, k ≤ N → E k ∩ F k ⊆ levSet M M₀ c N := by
    rintro k hk ω ⟨⟨h1, -⟩, h2⟩
    simp only [hF, Set.mem_ofPred_eq] at h2
    exact ⟨k, hk, by simp only [paddedProc]; linarith⟩
  have hkey := measure_le_two_mul_of_reflection_family (P := P) (N := N)
    (E := E) (F := F) (G := G) (target := levSet M M₀ c N) (R := fun _ => negPad N)
    hEm hFm hdisj hPR hEinv hFGk hcover hsub
  have hunion : (⋃ k ∈ Finset.range (N + 1), E k) = hitSet M N :=
    biUnion_firstIdx (fun (k : ℕ) (ω : Ω₁ × (Fin N → ℝ)) => M k ω.1 ≤ 0) N
  rwa [hunion] at hkey

end Padding

section Levy

variable {Ω : Type*} [MeasurableSpace Ω]

theorem hlevy_of_law {P : Measure Ω} {N : ℕ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {inc : Ω → (Fin N → ℝ)} (hinc : Measurable inc)
    (hlaw : P.map inc = Measure.pi fun _ : Fin N => ν) (r : ℝ) :
    P {ω | ∃ k ≤ N, r ≤ walkSum k (inc ω)} ≤ 2 * P {ω | r ≤ walkSum N (inc ω)} := by
  have hA : MeasurableSet {v : Fin N → ℝ | ∃ k ≤ N, r ≤ walkSum k v} := by
    have : {v : Fin N → ℝ | ∃ k ≤ N, r ≤ walkSum k v}
        = ⋃ k ∈ Finset.range (N + 1), {v : Fin N → ℝ | r ≤ walkSum k v} := by
      ext v
      simp only [Set.mem_iUnion, Finset.mem_range, Set.mem_ofPred_eq, exists_prop]
      constructor
      · rintro ⟨k, hk, hk1⟩; exact ⟨k, Nat.lt_succ_iff.mpr hk, hk1⟩
      · rintro ⟨k, hk, hk1⟩; exact ⟨k, Nat.lt_succ_iff.mp hk, hk1⟩
    rw [this]
    exact MeasurableSet.biUnion (Finset.range (N + 1)).countable_toSet
      (fun k _ => measurableSet_le measurable_const measurable_walkSum)
  have hB : MeasurableSet {v : Fin N → ℝ | r ≤ walkSum N v} :=
    measurableSet_le measurable_const measurable_walkSum
  have e1 : P {ω | ∃ k ≤ N, r ≤ walkSum k (inc ω)}
      = (Measure.pi fun _ : Fin N => ν) {v | ∃ k ≤ N, r ≤ walkSum k v} := by
    rw [← hlaw, Measure.map_apply hinc hA]
    rfl
  have e2 : P {ω | r ≤ walkSum N (inc ω)}
      = (Measure.pi fun _ : Fin N => ν) {v | r ≤ walkSum N v} := by
    rw [← hlaw, Measure.map_apply hinc hB]
    rfl
  rw [e1, e2]
  exact levy_maximal hν N r

end Levy

section Assembled

open ProbabilityTheory

variable {Ω₁ : Type*} [MeasurableSpace Ω₁] {N : ℕ}

theorem padded_tail_assembled {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving (fun x : ℝ => -x) ν ν)
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    {M₀ T q : ℝ} {v : ℝ≥0}
    (hT : 0 < T) (hq : 0 < q) (hM₀ : 0 < M₀) (hv : (v : ℝ) = T * q ^ 2)
    {inc : (Ω₁ × (Fin N → ℝ)) → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ (k : ℕ), k ≤ N → ∀ ω : Ω₁ × (Fin N → ℝ),
      walkSum k (inc ω) = -(paddedProc M M₀ c k ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin N => ν)).map inc
      = Measure.pi fun _ : Fin N => ν)
    (hlaw : (P₁.prod (Measure.pi fun _ : Fin N => ν)).map (fun ω => walkSum N (inc ω))
      = gaussianReal 0 v) :
    (P₁.prod (Measure.pi fun _ : Fin N => ν)) (hitSet M N)
      ≤ ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) := by
  set P : Measure (Ω₁ × (Fin N → ℝ)) := P₁.prod (Measure.pi fun _ : Fin N => ν) with hP
  have hlevset : levSet M M₀ c N = {ω | ∃ k ≤ N, M₀ ≤ walkSum k (inc ω)} := by
    ext ω
    simp only [levSet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, hk, hk2⟩
      exact ⟨k, hk, by rw [hincw k hk ω]; linarith⟩
    · rintro ⟨k, hk, hk2⟩
      refine ⟨k, hk, ?_⟩
      rw [hincw k hk ω] at hk2
      linarith
  have hlevy : P (levSet M M₀ c N)
      ≤ 2 * P ((fun ω => walkSum N (inc ω)) ⁻¹' Set.Ici M₀) := by
    rw [hlevset]
    exact hlevy_of_law hν hincm hincl M₀
  exact padded_increment_tail hT hq hM₀ hv (measurable_walkSum.comp hincm)
    (hsym_of_symmetric hν hM hc M₀ N) hlevy hlaw

end Assembled

section Overshoot

variable {N : ℕ}

end Overshoot

section TerminalLaw

open ProbabilityTheory

/-- The sum over a `Finset` of i.i.d. centred Gaussian coordinates is centred Gaussian. -/
theorem map_finsetSum_gaussian {N : ℕ} {δ : ℝ≥0} (s : Finset (Fin N)) :
    (Measure.pi fun _ : Fin N => gaussianReal 0 δ).map (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
      = gaussianReal 0 (s.card • δ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty, Finset.card_empty, zero_smul, gaussianReal_zero_var]
      rw [Measure.map_const]
      simp
  | insert a s ha ih =>
      have hindep : iIndepFun (fun (i : Fin N) (v : Fin N → ℝ) => v i)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        iIndepFun_pi (X := fun _ : Fin N => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
      have hXY : IndepFun (fun v : Fin N → ℝ => v a) (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) := by
        have h0 := hindep.indepFun_finsetSum_of_notMem (fun i => measurable_pi_apply i) ha
        have hfe : (∑ j ∈ s, fun v : Fin N → ℝ => v j)
            = (fun v : Fin N → ℝ => ∑ i ∈ s, v i) := by
          funext v; simp
        rw [hfe] at h0
        exact h0.symm
      have hX : HasLaw (fun v : Fin N → ℝ => v a) (gaussianReal 0 δ)
          (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin N => gaussianReal 0 δ) a).hasLaw
      have hY : HasLaw (fun v : Fin N → ℝ => ∑ i ∈ s, v i)
          (gaussianReal 0 (s.card • δ)) (Measure.pi fun _ : Fin N => gaussianReal 0 δ) :=
        ⟨(by fun_prop), ih⟩
      have hsum := gaussianReal_add_gaussianReal_of_indepFun hXY hX.map_eq hY.map_eq
      have hfun : (fun v : Fin N → ℝ => ∑ i ∈ insert a s, v i)
          = (fun v : Fin N → ℝ => v a) + (fun v : Fin N → ℝ => ∑ i ∈ s, v i) := by
        funext v
        simp [Finset.sum_insert ha]
      rw [hfun, hsum, Finset.card_insert_of_notMem ha]
      have hvar : (s.card + 1) • δ = δ + s.card • δ := by
        rw [add_smul, one_smul]
        exact add_comm _ _
      rw [hvar]
      norm_num

/-- **The terminal law.**  The walk's final value under i.i.d. `N(0,δ)` increments is `N(0, N·δ)`. -/
theorem map_walkSum_gaussian {N : ℕ} {δ : ℝ≥0} :
    (Measure.pi fun _ : Fin N => gaussianReal 0 δ).map (walkSum N)
      = gaussianReal 0 ((N : ℕ) • δ) := by
  have hfun : walkSum (N := N) N = fun v : Fin N → ℝ => ∑ i ∈ Finset.univ, v i := by
    funext v
    exact walkSum_total v
  rw [hfun, map_finsetSum_gaussian Finset.univ, Finset.card_univ, Fintype.card_fin]

/-- **`hlaw` from `hincl`.**  If the increment vector is i.i.d. `N(0,δ)`, the terminal value is
`N(0, N·δ)` — so `padded_tail_assembled`'s last premise is free. -/
theorem hlaw_of_hincl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ} {δ : ℝ≥0}
    {inc : Ω → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincl : P.map inc = Measure.pi fun _ : Fin N => gaussianReal 0 δ) :
    P.map (fun ω => walkSum N (inc ω)) = gaussianReal 0 ((N : ℕ) • δ) := by
  have hcomp : (fun ω => walkSum N (inc ω)) = (walkSum (N := N) N) ∘ inc := rfl
  rw [hcomp, ← Measure.map_map measurable_walkSum hincm, hincl, map_walkSum_gaussian]

/-- A centred real Gaussian is symmetric. -/
theorem measurePreserving_neg_gaussianReal (δ : ℝ≥0) :
    MeasurePreserving (fun x : ℝ => -x) (gaussianReal 0 δ) (gaussianReal 0 δ) :=
  ⟨by fun_prop, by simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := δ)⟩

theorem padded_tail_of_increments {Ω₁ : Type*} [MeasurableSpace Ω₁] {P₁ : Measure Ω₁}
    [IsProbabilityMeasure P₁] {N : ℕ} {δ : ℝ≥0}
    {M c : ℕ → Ω₁ → ℝ} (hM : ∀ k, Measurable (M k)) (hc : ∀ i, Measurable (c i))
    {M₀ T q : ℝ} (hT : 0 < T) (hq : 0 < q) (hM₀ : 0 < M₀)
    (hv : (((N : ℕ) • δ : ℝ≥0) : ℝ) = T * q ^ 2)
    {inc : (Ω₁ × (Fin N → ℝ)) → (Fin N → ℝ)} (hincm : Measurable inc)
    (hincw : ∀ (k : ℕ), k ≤ N → ∀ ω : Ω₁ × (Fin N → ℝ),
      walkSum k (inc ω) = -(paddedProc M M₀ c k ω))
    (hincl : (P₁.prod (Measure.pi fun _ : Fin N => gaussianReal 0 δ)).map inc
      = Measure.pi fun _ : Fin N => gaussianReal 0 δ) :
    (P₁.prod (Measure.pi fun _ : Fin N => gaussianReal 0 δ)) (hitSet M N)
      ≤ ENNReal.ofReal (4 * Phi (M₀ / (Real.sqrt T * q))) :=
  padded_tail_assembled (measurePreserving_neg_gaussianReal δ) hM hc hT hq hM₀ hv
    hincm hincw hincl (hlaw_of_hincl hincm hincl)

end TerminalLaw

end D5.S3.Arith.Lattices.Klartag
