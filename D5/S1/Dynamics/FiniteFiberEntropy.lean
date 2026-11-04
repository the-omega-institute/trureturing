/- GID: D5/S1/Dynamics/FiniteFiberEntropy
   generality: G
   mirror-B: D5/B/S1/Dynamics/FiniteFiberEntropy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniformly finite fibers of a compact factor map preserve topological entropy. -/

import Mathlib.Data.Set.Card
import Mathlib.Dynamics.TopologicalEntropy.CoverEntropy
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Dynamics.TopologicalEntropy.Semiconj
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
The classical finite-to-one entropy theorem is formalized without a novelty
claim. The missing content, fixed before compilation, is the reverse cover
bound: local length-n covers of each fiber extend to base neighborhoods,
and one representative per realized block code gives at most M^r lifts of
each base cover orbit of length n*r. No pointwise lifting or continuous
choice is assumed. Multiples of n suffice by monotonicity of covering
numbers. Their extra growth is log(M)/n, tending to zero.

The final theorem includes empty spaces and infinite entropy. Finiteness
of fibers is explicit, since Nat.card or Set.ncard alone vanishes on an
infinite set. The helpers below are consumed by the final theorem.
-/

noncomputable section
open Set Function Filter Dynamics ExpGrowth
open scoped Topology Uniformity ENNReal SetRel

namespace D5.S1.Dynamics.FiniteFiberEntropy

variable {X Y : Type*}

private lemma local_block_covers
    [UniformSpace X] [CompactSpace X]
    [UniformSpace Y] [CompactSpace Y] [T2Space Y]
    (π : X → Y) (hπ : Continuous π) (S : X → X) (hS : Continuous S)
    (M : ℕ)
    (hfib : ∀ y, (π ⁻¹' {y}).Finite ∧ (π ⁻¹' {y}).ncard ≤ M)
    (U : SetRel X X) (hU : U ∈ 𝓤 X) [U.IsSymm] (n : ℕ) :
    ∃ V ∈ 𝓤 Y, ∀ y, ∃ s : Finset X,
      s.card ≤ M ∧ IsDynCoverOf S (π ⁻¹' UniformSpace.ball y V) U n s := by
  classical
  let A : Y → Set Y := fun q =>
    {q' | ∀ x ∈ π ⁻¹' {q'},
      ∃ z ∈ π ⁻¹' {q}, (z, x) ∈ dynEntourage S U n}
  have hA (q : Y) : A q ∈ 𝓝 q := by
    apply hπ.isClosedMap.eventually_nhds_fiber q
    intro z hz
    filter_upwards [ball_dynEntourage_mem_nhds hS hU n z] with x hx
    exact ⟨z, hz, hx⟩
  obtain ⟨V, hV, hVA⟩ :=
    lebesgue_number_lemma_nhds isCompact_univ
      (fun q (_ : q ∈ (Set.univ : Set Y)) => hA q)
  refine ⟨V, hV, fun y => ?_⟩
  obtain ⟨q, hq⟩ := hVA y (Set.mem_univ y)
  let s : Finset X := (hfib q).1.toFinset
  refine ⟨s, ?_, ?_⟩
  · change (hfib q).1.toFinset.card ≤ M
    rw [← Set.ncard_eq_toFinset_card (π ⁻¹' {q}) (hfib q).1]
    exact (hfib q).2
  · intro x hx
    obtain ⟨z, hz, hzx⟩ := hq hx x (by simp)
    refine ⟨z, ?_, (dynEntourage S U n).symm hzx⟩
    exact (hfib q).1.mem_toFinset.mpr hz



/- The missing counting step: choose one actual orbit per realized block code.
The centers of a block need not lift the center of the base orbit. The code
construction follows Mathlib's Dynamics.IsDynCoverOf.iterate_le_pow. -/
private theorem block_cover_lift {X Y : Type*} [Nonempty X]
    (S : X → X) (T : Y → Y) (π : X → Y) (hπ : Semiconj π S T)
    (U : SetRel X X) [U.IsSymm] (V : SetRel Y Y) [V.IsSymm]
    (M n r : ℕ) (hn : 0 < n)
    (hloc : ∀ y, ∃ c : Finset X, c.card ≤ M ∧
      IsDynCoverOf S (π ⁻¹' UniformSpace.ball y V) U n c)
    (b : Finset Y) (hb : IsDynCoverOf T univ V (n * r) b) :
    ∃ a : Finset X, IsDynCoverOf S univ (U ○ U) (n * r) a ∧
      a.card ≤ b.card * M ^ r := by
  classical
  choose c hc_card hc using hloc
  let Code := (y : b) × ((k : Fin r) → c (T^[n * k.val] y.val))
  let cell (w : Code) : Set X :=
    {x | ∀ k : Fin r,
      (S^[n * k.val] x, (w.2 k).val) ∈ dynEntourage S U n}
  let representative (w : Code) : X :=
    if h : (cell w).Nonempty then h.choose else Classical.arbitrary X
  have hrep (w : Code) (x : X) (hx : x ∈ cell w) : representative w ∈ cell w := by
    have h : (cell w).Nonempty := ⟨x, hx⟩
    simpa only [representative, dite_eq_left h] using h.choose_spec
  let a : Finset X := Finset.univ.image representative
  refine ⟨a, ?_, ?_⟩
  · intro x _
    obtain ⟨y, hy, hxy⟩ := hb (mem_univ (π x))
    have hblock (k : Fin r) :
        S^[n * k.val] x ∈ π ⁻¹' UniformSpace.ball (T^[n * k.val] y) V := by
      change (T^[n * k.val] y, π (S^[n * k.val] x)) ∈ V
      rw [(hπ.iterate_right (n * k.val)) x]
      exact V.symm ((mem_dynEntourage.mp hxy) (n * k.val) (Nat.mul_lt_mul_of_pos_left k.isLt hn))
    have hchoose (k : Fin r) : ∃ z : c (T^[n * k.val] y),
        (S^[n * k.val] x, z.val) ∈ dynEntourage S U n := by
      obtain ⟨z, hz, hxz⟩ := hc (T^[n * k.val] y) (hblock k)
      exact ⟨⟨z, hz⟩, hxz⟩
    choose z hz using hchoose
    let w : Code := ⟨⟨y, hy⟩, z⟩
    have hx : x ∈ cell w := hz
    have hycell := hrep w x hx
    refine ⟨representative w, Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩, ?_⟩
    apply mem_dynEntourage.mpr
    intro i hi
    let k : Fin r := ⟨i / n, Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hi)⟩
    have hix := mem_dynEntourage.mp (hx k) (i % n) (Nat.mod_lt i hn)
    have hiy := mem_dynEntourage.mp (hycell k) (i % n) (Nat.mod_lt i hn)
    have he : i % n + n * k.val = i := Nat.mod_add_div i n
    rw [← iterate_add_apply, he] at hix hiy
    exact ⟨_, hix, U.symm hiy⟩
  · refine Finset.card_image_le.trans ?_
    simp only [Finset.card_univ, Code, Fintype.card_sigma, Fintype.card_pi,
      Fintype.card_coe]
    calc
      _ ≤ ∑ _y : b, M ^ r := Finset.sum_le_sum fun y _ => by
        calc
          _ ≤ ∏ _k : Fin r, M := Finset.prod_le_prod fun k _ => hc_card _
          _ = _ := by simp
      _ = b.card * M ^ r := by simp



/-- Arbitrarily long blocks with a uniformly bounded branching cost do not
increase covering entropy.  No nonemptiness or finiteness-of-entropy
assumption is needed; `EReal` handles all endpoint cases. -/
private lemma entropy_le_of_block_bound
    {X Y : Type*} [UniformSpace X] [UniformSpace Y]
    (S : X → X) (T : Y → Y) (U : SetRel X X)
    (M : ℕ) (hM : 0 < M)
    (hbound : ∀ n : ℕ, 0 < n → ∃ V : SetRel Y Y, V ∈ 𝓤 Y ∧
      ∀ r : ℕ, coverMincard S univ U (n * r) ≤
        (M : ℕ∞) ^ r * coverMincard T univ V (n * r)) :
    coverEntropyEntourage S univ U ≤ coverEntropy T univ := by
  have hlog_bot : ENNReal.log (M : ℝ≥0∞) ≠ ⊥ := by
    intro h
    have hzero : (M : ℝ≥0∞) = 0 := ENNReal.log_eq_bot_iff.mp h
    exact hM.ne' (by exact_mod_cast hzero)
  have hlog_top : ENNReal.log (M : ℝ≥0∞) ≠ ⊤ := by simp
  have hmonoS : Monotone (fun k => (coverMincard S univ U k).toENNReal) :=
    fun _ _ h => ENat.toENNReal_mono (coverMincard_monotone_time S univ U h)
  have happrox (n : ℕ) (hn : 0 < n) :
      coverEntropyEntourage S univ U ≤
        ENNReal.log (M : ℝ≥0∞) / n + coverEntropy T univ := by
    obtain ⟨V, hV, hb⟩ := hbound n hn
    have hmonoT : Monotone (fun k => (coverMincard T univ V k).toENNReal) :=
      fun _ _ h => ENat.toENNReal_mono (coverMincard_monotone_time T univ V h)
    have hcost : expGrowthSup (fun r : ℕ => (M : ℝ≥0∞) ^ r) =
        ENNReal.log (M : ℝ≥0∞) := expGrowthSup_pow
    have hproduct :
        expGrowthSup (fun r => (coverMincard S univ U (n * r)).toENNReal) ≤
        ENNReal.log (M : ℝ≥0∞) +
          expGrowthSup (fun r => (coverMincard T univ V (n * r)).toENNReal) := by
      calc
        _ ≤ expGrowthSup
            ((fun r : ℕ => (M : ℝ≥0∞) ^ r) *
              (fun r : ℕ => (coverMincard T univ V (n * r)).toENNReal)) := by
          apply expGrowthSup_monotone
          intro r
          simpa only [Pi.mul_apply, ENat.toENNReal_mul, ENat.toENNReal_pow,
            ENat.toENNReal_coe] using ENat.toENNReal_mono (hb r)
        _ ≤ _ := by
          have hp := expGrowthSup_mul_le
            (u := fun r : ℕ => (M : ℝ≥0∞) ^ r)
            (v := fun r : ℕ => (coverMincard T univ V (n * r)).toENNReal)
            (Or.inl (hcost.symm ▸ hlog_bot)) (Or.inl (hcost.symm ▸ hlog_top))
          simpa only [hcost] using hp
    have hs := hmonoS.expGrowthSup_comp_mul hn.ne'
    rw [mul_comm, ← EReal.div_eq_iff (EReal.natCast_ne_bot n)
      (EReal.natCast_ne_top n) (Nat.cast_ne_zero.2 hn.ne')] at hs
    change expGrowthSup (fun k => (coverMincard S univ U k).toENNReal) ≤ _
    rw [← hs]
    calc
      _ ≤ (ENNReal.log (M : ℝ≥0∞) +
          expGrowthSup (fun r => (coverMincard T univ V (n * r)).toENNReal)) / n :=
        EReal.monotone_div_right_of_nonneg n.cast_nonneg' hproduct
      _ = ENNReal.log (M : ℝ≥0∞) / n +
          coverEntropyEntourage T univ V := by
        rw [hmonoT.expGrowthSup_comp_mul hn.ne',
          EReal.add_div_of_nonneg_right n.cast_nonneg']
        congr 1
        apply (EReal.div_eq_iff (EReal.natCast_ne_bot n)
          (EReal.natCast_ne_top n) (Nat.cast_ne_zero.2 hn.ne')).2
        exact mul_comm _ _
      _ ≤ _ := add_le_add_right (coverEntropyEntourage_le_coverEntropy T univ hV) _
  have hzero : Tendsto (fun n : ℕ => ENNReal.log (M : ℝ≥0∞) / n)
      atTop (𝓝 (0 : EReal)) :=
    EReal.tendsto_const_div_atTop_nhds_zero_nat hlog_bot hlog_top
  have hlim : Tendsto
      (fun n : ℕ => ENNReal.log (M : ℝ≥0∞) / n + coverEntropy T univ)
      atTop (𝓝 (coverEntropy T univ)) := by
    simpa only [Function.comp_def, zero_add] using
      (EReal.continuousAt_add (p := (0, coverEntropy T univ))
        (Or.inl EReal.zero_ne_top) (Or.inl EReal.zero_ne_bot)).tendsto.comp
          (hzero.prodMk_nhds tendsto_const_nhds)
  exact ge_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact happrox n (by omega))

/- Final assembly; the local and counting lemmas precede this text. -/

/-- A continuous surjective semiconjugacy with a uniform finite bound on
its fibers preserves topological entropy. The source dynamics is continuous;
no continuity hypothesis on the factor dynamics is needed. -/
theorem finite_fiber_entropy
    {X Y : Type*} [UniformSpace X] [CompactSpace X]
    [UniformSpace Y] [CompactSpace Y] [T2Space Y]
    (S : X → X) (T : Y → Y) (π : X → Y)
    (hS : Continuous S) (hπ : Continuous π)
    (honto : Surjective π) (hsem : Semiconj π S T)
    (M : ℕ)
    (hfib : ∀ y, (π ⁻¹' {y}).Finite ∧ (π ⁻¹' {y}).ncard ≤ M) :
    coverEntropy S univ = coverEntropy T univ := by
  classical
  rcases isEmpty_or_nonempty X with hX | hX
  · letI := hX
    letI : IsEmpty Y := ⟨fun y => by
      obtain ⟨x, _⟩ := honto y
      exact isEmptyElim x⟩
    simp only [Set.eq_empty_of_isEmpty, coverEntropy_empty]
  letI := hX
  have hM : 0 < M := by
    let x : X := Classical.arbitrary X
    exact ((Set.ncard_pos (hfib (π x)).1).mpr ⟨x, by simp⟩).trans_le (hfib (π x)).2
  apply le_antisymm
  · unfold coverEntropy
    refine iSup₂_le fun U hU => ?_
    obtain ⟨W, hW, hWsymm, hWW⟩ := comp_symm_mem_uniformity_sets hU
    letI := hWsymm
    apply (coverEntropyEntourage_antitone S univ hWW).trans
    apply entropy_le_of_block_bound S T (W ○ W) M hM
    intro n hn
    obtain ⟨V₀, hV₀, hlocal₀⟩ := local_block_covers π hπ S hS M hfib W hW n
    obtain ⟨V, hV, hVsymm, hVV₀⟩ := symm_of_uniformity hV₀
    letI := hVsymm
    have hlocal : ∀ y, ∃ c : Finset X, c.card ≤ M ∧
        IsDynCoverOf S (π ⁻¹' UniformSpace.ball y V) W n c := by
      intro y
      obtain ⟨c, hc, hcover⟩ := hlocal₀ y
      exact ⟨c, hc, fun _ hx => hcover (hVV₀ hx)⟩
    refine ⟨V, hV, fun r => ?_⟩
    have hfinite := coverMincard_finite_of_isCompact_invariant
      (T := T) isCompact_univ (mapsTo_univ T univ) hV (n * r)
    obtain ⟨b, hb, hbcard⟩ := (coverMincard_finite_iff T univ V (n * r)).mp hfinite
    obtain ⟨a, ha, hacard⟩ := block_cover_lift S T π hsem W V M n r hn hlocal b hb
    calc
      _ ≤ (a.card : ℕ∞) := ha.coverMincard_le_card
      _ ≤ (b.card * M ^ r : ℕ) := by exact_mod_cast hacard
      _ = (M : ℕ∞) ^ r * coverMincard T univ V (n * r) := by
        rw [Nat.cast_mul, Nat.cast_pow, hbcard, mul_comm]
  · have hfactor := coverEntropy_image_le_of_uniformContinuous hsem
      (CompactSpace.uniformContinuous_of_continuous hπ) (Set.univ : Set X)
    simpa only [Set.image_univ, Set.range_eq_univ.mpr honto] using hfactor

#print axioms finite_fiber_entropy

end D5.S1.Dynamics.FiniteFiberEntropy
