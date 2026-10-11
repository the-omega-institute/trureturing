/- GID: D5/S3/Analytic/Convexity/LexicographicFlagRealization
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/LexicographicFlagRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite feasibility admits an orthonormal lexicographic list bounded by input rank. -/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

noncomputable section

open scoped InnerProductSpace
open Module Set Filter
open scoped Topology

namespace D5.S3.Analytic.Convexity.LexicographicFlagRealization

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {I : Type*}

/-- Every finite set of rows has one strictly positive input. -/
def FiniteFeasible (a : I → V) : Prop :=
  ∀ F : Finset I, ∃ x : V, ∀ i ∈ F, 0 < ⟪a i, x⟫_ℝ

/-- Every row has a positive first nonzero entry in the same ordered list. -/
def LexWitness (a : I → V) {r : ℕ} (v : Fin r → V) : Prop :=
  ∀ i, ∃ k, 0 < ⟪a i, v k⟫_ℝ ∧ ∀ j < k, ⟪a i, v j⟫_ℝ = 0

/-- The vector polynomial with the supplied positive-degree coefficients. -/
def curve {r : ℕ} (v : Fin r → V) (t : ℝ) : V :=
  ∑ k, t ^ (k.val + 1) • v k

private theorem curve_zero {r : ℕ} (v : Fin r → V) : curve v 0 = 0 := by
  simp [curve]

private theorem curve_tendsto {r : ℕ} (v : Fin r → V) :
    Tendsto (curve v) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (curve v) := by
    unfold curve
    exact continuous_finsetSum _ (fun i _ => (continuous_id.pow _).smul continuous_const)
  simpa only [curve_zero] using hc.tendsto 0

private theorem curve_cons {r : ℕ} (v : Fin (r + 1) → V) (t : ℝ) :
    curve v t = t • (v 0 + curve (fun k : Fin r => v k.succ) t) := by
  simp only [curve, Fin.sum_univ_succ, Fin.val_zero, zero_add, pow_one,
    Fin.val_succ, smul_add, Finset.smul_sum, smul_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ, mul_comm]

private theorem row_lex_cons (x : V) {r : ℕ} (v : Fin (r + 1) → V) :
    (∃ k, 0 < ⟪x, v k⟫_ℝ ∧ ∀ j < k, ⟪x, v j⟫_ℝ = 0) ↔
      0 < ⟪x, v 0⟫_ℝ ∨ (⟪x, v 0⟫_ℝ = 0 ∧
        ∃ k : Fin r, 0 < ⟪x, v k.succ⟫_ℝ ∧ ∀ j < k, ⟪x, v j.succ⟫_ℝ = 0) := by
  constructor
  · rintro ⟨k, hk, hz⟩
    refine Fin.cases (fun hk _ => Or.inl hk) (fun k hk hz => ?_) k hk hz
    exact Or.inr ⟨hz 0 (Fin.succ_pos k), k, hk,
      fun j hj => hz j.succ (Fin.succ_lt_succ_iff.mpr hj)⟩
  · rintro (h | ⟨hz, k, hk, hj⟩)
    · exact ⟨0, h, fun j h => (Fin.not_lt_zero j h).elim⟩
    · refine ⟨k.succ, hk, ?_⟩
      intro j hjk
      exact Fin.cases (fun _ => hz) (fun j h => hj j (Fin.succ_lt_succ_iff.mp h)) j hjk

private theorem row_lex_iff_eventually (x : V) {r : ℕ} (v : Fin r → V) :
    (∃ k, 0 < ⟪x, v k⟫_ℝ ∧ ∀ j < k, ⟪x, v j⟫_ℝ = 0) ↔
      ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < ⟪x, curve v t⟫_ℝ := by
  induction r with
  | zero =>
    constructor
    · rintro ⟨k, _⟩
      exact Fin.elim0 k
    · intro h
      obtain ⟨t, ht⟩ := h.exists
      simpa [curve] using ht
  | succ r ih =>
    rw [row_lex_cons]
    have ht : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    have hlim : Tendsto (fun t : ℝ => ⟪x, v 0 + curve (fun k : Fin r => v k.succ) t⟫_ℝ)
        (𝓝[>] 0) (𝓝 ⟪x, v 0⟫_ℝ) := by
      simpa using (tendsto_const_nhds.inner
        (tendsto_const_nhds.add (curve_tendsto (fun k : Fin r => v k.succ)))).mono_left
          nhdsWithin_le_nhds
    constructor
    · rintro (hpos | ⟨hz, htail⟩)
      · filter_upwards [ht, hlim.eventually (lt_mem_nhds hpos)] with t ht hp
        rw [curve_cons, inner_smul_right]
        exact mul_pos ht hp
      · filter_upwards [ht, (ih _).mp htail] with t ht hp
        rw [curve_cons, inner_smul_right, inner_add_right, hz, zero_add]
        exact mul_pos ht hp
    · intro hpos
      have hbase : ∀ᶠ t in 𝓝[>] (0 : ℝ),
          0 < ⟪x, v 0 + curve (fun k : Fin r => v k.succ) t⟫_ℝ := by
        filter_upwards [ht, hpos] with t ht hp
        rw [curve_cons, inner_smul_right] at hp
        exact (mul_pos_iff_of_pos_left ht).mp hp
      have hnonneg : 0 ≤ ⟪x, v 0⟫_ℝ := ge_of_tendsto hlim (hbase.mono fun _ h => h.le)
      rcases lt_or_eq_of_le hnonneg with hlt | heq
      · exact Or.inl hlt
      · refine Or.inr ⟨heq.symm, (ih _).mpr ?_⟩
        simpa only [inner_add_right, ← heq, zero_add] using hbase

/-- Each constraint has its own positive right-neighborhood of feasibility. -/
def EventuallyFeasible (a : I → V) {r : ℕ} (v : Fin r → V) : Prop :=
  ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∀ t, 0 < t → t < ε → 0 < ⟪a i, curve v t⟫_ℝ

private theorem lex_iff_eventually (a : I → V) {r : ℕ} (v : Fin r → V) :
    LexWitness a v ↔ EventuallyFeasible a v := by
  unfold LexWitness EventuallyFeasible
  apply forall_congr'
  intro i
  rw [row_lex_iff_eventually]
  exact mem_nhdsGT_iff_exists_Ioo_subset.trans (by simp [Set.subset_def])

private theorem lex_finite_feasible (a : I → V) {r : ℕ} (v : Fin r → V)
    (h : LexWitness a v) : FiniteFeasible a := by
  intro F
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i ∈ F, 0 < ⟪a i, curve v t⟫_ℝ :=
    (eventually_all_finset F).mpr fun i _ => (row_lex_iff_eventually (a i) v).mp (h i)
  obtain ⟨t, ht⟩ := he.exists
  exact ⟨curve v t, ht⟩

variable [FiniteDimensional ℝ V]

private theorem common_weak_unit (a : I → V) [Nonempty I] (h : FiniteFeasible a) :
    ∃ u : V, u ∈ Submodule.span ℝ (Set.range a) ∧ ‖u‖ = 1 ∧
      ∀ i, 0 ≤ ⟪a i, u⟫_ℝ := by
  classical
  let W := Submodule.span ℝ (Set.range a)
  let b : I → W := fun i => ⟨a i, Submodule.subset_span (Set.mem_range_self i)⟩
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have hfinite (F : Finset I) :
      (Metric.sphere (0 : W) 1 ∩ ⋂ i ∈ F, {u : W | 0 ≤ ⟪b i, u⟫_ℝ}).Nonempty := by
    obtain ⟨x, hx⟩ := h (insert i₀ F)
    let y : W := W.orthogonalProjectionOnto x
    have heval (i : I) : ⟪b i, y⟫_ℝ = ⟪a i, x⟫_ℝ :=
      W.inner_orthogonalProjectionOnto_eq_of_mem_left (b i) x
    have hy : y ≠ 0 := by
      intro hy
      have hp := hx i₀ (Finset.mem_insert_self _ _)
      rw [← heval i₀, hy, inner_zero_right] at hp
      exact lt_irrefl _ hp
    refine ⟨NormedSpace.normalize y, ?_, ?_⟩
    · simpa only [Metric.mem_sphere, dist_zero_right] using NormedSpace.norm_normalize hy
    · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
      intro i hi
      rw [NormedSpace.normalize, inner_smul_right, heval]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg y))
        (le_of_lt (hx i (Finset.mem_insert_of_mem hi)))
  obtain ⟨u, hu, hi⟩ := (isCompact_sphere (0 : W) 1).inter_iInter_nonempty
    (fun i => {u : W | 0 ≤ ⟪b i, u⟫_ℝ})
    (fun i => isClosed_le continuous_const (continuous_const.inner continuous_id)) hfinite
  refine ⟨u, u.property, ?_, ?_⟩
  · simpa using hu
  · intro i
    exact Set.mem_iInter.mp hi i

/-- A common orthonormal list in the row span settles every row, with length at most its rank. -/
theorem orthonormal_realization (a : I → V) (h : FiniteFeasible a) :
    ∃ (r : ℕ) (v : Fin r → V), r ≤ finrank ℝ (Submodule.span ℝ (Set.range a)) ∧
      Orthonormal ℝ v ∧ (∀ k, v k ∈ Submodule.span ℝ (Set.range a)) ∧ LexWitness a v := by
  classical
  suffices aux : ∀ n, ∀ (J : Type _) (b : J → V),
      finrank ℝ (Submodule.span ℝ (Set.range b)) = n → FiniteFeasible b →
      ∃ (r : ℕ) (v : Fin r → V), r ≤ n ∧ Orthonormal ℝ v ∧
        (∀ k, v k ∈ Submodule.span ℝ (Set.range b)) ∧ LexWitness b v by
    exact aux _ I a rfl h
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J b hn hb
    cases isEmpty_or_nonempty J with
    | inl hempty =>
      exact ⟨0, Fin.elim0, Nat.zero_le _, Orthonormal.of_isEmpty _,
        fun k => Fin.elim0 k, fun j => isEmptyElim j⟩
    | inr hnonempty =>
      obtain ⟨u, huW, hu, hupos⟩ := common_weak_unit b hb
      let K := {j : J // ⟪b j, u⟫_ℝ = 0}
      let c : K → V := fun j => b j.val
      let W := Submodule.span ℝ (Set.range b)
      let W' := Submodule.span ℝ (Set.range c)
      have hle : W' ≤ W := Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span (Set.mem_range_self j.val))
      have horth : W' ≤ (ℝ ∙ u)ᗮ := Submodule.span_le.mpr (by
        rintro _ ⟨j, rfl⟩
        exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr j.property)
      have hnot : u ∉ W' := by
        intro hu'
        have hz := Submodule.mem_orthogonal_singleton_iff_inner_right.mp (horth hu')
        have : u = 0 := inner_self_eq_zero.mp hz
        simpa [this] using hu
      have hrank : finrank ℝ W' < n := by
        rw [← hn]
        exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle (by
          intro heq
          exact hnot (heq.symm ▸ huW)))
      have hc : FiniteFeasible c := by
        intro F
        obtain ⟨x, hx⟩ := hb (F.image Subtype.val)
        exact ⟨x, fun j hj => hx j.val (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
      obtain ⟨s, w, hs, hw, hwW, hwlex⟩ := ih _ hrank K c rfl hc
      refine ⟨s + 1, Matrix.vecCons u w, by omega, ?_, ?_, ?_⟩
      · apply orthonormal_vecCons_iff.mpr
        exact ⟨hu, fun k =>
          Submodule.mem_orthogonal_singleton_iff_inner_right.mp (horth (hwW k)), hw⟩
      · intro k
        exact Fin.cases huW (fun j => hle (hwW j)) k
      · intro j
        by_cases hj : ⟪b j, u⟫_ℝ = 0
        · obtain ⟨k, hk, hkzero⟩ := hwlex ⟨j, hj⟩
          refine ⟨k.succ, hk, ?_⟩
          intro l hl
          refine Fin.cases ?_ (fun q hq => ?_) l hl
          · intro _
            exact hj
          · exact hkzero q (Fin.succ_lt_succ_iff.mp hq)
        · refine ⟨0, lt_of_le_of_ne (hupos j) (Ne.symm hj), ?_⟩
          intro k hk
          exact (Fin.not_lt_zero k hk).elim

/-- Finite feasibility, a lexicographic list, and a constraintwise feasible curve are equivalent.
The list furnished from finite feasibility is orthonormal in the row span. -/
theorem realization_equivalences (a : I → V) :
    (FiniteFeasible a ↔ ∃ (r : ℕ) (v : Fin r → V), LexWitness a v) ∧
    ((∃ (r : ℕ) (v : Fin r → V), LexWitness a v) ↔
      ∃ (r : ℕ) (v : Fin r → V), EventuallyFeasible a v) ∧
    (FiniteFeasible a → ∃ (r : ℕ) (v : Fin r → V),
      r ≤ finrank ℝ (Submodule.span ℝ (Set.range a)) ∧
      finrank ℝ (Submodule.span ℝ (Set.range a)) ≤ finrank ℝ V ∧
      Orthonormal ℝ v ∧ (∀ k, v k ∈ Submodule.span ℝ (Set.range a)) ∧
      LexWitness a v ∧ EventuallyFeasible a v ∧
      Tendsto (curve v) (𝓝 0) (𝓝 0) ∧ (Nonempty I → 1 ≤ r)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    obtain ⟨r, v, _, _, _, hv⟩ := orthonormal_realization a h
    exact ⟨r, v, hv⟩
  · rintro ⟨r, v, h⟩
    exact lex_finite_feasible a v h
  · rintro ⟨r, v, h⟩
    exact ⟨r, v, (lex_iff_eventually a v).mp h⟩
  · rintro ⟨r, v, h⟩
    exact ⟨r, v, (lex_iff_eventually a v).mpr h⟩
  · intro h
    obtain ⟨r, v, hr, hv, hW, hlex⟩ := orthonormal_realization a h
    refine ⟨r, v, hr, Submodule.finrank_le _, hv, hW, hlex,
      (lex_iff_eventually a v).mp hlex, curve_tendsto v, ?_⟩
    rintro ⟨i⟩
    obtain ⟨k, _, _⟩ := hlex i
    exact Nat.succ_le_of_lt (lt_of_le_of_lt (Nat.zero_le k.val) k.isLt)

end D5.S3.Analytic.Convexity.LexicographicFlagRealization
