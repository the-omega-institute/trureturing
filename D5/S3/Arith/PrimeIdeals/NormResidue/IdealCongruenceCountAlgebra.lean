/- GID: D5/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra
   generality: G
   mirror-B: D5/B/S3/Arith/PrimeIdeals/NormResidue/IdealCongruenceCountAlgebra
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Intersecting a bounded Lipschitz-frontier region with a coordinate orthant preserves a Lipschitz frontier cover. -/
module

public import D5.S3.Arith.Lattices.Counting.IdealCongruenceCountRealScale

@[expose] public section

noncomputable section

namespace Chebotarev

open NumberField Set Submodule

open scoped NNReal nonZeroDivisors Pointwise

/-- **Bounded coordinate-hyperplane pieces are Lipschitz cube-coverable.** For a coordinate `j` and
radius `R ≥ 0`, the slab `{x : x j = 0, ∀ i, |x i| ≤ R}` of the hyperplane `{x j = 0}` in `ι → ℝ`
is contained in a single Lipschitz image of the unit cube `[0,1]^(card ι - 1)` (constant `2R`):
parametrise the `card ι - 1` free coordinates affinely by `c ↦ 2R·c - R` (a bijection
`Fin (card ι - 1) ≃ {i // i ≠ j}` supplies the indices) and set coordinate `j` to `0`. This is the
boundary contribution of an orthant cut, feeding the workhorse's frontier-cover hypothesis. -/
private theorem exists_lipschitz_cube_cover_hyperplane_slab {ι : Type*} [Fintype ι]
    (j : ι) {R : ℝ} (hR : 0 ≤ R) :
    ∃ (M : ℝ≥0) (φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      LipschitzWith M φ ∧
        {x : ι → ℝ | x j = 0 ∧ ∀ i, |x i| ≤ R} ⊆ φ '' Set.Icc 0 1 := by
  classical
  have hcard : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]; simp
  set σ : Fin (Fintype.card ι - 1) ≃ {i : ι // i ≠ j} :=
    (Fintype.equivFinOfCardEq hcard).symm
  set φ : (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun c i ↦ if h : i = j then 0 else (2 * R) * c (σ.symm ⟨i, h⟩) - R with hφ
  refine ⟨(2 * R).toNNReal, φ, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun c c' ↦ ?_
    rw [dist_pi_le_iff (by positivity)]
    intro i
    by_cases hij : i = j
    · simp only [hφ, dif_pos hij, dist_self]; positivity
    · simp only [hφ, dif_neg hij]
      have hreorg : (2 * R) * c (σ.symm ⟨i, hij⟩) - R - ((2 * R) * c' (σ.symm ⟨i, hij⟩) - R)
          = (2 * R) * (c (σ.symm ⟨i, hij⟩) - c' (σ.symm ⟨i, hij⟩)) := by ring
      rw [Real.dist_eq, hreorg, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * R),
        Real.coe_toNNReal _ (by positivity)]
      gcongr
      rw [← Real.dist_eq]
      exact dist_le_pi_dist c c' (σ.symm ⟨i, hij⟩)
  · rintro x ⟨hxj, hxbd⟩
    rcases eq_or_lt_of_le hR with hR0 | hR0
    · have hx0 : x = 0 := by
        ext i; have := hxbd i; rw [← hR0] at this; exact abs_nonpos_iff.mp this
      refine ⟨0, ⟨le_refl _, zero_le_one⟩, ?_⟩
      ext i; simp only [hφ]
      by_cases hij : i = j
      · rw [dif_pos hij, hx0]; rfl
      · rw [dif_neg hij, hx0]; simp [← hR0]
    · refine ⟨fun k ↦ (x (σ k) + R) / (2 * R), ⟨?_, ?_⟩, ?_⟩
      · intro k; simp only [Pi.zero_apply]
        rw [le_div_iff₀ (by positivity)]; have := (abs_le.mp (hxbd (σ k))).1; linarith
      · intro k; simp only [Pi.one_apply]
        rw [div_le_one (by positivity)]; have := (abs_le.mp (hxbd (σ k))).2; linarith
      · ext i
        by_cases hij : i = j
        · rw [hφ]; simp only; rw [dif_pos hij, hij]; exact hxj.symm
        · rw [hφ]; simp only [dif_neg hij, Equiv.apply_symm_apply]; field_simp; ring

/-- **Lipschitz frontier cover of an orthant-cut region.** If `D₀` is bounded with a Lipschitz cube
cover of its frontier, then `D₀ ∩ orthant` (orthant cutting the coordinates `g k`) also has a
Lipschitz cube-covered frontier: `frontier (D₀ ∩ O) ⊆ frontier D₀ ∪ (closure D₀ ∩ frontier O)`
(`frontier_inter_subset`), the orthant boundary lands in finitely many coordinate hyperplanes,
and each bounded hyperplane slice is cube-covered by
`exists_lipschitz_cube_cover_hyperplane_slab`. -/
theorem exists_frontier_cover_inter_orthant {ι : Type*} [Fintype ι] {κ : Type*} [Finite κ]
    (g : κ → ι) (s : Finset κ) (D₀ : Set (ι → ℝ)) (hbdd : Bornology.IsBounded D₀)
    (hcov : ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧ frontier D₀ ⊆ ⋃ j, φ j '' Set.Icc 0 1) :
    ∃ (m : ℕ) (M : ℝ≥0) (φ : Fin m → (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ)),
      (∀ j, LipschitzWith M (φ j)) ∧
        frontier (D₀ ∩ {y : ι → ℝ | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))})
          ⊆ ⋃ j, φ j '' Set.Icc 0 1 := by
  classical
  obtain ⟨R, hR0, hRbd⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ closure D₀, ∀ i, |x i| ≤ R := by
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd.closure
    refine ⟨max R 0, le_max_right _ _, fun x hx i ↦ ?_⟩
    calc |x i| = ‖x i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖x‖ := norm_le_pi_norm x i
      _ ≤ max R 0 := le_max_of_le_left (hR x hx)
  set O : Set (ι → ℝ) := {y | (∀ k ∈ s, y (g k) ≤ 0) ∧ (∀ k ∉ s, 0 ≤ y (g k))}
  have hfront : frontier O ⊆ ⋃ k : κ, {y : ι → ℝ | y (g k) = 0} := by
    set Os : Set (ι → ℝ) :=
      {y | (∀ k ∈ s, y (g k) < 0) ∧ (∀ k ∉ s, 0 < y (g k))} with hOs
    have hOclosed : IsClosed O := by
      simp only [O, Set.setOf_and, Set.setOf_forall]
      exact (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦
          isClosed_le (continuous_apply (g k)) continuous_const).inter
        (isClosed_iInter fun k ↦ isClosed_iInter fun _ ↦
          isClosed_le continuous_const (continuous_apply (g k)))
    have hOsopen : IsOpen Os := by
      simp only [hOs, Set.setOf_and, Set.setOf_forall]
      exact (isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun _ ↦
          isOpen_lt (continuous_apply (g k)) continuous_const).inter
        (isOpen_iInter_of_finite fun k ↦ isOpen_iInter_of_finite fun _ ↦
          isOpen_lt continuous_const (continuous_apply (g k)))
    have hOsO : Os ⊆ O :=
      fun y hy ↦ ⟨fun k hk ↦ (hy.1 k hk).le, fun k hk ↦ (hy.2 k hk).le⟩
    intro y hy
    have hyO : y ∈ O := hOclosed.closure_eq ▸ frontier_subset_closure hy
    have hyni : y ∉ interior O := by
      rw [frontier_eq_closure_inter_closure] at hy
      rw [interior_eq_compl_closure_compl]; exact fun hh ↦ hh hy.2
    by_contra hcon
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, not_exists] at hcon
    exact hyni (mem_interior.mpr ⟨Os, hOsO, hOsopen,
      ⟨fun k hk ↦ lt_of_le_of_ne (hyO.1 k hk) (hcon k),
       fun k hk ↦ lt_of_le_of_ne (hyO.2 k hk) (Ne.symm (hcon k))⟩⟩)
  have hsub : frontier (D₀ ∩ O)
      ⊆ frontier D₀ ∪ ⋃ k : κ, {x : ι → ℝ | x (g k) = 0 ∧ ∀ i, |x i| ≤ R} := by
    refine (frontier_inter_subset D₀ O).trans (Set.union_subset ?_ ?_)
    · exact Set.inter_subset_left.trans Set.subset_union_left
    · refine fun x hx ↦ Or.inr ?_
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp (hfront hx.2)
      exact Set.mem_iUnion.mpr ⟨k, hxk, hRbd x hx.1⟩
  letI : Fintype κ := Fintype.ofFinite κ
  choose Mk φk hLk hck using
    (fun k : κ ↦ exists_lipschitz_cube_cover_hyperplane_slab (g k) hR0)
  obtain ⟨m, M, φ, hL, hc⟩ := hcov
  let e : κ ≃ Fin (Fintype.card κ) := Fintype.equivFin κ
  let Ψ : Fin (m + Fintype.card κ) →
      (Fin (Fintype.card ι - 1) → ℝ) → (ι → ℝ) :=
    fun j ↦ Sum.elim φ (fun k ↦ φk (e.symm k)) (finSumFinEquiv.symm j)
  refine ⟨m + Fintype.card κ, max M (Finset.univ.sup Mk), Ψ, ?_, hsub.trans ?_⟩
  · intro j
    change LipschitzWith (max M (Finset.univ.sup Mk))
      (Sum.elim φ (fun k ↦ φk (e.symm k)) (finSumFinEquiv.symm j))
    rcases h : finSumFinEquiv.symm j with k | k
    · rw [Sum.elim_inl]
      exact (hL k).weaken (le_max_left _ _)
    · rw [Sum.elim_inr]
      exact (hLk (e.symm k)).weaken
        (le_trans (Finset.le_sup (Finset.mem_univ _)) (le_max_right _ _))
  · refine Set.union_subset ?_ ?_
    · refine hc.trans (Set.iUnion_subset fun j ↦ ?_)
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inl j)) ?_
      simp only [Ψ, Equiv.symm_apply_apply, Sum.elim_inl, subset_rfl]
    · refine Set.iUnion_subset fun k ↦ (hck k).trans ?_
      refine Set.subset_iUnion_of_subset (finSumFinEquiv (Sum.inr (e k))) ?_
      simp only [Ψ, Equiv.symm_apply_apply, Sum.elim_inr, Equiv.symm_apply_apply, subset_rfl]

end Chebotarev
