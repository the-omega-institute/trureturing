/- GID: D5/S1/Dynamics/Shadowing/CantorCircleExpansivity
   generality: I
   mirror-B: D5/B/S1/Dynamics/Shadowing/CantorCircleExpansivity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact positive expansivity order for circles glued along the ternary Cantor image. -/

import D5.S1.Dynamics.Shadowing.CircleFinitePositiveExpansiveness.Basic
import D5.S1.Dynamics.Shadowing.InvarianceGluedSheets
import Mathlib.Topology.Instances.CantorSet

/-!
Tripling on the unit circle preserves the image of the ternary Cantor set.
Points in the open middle third can start arbitrarily close to the gluing set
and enter it at time one, giving every finite order on the corresponding union of sheets.
-/

noncomputable section

open Function Set

namespace D5.S1.Dynamics.Shadowing.CantorCircleExpansivity

open CircleFinitePositiveExpansiveness (Circle coordinate project project_coordinate
  continuous_project project_dist_eq)

/-- Tripling on the unit circle. -/
def tripling (x : Circle) : Circle := 3 • x

private theorem tripling_project (x : ℝ) : tripling (project x) = project (3 * x) := by
  change 3 • (x : Circle) = ((3 * x : ℝ) : Circle)
  rw [← AddCircle.coe_nsmul, nsmul_eq_mul]
  norm_num

private theorem project_int (z : ℤ) : project (z : ℝ) = 0 :=
  (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z, by simp [zsmul_eq_mul]⟩

private theorem project_one_add (x : ℝ) : project (1 + x) = project x := by
  change ((1 + x : ℝ) : Circle) = (x : Circle)
  rw [add_comm, AddCircle.coe_add_period]

theorem continuous_tripling : Continuous tripling := by
  unfold tripling
  fun_prop

theorem surjective_tripling : Surjective tripling := by
  intro x
  refine ⟨project (coordinate 0 x / 3), ?_⟩
  rw [tripling_project, show 3 * (coordinate 0 x / 3) = coordinate 0 x by ring,
    project_coordinate]

private theorem dist_tripling_of_lt {x y : Circle} (h : dist x y < 1 / 8) :
    dist (tripling x) (tripling y) = 3 * dist x y := by
  let r := coordinate 0 (x - y)
  let u := r - (round r : ℝ)
  have hr : (r : Circle) = x - y := project_coordinate 0 (x - y)
  have hu : (u : Circle) = x - y := by
    change ((r - (round r : ℝ) : ℝ) : Circle) = x - y
    rw [AddCircle.coe_sub, hr, show ((round r : ℝ) : Circle) = 0 from project_int (round r),
      sub_zero]
  have habs : dist x y = |u| := by
    rw [dist_eq_norm, ← hr, AddCircle.norm_eq]
    simp [u]
  have hsmall : |3 * u| ≤ |(1 : ℝ)| / 2 := by
    rw [abs_mul, ← habs]
    norm_num
    linarith
  rw [dist_eq_norm, tripling, tripling, ← nsmul_sub, ← hu, ← AddCircle.coe_nsmul,
    nsmul_eq_mul]
  have hnorm := (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero).mpr hsmall
  simpa [abs_mul, habs] using hnorm

/-- At scales below one eighth, forward closeness forces equality. -/
theorem tripling_positivelyExpansive : PositivelyExpansive tripling := by
  refine ⟨1 / 8, by norm_num, fun x y h => dist_eq_zero.mp ?_⟩
  have hgrowth (n : ℕ) :
      dist (tripling^[n] x) (tripling^[n] y) = (3 : ℝ)^n * dist x y := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [iterate_succ_apply', iterate_succ_apply', dist_tripling_of_lt (h n), ih, pow_succ]
        ring
  by_contra hne
  have hd : 0 < dist x y := lt_of_le_of_ne dist_nonneg (Ne.symm hne)
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 / 8) / dist x y) (by norm_num : (1 : ℝ) < 3)
  exact (not_lt_of_ge ((div_lt_iff₀ hd).mp hn).le) (hgrowth n ▸ h n)

/-- The image of Mathlib's ternary Cantor set in the unit circle. -/
def cantorCircle : Set Circle := project '' cantorSet

theorem isCompact_cantorCircle : IsCompact cantorCircle :=
  isCompact_cantorSet.image continuous_project

private theorem cantorCircle_nonempty : cantorCircle.Nonempty :=
  ⟨project 0, 0, zero_mem_cantorSet, rfl⟩

theorem mapsTo_tripling_cantorCircle : MapsTo tripling cantorCircle cantorCircle := by
  rintro _ ⟨x, hx, rfl⟩
  rw [cantorSet_eq_union_halves] at hx
  rcases hx with ⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩
  · exact ⟨y, hy, by rw [tripling_project]; congr 1; ring⟩
  · refine ⟨y, hy, ?_⟩
    rw [tripling_project, show 3 * ((2 + y) / 3) = 2 + y by ring,
      show 2 + y = 1 + (1 + y) by ring, project_one_add, project_one_add]

private theorem one_mem_cantorSet : (1 : ℝ) ∈ cantorSet := by
  refine mem_iInter.mpr fun n => ?_
  induction n with
  | zero => exact ⟨zero_le_one, le_rfl⟩
  | succ n ih =>
      rw [preCantorSet_succ]
      exact Or.inr ⟨1, ih, by norm_num⟩

private theorem div_three_mem_cantorSet {x : ℝ} (hx : x ∈ cantorSet) : x / 3 ∈ cantorSet := by
  rw [cantorSet_eq_union_halves]
  exact Or.inl ⟨x, hx, rfl⟩

private theorem project_notMem_cantorCircle_of_middle_third {y : ℝ}
    (h₁ : 1 / 3 < y) (h₂ : y < 2 / 3) : project y ∉ cantorCircle := by
  rintro ⟨x, hx, he⟩
  obtain ⟨hx₀, hx₁⟩ := cantorSet_subset_unitInterval hx
  have hy : y ∈ Ico (0 : ℝ) (0 + 1) := ⟨by linarith, by linarith⟩
  rcases hx₁.eq_or_lt with he₁ | hlt
  · have hzero : (0 : ℝ) ∈ Ico (0 : ℝ) (0 + 1) := ⟨le_rfl, by norm_num⟩
    have h₀ : (0 : Circle) = (y : Circle) := by
      rw [he₁] at he
      simpa only [project, AddCircle.coe_period] using he
    have hy₀ := (AddCircle.coe_eq_coe_iff_of_mem_Ico hzero hy).mp (by simpa using h₀)
    linarith
  · have hx' : x ∈ Ico (0 : ℝ) (0 + 1) := ⟨hx₀, by simpa using hlt⟩
    have hxy := (AddCircle.coe_eq_coe_iff_of_mem_Ico hx' hy).mp he
    rw [cantorSet_eq_union_halves] at hx
    rcases hx with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · linarith [(cantorSet_subset_unitInterval hz).2]
    · linarith [(cantorSet_subset_unitInterval hz).1]

/-- Points in the middle gap approach the left endpoint and enter the Cantor image in one step. -/
theorem exists_near_coalescing_point {δ : ℝ} (hδ : 0 < δ) :
    ∃ y ∉ cantorCircle, tripling y ∈ cantorCircle ∧ Metric.infDist y cantorCircle < δ := by
  have hpow (n : ℕ) : (1 / 3 : ℝ)^n ∈ cantorSet := by
    induction n with
    | zero => simpa using one_mem_cantorSet
    | succ n ih =>
        rw [pow_succ, mul_one_div]
        exact div_three_mem_cantorSet ih
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 3 : ℝ) < 1)
  let x : ℝ := (1 / 3 : ℝ)^(n + 1)
  let y : ℝ := (1 + x) / 3
  have hxpos : 0 < x := pow_pos (by norm_num) _
  have hxmem : x ∈ cantorSet := hpow (n + 1)
  have hxle : x ≤ 1 / 3 := by
    dsimp [x]
    rw [pow_succ]
    have h := (cantorSet_subset_unitInterval (hpow n)).2
    linarith
  have hxlt : x < δ := by
    dsimp [x]
    rw [pow_succ]
    linarith [show 0 < (1 / 3 : ℝ)^n from pow_pos (by norm_num) _]
  refine ⟨project y, project_notMem_cantorCircle_of_middle_third
    (by dsimp [y]; linarith) (by dsimp [y]; linarith), ?_, ?_⟩
  · refine ⟨x, hxmem, ?_⟩
    rw [tripling_project, show 3 * y = 1 + x by dsimp [y]; ring, project_one_add]
  · have hthird : project (1 / 3) ∈ cantorCircle :=
      ⟨1 / 3, div_three_mem_cantorSet one_mem_cantorSet, rfl⟩
    have hdiff : y - 1 / 3 = x / 3 := by dsimp [y]; ring
    have habs : |y - 1 / 3| = x / 3 := by rw [hdiff, abs_of_pos (by positivity)]
    calc
      _ ≤ dist (project y) (project (1 / 3)) := Metric.infDist_le_dist_of_mem hthird
      _ = x / 3 := by
        rw [project_dist_eq (by rw [habs]; linarith), Real.dist_eq, habs]
      _ < δ := by linarith

theorem cantorCircle_not_isolating :
    ¬ ∃ U : Set Circle, IsOpen U ∧ cantorCircle ⊆ U ∧
      cantorCircle = ⋂ n : ℕ, (tripling^[n]) ⁻¹' U := by
  intro hiso
  obtain ⟨δ, hδ, hescape⟩ := (InvarianceGluedSheets.uniformOrbitEscape_infDist_iff
    isCompact_cantorCircle cantorCircle_nonempty mapsTo_tripling_cantorCircle).mpr hiso
  obtain ⟨y, hy, hy₁, hyδ⟩ := exists_near_coalescing_point hδ
  have hd : Metric.infDist y cantorCircle ≠ 0 :=
    fun h => hy ((isCompact_cantorCircle.isClosed.mem_iff_infDist_zero cantorCircle_nonempty).mpr h)
  obtain ⟨n, hn⟩ := hescape y hd
  cases n with
  | zero => exact (not_lt_of_ge hn) hyδ
  | succ n =>
      change δ ≤ Metric.infDist (tripling^[n + 1] y) cantorCircle at hn
      rw [iterate_succ_apply, Metric.infDist_zero_of_mem (mapsTo_tripling_cantorCircle.iterate n hy₁)]
        at hn
      exact (not_lt_of_ge hn) hδ

/-- The `N` circle sheets, with heights given by distance to the Cantor image. -/
abbrev Space (N : ℕ) := InvarianceGluedSheets.Space N (fun y => Metric.infDist y cantorCircle)

/-- Tripling on every circle sheet. -/
def sheetMap (N : ℕ) : Space N → Space N :=
  InvarianceGluedSheets.map tripling (InvarianceGluedSheets.infDist_zero_invariant
    isCompact_cantorCircle.isClosed cantorCircle_nonempty mapsTo_tripling_cantorCircle)

private theorem connectedSpace_space {N : ℕ} (hN : 0 < N) : ConnectedSpace (Space N) := by
  let sheet (i : Fin N) : Circle → Space N :=
    InvarianceGluedSheets.lift (fun y => Metric.infDist y cantorCircle) i
  have hcover : (⋃ i, range (sheet i)) = univ := by
    refine eq_univ_of_forall fun p => ?_
    obtain ⟨i, hi⟩ := p.property
    exact mem_iUnion.mpr ⟨i, p.val.1, Subtype.ext (Prod.ext rfl hi.symm)⟩
  obtain ⟨y, hy⟩ := cantorCircle_nonempty
  let p := sheet ⟨0, hN⟩ y
  have hp : ∀ i, p ∈ range (sheet i) := by
    intro i
    refine ⟨y, Subtype.ext (Prod.ext rfl ?_)⟩
    simp [p, sheet, InvarianceGluedSheets.lift, Metric.infDist_zero_of_mem hy]
  refine connectedSpace_iff_univ.mpr ⟨⟨p, mem_univ _⟩, ?_⟩
  rw [← hcover]
  refine isPreconnected_iUnion ⟨p, mem_iInter.mpr hp⟩ fun i => isPreconnected_range ?_
  exact (continuous_id.prodMk
    (continuous_const.mul (Metric.continuous_infDist_pt cantorCircle))).subtype_mk _

/-- For every `N ≥ 2`, the compact connected Cantor gluing carries a continuous onto
map of exact positive expansivity order `N`. -/
theorem exact_order {N : ℕ} (hN : 2 ≤ N) :
    CompactSpace (Space N) ∧ ConnectedSpace (Space N) ∧
      Continuous (sheetMap N) ∧ Surjective (sheetMap N) ∧
      (∃ ε > 0, ForwardBowenBound (sheetMap N) univ ε N) ∧
      (∀ ε > 0, ¬ ForwardBowenBound (sheetMap N) univ ε (N - 1)) := by
  let _ : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  have hρ := Metric.continuous_infDist_pt cantorCircle
  obtain ⟨hbound, _, hexact⟩ := InvarianceGluedSheets.exact_order_infDist hN
    tripling_positivelyExpansive isCompact_cantorCircle cantorCircle_nonempty
    mapsTo_tripling_cantorCircle
  exact ⟨InvarianceGluedSheets.compactSpace_space hρ, connectedSpace_space (by omega),
    InvarianceGluedSheets.continuous_map hρ continuous_tripling _,
    InvarianceGluedSheets.surjective_map surjective_tripling _, hbound,
    hexact.mpr cantorCircle_not_isolating⟩

end D5.S1.Dynamics.Shadowing.CantorCircleExpansivity
