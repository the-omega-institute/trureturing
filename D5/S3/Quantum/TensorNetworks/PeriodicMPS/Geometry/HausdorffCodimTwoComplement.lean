/- GID: D5/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/PeriodicMPS/Geometry/HausdorffCodimTwoComplement
   mirror-E: none(waiver:static-algebraic-identifiability)
   anchors: [lake/module/D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularComplement]
   utility: none
   digest: Removing a subset of Hausdorff codimension at least two from an open connected real chart leaves a dense path-connected complement. -/
import D5.S3.Quantum.TensorNetworks.PeriodicMPS.PeriodicMPSRegularComplement
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! An open connected real chart stays path connected after removing an exceptional set
whose Hausdorff dimension is at least two below the dimension of the chart. -/

set_option autoImplicit false

open Set Filter
open scoped ENNReal Topology

namespace D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularComplement

/-- A dense subset of an open connected set is path connected if each point of the
open set has an open neighborhood whose intersection with the subset is path connected. -/
theorem isPathConnected_of_locally_pathConnected_inter
    {X : Type*} [TopologicalSpace X] {U G : Set X}
    (hUo : IsOpen U) (hUc : IsConnected U) (hGU : G ⊆ U) (hGd : U ⊆ closure G)
    (hlocal : ∀ x ∈ U, ∃ V : Set X, IsOpen V ∧ x ∈ V ∧
      IsPathConnected (V ∩ G)) : IsPathConnected G := by
  obtain ⟨w, hw⟩ := hUc.nonempty
  obtain ⟨V, hVo, hwV, hVG⟩ := hlocal w hw
  obtain ⟨x, _, hx⟩ := hVG.nonempty
  let P : Set X := {y | JoinedIn G x y}
  have hxP : x ∈ P := JoinedIn.refl hx
  have hlocalP (y : X) (hy : y ∈ U ∩ closure P) :
      ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ V ∩ G ⊆ P := by
    obtain ⟨V, hVo, hyV, hVG⟩ := hlocal y hy.1
    obtain ⟨z, hzV, hzP⟩ := (mem_closure_iff.mp hy.2) V hVo hyV
    refine ⟨V, hVo, hyV, fun a ha => ?_⟩
    exact (show JoinedIn G x z from hzP).trans
      ((hVG.joinedIn z ⟨hzV, (show JoinedIn G x z from hzP).target_mem⟩ a ha).mono
        inter_subset_right)
  have hopen : IsOpen (U ∩ closure P) := isOpen_iff_mem_nhds.mpr fun y hy => by
    obtain ⟨V, hVo, hyV, hVP⟩ := hlocalP y hy
    refine Filter.mem_of_superset ((hUo.inter hVo).mem_nhds ⟨hy.1, hyV⟩) ?_
    intro z hz
    exact ⟨hz.1, closure_mono hVP (hVo.inter_closure ⟨hz.2, hGd hz.1⟩)⟩
  have hUP : U ⊆ U ∩ closure P := by
    apply hUc.isPreconnected.subset_left_of_subset_union hopen isClosed_closure.isOpen_compl
    · exact disjoint_left.mpr fun z hz hn => hn hz.2
    · intro z hz
      by_cases hp : z ∈ closure P
      · exact Or.inl ⟨hz, hp⟩
      · exact Or.inr hp
    · exact ⟨x, hGU hx, hGU hx, subset_closure hxP⟩
  refine ⟨x, hx, fun y hy => ?_⟩
  obtain ⟨V, _, hyV, hVP⟩ := hlocalP y (hUP (hGU hy))
  exact hVP ⟨hyV, hy⟩

section Product

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [FiniteDimensional ℝ H]

/-- Perspective projection to a horizontal slice, with the slice coordinate omitted. -/
private noncomputable def project (x : H × ℝ) (t : ℝ) (z : H × ℝ) : H :=
  x.1 + ((t - x.2) / (z.2 - x.2)) • (z.1 - x.1)

omit [FiniteDimensional ℝ H] in
private theorem project_dim (x : H × ℝ) (t : ℝ) (B : Set (H × ℝ)) :
    dimH (project x t '' (B ∩ {z | z.2 ≠ x.2})) ≤ dimH B := by
  refine le_trans (DifferentiableOn.dimH_image_le (𝕜 := ℝ) ?_)
    (dimH_mono inter_subset_left)
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hn : z.2 - x.2 ≠ 0 := sub_ne_zero.mpr hz.2
  have hs : DifferentiableAt ℝ (fun a : H × ℝ => (t - x.2) / (a.2 - x.2)) z := by
    have hden : DifferentiableAt ℝ (fun a : H × ℝ => a.2 - x.2) z :=
      differentiableAt_snd.sub_const x.2
    have hnum : DifferentiableAt ℝ (fun _ : H × ℝ => t - x.2) z :=
      differentiableAt_const _
    simpa only [div_eq_mul_inv] using hnum.fun_mul (hden.fun_inv hn)
  exact (differentiableAt_const x.1).add (hs.smul (differentiableAt_fst.sub_const _))

omit [FiniteDimensional ℝ H] in
private theorem segment_avoids_project (B : Set (H × ℝ)) {x : H × ℝ} {t : ℝ} {a : H}
    (hx : x ∉ B) (ht : t ≠ x.2) (ha : a ∉ project x t '' (B ∩ {z | z.2 ≠ x.2})) :
    segment ℝ x (a, t) ⊆ Bᶜ := by
  intro z hz hzB
  obtain ⟨r, _, rfl⟩ := segment_eq_image_lineMap ℝ x (a, t) ▸ hz
  have hr : r ≠ 0 := by
    intro he
    subst r
    exact hx (by simpa using hzB)
  have hfst : (AffineMap.lineMap x (a, t) r).1 - x.1 = r • (a - x.1) := by
    rw [AffineMap.lineMap_apply_module']
    change r • (a - x.1) + x.1 - x.1 = _
    abel
  have hsnd : (AffineMap.lineMap x (a, t) r).2 - x.2 = r * (t - x.2) := by
    rw [AffineMap.lineMap_apply_module']
    change r * (t - x.2) + x.2 - x.2 = _
    ring
  have hden : (AffineMap.lineMap x (a, t) r).2 - x.2 ≠ 0 := by
    rw [hsnd]
    exact mul_ne_zero hr (sub_ne_zero.mpr ht)
  apply ha
  refine ⟨_, ⟨hzB, sub_ne_zero.mp hden⟩, ?_⟩
  rw [project, hfst, hsnd, smul_smul]
  have hratio : (t - x.2) / (r * (t - x.2)) * r = 1 := by
    field_simp
  rw [hratio, one_smul]
  abel

/-- An open convex patch admits a two-segment path around a set of Hausdorff
dimension strictly below the dimension of a hyperplane. -/
private theorem convex_diff_pathConnected
    {V B : Set (H × ℝ)} (hVo : IsOpen V) (hVc : Convex ℝ V) (hV : V.Nonempty)
    (hB : dimH B < Module.finrank ℝ H) : IsPathConnected (V \ B) := by
  have hdim : dimH B < Module.finrank ℝ (H × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, Nat.cast_add, Nat.cast_one]
    exact hB.trans_le le_self_add
  obtain ⟨x, hxV, hxB⟩ := (dense_compl_of_dimH_lt_finrank hdim).inter_open_nonempty V hVo hV
  refine ⟨x, ⟨hxV, hxB⟩, fun y hy => ?_⟩
  let T : Set ℝ := (fun t : ℝ => (x.1, t)) ⁻¹' V
  have hTo : IsOpen T := hVo.preimage (continuous_const.prodMk continuous_id)
  let S : Set ℝ := {x.2, y.2}
  have hS : dimH S < Module.finrank ℝ ℝ := by
    rw [(finite_singleton y.2 |>.insert x.2).dimH_zero, Module.finrank_self]
    norm_num
  obtain ⟨t, htV, htS⟩ := (dense_compl_of_dimH_lt_finrank hS).inter_open_nonempty T hTo
    ⟨x.2, hxV⟩
  have htx : t ≠ x.2 := fun h => htS (Or.inl h)
  have hty : t ≠ y.2 := fun h => htS (Or.inr (mem_singleton_iff.mpr h))
  let Aₓ := project x t '' (B ∩ {z | z.2 ≠ x.2})
  let Aᵧ := project y t '' (B ∩ {z | z.2 ≠ y.2})
  let W : Set H := (fun a : H => (a, t)) ⁻¹' V
  have hWo : IsOpen W := hVo.preimage (continuous_id.prodMk continuous_const)
  have hA : dimH (Aₓ ∪ Aᵧ) < Module.finrank ℝ H := by
    rw [dimH_union]
    exact (max_le (project_dim x t B) (project_dim y t B)).trans_lt hB
  obtain ⟨a, haW, haA⟩ := (dense_compl_of_dimH_lt_finrank hA).inter_open_nonempty W hWo
    ⟨x.1, htV⟩
  have join (z : H × ℝ) (hzV : z ∈ V) (hz : segment ℝ z (a, t) ⊆ Bᶜ) :
      JoinedIn (V \ B) z (a, t) := by
    have hs : segment ℝ z (a, t) ⊆ V \ B :=
      fun _ hp => ⟨hVc.segment_subset hzV haW hp, hz hp⟩
    exact (((convex_segment z (a, t)).isPathConnected ⟨z, left_mem_segment ..⟩).joinedIn
      z (left_mem_segment ..) (a, t) (right_mem_segment ..)).mono hs
  exact (join x hxV (segment_avoids_project B hxB htx (fun h => haA (Or.inl h)))).trans
    (join y hy.1 (segment_avoids_project B hy.2 hty (fun h => haA (Or.inr h)))).symm

end Product

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hausdorff-dimension condition alone gives paths and relative density in
an open connected chart. Closedness of the exceptional set is only needed to
infer openness of the complement. -/
theorem isPathConnected_diff_of_dimH_add_one_lt
    {U B : Set E} (hUo : IsOpen U) (hUc : IsConnected U)
    (hB : dimH B + 1 < Module.finrank ℝ E) :
    IsPathConnected (U \ B) ∧ U ⊆ closure (U \ B) := by
  have hdB : dimH B < Module.finrank ℝ E := hB.trans_le' le_self_add
  have hDense := dense_compl_of_dimH_lt_finrank hdB
  have hrel : U ⊆ closure (U \ B) :=
    fun z hz => hUo.inter_closure ⟨hz, hDense z⟩
  refine ⟨isPathConnected_of_locally_pathConnected_inter hUo hUc sdiff_subset hrel ?_, hrel⟩
  have hd : 0 < Module.finrank ℝ E := by
    exact Nat.cast_pos.mp (lt_of_le_of_lt bot_le hB)
  let H := Fin (Module.finrank ℝ E - 1) → ℝ
  have hH : Module.finrank ℝ H = Module.finrank ℝ E - 1 := by
    simp [H]
  have hr : Module.finrank ℝ E = Module.finrank ℝ (H × ℝ) := by
    rw [Module.finrank_prod, Module.finrank_self, hH]
    omega
  let e : E ≃L[ℝ] H × ℝ := (LinearEquiv.ofFinrankEq E (H × ℝ) hr).toContinuousLinearEquiv
  have hsmall : dimH (e '' B) < Module.finrank ℝ H := by
    rw [e.dimH_image]
    have he : Module.finrank ℝ E = Module.finrank ℝ H + 1 := by
      simpa only [Module.finrank_prod, Module.finrank_self] using hr
    rw [he, Nat.cast_add, Nat.cast_one] at hB
    exact lt_of_not_ge fun hn => (not_le_of_gt hB) (add_le_add_left hn 1)
  intro z hz
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hUo z hz
  let V := Metric.ball z r
  have hVo : IsOpen V := Metric.isOpen_ball
  have hzV : z ∈ V := Metric.mem_ball_self hr
  have hV : IsPathConnected ((e '' V) \ (e '' B)) :=
    convex_diff_pathConnected (e.toHomeomorph.isOpenMap V hVo)
      ((convex_ball z r).linear_image e.toLinearMap) ⟨e z, z, hzV, rfl⟩ hsmall
  refine ⟨V, hVo, hzV, ?_⟩
  have heq : e.symm '' ((e '' V) \ (e '' B)) = V ∩ (U \ B) := by
    ext a
    constructor
    · rintro ⟨w, ⟨⟨b, hb, rfl⟩, hn⟩, rfl⟩
      rw [e.symm_apply_apply]
      exact ⟨hb, hsub hb, fun h => hn ⟨b, h, rfl⟩⟩
    · rintro ⟨haV, _, haB⟩
      refine ⟨e a, ⟨⟨a, haV, rfl⟩, ?_⟩, e.symm_apply_apply a⟩
      rintro ⟨b, hb, he⟩
      exact haB (e.injective he ▸ hb)
  exact heq ▸ hV.image e.symm.continuous

/-- In dimension `d ≥ 2`, a closed subset of Hausdorff dimension at most `d - 2`
has a relatively open, dense, path-connected complement in every open connected chart. -/
theorem open_pathConnected_diff_of_dimH_le_codim_two
    {U B : Set E} (hUo : IsOpen U) (hUc : IsConnected U) (hBc : IsClosed B)
    (hd : 2 ≤ Module.finrank ℝ E)
    (hB : dimH B ≤ ((Module.finrank ℝ E - 2 : ℕ) : ℝ≥0∞)) :
    IsOpen (U \ B) ∧ IsPathConnected (U \ B) ∧ U ⊆ closure (U \ B) := by
  refine ⟨hUo.sdiff hBc, isPathConnected_diff_of_dimH_add_one_lt hUo hUc ?_⟩
  have hn : Module.finrank ℝ E - 2 + 1 < Module.finrank ℝ E := by omega
  apply (add_le_add_left hB 1).trans_lt
  exact_mod_cast hn

end D5.S3.Quantum.TensorNetworks.PeriodicMPSRegularComplement
