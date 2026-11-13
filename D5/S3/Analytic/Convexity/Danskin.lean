/- GID: D5/S3/Analytic/Convexity/Danskin
   generality: G
   mirror-B: D5/B/S3/Analytic/Convexity/Danskin
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A compact envelope attains its maximal optimizer directional derivative. -/

import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Order.IsLUB
import Mathlib.Tactic

/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in
`docs/reports/licenses/econlib-Danskin-LICENSE.txt`.
Authors: Daniel Lyng

Source: https://github.com/danlyng/Econlib/blob/d7bd9477476cade1c6695c8891746048ceddc52f/Econlib/Math/Analysis/Danskin.lean
Faithful extraction of hasRightDirDeriv_iSup and its live support closure.
Adaptation: project header and imports; module/public syntax removed for local content routing.
No Optlib source is retained.

Retirement: remove this transplant when this repository's resolved Mathlib pin
provides an equivalent declaration with the full telescope and attaining/dominating
conclusion, and its two generic compact-subtype affine applications establish the
literal right maximum and minimum little-o expansions without additional premises.
-/

open Set Filter Topology InnerProductSpace

namespace Danskin

/-! ### Core Definitions -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Z : Type*} [TopologicalSpace Z] [CompactSpace Z] [Nonempty Z]

/-- The value function `V(x) = sup_{z ∈ Z} f(x, z)`. -/
noncomputable def valueFunction (f : E → Z → ℝ) (x : E) : ℝ :=
  ⨆ z : Z, f x z

/-- The optimizer set `Z*(x) = {z : Z | f(x, z) = V(x)}`. -/
def argmax_iSup (f : E → Z → ℝ) (x : E) : Set Z :=
  { z : Z | f x z = valueFunction f x }

/-- Right-sided directional derivative of `g` at `x` in direction `v`. -/
def HasRightDirDerivAt (g : E → ℝ) (x v : E) (d : ℝ) : Prop :=
  Filter.Tendsto (fun t ↦ (g (x + t • v) - g x) / t)
    (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d)

/-! ### Hypotheses -/

/-- Joint continuity of `f` on `X × Z`. -/
def ContinuousOnProd (f : E → Z → ℝ) (X : Set E) : Prop :=
  ContinuousOn (fun p : E × Z ↦ f p.1 p.2) (X ×ˢ univ)

/-- Convexity of `f(·, z)` on `X` for each `z`. -/
def ConvexOnFiber (f : E → Z → ℝ) (X : Set E) : Prop :=
  ∀ z : Z, ConvexOn ℝ X (fun x ↦ f x z)

/-! ### Auxiliary Lemmas -/

omit [InnerProductSpace ℝ E] [CompleteSpace E] [CompactSpace Z] [Nonempty Z] in
/-- Continuity of `z ↦ f(x, z)` for fixed `x ∈ X`, extracted from joint continuity. -/
lemma ContinuousOnProd.continuous_right {f : E → Z → ℝ} {X : Set E}
    (h_cont : ContinuousOnProd f X) (x : E) (hx : x ∈ X) :
    Continuous (fun z ↦ f x z) := by
  rw [show (fun z ↦ f x z) = (fun p : E × Z ↦ f p.1 p.2) ∘ (fun z ↦ (x, z)) from rfl]
  apply ContinuousOn.comp_continuous h_cont
    (continuous_prodMk.mpr ⟨continuous_const, continuous_id'⟩)
  intro z; exact ⟨hx, mem_univ z⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The supremum `⨆ z, f x z` is attained when `Z` is compact and `z ↦ f x z` is continuous. -/
lemma exists_eq_ciSup {x : E} (f : E → Z → ℝ)
    (hf : Continuous (fun z ↦ f x z)) :
    ∃ z : Z, f x z = ⨆ z : Z, f x z := by
  obtain ⟨z, _, hz⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hf.continuousOn
  exact ⟨z, le_antisymm
    (le_ciSup (isCompact_range hf).bddAbove z)
    (ciSup_le fun z' ↦ hz (mem_univ z'))⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The optimizer set is nonempty when `z ↦ f x z` is continuous. -/
lemma argmax_iSup_nonempty {x : E} (f : E → Z → ℝ)
    (hf : Continuous (fun z ↦ f x z)) :
    (argmax_iSup f x).Nonempty :=
  (exists_eq_ciSup f hf).imp fun _ hz ↦ hz

omit [CompleteSpace E] [TopologicalSpace Z] [CompactSpace Z] in
/-- The value function `V(x) = ⨆ z, f x z` is convex on `X` when each fiber `f(·, z)` is convex and
the supremum is bounded above pointwise. -/
lemma convexOn_valueFunction {f : E → Z → ℝ} {X : Set E}
    (hX : Convex ℝ X)
    (h_conv : ConvexOnFiber f X)
    (h_bdd : ∀ x ∈ X, BddAbove (range (fun z ↦ f x z))) :
    ConvexOn ℝ X (valueFunction f) := by
  constructor
  · exact hX
  · intro x hx y hy a b ha hb hab
    apply ciSup_le
    intro z
    calc f (a • x + b • y) z
        ≤ a * f x z + b * f y z := (h_conv z).2 hx hy ha hb hab
      _ ≤ a * valueFunction f x + b * valueFunction f y := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (le_ciSup (h_bdd x hx) z) ha
          · exact mul_le_mul_of_nonneg_left (le_ciSup (h_bdd y hy) z) hb

/-! ### Part (i): Attainment, Finiteness, and Convexity -/

omit [CompleteSpace E] in
/-- **Danskin Part 1.** Under joint continuity and pointwise convexity, the value function `V` is
convex, the supremum is bounded, and the optimizer set is nonempty. -/
theorem convexOn_valueFunction_argmax (f : E → Z → ℝ) (X : Set E)
    (hX_convex : Convex ℝ X)
    (h_cont : ContinuousOnProd f X) (h_conv : ConvexOnFiber f X)
    (x : E) (hx : x ∈ X) :
    ConvexOn ℝ X (valueFunction f) ∧
    BddAbove (range (f x)) ∧
    (argmax_iSup f x).Nonempty := by
  have hfx := ContinuousOnProd.continuous_right h_cont x hx
  exact ⟨convexOn_valueFunction hX_convex h_conv fun y hy ↦
      (isCompact_range (ContinuousOnProd.continuous_right h_cont y hy)).bddAbove,
    (isCompact_range hfx).bddAbove,
    argmax_iSup_nonempty f hfx⟩

/-! ### Part (ii): Directional Derivative Formula -/

omit [CompleteSpace E] in
/-- **Danskin Part (ii).** The right directional derivative of the value function exists and equals
the maximum of directional derivatives over the optimizer set:
`V'(x; v) = max_{z ∈ Z*(x)} f'(x, z; v)`. The conclusion delivers this maximum explicitly: The
value `d` is attained at some `z_max ∈ Z*(x)`, and it dominates the directional derivative at every
optimizer. -/
theorem hasRightDirDeriv_iSup (f : E → Z → ℝ) (X : Set E)
    (hX_open : IsOpen X) (hX_convex : Convex ℝ X)
    (h_cont : ContinuousOnProd f X) (h_conv : ConvexOnFiber f X)
    (x v : E) (hx : x ∈ X)
    (h_dir : ∀ z ∈ argmax_iSup f x,
      ∃ d : ℝ, HasRightDirDerivAt (fun w ↦ f w z) x v d) :
    ∃ d : ℝ, HasRightDirDerivAt (valueFunction f) x v d ∧
      (∃ z_max ∈ argmax_iSup f x,
        HasRightDirDerivAt (fun w ↦ f w z_max) x v d) ∧
      ∀ z ∈ argmax_iSup f x, ∀ d_z : ℝ,
        HasRightDirDerivAt (fun w ↦ f w z) x v d_z → d_z ≤ d := by
  have hfx_cont := ContinuousOnProd.continuous_right h_cont x hx
  have ⟨hV_convex, hbdd_x, hopt_ne⟩ :=
    convexOn_valueFunction_argmax f X hX_convex h_cont h_conv x hx
  have h_ray_cts : Continuous (fun t : ℝ ↦ x + t • v) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- x + tv ∈ X for small t (X is open)
  have h_small_t : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), x + t • v ∈ X := by
    have : Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
      simpa using h_ray_cts.tendsto 0
    exact (this.eventually (hX_open.mem_nhds hx)).filter_mono nhdsWithin_le_nhds
  have h_bdd_at : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
      BddAbove (range (fun z ↦ f (x + t • v) z)) := by
    filter_upwards [h_small_t] with t ht
    exact (isCompact_range (ContinuousOnProd.continuous_right h_cont _ ht)).bddAbove
  /- ## Step 1: Reduce to existence of g'(0+) for g(t) = V(x + tv)
     g is convex on the preimage interval S = {t | x + tv ∈ X}
     Since V is convex on X and the map t ↦ x + tv is affine, g is convex on S.
     S is open (preimage of open set under continuous map) and contains 0.
     By ConvexOn.hasDerivWithinAt_rightDeriv_of_mem_interior, g has a right derivative at 0.
     This right derivative is the directional derivative of V. -/
  let ray : ℝ →ᵃ[ℝ] E :=
    { toFun := fun t ↦ x + t • v
      linear := (LinearMap.lsmul ℝ E).flip v
      map_vadd' := by intro p q; simp [vadd_eq_add, add_smul]; abel }
  let S := (fun t : ℝ ↦ x + t • v) ⁻¹' X
  have hS_open : IsOpen S := hX_open.preimage h_ray_cts
  have h0_in_S : (0 : ℝ) ∈ S := by simp [S, hx]
  have h0_interior : (0 : ℝ) ∈ interior S := by rwa [hS_open.interior_eq]
  -- g is convex on S, the preimage of X under the affine ray.
  have hg_convex : ConvexOn ℝ S (fun t ↦ valueFunction f (x + t • v)) :=
    hV_convex.comp_affineMap ray
  -- g has a right derivative at 0 — convert to HasRightDirDerivAt
  set d_V := derivWithin (fun t : ℝ ↦ valueFunction f (x + t • v)) (Ioi 0) (0 : ℝ)
  have hV_dir : HasRightDirDerivAt (valueFunction f) x v d_V := by
    rw [HasRightDirDerivAt]
    have hg_deriv := hg_convex.hasDerivWithinAt_rightDeriv_of_mem_interior h0_interior
    rw [hasDerivWithinAt_iff_tendsto_slope' (show (0 : ℝ) ∉ Ioi (0 : ℝ) by simp)] at hg_deriv
    have : (fun t : ℝ ↦ (valueFunction f (x + t • v) - valueFunction f x) / t) =
        slope (fun t ↦ valueFunction f (x + t • v)) 0 := by
      ext t; simp [slope, sub_zero, div_eq_inv_mul]
    rw [this]; exact hg_deriv
  -- ── Step 2: Lower bound — d_V ≥ d_z for any z ∈ Z*(x) ──
  have h_lower_bound : ∀ z ∈ argmax_iSup f x,
      ∀ d_z, HasRightDirDerivAt (fun w ↦ f w z) x v d_z → d_z ≤ d_V := by
    intro z hz d_z hd_z
    /- V(x+tv) ≥ f(x+tv, z) and V(x) = f(x, z) since z ∈ Z*(x)
       So (V(x+tv) - V(x))/t ≥ (f(x+tv, z) - f(x, z))/t for t > 0
       Taking limits: d_V ≥ d_z -/
    apply le_of_tendsto_of_tendsto hd_z hV_dir
    filter_upwards [h_small_t, h_bdd_at, self_mem_nhdsWithin] with t ht_X ht_bdd ht_pos
    rw [Set.mem_Ioi] at ht_pos
    apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
    have hle : f (x + t • v) z ≤ valueFunction f (x + t • v) := le_ciSup ht_bdd z
    rw [hz]; linarith
  /- ## Step 3: Upper bound — d_V ≤ d_{z̄} for some z̄ ∈ Z*(x)
     This is the sequential compactness argument.
     For the existential conclusion, we need to find z_max with d_V = d_{z_max}.
     From Step 2, d_V ≥ d_z for all z ∈ Z*(x).
     The upper bound d_V ≤ max_{z ∈ Z*(x)} d_z requires:
       (a) choosing optimizers z_t at x+tv (IsCompact.exists_isMaxOn)
       (b) extracting z_t → z̄ (IsCompact.tendsto_subseq)
       (c) showing z̄ ∈ Z*(x) (joint continuity + Berge)
       (d) showing d_V ≤ d_{z̄} (convex slope monotonicity + continuity) -/
  have h_upper_bound : ∃ zb : Z, zb ∈ argmax_iSup f x ∧
      ∃ db : ℝ, HasRightDirDerivAt (fun w ↦ f w zb) x v db ∧ d_V ≤ db := by
    -- ### (a) Choose optimizers z_t at x+tv via classical choice
    have h_opt_choice : ∃ zc : ℝ → Z, ∀ t : ℝ, x + t • v ∈ X →
        f (x + t • v) (zc t) = valueFunction f (x + t • v) := by
      have : ∀ t : ℝ, ∃ z : Z, x + t • v ∈ X →
          f (x + t • v) z = valueFunction f (x + t • v) := by
        intro t; by_cases ht : x + t • v ∈ X
        · exact ⟨_, fun _ ↦ exists_eq_ciSup f
            (ContinuousOnProd.continuous_right h_cont _ ht) |>.choose_spec⟩
        · exact ⟨Classical.arbitrary Z, fun h ↦ absurd h ht⟩
      exact ⟨fun t ↦ (this t).choose, fun t ht ↦ (this t).choose_spec ht⟩
    obtain ⟨zc, hzc_opt⟩ := h_opt_choice
    -- ### (b) Extract cluster point z̄ of z_t as t → 0⁺ (compactness of Z)
    have hne : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
    obtain ⟨z_bar, hz_cluster⟩ : ∃ z_bar : Z,
        MapClusterPt z_bar (nhdsWithin (0 : ℝ) (Ioi 0)) zc := by
      obtain ⟨z, hz⟩ := exists_clusterPt_of_compactSpace
        (map zc (nhdsWithin (0 : ℝ) (Ioi 0)))
      exact ⟨z, by rwa [mapClusterPt_def]⟩
    -- ### (c) Show z̄ ∈ Z*(x) via Berge-style argument
    have hz_bar_opt : z_bar ∈ argmax_iSup f x := by
      apply le_antisymm (le_ciSup ((isCompact_range hfx_cont).bddAbove) z_bar)
      -- V(x) ≤ f(x, z̄): cluster point of V(x+tv) = f(x+tv, z_t) at f(x, z̄),
      -- and f(x+tv, z_star) → V(x) ≤ f(x+tv, z_t), squeeze gives V(x) ≤ f(x, z̄)
      obtain ⟨z_star, hz_star⟩ := hopt_ne
      set Vx := valueFunction f x
      have h_ray_tends : Tendsto (fun t : ℝ ↦ x + t • v)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds x) := by
        have : Tendsto (fun t : ℝ ↦ x + t • v) (nhds 0) (nhds x) := by
          conv => arg 3; rw [show x = x + (0 : ℝ) • v by simp]
          exact tendsto_const_nhds.add
            (continuous_id.tendsto 0 |>.smul tendsto_const_nhds)
        exact this.mono_left nhdsWithin_le_nhds
      have h_pair : MapClusterPt (x, z_bar) (nhdsWithin (0 : ℝ) (Ioi 0))
          (fun t ↦ ((x + t • v : E), zc t)) := by
        rw [mapClusterPt_iff_frequently]; intro s hs; rw [nhds_prod_eq] at hs
        obtain ⟨u, hu, w, hw, huw⟩ := Filter.mem_prod_iff.mp hs
        exact (hz_cluster.frequently hw).and_eventually
          (h_ray_tends.eventually hu) |>.mono fun t ⟨hzw, hxu⟩ ↦ huw ⟨hxu, hzw⟩
      have h_fcluster : MapClusterPt (f x z_bar) (nhdsWithin (0 : ℝ) (Ioi 0))
          (fun t ↦ f (x + t • v) (zc t)) :=
        ((h_cont (x, z_bar) ⟨hx, mem_univ z_bar⟩).continuousAt
          ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_bar⟩)).mapClusterPt h_pair
      have h_fz_tends : Tendsto (fun t : ℝ ↦ f (x + t • v) z_star)
          (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds Vx) := by
        rw [show Vx = f x z_star from hz_star.symm]
        exact ((h_cont (x, z_star) ⟨hx, mem_univ z_star⟩).continuousAt
          ((hX_open.prod isOpen_univ).mem_nhds ⟨hx, mem_univ z_star⟩)).tendsto.comp
          (Tendsto.prodMk_nhds h_ray_tends tendsto_const_nhds)
      have h_le_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
          f (x + t • v) z_star ≤ f (x + t • v) (zc t) := by
        filter_upwards [h_small_t, h_bdd_at] with t ht_mem ht_bdd
        rw [hzc_opt t ht_mem]; exact le_ciSup ht_bdd z_star
      by_contra hlt; push Not at hlt
      -- f(x, z̄) < Vx, midpoint squeeze contradiction
      change f x z_bar < Vx at hlt
      have hm1 : f x z_bar < (Vx + f x z_bar) / 2 := by linarith
      have hm2 : (Vx + f x z_bar) / 2 < Vx := by linarith
      exact (h_fcluster.frequently (Iio_mem_nhds hm1))
        (by filter_upwards [h_le_ev, h_fz_tends.eventually (Ioi_mem_nhds hm2)]
            with t hle hfm; linarith)
    -- ### (d) Get directional derivative at z̄ and show d_V ≤ d_{z̄}
    obtain ⟨db, hdb⟩ := h_dir z_bar hz_bar_opt
    refine ⟨z_bar, hz_bar_opt, db, hdb, ?_⟩
    -- Use ge_of_tendsto: db is the limit of slopes of g_{z̄}, and d_V ≤ each slope
    apply ge_of_tendsto hdb
    /- For T > 0 in S: d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
       via slope chain: d_V ≤ slope g_V 0 t ≤ slope g_{z_t} 0 t ≤ slope g_{z_t} 0 T
       then cluster point argument for fixed T. -/
    have h_S_ev : ∀ᶠ T in nhdsWithin (0 : ℝ) (Ioi 0), T ∈ S :=
      nhdsWithin_le_nhds (hS_open.mem_nhds h0_in_S)
    filter_upwards [h_S_ev, self_mem_nhdsWithin (s := Ioi 0)] with T hT_S hT_pos_mem
    rw [mem_Ioi] at hT_pos_mem
    -- For this fixed T: show d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
    have hT_mem_X : x + T • v ∈ X := by rw [show S = _ from rfl] at hT_S; exact hT_S
    have h_bound_ev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0),
        d_V ≤ (f (x + T • v) (zc t) - f x (zc t)) / T := by
      filter_upwards [nhdsWithin_le_nhds (hS_open.mem_nhds h0_in_S),
        nhdsWithin_le_nhds (Iio_mem_nhds hT_pos_mem),
        self_mem_nhdsWithin (s := Ioi 0)] with t ht_S ht_lt ht_pos
      rw [mem_Ioi] at ht_pos; rw [mem_Iio] at ht_lt
      have ht_mem_X : x + t • v ∈ X := by rw [show S = _ from rfl] at ht_S; exact ht_S
      have h1 : d_V ≤ slope (fun s ↦ valueFunction f (x + s • v)) 0 t := by
        rw [show d_V = derivWithin _ _ _ from rfl]
        exact hg_convex.rightDeriv_le_slope_of_mem_interior h0_interior ht_S ht_pos
      have h_slope_eq : slope (fun s ↦ valueFunction f (x + s • v)) 0 t =
          (valueFunction f (x + t • v) - valueFunction f x) / t := by
        simp [slope, sub_zero, div_eq_inv_mul]
      -- (V(x+tv) - V(x))/t ≤ (f(x+tv, z_t) - f(x, z_t))/t
      have h2 : (valueFunction f (x + t • v) - valueFunction f x) / t ≤
          (f (x + t • v) (zc t) - f x (zc t)) / t := by
        apply div_le_div_of_nonneg_right _ (le_of_lt ht_pos)
        have hfx_le : f x (zc t) ≤ valueFunction f x :=
          le_ciSup ((isCompact_range hfx_cont).bddAbove) (zc t)
        rw [hzc_opt t ht_mem_X]; linarith
      -- slope g_{z_t} 0 t ≤ slope g_{z_t} 0 T
      have hgz : ConvexOn ℝ S (fun s ↦ f (x + s • v) (zc t)) :=
        (h_conv (zc t)).comp_affineMap ray
      have h_slt : slope (fun s ↦ f (x + s • v) (zc t)) 0 t =
          (f (x + t • v) (zc t) - f x (zc t)) / t := by
        simp [slope, sub_zero, div_eq_inv_mul]
      have h_slT : slope (fun s ↦ f (x + s • v) (zc t)) 0 T =
          (f (x + T • v) (zc t) - f x (zc t)) / T := by
        simp [slope, sub_zero, div_eq_inv_mul]
      have h3 := hgz.slope_mono h0_in_S ⟨ht_S, ne_of_gt ht_pos⟩
          ⟨hT_S, ne_of_gt (lt_trans ht_pos ht_lt)⟩ (le_of_lt ht_lt)
      rw [h_slt, h_slT] at h3
      linarith [h_slope_eq]
    -- Cluster point: d_V ≤ (f(x+Tv, z̄) - f(x, z̄))/T
    have hfT_cont : Continuous (fun z : Z ↦ f (x + T • v) z) :=
      ContinuousOnProd.continuous_right h_cont _ hT_mem_X
    have h_comp : MapClusterPt ((f (x + T • v) z_bar - f x z_bar) / T)
        (nhdsWithin (0 : ℝ) (Ioi 0))
        (fun t ↦ (f (x + T • v) (zc t) - f x (zc t)) / T) :=
      ((hfT_cont.sub hfx_cont).div_const T).continuousAt.mapClusterPt hz_cluster
    rw [hz_bar_opt] at h_comp ⊢
    by_contra hlt; push Not at hlt
    obtain ⟨t, ht1, ht2⟩ :=
      ((h_comp.frequently (Iio_mem_nhds hlt)).and_eventually h_bound_ev).exists
    exact absurd ht2 (not_le.mpr ht1)
  -- ## Step 4: Combine
  obtain ⟨zb, hzb, db, hdb, hle⟩ := h_upper_bound
  -- From Step 2: db ≤ d_V, from upper bound: d_V ≤ db, so d_V = db
  have h_eq : d_V = db := le_antisymm hle (h_lower_bound zb hzb db hdb)
  -- `d_V` is the maximum: attained at `zb` (upper bound) and dominating every optimizer (Step 2)
  exact ⟨d_V, hV_dir, ⟨zb, hzb, h_eq ▸ hdb⟩, h_lower_bound⟩


end Danskin
