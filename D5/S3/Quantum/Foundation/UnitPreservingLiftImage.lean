/- GID: D5/S3/Quantum/Foundation/UnitPreservingLiftImage
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/UnitPreservingLiftImage
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Retaining the original unit gives a closed full cone lift and exact cost perspective. -/

import D5.S3.Quantum.Foundation.RealRogFailureQuantitative
import Mathlib.Data.EReal.Basic

/-! The full original cone and its original unit are retained. The target readout
space is arbitrary; in the quantum application it is the original three-dimensional
chart coordinate space. No minimum, closed image, upper cost bound, positive
linear section, retraction, instrument or joint preparation is assumed. -/

noncomputable section
open Set Filter Topology

namespace D5.S3.Quantum.Foundation.UnitPreservingLiftImage

open CircuitBalancedConfirmation RealRogFailureQuantitative

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- All original cone lifts with unit g-mass and prescribed full readout. -/
def fiber (C : PointedCone ℝ V) (g : V →ₗ[ℝ] ℝ) (H : V →ₗ[ℝ] W) (z : W) : Set V :=
  {y | y ∈ C ∧ g y = 1 ∧ H y = z}

/-- The entire feasible readout domain. -/
def domain (C : PointedCone ℝ V) (g : V →ₗ[ℝ] ℝ) (H : V →ₗ[ℝ] W) : Set W :=
  {z | (fiber C g H z).Nonempty}

/-- Real value on the feasible domain; used only with domain membership. -/
def leastUnit (C : PointedCone ℝ V) (u g : V →ₗ[ℝ] ℝ)
    (H : V →ₗ[ℝ] W) (z : W) : ℝ := sInf (u '' fiber C g H z)

/-- Original lifting cost, with positive infinity on every infeasible readout. -/
def unitCost (C : PointedCone ℝ V) (u g : V →ₗ[ℝ] ℝ)
    (H : V →ₗ[ℝ] W) (z : W) : EReal := by
  classical
  exact if z ∈ domain C g H then (leastUnit C u g H z : EReal) else ⊤

/-- Retain the original unit together with the entire original readout. -/
def liftMap (u g : V →ₗ[ℝ] ℝ) (H : V →ₗ[ℝ] W) : V →ₗ[ℝ] ℝ × ℝ × W :=
  u.prod (g.prod H)

omit [FiniteDimensional ℝ V] in
private theorem unit_nonneg {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) {x : V} (hx : x ∈ C) : 0 ≤ u x := by
  by_cases hz : x = 0
  · simp [hz]
  · exact (hs x hx hz).le

private theorem minimum_lift {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}
    {H : V →ₗ[ℝ] W} (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) {z : W} (hz : z ∈ domain C g H) :
    ∃ y ∈ fiber C g H z, u y = leastUnit C u g H z ∧
      ∀ x ∈ fiber C g H z, u y ≤ u x := by
  obtain ⟨x₀, hx₀⟩ := hz
  have hR := unit_nonneg hs hx₀.1
  have hcap := mass_cap_compact C u (base_compact hc hs) hs (u x₀) hR
  let F := {x : V | x ∈ C ∧ u x ≤ u x₀ ∧ g x = 1 ∧ H x = z}
  have hF : IsCompact F := by
    convert hcap.inter_right
      ((isClosed_eq g.continuous_of_finiteDimensional
        (continuous_const : Continuous (fun _ : V => (1 : ℝ)))).inter
      (isClosed_eq H.continuous_of_finiteDimensional
        (continuous_const : Continuous (fun _ : V => z)))) using 1
    ext x
    exact and_assoc.symm
  obtain ⟨y, hy, hmin⟩ := hF.exists_isMinOn ⟨x₀, hx₀.1, le_rfl, hx₀.2⟩
    u.continuous_of_finiteDimensional.continuousOn
  have hyf : y ∈ fiber C g H z := ⟨hy.1, hy.2.2⟩
  have hglobal (x) (hx : x ∈ fiber C g H z) : u y ≤ u x := by
    by_cases hle : u x ≤ u x₀
    · exact hmin ⟨hx.1, hle, hx.2⟩
    · exact hy.2.1.trans (le_of_lt (lt_of_not_ge hle))
  refine ⟨y, hyf, ?_, hglobal⟩
  apply le_antisymm
  · exact le_csInf ⟨u y, mem_image_of_mem u hyf⟩ (by
      rintro r ⟨x, hx, rfl⟩; exact hglobal x hx)
  · exact csInf_le ⟨0, by rintro r ⟨x, hx, rfl⟩; exact unit_nonneg hs hx.1⟩
      (mem_image_of_mem u hyf)

private theorem closed_lift_image {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}
    {H : V →ₗ[ℝ] W} (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x) :
    IsClosed (liftMap u g H '' (C : Set V)) := by
  apply isSeqClosed_iff_isClosed.mp
  intro a w ha hw
  choose y hy he using ha
  have ht : Tendsto (fun n => u (y n)) atTop (𝓝 w.1) := by
    have heq : (fun n => u (y n)) = fun n => (a n).1 := by
      funext n; exact congrArg Prod.fst (he n)
    rw [heq]
    exact continuous_fst.tendsto w |>.comp hw
  obtain ⟨R, hR⟩ := ht.cauchySeq.isBounded_range.bddAbove
  have hR0 : 0 ≤ max 0 R := le_max_left _ _
  have hycap (n) : y n ∈ {x | x ∈ C ∧ u x ≤ max 0 R} :=
    ⟨hy n, (hR (mem_range_self n)).trans (le_max_right _ _)⟩
  obtain ⟨y₀, hy₀, φ, hφ, hlim⟩ :=
    (mass_cap_compact C u (base_compact hc hs) hs (max 0 R) hR0).tendsto_subseq hycap
  refine ⟨y₀, hy₀.1, ?_⟩
  have hl := (liftMap u g H).continuous_of_finiteDimensional.continuousAt.tendsto.comp hlim
  have hr := hw.comp hφ.tendsto_atTop
  have heq : (fun n => liftMap u g H (y (φ n))) = fun n => a (φ n) := by
    funext n; exact he (φ n)
  change Tendsto (fun n => liftMap u g H (y (φ n))) atTop _ at hl
  rw [heq] at hl
  exact tendsto_nhds_unique hl hr

omit [FiniteDimensional ℝ V] in
private theorem normalized_domain {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}
    {H : V →ₗ[ℝ] W} (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : V) (hp : p ∈ base C u) (hg : ∀ x ∈ C, 0 ≤ g x) (hgp : g p = 0)
    (hzero : ∀ x ∈ C, g x = 0 → ∃ t : ℝ, 0 ≤ t ∧ x = t • p) :
    domain C g H = {z | ∃ x ∈ base C u, x ≠ p ∧ (g x)⁻¹ • H x = z} := by
  ext z
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by intro h; simpa [h] using hy.2.1
    have hu : 0 < u y := hs y hy.1 hy0
    let x := (u y)⁻¹ • y
    have hx : x ∈ base C u := normalized_mem hs hy.1 hy0
    have hgx : g x = (u y)⁻¹ := by simp [x, map_smul, hy.2.1]
    refine ⟨x, hx, ?_, ?_⟩
    · intro he
      rw [he, hgp] at hgx
      exact (inv_ne_zero hu.ne') hgx.symm
    · rw [hgx]
      simp [x, map_smul, smul_smul, hu.ne', hy.2.2]
  · rintro ⟨x, hx, hxp, rfl⟩
    have hgx : 0 < g x := by
      apply lt_of_le_of_ne (hg x hx.1)
      intro he
      obtain ⟨t, ht, rfl⟩ := hzero x hx.1 he.symm
      have ht1 : t = 1 := by simpa [map_smul, hp.2] using hx.2
      exact hxp (by simp [ht1])
    refine ⟨(g x)⁻¹ • x, C.smul_mem (inv_nonneg.mpr hgx.le) hx.1, ?_, ?_⟩
    · simp [map_smul, hgx.ne']
    · simp [map_smul]

/-- The complete original cone image is closed and convex, is a cone, and is
exactly the perspective of the attained original unit cost. Its unit slice is
the compact convex image of the entire original normalized base. -/
theorem unit_preserving_lift_image {C : PointedCone ℝ V} {u g : V →ₗ[ℝ] ℝ}
    {H : V →ₗ[ℝ] W} (hc : IsClosed (C : Set V))
    (hs : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (p : V) (hp : p ∈ base C u)
    (hg : ∀ x ∈ C, 0 ≤ g x) (hgp : g p = 0) (hHp : H p = 0)
    (hzero : ∀ x ∈ C, g x = 0 → ∃ t : ℝ, 0 ≤ t ∧ x = t • p) :
    IsClosed (liftMap u g H '' (C : Set V)) ∧
    Convex ℝ (liftMap u g H '' (C : Set V)) ∧
    (∀ t : ℝ, 0 ≤ t → ∀ w ∈ liftMap u g H '' (C : Set V),
      t • w ∈ liftMap u g H '' (C : Set V)) ∧
    (∀ t s z, (t, s, z) ∈ liftMap u g H '' (C : Set V) ↔
      (0 ≤ t ∧ s = 0 ∧ z = 0) ∨
      (0 < s ∧ s⁻¹ • z ∈ domain C g H ∧
        s * leastUnit C u g H (s⁻¹ • z) ≤ t)) ∧
    IsCompact ((g.prod H) '' base C u) ∧ Convex ℝ ((g.prod H) '' base C u) ∧
    (∀ s z, (s, z) ∈ (g.prod H) '' base C u ↔
      (s = 0 ∧ z = 0) ∨
      (0 < s ∧ s⁻¹ • z ∈ domain C g H ∧
        s * leastUnit C u g H (s⁻¹ • z) ≤ 1)) ∧
    domain C g H = {z | ∃ x ∈ base C u, x ≠ p ∧ (g x)⁻¹ • H x = z} ∧
    (∀ z ∈ domain C g H, ∃ y ∈ fiber C g H z,
      unitCost C u g H z = (u y : EReal) ∧
      u y = leastUnit C u g H z ∧ ∀ x ∈ fiber C g H z, u y ≤ u x) ∧
    (∀ L : Submodule ℝ V, p ∈ L →
      ¬ ∃ v : (V ⧸ L) →ₗ[ℝ] ℝ, v.comp L.mkQ = u) := by
  have hH0 (x : V) (hx : x ∈ C) (hgz : g x = 0) : H x = 0 := by
    obtain ⟨t, ht, rfl⟩ := hzero x hx hgz
    simp [map_smul, hHp]
  have hmem (t s : ℝ) (z : W) :
      (t, s, z) ∈ liftMap u g H '' (C : Set V) ↔
      (0 ≤ t ∧ s = 0 ∧ z = 0) ∨
      (0 < s ∧ s⁻¹ • z ∈ domain C g H ∧
        s * leastUnit C u g H (s⁻¹ • z) ≤ t) := by
    constructor
    · rintro ⟨y, hy, he⟩
      have hut : u y = t := congrArg Prod.fst he
      have hgs : g y = s := congrArg (fun a : ℝ × ℝ × W => a.2.1) he
      have hHz : H y = z := congrArg (fun a : ℝ × ℝ × W => a.2.2) he
      have hs0 : 0 ≤ s := hgs ▸ hg y hy
      by_cases hsZ : s = 0
      · exact Or.inl ⟨hut ▸ unit_nonneg hs hy, hsZ, hHz ▸ hH0 y hy (hgs.trans hsZ)⟩
      have hsP : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hsZ)
      have hyf : s⁻¹ • y ∈ fiber C g H (s⁻¹ • z) := by
        refine ⟨C.smul_mem (inv_nonneg.mpr hs0) hy, ?_, ?_⟩
        · simp [map_smul, hgs, hsZ]
        · simp [map_smul, hHz]
      have hzD : s⁻¹ • z ∈ domain C g H := ⟨_, hyf⟩
      obtain ⟨ym, hym, hm, hmin⟩ := minimum_lift hc hs hzD
      refine Or.inr ⟨hsP, hzD, ?_⟩
      have hl := mul_le_mul_of_nonneg_left (hmin _ hyf) hs0
      simpa [hm, map_smul, hut, ← mul_assoc, hsZ] using hl
    · rintro (⟨ht, rfl, rfl⟩ | ⟨hsP, hzD, hcost⟩)
      · refine ⟨t • p, C.smul_mem ht hp.1, ?_⟩
        simp [liftMap, map_smul, hp.2, hgp, hHp]
      · obtain ⟨y, hy, hm, hmin⟩ := minimum_lift hc hs hzD
        let r := t - s * u y
        have hr : 0 ≤ r := by dsimp [r]; rw [hm]; linarith
        refine ⟨s • y + r • p, C.add_mem (C.smul_mem hsP.le hy.1)
          (C.smul_mem hr hp.1), ?_⟩
        apply Prod.ext
        · change u (s • y + r • p) = t
          simp [map_add, map_smul, hp.2, r]
        · apply Prod.ext
          · change g (s • y + r • p) = s
            simp [map_add, map_smul, hy.2.1, hgp]
          · change H (s • y + r • p) = z
            simp [map_add, map_smul, hy.2.2, hHp, smul_smul, hsP.ne']
  refine ⟨closed_lift_image hc hs, C.convex.linear_image (liftMap u g H), ?_,
    hmem, (base_compact hc hs).image (g.prod H).continuous_of_finiteDimensional,
    (base_convex C u).linear_image (g.prod H), ?_,
    normalized_domain hs p hp hg hgp hzero, ?_, ?_⟩
  · rintro t ht w ⟨y, hy, rfl⟩
    exact ⟨t • y, C.smul_mem ht hy, map_smul _ _ _⟩
  · intro s z
    have hslice : (s, z) ∈ (g.prod H) '' base C u ↔
        (1, s, z) ∈ liftMap u g H '' (C : Set V) := by
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨y, hy.1, Prod.ext hy.2 he⟩
      · rintro ⟨y, hy, he⟩
        exact ⟨y, ⟨hy, congrArg Prod.fst he⟩, congrArg Prod.snd he⟩
    rw [hslice, hmem]
    simp
  · intro z hz
    obtain ⟨y, hy, hm, hmin⟩ := minimum_lift hc hs hz
    exact ⟨y, hy, by simp [unitCost, hz, hm], hm, hmin⟩
  · rintro L hpL ⟨v, hv⟩
    have he := LinearMap.congr_fun hv p
    change v (L.mkQ p) = u p at he
    rw [show L.mkQ p = 0 from (Submodule.Quotient.mk_eq_zero L).mpr hpL,
      map_zero, hp.2] at he
    norm_num at he

#print axioms unit_preserving_lift_image

end D5.S3.Quantum.Foundation.UnitPreservingLiftImage
