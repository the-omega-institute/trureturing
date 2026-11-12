/- GID: D5/S3/Quantum/Foundation/WholeExclusionSupport
   generality: G
   mirror-B: D5/B/S3/Quantum/Foundation/WholeExclusionSupport
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Global positivity from vanishing on an entire original exclusion set. -/

import D5.S3.Quantum.Foundation.FacetZeroGluing

/-! A normalization prerequisite for original three-effect completion. -/

noncomputable section

namespace D5.S3.Quantum.Foundation.WholeExclusionSupport

open CircuitBalancedConfirmation FacetZeroGluing

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- An original linear candidate, bounded above by the original unit and equal
to one at an original pure point, is proper if it vanishes on that point's
entire original exclusion set. Positivity is a conclusion, not an input. -/
theorem whole_exclusion_support {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (r : pure C u) (h : V →ₗ[ℝ] ℝ) (hr : h r = 1)
    (hupper : ∀ x ∈ C, h x ≤ u x)
    (hzero : ∀ x ∈ exclusion C u r, h x = 0) : confirms C u r h := by
  have hK := base_compact hclosed hstrict
  obtain ⟨x, hx, hmin⟩ := hK.exists_isMinOn ⟨r, pure_mem r⟩
    h.continuous_of_finiteDimensional.continuousOn
  have hnonneg : 0 ≤ h x := by
    by_contra! hneg
    let c : ℝ := h x
    have hc : c < 0 := hneg
    have hd : 0 < 1 - c := by linarith
    let g : V →ₗ[ℝ] ℝ := (1 - c)⁻¹ • (h - c • u)
    have hgproper : proper C u g := cone_bound hK hstrict (by
      intro p
      have hcp : c ≤ h p := hmin (pure_mem p)
      have hpu : u p = 1 := (pure_mem p).2
      have hpupper : h p ≤ 1 := by simpa only [hpu] using hupper p (pure_mem p).1
      change 0 ≤ (1 - c)⁻¹ * (h p - c * u p) ∧
        (1 - c)⁻¹ * (h p - c * u p) ≤ 1
      rw [hpu, mul_one]
      constructor
      · exact mul_nonneg (inv_nonneg.mpr hd.le) (sub_nonneg.mpr hcp)
      · rw [← div_eq_inv_mul, div_le_one hd]
        linarith)
    have hgr : g r = 1 := by
      simp [g, hr, (pure_mem r).2, ne_of_gt hd]
    have hgx : g x = 0 := by
      simp [g, hx.2, c]
    have hxD : x ∈ exclusion C u r := ⟨hx, g, ⟨hgproper, hgr⟩, hgx⟩
    have hz := hzero x hxD
    linarith
  refine ⟨?_, hr⟩
  intro y hy
  refine ⟨nonneg_on_cone hK hstrict (fun p => hnonneg.trans (hmin (pure_mem p))) y hy,
    hupper y hy⟩



/-- A finite normalized spanning probe set has a nonzero positive functional
whose zero probes span its entire kernel. -/
private theorem finite_zero_span {P : Set V} [Finite P]
    (hspan : Submodule.span ℝ P = ⊤) (u : V →ₗ[ℝ] ℝ)
    (hu : ∀ p ∈ P, u p = 1) (hu0 : u ≠ 0) :
    ∃ f : V →ₗ[ℝ] ℝ, f ≠ 0 ∧ (∀ p ∈ P, 0 ≤ f p) ∧
      Submodule.span ℝ {p | p ∈ P ∧ f p = 0} = LinearMap.ker f := by
  classical
  let Z (f : V →ₗ[ℝ] ℝ) := Submodule.span ℝ {p | p ∈ P ∧ f p = 0}
  let Q (f : V →ₗ[ℝ] ℝ) := f ≠ 0 ∧ ∀ p ∈ P, 0 ≤ f p
  have hZ (f : V →ₗ[ℝ] ℝ) : Z f ≤ LinearMap.ker f :=
    Submodule.span_le.mpr (fun _ hp => hp.2)
  let ranks := (Finset.range (Module.finrank ℝ V + 1)).filter
    (fun n => ∃ f, Q f ∧ Module.finrank ℝ (Z f) = n)
  have rank_mem (f : V →ₗ[ℝ] ℝ) (hf : Q f) :
      Module.finrank ℝ (Z f) ∈ ranks := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by
      have hh := (Z f).finrank_le
      omega), f, hf, rfl⟩
  have huQ : Q u := ⟨hu0, fun p hp => by rw [hu p hp]; norm_num⟩
  obtain ⟨n, hn, hmax⟩ := ranks.exists_max_image id ⟨_, rank_mem u huQ⟩
  obtain ⟨f, hf, hfn⟩ := (Finset.mem_filter.mp hn).2
  refine ⟨f, hf.1, hf.2, ?_⟩
  by_contra hne
  have hlt : Z f < LinearMap.ker f := lt_of_le_of_ne (hZ f) hne
  obtain ⟨x, hx, hxZ⟩ := Set.exists_of_ssubset hlt
  obtain ⟨a, hax, haZ⟩ := Submodule.exists_le_ker_of_notMem hxZ
  have haP : ∃ q ∈ P, a q ≠ 0 := by
    by_contra! h
    have hh : Submodule.span ℝ P ≤ LinearMap.ker a := Submodule.span_le.mpr h
    rw [hspan] at hh
    have ha0 := LinearMap.ker_eq_top.mp (top_le_iff.mp hh)
    exact hax (by simp [ha0])
  obtain ⟨q, hq, haq⟩ := haP
  let b : V →ₗ[ℝ] ℝ := if 0 < a q then -a else a
  have hbq : b q < 0 := by
    dsimp [b]
    split_ifs with h
    · simpa using neg_neg_of_pos h
    · exact lt_of_le_of_ne (le_of_not_gt h) haq
  have hbZ : Z f ≤ LinearMap.ker b := by
    intro y hy
    have hay : a y = 0 := haZ hy
    dsimp [b]
    split_ifs <;> simpa [hay]
  have hbx : b x ≠ 0 := by
    dsimp [b]
    split_ifs <;> simpa using hax
  letI := Fintype.ofFinite P
  let N : Finset P := Finset.univ.filter (fun p : P => b p < 0)
  have hN : N.Nonempty := ⟨⟨q, hq⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbq⟩⟩
  have hfpos (p : P) (hp : p ∈ N) : 0 < f p := by
    have hbp := (Finset.mem_filter.mp hp).2
    apply lt_of_le_of_ne (hf.2 p p.property)
    intro he
    have hz : (p : V) ∈ Z f := Submodule.subset_span ⟨p.property, he.symm⟩
    have hh : b p = 0 := hbZ hz
    linarith
  obtain ⟨p, hp, hmin⟩ := N.exists_min_image (fun p : P => f p / (-b p)) hN
  let t : ℝ := f p / (-b p)
  have hbp : b p < 0 := (Finset.mem_filter.mp hp).2
  have ht : 0 < t := div_pos (hfpos p hp) (neg_pos.mpr hbp)
  let g : V →ₗ[ℝ] ℝ := f + t • b
  have hgpos : ∀ y ∈ P, 0 ≤ g y := by
    intro y hy
    change 0 ≤ f y + t * b y
    by_cases hby : b y < 0
    · have hyt : t ≤ f y / (-b y) := hmin ⟨y, hy⟩
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hby⟩)
      have hh := (le_div_iff₀ (neg_pos.mpr hby)).mp hyt
      nlinarith
    · exact add_nonneg (hf.2 y hy) (mul_nonneg ht.le (le_of_not_gt hby))
  have hgp : g p = 0 := by
    change f p + (f p / (-b p)) * b p = 0
    field_simp
    <;> ring
  have hg0 : g ≠ 0 := by
    intro he
    have hgx : g x = 0 := by simp [he]
    have hfx : f x = 0 := hx
    change f x + t * b x = 0 at hgx
    rw [hfx, zero_add] at hgx
    exact hbx ((mul_eq_zero.mp hgx).resolve_left ht.ne')
  have hle : Z f ≤ Z g := by
    apply Submodule.span_le.mpr
    intro y hy
    have hyZ : y ∈ Z f := Submodule.subset_span hy
    have hby : b y = 0 := hbZ hyZ
    exact Submodule.subset_span ⟨hy.1, by simp [g, hy.2, hby]⟩
  have hstrict : Z f < Z g := by
    apply lt_of_le_of_ne hle
    intro he
    have hpZ : (p : V) ∈ Z g := Submodule.subset_span ⟨p.property, hgp⟩
    rw [← he] at hpZ
    have hh : b p = 0 := hbZ hpZ
    linarith
  have hdim := Submodule.finrank_lt_finrank_of_lt hstrict
  have hbound := hmax _ (rank_mem g ⟨hg0, hgpos⟩)
  change Module.finrank ℝ (Z g) ≤ n at hbound
  omega

/-- Finiteness of all original pure points supplies a native codimension-one
face of the original cone. No EB, pair, zero-gluing or frame premise is needed. -/
theorem finite_pure_facet [Nontrivial V]
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ} [Finite (pure C u)]
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hgen : Submodule.span ℝ (C : Set V) = ⊤) : Nonempty (facets C) := by
  have hK := base_compact hclosed hstrict
  have hP := pure_span hK hstrict hgen
  have hu0 : u ≠ 0 := by
    intro he
    have hnone : pure C u = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hh := (pure_mem (⟨p, hp⟩ : pure C u)).2
      simpa [he] using hh
    rw [hnone, Submodule.span_empty] at hP
    exact bot_ne_top hP
  obtain ⟨f, hf0, hfP, hzero⟩ := finite_zero_span hP u
    (fun p hp => (pure_mem (⟨p, hp⟩ : pure C u)).2) hu0
  have hfC : ∀ x ∈ C, 0 ≤ f x := nonneg_on_cone hK hstrict (fun p => hfP p p.property)
  let F : PointedCone.Face C :=
    { toSubmodule := C ⊓ (LinearMap.ker f : PointedCone ℝ V)
      isFaceOf :=
        { le := inf_le_left
          mem_of_smul_add_mem := by
            intro x y a hx hy ha hxy
            refine ⟨hx, ?_⟩
            have hh : a * f x + f y = 0 := by
              simpa only [map_add, map_smul, smul_eq_mul] using hxy.2
            have hfx := hfC x hx
            have hfy := hfC y hy
            change f x = 0
            nlinarith } }
  have hspanF : Submodule.span ℝ (F : Set V) = LinearMap.ker f := by
    apply le_antisymm
    · exact Submodule.span_le.mpr (fun _ hx => hx.2)
    · rw [← hzero]
      apply Submodule.span_mono
      intro p hp
      exact ⟨(pure_mem (⟨p, hp.1⟩ : pure C u)).1, hp.2⟩
  refine ⟨⟨F, ?_⟩⟩
  rw [hspanF]
  exact Module.Dual.finrank_ker_add_one_of_ne_zero hf0

#print axioms whole_exclusion_support
#print axioms finite_pure_facet

end D5.S3.Quantum.Foundation.WholeExclusionSupport
