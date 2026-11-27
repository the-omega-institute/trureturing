/- GID: D5/S3/Combinatorics/Lattices/EuclideanSlopeMorphism
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Lattices/EuclideanSlopeMorphism
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Integral maps of Euclidean lattices respect Harder--Narasimhan slopes. -/

import D5.S3.Combinatorics.Lattices.EuclideanHarderNarasimhan
import Mathlib.Analysis.InnerProductSpace.NormDet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism

open Module Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

private theorem normDet_bound (f : E →ₗ[ℝ] F) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖) : f.normDet ≤ C ^ finrank ℝ E := by
  rw [f.normDet_eq_prod_singularValues]
  calc
    ∏ i ∈ range (finrank ℝ E), f.singularValues i ≤
        ∏ _i ∈ range (finrank ℝ E), C := by
      apply prod_le_prod₀
      · intro i _
        exact f.singularValues_nonneg i
      · intro i hi
        let j : Fin (finrank ℝ E) := ⟨i, mem_range.mp hi⟩
        let S := f.isSymmetric_adjoint_comp_self
        let b := S.eigenvectorBasis rfl
        have hb : ‖b j‖ = 1 := b.orthonormal.norm_eq_one j
        have he : ‖f (b j)‖ ^ 2 = S.eigenvalues rfl j := by
          have h := S.apply_eigenvectorBasis rfl j
          have hinner := congrArg (fun x => inner ℝ (b j) x) h
          change inner ℝ (b j) (f.adjoint (f (b j))) =
            inner ℝ (b j) (S.eigenvalues rfl j • b j) at hinner
          simpa only [LinearMap.adjoint_inner_right, real_inner_smul_right,
            real_inner_self_eq_norm_sq, hb, one_pow, mul_one] using hinner
        have hbound := hf (b j)
        rw [hb, mul_one] at hbound
        have hsq := f.sq_singularValues_fin rfl j
        change f.singularValues i ^ 2 = _ at hsq
        rw [← he] at hsq
        have hnorm : ‖f (b j)‖ ^ 2 ≤ C ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _) hC).mpr hbound
        exact le_of_sq_le_sq (hsq.le.trans hnorm) hC
    _ = C ^ finrank ℝ E := by simp

private def combination {ι : Type*} [Fintype ι] (v : ι → E) :
    EuclideanSpace ℝ ι →ₗ[ℝ] E where
  toFun x := ∑ i, x i • v i
  map_add' x y := by simp [add_smul, sum_add_distrib]
  map_smul' c x := by simp [smul_sum, smul_smul]

private theorem gram_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : E →ₗ[ℝ] F) (v : ι → E) (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ x, ‖f x‖ ≤ C * ‖x‖) :
    (Matrix.gram ℝ (fun i => f (v i))).det ≤
      C ^ (2 * Fintype.card ι) * (Matrix.gram ℝ v).det := by
  let g := combination v
  have hv : ∀ i, g (EuclideanSpace.basisFun ι ℝ i) = v i := by
    intro i
    simp [g, combination, EuclideanSpace.basisFun_apply,
      PiLp.single_apply, ite_smul]
  have hvg := g.normDet_sq_eq_det_gram (EuclideanSpace.basisFun ι ℝ)
  have hwg := (f ∘ₗ g).normDet_sq_eq_det_gram (EuclideanSpace.basisFun ι ℝ)
  simp only [LinearMap.comp_apply, hv] at hvg hwg
  rw [← hwg, ← hvg, LinearMap.normDet_comp]
  have hbound := normDet_bound (f.domRestrict g.range) C hC (fun x => hf x)
  have hfin : finrank ℝ g.range = Fintype.card ι ∨ g.normDet = 0 := by
    by_cases hg : Function.Injective g
    · exact Or.inl (by simpa using LinearMap.finrank_range_of_inj hg)
    · exact Or.inr (g.normDet_eq_zero_iff_ker_ne_bot.mpr
        (fun hk => hg (LinearMap.ker_eq_bot.mp hk)))
  rcases hfin with hr | hg
  · rw [hr] at hbound
    have hm := mul_le_mul_of_nonneg_right hbound g.normDet_nonneg
    calc
      ((f.domRestrict g.range).normDet * g.normDet) ^ 2 ≤
          (C ^ Fintype.card ι * g.normDet) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (LinearMap.normDet_nonneg _) g.normDet_nonneg) hm 2
      _ = C ^ (2 * Fintype.card ι) * g.normDet ^ 2 := by ring
  · simp [hg]

open EuclideanSublattices EuclideanHarderNarasimhan HarderNarasimhan

private def sectionLattice (L : Submodule ℤ E) (W : Submodule ℝ E) : Sublattice L := by
  refine ⟨(W.restrictScalars ℤ).comap L.subtype, ?_⟩
  change
    ((Submodule.span ℝ
      (((W.restrictScalars ℤ).comap L.subtype).map L.subtype : Set E)).restrictScalars ℤ).comap
      L.subtype = (W.restrictScalars ℤ).comap L.subtype
  apply le_antisymm
  · intro x hx
    change (x : E) ∈ W
    change (x : E) ∈ Submodule.span ℝ
      (((W.restrictScalars ℤ).comap L.subtype).map L.subtype : Set E) at hx
    have hs : Submodule.span ℝ
        (((W.restrictScalars ℤ).comap L.subtype).map L.subtype : Set E) ≤ W :=
      Submodule.span_le.mpr (by
      rintro _ ⟨y, hy, rfl⟩
      exact hy)
    exact hs hx
  · intro x hx
    exact Submodule.subset_span ⟨x, hx, rfl⟩

private theorem integral_section (L : Submodule ℤ E) (W : Submodule ℝ E) :
    integral L (sectionLattice L W) = L ⊓ W.restrictScalars ℤ := by
  change ((W.restrictScalars ℤ).comap L.subtype).map L.subtype = _
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨⟨x, hx⟩, hy, rfl⟩

private theorem section_span (L M : Submodule ℤ E) (hML : M ≤ L) :
    Submodule.span ℝ
      (integral L (sectionLattice L (Submodule.span ℝ (M : Set E))) : Set E) =
      Submodule.span ℝ (M : Set E) := by
  rw [integral_section]
  apply le_antisymm
  · exact Submodule.span_le.mpr fun _ hx => hx.2
  · apply Submodule.span_mono
    intro x hx
    exact ⟨hML hx, Submodule.subset_span hx⟩

private theorem slope_extreme_bounds {Λ : Type*} [Lattice Λ] (D : SlopeData Λ)
    {a b : Λ} (hab : a < b) :
    (∀ x, a ≤ x → x < b → D.muMin a b ≤ D.slope x b) ∧
    (∀ x, a < x → x ≤ b → D.slope a x ≤ D.muMax a b) := by
  obtain ⟨l, hl, _⟩ := (exists_unique_filtration D a b).mpr hab.le
  cases l with
  | nil =>
    cases hl
    exact (lt_irrefl _ hab).elim
  | cons e l =>
    have h := filtration_extremes D a b e l hl
    refine ⟨?_, ?_⟩
    · intro x hax hxb
      rw [h.2.2.2.2.2.1]
      exact h.2.2.2.1.2 ⟨x, hax, hxb, rfl⟩
    · intro x hax hxb
      rw [h.2.2.2.2.1]
      exact h.2.2.1.2 ⟨x, hax, hxb, rfl⟩

private theorem gram_projection_split {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (v : ι → E) (w : κ → E) :
    let W := Submodule.span ℝ (Set.range v)
    (Matrix.gram ℝ (Sum.elim v w)).det = (Matrix.gram ℝ v).det *
      (Matrix.gram ℝ (fun j => Wᗮ.starProjection (w j))).det := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  let P := Wᗮ.starProjection
  have hdiff (j : κ) : w j - P (w j) ∈ W := by
    simpa only [Submodule.orthogonal_orthogonal] using
      Wᗮ.sub_starProjection_mem_orthogonal (w j)
  have hcoeff (j : κ) : ∃ a : ι → ℝ, ∑ i, a i • v i = w j - P (w j) :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp (hdiff j)
  choose a ha using hcoeff
  let z : ι ⊕ κ → E := Sum.elim v (fun j => P (w j))
  let T : Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
    Matrix.fromBlocks 1 (Matrix.of fun i j => a j i) 0 1
  have hT : T.det = 1 := by
    simp only [T]
    rw [Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, Matrix.det_one, one_mul]
  have hvw : Sum.elim v w = fun j => ∑ i, T i j • z i := by
    funext j
    rw [Fintype.sum_sum_type]
    cases j with
    | inl j => simp [T, z, Matrix.one_apply, ite_smul]
    | inr j =>
      simp only [T, z, Sum.elim_inl, Sum.elim_inr,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.one_apply,
        Matrix.of_apply, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, ite_true]
      rw [ha, sub_add_cancel]
  have hzero (i : ι) (j : κ) : inner ℝ (v i) (P (w j)) = 0 := by
    exact (Submodule.mem_orthogonal W _).mp
      ((Wᗮ.orthogonalProjection (w j)).property) (v i) (Submodule.subset_span ⟨i, rfl⟩)
  have hblock : Matrix.gram ℝ z =
      Matrix.fromBlocks (Matrix.gram ℝ v) 0 0 (Matrix.gram ℝ (fun j => P (w j))) := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => rfl
      | inr j => exact hzero i j
    | inr i =>
      cases j with
      | inl j =>
        change inner ℝ (P (w i)) (v j) = 0
        rw [real_inner_comm]
        exact hzero j i
      | inr j => rfl
  change (Matrix.gram ℝ (Sum.elim v w)).det = _
  rw [hvw, gram_linear_combination, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    hT, hblock, Matrix.det_fromBlocks_zero₂₁, one_mul, mul_one]

private def imageBasis {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (N K : Submodule ℤ E) (f : E →ₗ[ℝ] F)
    (c : Basis ι ℤ K) (b : Basis (ι ⊕ κ) ℤ N)
    (hleft : ∀ i, (b (Sum.inl i) : E) = c i)
    (hker : ∀ x ∈ N, f x = 0 ↔ x ∈ K) :
    Basis κ ℤ (N.map (f.restrictScalars ℤ)) := by
  classical
  let y : κ → N.map (f.restrictScalars ℤ) := fun j =>
    ⟨f (b (Sum.inr j)), Submodule.mem_map_of_mem (b (Sum.inr j)).property⟩
  have hzero (i : ι) : f (b (Sum.inl i)) = 0 := by
    apply (hker _ (b (Sum.inl i)).property).mpr
    rw [hleft]
    exact (c i).property
  have hli : LinearIndependent ℤ y := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    let x : N := ∑ j, a j • b (Sum.inr j)
    have hfx : f x = 0 := by
      have h := congrArg Subtype.val ha
      simpa only [y, x, Submodule.coe_sum, Submodule.coe_smul,
        map_sum, map_zsmul, Submodule.coe_zero] using h
    have hx : (x : E) ∈ K := (hker x x.property).mp hfx
    let k : K := ⟨x, hx⟩
    have hrel : ∑ j, (Sum.elim (fun i => -c.repr k i) a j) • b j = 0 := by
      apply Subtype.ext
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, sum_neg_distrib,
        Submodule.coe_add, Submodule.coe_neg, Submodule.coe_sum, Submodule.coe_smul]
      simp_rw [hleft]
      have hc := congrArg Subtype.val (c.sum_repr k)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at hc
      rw [hc]
      simpa only [k, x, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero]
        using neg_add_cancel (x : E)
    intro j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent _ hrel (Sum.inr j)
  refine Basis.mk hli ?_
  rintro ⟨z, x, hx, rfl⟩ -
  let xn : N := ⟨x, hx⟩
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun j => b.repr xn (Sum.inr j), ?_⟩
  apply Subtype.ext
  have h := congrArg (fun t : N => f (t : E)) (b.sum_repr xn)
  simp only [Fintype.sum_sum_type, Submodule.coe_add, Submodule.coe_sum,
    Submodule.coe_smul, map_add, map_sum, map_zsmul,
    hzero, smul_zero, sum_const_zero, zero_add] at h
  simpa only [y, xn, Submodule.coe_sum, Submodule.coe_smul,
    LinearMap.restrictScalars_apply] using h

theorem integral_top (L : Submodule ℤ E) : integral L ⊤ = L := by
  change (⊤ : Submodule ℤ L).map L.subtype = L
  simp

private def relativeImageBasis {ι σ κ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    [Fintype κ] [DecidableEq κ]
    (N K : Submodule ℤ E) (A : Submodule ℤ F) (f : E →ₗ[ℝ] F) (p : F →ₗ[ℝ] F)
    (c : Basis ι ℤ K) (b : Basis (ι ⊕ κ) ℤ N) (v : Basis σ ℤ A)
    (hleft : ∀ i, (b (Sum.inl i) : E) = c i)
    (hpA : ∀ z ∈ A, p z = 0)
    (hker : ∀ x ∈ N, p (f x) = 0 ↔ x ∈ K)
    (hfK : ∀ x ∈ K, f x ∈ A) :
    Basis (σ ⊕ κ) ℤ (A ⊔ N.map (f.restrictScalars ℤ) : Submodule ℤ F) := by
  classical
  let T := A ⊔ N.map (f.restrictScalars ℤ)
  let d := imageBasis N K (p ∘ₗ f) c b hleft hker
  have hd (j : κ) : (d j : F) = p (f (b (Sum.inr j))) := by
    simp only [d, imageBasis, Basis.mk_apply]
    rfl
  let iA : A →ₗ[ℤ] T := Submodule.inclusion le_sup_left
  let g : N →ₗ[ℤ] T :=
    ((f.restrictScalars ℤ).domRestrict N).codRestrict T
      (fun z => (show N.map (f.restrictScalars ℤ) ≤ T from le_sup_right)
        (Submodule.mem_map_of_mem z.property))
  let y : σ ⊕ κ → T := Sum.elim (fun i => iA (v i)) (fun j => g (b (Sum.inr j)))
  have hpv (i : σ) : p (v i) = 0 := hpA _ (v i).property
  have hli : LinearIndependent ℤ y := by
    rw [Fintype.linearIndependent_iff]
    intro a ha
    have hpa := congrArg (fun z : T => p (z : F)) ha
    simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
      map_add, map_sum, map_zsmul, map_zero, Fintype.sum_sum_type, y,
      Sum.elim_inl, Sum.elim_inr] at hpa
    change (∑ i, a (Sum.inl i) • p (v i)) +
      (∑ j, a (Sum.inr j) • p (f (b (Sum.inr j)))) = 0 at hpa
    simp only [hpv, smul_zero, sum_const_zero, zero_add] at hpa
    have hz : ∑ j, a (Sum.inr j) • d j = 0 := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero, hd] using hpa
    have hr (j : κ) : a (Sum.inr j) = 0 :=
      Fintype.linearIndependent_iff.mp d.linearIndependent _ hz j
    have hl : ∑ i, a (Sum.inl i) • v i = 0 := by
      apply Subtype.ext
      have h := congrArg Subtype.val ha
      simp only [Submodule.coe_add, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero,
        Fintype.sum_sum_type, y, Sum.elim_inl, Sum.elim_inr,
        hr, zero_smul, sum_const_zero, add_zero] at h
      simpa only [iA, Submodule.coe_inclusion, Submodule.coe_sum,
        Submodule.coe_smul, Submodule.coe_zero] using h
    intro j
    cases j with
    | inl i => exact Fintype.linearIndependent_iff.mp v.linearIndependent _ hl i
    | inr j => exact hr j
  have hA (z : A) : iA z ∈ Submodule.span ℤ (Set.range y) := by
    rw [← v.sum_repr z, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hF (z : N) : g z ∈ Submodule.span ℤ (Set.range y) := by
    rw [← b.sum_repr z, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul]
    apply Submodule.smul_mem
    cases i with
    | inl i =>
      have hz : f (b (Sum.inl i)) ∈ A := by
        rw [hleft]
        exact hfK _ (c i).property
      have he : g (b (Sum.inl i)) = iA ⟨f (b (Sum.inl i)), hz⟩ := by
        apply Subtype.ext
        rfl
      rw [he]
      exact hA _
    | inr j => exact Submodule.subset_span ⟨Sum.inr j, rfl⟩
  refine Basis.mk hli ?_
  rintro ⟨z, hz⟩ -
  obtain ⟨a, ha, w, hw, haw⟩ := Submodule.mem_sup.mp hz
  obtain ⟨n, hn, hfn⟩ := hw
  simp only [LinearMap.restrictScalars_apply] at hfn
  have he : (⟨z, hz⟩ : T) = iA ⟨a, ha⟩ + g ⟨n, hn⟩ := by
    apply Subtype.ext
    change z = a + f n
    rw [hfn]
    exact haw.symm
  rw [he]
  exact Submodule.add_mem _ (hA _) (hF _)

private theorem relative_full_slope_morphism (N : Submodule ℤ E) (C : Submodule ℤ F)
    [DiscreteTopology N] [DiscreteTopology C] (β : Sublattice C)
    (f : E →L[ℝ] F) (h : ℝ) (hfC : ∀ x ∈ N, f x ∈ C)
    (hfmod : ∃ x ∈ N, f x ∉ Submodule.span ℝ (integral C β : Set F))
    (hf : ∀ x, ‖(Submodule.span ℝ (integral C β : Set F))ᗮ.starProjection (f x)‖ ≤
      Real.exp h * ‖x‖) :
    (slopeData N).muMin ⊥ ⊤ ≤ (slopeData C).muMax β ⊤ + h := by
  classical
  let B := integral C β
  let U := Submodule.span ℝ (B : Set F)
  let p := Uᗮ.starProjection
  let g := p.toLinearMap ∘ₗ f.toLinearMap
  have hpzero (y : F) : p y = 0 ↔ y ∈ U := by
    simpa only [Submodule.orthogonal_orthogonal] using
      (Submodule.starProjection_apply_eq_zero_iff (K := Uᗮ) (v := y))
  have hBC : B ≤ C := integral_le C β
  have hBsaturated (y : F) (hy : y ∈ C) (hu : y ∈ U) : y ∈ B :=
    integral_saturated C β y hy hu
  let k := sectionLattice N g.ker
  let K := integral N k
  have hK : K = N ⊓ g.ker.restrictScalars ℤ := integral_section N g.ker
  have hKN : K ≤ N := by rw [hK]; exact inf_le_left
  letI : DiscreteTopology K := DiscreteTopology.of_subset inferInstance hKN
  letI : DiscreteTopology (K ⊓ N : Submodule ℤ E) :=
    DiscreteTopology.of_subset (inferInstance : DiscreteTopology N) inf_le_right
  have hker (x : E) (hx : x ∈ N) : g x = 0 ↔ x ∈ K := by
    rw [hK]
    exact ⟨fun hz => ⟨hx, hz⟩, fun hz => hz.2⟩
  have hkill : Submodule.span ℝ (K : Set E) ≤ g.ker :=
    Submodule.span_le.mpr fun x hx => (hker x (hKN hx)).mpr hx
  have hsat (x : E) (hx : x ∈ N) (hs : x ∈ Submodule.span ℝ (K : Set E)) : x ∈ K :=
    (hker x hx).mp (hkill hs)
  have hfK (x : E) (hx : x ∈ K) : f x ∈ B :=
    hBsaturated _ (hfC x (hKN hx)) ((hpzero _).mp ((hker x (hKN hx)).mpr hx))
  let c₀ := Module.finBasis ℤ (K ⊓ N : Submodule ℤ E)
  let ad := EuclideanSaturation.adaptedBasesOfSaturated (K := ℝ) N K N hKN le_rfl
    hsat (fun _ hx _ => hx) c₀
  let c := c₀.map (LinearEquiv.ofEq (K ⊓ N) K (inf_eq_left.mpr hKN))
  let b := ad.b
  have hleft (i : Fin (finrank ℤ (K ⊓ N : Submodule ℤ E))) :
      (b (Sum.inl i) : E) = c i := by
    simpa only [c, Basis.map_apply, LinearEquiv.coe_ofEq_apply] using ad.b_left i
  let Im := N.map (g.restrictScalars ℤ)
  let d := imageBasis N K g c b hleft hker
  let T := B ⊔ N.map (f.toLinearMap.restrictScalars ℤ)
  have hTC : T ≤ C := by
    apply sup_le hBC
    rintro _ ⟨x, hx, rfl⟩
    exact hfC x hx
  letI : DiscreteTopology T := DiscreteTopology.of_subset inferInstance hTC
  let vB := Module.finBasis ℤ B
  let dT := relativeImageBasis N K B f.toLinearMap p.toLinearMap c b vB hleft
    (fun z hz => (hpzero z).mpr (Submodule.subset_span hz)) hker hfK
  let j := sectionLattice C (Submodule.span ℝ (T : Set F))
  let J := integral C j
  have hJ : J = C ⊓ (Submodule.span ℝ (T : Set F)).restrictScalars ℤ :=
    integral_section C (Submodule.span ℝ (T : Set F))
  have hJC : J ≤ C := by rw [hJ]; exact inf_le_left
  letI : DiscreteTopology J := DiscreteTopology.of_subset inferInstance hJC
  have hTJ : T ≤ J := by
    intro y hy
    rw [hJ]
    exact ⟨hTC hy, Submodule.subset_span hy⟩
  have hspan : Submodule.span ℝ (T : Set F) = Submodule.span ℝ (J : Set F) :=
    (section_span C T hTC).symm
  let v := fun i => (c i : E)
  let w := fun i => (b (Sum.inr i) : E)
  let W := Submodule.span ℝ (Set.range v)
  let P := Wᗮ.starProjection
  have hspanK : W = Submodule.span ℝ (K : Set E) := by
    have hc : Submodule.span ℤ (Set.range v) = K := by
      rw [show Set.range v = K.subtype '' Set.range c from Set.range_comp _ _,
        Submodule.span_image, c.span_eq, Submodule.map_top, Submodule.range_subtype]
    change Submodule.span ℝ (Set.range v) = Submodule.span ℝ (K : Set E)
    rw [← Submodule.span_span_of_tower ℤ ℝ, hc]
  have hmapP (i) : g (P (w i)) = g (w i) := by
    have hd : w i - P (w i) ∈ W := by
      simpa only [Submodule.orthogonal_orthogonal] using
        Wᗮ.sub_starProjection_mem_orthogonal (w i)
    rw [hspanK] at hd
    have hz : g (w i - P (w i)) = 0 := hkill hd
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).symm
  have hfamily : (fun i => (b i : E)) = Sum.elim v w := by
    funext i
    cases i with
    | inl i => exact hleft i
    | inr i => rfl
  have hvolN : covolume N = covolume K * Real.sqrt
      (Matrix.gram ℝ (fun i => P (w i))).det := by
    rw [covolume_eq_gram N b, hfamily, gram_projection_split,
      Real.sqrt_mul (Matrix.posSemidef_gram ℝ v).det_nonneg,
      ← covolume_eq_gram K c]
  have hspanB : Submodule.span ℝ (Set.range fun i => (vB i : F)) = U := by
    have hb : Submodule.span ℤ (Set.range fun i => (vB i : F)) = B := by
      rw [show (Set.range fun i => (vB i : F)) = B.subtype '' Set.range vB from
        Set.range_comp _ _, Submodule.span_image, vB.span_eq,
        Submodule.map_top, Submodule.range_subtype]
    change _ = Submodule.span ℝ (B : Set F)
    rw [← Submodule.span_span_of_tower ℤ ℝ, hb]
  have hfamilyT : (fun i => (dT i : F)) =
      Sum.elim (fun i => (vB i : F)) (fun i => f (w i)) := by
    funext i
    cases i <;> simp only [dT, relativeImageBasis, Basis.mk_apply,
      Sum.elim_inl, Sum.elim_inr, Submodule.coe_inclusion, LinearMap.codRestrict_apply,
      LinearMap.domRestrict_apply, LinearMap.restrictScalars_apply]
    all_goals rfl
  have hvolT : covolume T = covolume B * Real.sqrt
      (Matrix.gram ℝ (fun i => g (w i))).det := by
    rw [covolume_eq_gram T dT, hfamilyT, gram_projection_split,
      Real.sqrt_mul (Matrix.posSemidef_gram ℝ (fun i => (vB i : F))).det_nonneg,
      ← covolume_eq_gram B vB, hspanB]
    rfl
  have hcont : Real.sqrt (Matrix.gram ℝ (fun i => g (w i))).det ≤
      Real.exp h ^ finrank ℤ Im * Real.sqrt
        (Matrix.gram ℝ (fun i => P (w i))).det := by
    have hc := gram_contraction g (fun i => P (w i)) (Real.exp h)
      (Real.exp_nonneg h) hf
    simp only [hmapP] at hc
    have hdim := Module.finrank_eq_card_basis d
    have hc' : (Matrix.gram ℝ (fun i => g (w i))).det ≤
        Real.exp h ^ (2 * finrank ℤ Im) *
          (Matrix.gram ℝ (fun i => P (w i))).det := by
      simpa only [← hdim] using hc
    calc
      _ ≤ Real.sqrt (Real.exp h ^ (2 * finrank ℤ Im) *
          (Matrix.gram ℝ (fun i => P (w i))).det) := Real.sqrt_le_sqrt hc'
      _ = _ := by
        rw [Real.sqrt_mul (by positivity), pow_mul', Real.sqrt_sq (by positivity)]
  have hv : covolume T * covolume K ≤
      Real.exp h ^ finrank ℤ Im * covolume N * covolume B := by
    rw [hvolT, hvolN]
    nlinarith [mul_le_mul_of_nonneg_right hcont
      (mul_nonneg (covolume_pos B).le (covolume_pos K).le)]
  have hlog := Real.log_le_log (mul_pos (covolume_pos T) (covolume_pos K)) hv
  rw [Real.log_mul (covolume_pos T).ne' (covolume_pos K).ne',
    Real.log_mul (mul_pos (by positivity) (covolume_pos N)).ne' (covolume_pos B).ne',
    Real.log_mul (by positivity) (covolume_pos N).ne', Real.log_pow, Real.log_exp] at hlog
  obtain ⟨hi, hindex, _⟩ := covolume_index T J hTJ hspan
  have hcov : covolume J ≤ covolume T := by
    have hi1 : (1 : ℝ) ≤ T.toAddSubgroup.relIndex J.toAddSubgroup := by
      exact_mod_cast (Nat.succ_le_iff.mpr hi)
    rw [hindex]
    nlinarith [covolume_pos J]
  have hlogJ := Real.log_le_log (covolume_pos J) hcov
  have hrTJ : finrank ℤ T = finrank ℤ J := by
    have htR := EuclideanHarderNarasimhan.integral_rank_eq T
    have hjR := EuclideanHarderNarasimhan.integral_rank_eq J
    change finrank ℤ T = finrank ℝ (Submodule.span ℝ (T : Set F)) at htR
    change finrank ℤ J = finrank ℝ (Submodule.span ℝ (J : Set F)) at hjR
    rw [hspan] at htR
    exact htR.trans hjR.symm
  have hrNK : (finrank ℤ N : ℝ) - finrank ℤ K = finrank ℤ Im := by
    have hb := Module.finrank_eq_card_basis b
    have hc := Module.finrank_eq_card_basis c
    have hd := Module.finrank_eq_card_basis d
    simp only [Fintype.card_sum, Fintype.card_fin] at hb hc hd
    change finrank ℤ Im = _ at hd
    have he : finrank ℤ N = finrank ℤ K + finrank ℤ Im := by omega
    have heR : (finrank ℤ N : ℝ) = (finrank ℤ K : ℝ) + finrank ℤ Im := by
      exact_mod_cast he
    linarith
  have hrJB : (finrank ℤ J : ℝ) - finrank ℤ B = finrank ℤ Im := by
    have ht := Module.finrank_eq_card_basis dT
    have hb := Module.finrank_eq_card_basis vB
    have hd := Module.finrank_eq_card_basis d
    simp only [Fintype.card_sum, Fintype.card_fin] at ht hb hd
    change finrank ℤ T = _ at ht
    change finrank ℤ Im = _ at hd
    have he : finrank ℤ J = finrank ℤ B + finrank ℤ Im := by omega
    have heR : (finrank ℤ J : ℝ) = (finrank ℤ B : ℝ) + finrank ℤ Im := by
      exact_mod_cast he
    linarith
  have hklt : k < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro hk
    obtain ⟨x, hx, hfx⟩ := hfmod
    have hxK : x ∈ K := by
      change x ∈ integral N k
      rw [hk, integral_top]
      exact hx
    exact hfx ((hpzero _).mp ((hker x hx).mpr hxK))
  have hβj : β < j := by
    have hle : β ≤ j := by
      apply (Submodule.map_le_map_iff_of_injective
        (f := C.subtype) Subtype.val_injective β.val j.val).mp
      change B ≤ J
      exact le_sup_left.trans hTJ
    refine lt_of_le_of_ne hle ?_
    intro heq
    obtain ⟨x, hx, hfx⟩ := hfmod
    have hIT : N.map (f.toLinearMap.restrictScalars ℤ) ≤ T := le_sup_right
    have hm : f x ∈ J := hTJ (hIT (Submodule.mem_map_of_mem hx))
    change f x ∈ integral C j at hm
    rw [← heq] at hm
    exact hfx (Submodule.subset_span hm)
  have hn := (slope_extreme_bounds (slopeData N) (bot_le.trans_lt hklt)).1 k bot_le hklt
  have hc := (slope_extreme_bounds (slopeData C) (hβj.trans_le le_top)).2 j hβj le_top
  have hr (L : Submodule ℤ E) [DiscreteTopology L] (a : Sublattice L) :
      ((slopeData L).rank a : ℝ) = finrank ℤ (integral L a) := by
    change (finrank ℤ a.val : ℝ) = _
    exact_mod_cast (Submodule.finrank_map_subtype_eq L a.val).symm
  have hrF (L : Submodule ℤ F) [DiscreteTopology L] (a : Sublattice L) :
      ((slopeData L).rank a : ℝ) = finrank ℤ (integral L a) := by
    change (finrank ℤ a.val : ℝ) = _
    exact_mod_cast (Submodule.finrank_map_subtype_eq L a.val).symm
  have hdimpos : (0 : ℝ) < finrank ℤ Im := by
    have hrank := (slopeData N).rank_strictMono hklt
    have hrankR : ((slopeData N).rank k : ℝ) < (slopeData N).rank ⊤ := by
      exact_mod_cast hrank
    rw [hr, hr, integral_top] at hrankR
    change (finrank ℤ K : ℝ) < finrank ℤ N at hrankR
    linarith
  dsimp only [SlopeData.slope] at hn hc
  change _ ≤
    (-Real.log (covolume (integral N ⊤)) - -Real.log (covolume K)) /
      (((slopeData N).rank ⊤ : ℝ) - (slopeData N).rank k) at hn
  change (-Real.log (covolume J) - -Real.log (covolume B)) /
    (((slopeData C).rank j : ℝ) - (slopeData C).rank β) ≤ _ at hc
  have hcovtopN : covolume (integral N ⊤) = covolume N := by simp only [integral_top]
  have hrtopN : ((slopeData N).rank ⊤ : ℝ) = finrank ℤ N := by
    have ht := (LinearEquiv.ofEq _ _ (integral_top N)).finrank_eq
    exact (hr N ⊤).trans (by exact_mod_cast ht)
  rw [hcovtopN, hrtopN, hr N k] at hn
  change _ ≤ (-Real.log (covolume N) - -Real.log (covolume K)) /
    ((finrank ℤ N : ℝ) - finrank ℤ K) at hn
  rw [hrNK, sub_neg_eq_add] at hn
  rw [hrF C j, hrF C β] at hc
  change (-Real.log (covolume J) - -Real.log (covolume B)) /
    ((finrank ℤ J : ℝ) - finrank ℤ B) ≤ _ at hc
  rw [hrJB, sub_neg_eq_add] at hc
  have hcomp :
      (-Real.log (covolume N) + Real.log (covolume K)) / finrank ℤ Im ≤
        (-Real.log (covolume J) + Real.log (covolume B)) / finrank ℤ Im + h := by
    apply (div_le_iff₀ hdimpos).mpr
    have heq : ((-Real.log (covolume J) + Real.log (covolume B)) / finrank ℤ Im + h) *
        finrank ℤ Im = -Real.log (covolume J) + Real.log (covolume B) +
          h * finrank ℤ Im := by field_simp [ne_of_gt hdimpos]
    rw [heq]
    nlinarith
  exact hn.trans (hcomp.trans (by simpa only [add_comm] using add_le_add_right hc h))

private theorem carrier_le_iff (L : Submodule ℤ E) (a b : Sublattice L) :
    integral L a ≤ integral L b ↔ a ≤ b := by
  change a.val.map L.subtype ≤ b.val.map L.subtype ↔ a.val ≤ b.val
  exact Submodule.map_le_map_iff_of_injective Subtype.val_injective _ _

private theorem carrier_section_eq (L M : Submodule ℤ E) (hML : M ≤ L)
    (hsat : ∀ x : E, x ∈ L → x ∈ Submodule.span ℝ (M : Set E) → x ∈ M) :
    integral L (sectionLattice L (Submodule.span ℝ (M : Set E))) = M := by
  rw [integral_section]
  exact le_antisymm (fun x hx => hsat x hx.1 hx.2)
    (fun x hx => ⟨hML hx, Submodule.subset_span hx⟩)

private def liftSection (L : Submodule ℤ E) (a : Sublattice L)
    (b : Sublattice (integral L a)) : Sublattice L :=
  sectionLattice L (Submodule.span ℝ (integral (integral L a) b : Set E))

private theorem liftSection_carrier (L : Submodule ℤ E) (a : Sublattice L)
    (b : Sublattice (integral L a)) :
    integral L (liftSection L a b) = integral (integral L a) b := by
  apply carrier_section_eq
  · exact (integral_le _ b).trans (integral_le _ a)
  · intro x hx hs
    have ha : x ∈ integral L a := integral_saturated L a x hx
      (Submodule.span_mono (integral_le _ b) hs)
    exact integral_saturated _ b x ha hs

private def lowerSection (L : Submodule ℤ E) (a b : Sublattice L) :
    Sublattice (integral L a) :=
  sectionLattice (integral L a) (Submodule.span ℝ (integral L b : Set E))

private theorem lowerSection_carrier (L : Submodule ℤ E) (a b : Sublattice L)
    (hba : b ≤ a) : integral (integral L a) (lowerSection L a b) = integral L b := by
  apply carrier_section_eq
  · exact (carrier_le_iff L b a).mpr hba
  · intro x hx hs
    exact integral_saturated L b x (integral_le L a hx) hs

private theorem carrier_rank (L : Submodule ℤ E) [DiscreteTopology L]
    (a : Sublattice L) : (slopeData L).rank a = (finrank ℤ (integral L a) : ℤ) := by
  change (finrank ℤ a.val : ℤ) = _
  exact_mod_cast (Submodule.finrank_map_subtype_eq L a.val).symm

private theorem interval_slope_transport (L : Submodule ℤ E) [DiscreteTopology L]
    (a : Sublattice L) (b : Sublattice (integral L a)) :
    (slopeData (integral L a)).slope b ⊤ =
      (slopeData L).slope (liftSection L a b) a := by
  unfold SlopeData.slope
  simp only [slopeData, degree, sub_neg_eq_add]
  change
    (-Real.log (covolume (integral (integral L a) ⊤)) +
      Real.log (covolume (integral (integral L a) b))) /
        (((slopeData (integral L a)).rank ⊤ : ℝ) -
          (slopeData (integral L a)).rank b) =
    (-Real.log (covolume (integral L a)) +
      Real.log (covolume (integral L (liftSection L a b)))) /
        (((slopeData L).rank a : ℝ) - (slopeData L).rank (liftSection L a b))
  have ht : (slopeData (integral L a)).rank ⊤ = (slopeData L).rank a := by
    rw [carrier_rank, carrier_rank]
    exact_mod_cast (LinearEquiv.finrank_eq
      (LinearEquiv.ofEq _ _ (integral_top (integral L a))))
  have hb : (slopeData L).rank (liftSection L a b) =
      (slopeData (integral L a)).rank b := by
    rw [carrier_rank, carrier_rank]
    exact_mod_cast (LinearEquiv.finrank_eq
      (LinearEquiv.ofEq _ _ (liftSection_carrier L a b)))
  have hc (M N : Submodule ℤ E) [Module.Free ℤ M] [Module.Finite ℤ M]
      [Module.Free ℤ N] [Module.Finite ℤ N] (h : M = N) : covolume M = covolume N := by
    subst N
    rfl
  rw [ht, hb, hc _ _ (integral_top (integral L a)),
    hc _ _ (liftSection_carrier L a b)]

private theorem muMin_restriction (L : Submodule ℤ E) [DiscreteTopology L]
    (a : Sublattice L) :
    (slopeData (integral L a)).muMin ⊥ ⊤ = (slopeData L).muMin ⊥ a := by
  unfold SlopeData.muMin
  congr 1
  ext s
  constructor
  · rintro ⟨b, hb, hbt, hs⟩
    refine ⟨liftSection L a b, bot_le, ?_, ?_⟩
    · rw [lt_iff_le_and_ne]
      constructor
      · apply (carrier_le_iff L _ _).mp
        rw [liftSection_carrier]
        exact integral_le _ b
      · intro heq
        have he : integral (integral L a) b = integral (integral L a) ⊤ := by
          rw [integral_top, ← liftSection_carrier L a b, heq]
        have hbtop : b = ⊤ := le_antisymm le_top
          ((carrier_le_iff _ _ _).mp he.ge)
        exact hbt.ne hbtop
    · exact (interval_slope_transport L a b).symm.trans hs
  · rintro ⟨b, hb, hba, hs⟩
    let q := lowerSection L a b
    have hq : integral (integral L a) q = integral L b := lowerSection_carrier L a b hba.le
    refine ⟨q, bot_le, ?_, ?_⟩
    · apply lt_top_iff_ne_top.mpr
      intro heq
      have hcb : integral L b = integral L a := by rw [← hq, heq, integral_top]
      exact hba.ne (le_antisymm hba.le ((carrier_le_iff _ _ _).mp hcb.ge))
    · have hl : liftSection L a q = b := by
        apply le_antisymm
        · apply (carrier_le_iff L _ _).mp
          rw [liftSection_carrier, hq]
        · apply (carrier_le_iff L _ _).mp
          rw [liftSection_carrier, hq]
      rw [interval_slope_transport, hl]
      exact hs

/-- A map nonzero modulo a saturated target section obeys the interval HN slope bound. -/
theorem slope_morphism (N : Submodule ℤ E) (C : Submodule ℤ F)
    [DiscreteTopology N] [DiscreteTopology C] (a : Sublattice N) (b : Sublattice C)
    (f : E →L[ℝ] F) (h : ℝ)
    (hfC : ∀ x ∈ integral N a, f x ∈ C)
    (hfmod : ∃ x ∈ integral N a, f x ∉ Submodule.span ℝ (integral C b : Set F))
    (hf : ∀ x ∈ Submodule.span ℝ (integral N a : Set E),
      ‖(Submodule.span ℝ (integral C b : Set F))ᗮ.starProjection (f x)‖ ≤
      Real.exp h * ‖x‖) :
    (slopeData N).muMin ⊥ a ≤ (slopeData C).muMax b ⊤ + h := by
  rw [← muMin_restriction N a]
  let S := Submodule.span ℝ (integral N a : Set E)
  let g := f.comp S.starProjection
  have hg (x : E) (hx : x ∈ integral N a) : g x = f x := by
    change f (S.starProjection x) = f x
    rw [S.starProjection_eq_self_iff.mpr (Submodule.subset_span hx)]
  apply relative_full_slope_morphism (integral N a) C b g h
  · intro x hx
    rw [hg x hx]
    exact hfC x hx
  · obtain ⟨x, hx, hfx⟩ := hfmod
    exact ⟨x, hx, by rwa [hg x hx]⟩
  · intro x
    exact (hf _ (S.starProjection_apply_mem x)).trans
      (mul_le_mul_of_nonneg_left (S.norm_starProjection_apply_le x) (Real.exp_pos h).le)

end D5.S3.Combinatorics.Lattices.EuclideanSlopeMorphism
