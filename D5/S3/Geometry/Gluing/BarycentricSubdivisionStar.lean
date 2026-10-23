/- GID: D5/S3/Geometry/Gluing/BarycentricSubdivisionStar
   generality: G
   mirror-B: D5/B/S3/Geometry/Gluing/BarycentricSubdivisionStar
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Intrinsic]
   utility: none
   digest: Actual face-chain barycenters and the stars of an original tetrahedron vertex. -/

import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace D5.S3.Geometry.Gluing.BarycentricSubdivisionStar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonempty chain of nonempty faces of the parent tetrahedron. -/
structure FaceChain where
  faces : Finset (Finset (Fin 4))
  nonempty : faces.Nonempty
  face_nonempty : ∀ F ∈ faces, F.Nonempty
  comparable : ∀ F ∈ faces, ∀ G ∈ faces, F ⊆ G ∨ G ⊆ F

/-- The geometric barycenter, with no coordinate inequalities in its definition. -/
noncomputable def barycenter (p : Fin 4 → E) (F : Finset (Fin 4)) : E :=
  (F.card : ℝ)⁻¹ • ∑ i ∈ F, p i

/-- The actual geometric simplex of a face chain. -/
noncomputable def chainHull (p : Fin 4 → E) (C : FaceChain) : Set E :=
  convexHull ℝ (barycenter p '' (C.faces : Set (Finset (Fin 4))))

/-- Union of the closed chain simplices geometrically incident to the original vertex. -/
def closedStar (p : Fin 4 → E) : Set E :=
  {x | ∃ C : FaceChain, p 0 ∈ barycenter p '' (C.faces : Set (Finset (Fin 4))) ∧
    x ∈ chainHull p C}

/-- Union of the intrinsic interiors of all geometrically incident chain simplices. -/
def openStar (p : Fin 4 → E) : Set E :=
  {x | ∃ C : FaceChain, p 0 ∈ barycenter p '' (C.faces : Set (Finset (Fin 4))) ∧
    x ∈ intrinsicInterior ℝ (chainHull p C)}

noncomputable def faceWeight (F : Finset (Fin 4)) (i : Fin 4) : ℝ :=
  if i ∈ F then (F.card : ℝ)⁻¹ else 0

lemma faceWeight_sum (F : Finset (Fin 4)) (hF : F.Nonempty) :
    ∑ i, faceWeight F i = 1 := by
  classical
  simp only [faceWeight]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
    nsmul_eq_mul]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hF))

lemma barycenter_eq_sum (p : Fin 4 → E) (F : Finset (Fin 4)) :
    barycenter p F = ∑ i, faceWeight F i • p i := by
  classical
  simp only [faceWeight, ite_smul, zero_smul, ← Finset.sum_filter]
  simp [barycenter, Finset.smul_sum]

lemma weights_unique (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (a b : Fin 4 → ℝ) (ha : ∑ i, a i = 1) (hb : ∑ i, b i = 1)
    (heq : ∑ i, a i • p i = ∑ i, b i • p i) : a = b := by
  apply (affineIndependent_iff_eq_of_fintype_affineCombination_eq ℝ p).mp hp a b ha hb
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ ha,
    Finset.affineCombination_eq_linear_combination _ _ _ hb] using heq

private lemma barycenter_eq_vertex_iff (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (F : Finset (Fin 4)) (hF : F.Nonempty) (v : Fin 4) :
    barycenter p F = p v ↔ F = {v} := by
  classical
  constructor
  · intro h
    have hu := weights_unique p hp (faceWeight F) (fun i => if i = v then 1 else 0)
      (faceWeight_sum F hF) (by simp) (by simpa [← barycenter_eq_sum] using h)
    have hn : (F.card : ℝ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr
      (Finset.card_ne_zero.mpr hF))
    ext i
    have hi := congrFun hu i
    simp only [faceWeight] at hi
    simp only [Finset.mem_singleton]
    by_cases hmem : i ∈ F <;> by_cases hiv : i = v <;> simp_all
  · rintro rfl
    simp [barycenter]

private lemma incident_faces_contain_zero (p : Fin 4 → E)
    (hp : AffineIndependent ℝ p) (C : FaceChain)
    (hinc : p 0 ∈ barycenter p '' (C.faces : Set (Finset (Fin 4)))) :
    ∀ F ∈ C.faces, (0 : Fin 4) ∈ F := by
  obtain ⟨G, hG, hGp⟩ := hinc
  have hG0 := (barycenter_eq_vertex_iff p hp G (C.face_nonempty G hG) 0).mp hGp
  subst G
  intro F hF
  rcases C.comparable {0} hG F hF with h | h
  · exact h (Finset.mem_singleton_self 0)
  · obtain ⟨i, hi⟩ := C.face_nonempty F hF
    have hi0 : i = 0 := Finset.mem_singleton.mp (h hi)
    simpa [hi0] using hi

private lemma closedStar_dominates (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (β : Fin 4 → ℝ) (hβ : ∑ j, β j = 1) (x : E)
    (hx : x = ∑ j, β j • p j) (hstar : x ∈ closedStar p) :
    ∀ j, β j ≤ β 0 := by
  classical
  obtain ⟨C, hinc, hmem⟩ := hstar
  have hzero := incident_faces_contain_zero p hp C hinc
  obtain ⟨I, hI, w, z, hw, hwone, hz, hzx⟩ :=
    mem_convexHull_iff_exists_fintype.mp hmem
  choose G hG hGz using hz
  let a : Fin 4 → ℝ := fun j => ∑ i, w i * faceWeight (G i) j
  have hasum : ∑ j, a j = 1 := by
    dsimp [a]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, faceWeight_sum _ (C.face_nonempty _ (hG _)), mul_one]
    exact hwone
  have haeq : ∑ j, a j • p j = ∑ j, β j • p j := by
    calc
      ∑ j, a j • p j = ∑ i, w i • barycenter p (G i) := by
        simp only [a, Finset.sum_smul, mul_smul, barycenter_eq_sum, Finset.smul_sum]
        exact Finset.sum_comm
      _ = x := by simp_rw [hGz]; exact hzx
      _ = _ := hx
  have hab := weights_unique p hp a β hasum hβ haeq
  intro j
  rw [← hab]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (hw i)
  simp only [faceWeight, if_pos (hzero _ (hG i))]
  split_ifs
  · exact le_rfl
  · positivity

def prefixFace (π : Equiv.Perm (Fin 4)) (k : Fin 4) : Finset (Fin 4) :=
  (Finset.Iic k).image π

private lemma prefix_mono (π : Equiv.Perm (Fin 4)) {k l : Fin 4} (h : k ≤ l) :
    prefixFace π k ⊆ prefixFace π l :=
  Finset.image_subset_image (Finset.Iic_subset_Iic.mpr h)

def flagChain (π : Equiv.Perm (Fin 4)) : FaceChain where
  faces := Finset.univ.image (prefixFace π)
  nonempty := Finset.univ_nonempty.image _
  face_nonempty := by
    intro F hF
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
    exact ⟨π k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
  comparable := by
    intro F hF G hG
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
    obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hG
    rcases le_total k l with h | h
    · exact Or.inl (prefix_mono π h)
    · exact Or.inr (prefix_mono π h)

lemma prefix_barycenters (p : Fin 4 → E) (π : Equiv.Perm (Fin 4)) (k : Fin 4) :
    barycenter p (prefixFace π k) =
      ![p (π 0), (1 / 2 : ℝ) • (p (π 0) + p (π 1)),
        (1 / 3 : ℝ) • (p (π 0) + p (π 1) + p (π 2)),
        (1 / 4 : ℝ) • (p (π 0) + p (π 1) + p (π 2) + p (π 3))] k := by
  classical
  have hc : (prefixFace π k).card = (Finset.Iic k).card :=
    Finset.card_image_of_injective _ π.injective
  simp only [barycenter, hc, prefixFace,
    Finset.sum_image (fun a _ b _ h => π.injective h)]
  have h0 : Finset.Iic (0 : Fin 4) = {0} := by decide
  have h1 : Finset.Iic (1 : Fin 4) = {0, 1} := by decide
  have h2 : Finset.Iic (2 : Fin 4) = {0, 1, 2} := by decide
  have h3 : Finset.Iic (3 : Fin 4) = {0, 1, 2, 3} := by decide
  fin_cases k <;> simp [h0, h1, h2, h3, add_assoc]

private noncomputable def flagWeight (β : Fin 4 → ℝ) (π : Equiv.Perm (Fin 4)) : Fin 4 → ℝ :=
  ![β (π 0) - β (π 1), 2 * (β (π 1) - β (π 2)),
    3 * (β (π 2) - β (π 3)), 4 * β (π 3)]

private lemma flag_reconstruction (p : Fin 4 → E) (β : Fin 4 → ℝ)
    (π : Equiv.Perm (Fin 4)) :
    (∑ k, flagWeight β π k = ∑ j, β j) ∧
    (∑ k, flagWeight β π k • barycenter p (prefixFace π k) = ∑ j, β j • p j) := by
  have hsum := Equiv.sum_comp π β
  have hvec := Equiv.sum_comp π (fun j => β j • p j)
  constructor
  · rw [← hsum]
    simp [flagWeight, Fin.sum_univ_succ]
    ring
  · rw [← hvec]
    simp [prefix_barycenters, flagWeight, Fin.sum_univ_succ]

    module

private lemma sorted_flag (β : Fin 4 → ℝ) (hmax : ∀ j, β j ≤ β 0) :
    ∃ π : Equiv.Perm (Fin 4), π 0 = 0 ∧ Antitone (β ∘ π) := by
  let π := Tuple.sort (fun j => -β j)
  have ho := (Tuple.eq_sort_iff (f := fun j => -β j) (σ := π)).mp rfl
  have hanti : Antitone (β ∘ π) := by
    intro i j hij
    have h := ho.1 hij
    dsimp [Function.comp_def] at h ⊢
    linarith
  refine ⟨π, ?_, hanti⟩
  have hb : β (π 0) = β 0 := by
    have h := hanti (Fin.zero_le (π.symm 0))
    simp only [Function.comp_apply, Equiv.apply_symm_apply] at h
    exact le_antisymm (hmax _) h
  by_contra hne
  have hi : (0 : Fin 4) < π.symm 0 := by
    have : π.symm 0 ≠ 0 := by
      intro h
      apply hne
      simpa [h] using π.apply_symm_apply 0
    exact Fin.pos_iff_ne_zero.mpr this
  have h := ho.2 0 (π.symm 0) hi (by simp [hb])
  simpa using h

private lemma dominates_closedStar (p : Fin 4 → E) (β : Fin 4 → ℝ)
    (hn : ∀ j, 0 ≤ β j) (hs : ∑ j, β j = 1)
    (x : E) (hx : x = ∑ j, β j • p j) (hmax : ∀ j, β j ≤ β 0) :
    x ∈ closedStar p := by
  classical
  obtain ⟨π, hπ, hsort⟩ := sorted_flag β hmax
  refine ⟨flagChain π, ?_, ?_⟩
  · refine ⟨prefixFace π 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa [hπ] using prefix_barycenters p π 0
  · apply mem_convexHull_of_exists_fintype (flagWeight β π)
      (fun k => barycenter p (prefixFace π k))
    · intro k
      have h01 := hsort (show (0 : Fin 4) ≤ 1 by decide)
      have h12 := hsort (show (1 : Fin 4) ≤ 2 by decide)
      have h23 := hsort (show (2 : Fin 4) ≤ 3 by decide)
      have h3 := hn (π 3)
      dsimp [Function.comp_def] at h01 h12 h23
      fin_cases k <;> simp [flagWeight] <;> linarith
    · exact (flag_reconstruction p β π).1.trans hs
    · intro k
      exact ⟨prefixFace π k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩, rfl⟩
    · exact (flag_reconstruction p β π).2.trans hx.symm

private lemma flag_independent (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (π : Equiv.Perm (Fin 4)) :
    AffineIndependent ℝ (fun k => barycenter p (prefixFace π k)) := by
  classical
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro u v hu hv huv
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hu,
    Finset.affineCombination_eq_linear_combination _ _ _ hv] at huv
  let T : (Fin 4 → ℝ) → Fin 4 → ℝ := fun a =>
    ![a 0 + a 1 / 2 + a 2 / 3 + a 3 / 4,
      a 1 / 2 + a 2 / 3 + a 3 / 4, a 2 / 3 + a 3 / 4, a 3 / 4]
  have hsum (a : Fin 4 → ℝ) : ∑ k, T a k = ∑ k, a k := by
    simp [T, Fin.sum_univ_succ]
    ring
  have heq (a : Fin 4 → ℝ) :
      ∑ k, a k • barycenter p (prefixFace π k) = ∑ k, T a k • p (π k) := by
    simp [prefix_barycenters, T, Fin.sum_univ_succ]

    module
  have hpπ := hp.comp_embedding π.toEmbedding
  have hT := weights_unique (p ∘ π) hpπ (T u) (T v)
    ((hsum u).trans hu) ((hsum v).trans hv) (by
      simpa only [Function.comp_apply, ← heq] using huv)
  have h0 := congrFun hT 0
  have h1 := congrFun hT 1
  have h2 := congrFun hT 2
  have h3 := congrFun hT 3
  simp [T] at h0 h1 h2 h3
  ext k
  fin_cases k
  · change u 0 = v 0; linarith
  · change u 1 = v 1; linarith
  · change u 2 = v 2; linarith
  · change u 3 = v 3; exact h3

private lemma positive_mem_intrinsicInterior {I : Type*} [Fintype I] [Nonempty I]
    (q : I → E) (hq : AffineIndependent ℝ q) (w : I → ℝ)
    (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    (∑ i, w i • q i) ∈ intrinsicInterior ℝ (convexHull ℝ (Set.range q)) := by
  classical
  let A := affineSpan ℝ (Set.range q)
  let qa : I → A := fun i => ⟨q i, subset_affineSpan ℝ _ (Set.mem_range_self i)⟩
  letI : Nonempty A := ⟨qa (Classical.arbitrary I)⟩
  let e : A.direction ≃ᵃⁱ[ℝ] A := AffineIsometryEquiv.vaddConst ℝ (qa (Classical.arbitrary I))
  let r : I → A.direction := fun i => e.symm (qa i)
  have hqa : AffineIndependent ℝ qa := hq.of_comp A.subtype
  have hr : AffineIndependent ℝ r := hqa.map' e.symm.toAffineEquiv.toAffineMap e.symm.injective
  have hspan : affineSpan ℝ (Set.range qa) = ⊤ := by
    have heq : Set.range qa = ((↑) : A → E) ⁻¹' Set.range q := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, hi⟩; exact ⟨i, Subtype.ext hi⟩
    rw [heq]
    exact affineSpan_coe_preimage_eq_top (Set.range q)
  let b : AffineBasis I ℝ A.direction := ⟨r, hr, by
    change affineSpan ℝ (Set.range (e.symm ∘ qa)) = ⊤
    rw [Set.range_comp]
    exact e.symm.toAffineEquiv.toAffineMap.span_eq_top_of_surjective e.symm.surjective hspan⟩
  let f : A.direction →ᵃⁱ[ℝ] E := A.subtypeₐᵢ.comp e.toAffineIsometry
  have hf : ∀ i, f (b i) = q i := by
    intro i
    change ((e (e.symm (qa i)) : A) : E) = q i
    simp [qa]
  have hconv : f '' convexHull ℝ (Set.range b) = convexHull ℝ (Set.range q) := by
    change f.toAffineMap '' convexHull ℝ (Set.range b) = _
    rw [f.toAffineMap.image_convexHull, ← Set.range_comp]
    congr 2
    funext i
    exact hf i
  have hm : (∑ i, w i • b i) ∈ interior (convexHull ℝ (Set.range b)) := by
    rw [b.interior_convexHull]
    intro i
    have hc := b.coord_apply_combination_of_mem (Finset.mem_univ i) hs
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hc
    simpa only [hc] using hw i
  have hm' := interior_subset_intrinsicInterior (𝕜 := ℝ) hm
  have him := Set.mem_image_of_mem f hm'
  rw [← f.intrinsicInterior_image, hconv] at him
  convert him using 1
  have hmap := Finset.map_affineCombination Finset.univ b w hs f.toAffineMap
  simpa only [Finset.affineCombination_eq_linear_combination _ _ _ hs, Function.comp_apply, AffineIsometry.coe_toAffineMap, hf] using hmap.symm

private lemma intrinsic_extension (s : Set E) (x y : E)
    (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ t : ℝ, 0 < t ∧ x + t • (x - y) ∈ s := by
  obtain ⟨a, ha, hax⟩ := mem_intrinsicInterior.mp hx
  let b : affineSpan ℝ s := ⟨y, subset_affineSpan ℝ s hy⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior a ha
  letI : Nonempty (affineSpan ℝ s) := ⟨a⟩
  let v : (affineSpan ℝ s).direction := a -ᵥ b
  let t := ε / (2 * (‖v‖ + 1))
  have hn : 0 ≤ ‖v‖ := norm_nonneg v
  have ht : 0 < t := div_pos hε (by positivity)
  have hbound : t * ‖v‖ < ε := by
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2 * (‖v‖ + 1))).mpr
    change ε * ‖v‖ < ε * (2 * (‖v‖ + 1))
    nlinarith
  have hm : t • v +ᵥ a ∈ Metric.ball a ε := by
    rw [Metric.mem_ball, dist_vadd_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact hbound
  have hmem := interior_subset (hball hm)
  refine ⟨t, ht, ?_⟩
  change t • ((a : E) - (b : E)) + (a : E) ∈ s at hmem
  simpa only [hax, b, add_comm] using hmem

private lemma openStar_strict (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (β : Fin 4 → ℝ) (hs : ∑ i, β i = 1) (x : E)
    (hx : x = ∑ i, β i • p i) (hm : x ∈ openStar p) :
    ∀ j ≠ 0, β j < β 0 := by
  classical
  obtain ⟨C, hinc, hc⟩ := hm
  have hy : p 0 ∈ chainHull p C := subset_convexHull ℝ _ hinc
  obtain ⟨t, ht, hext⟩ := intrinsic_extension (chainHull p C) x (p 0) hc hy
  let b : Fin 4 → ℝ := fun i => (1 + t) * β i - if i = 0 then t else 0
  have hb : ∑ i, b i = 1 := by
    simp [b, Finset.sum_sub_distrib, ← Finset.mul_sum, hs]
  have heq : x + t • (x - p 0) = ∑ i, b i • p i := by
    simp only [b, sub_smul, Finset.sum_sub_distrib, mul_smul,
      ← Finset.smul_sum, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      if_true]
    rw [← hx]
    module
  have hle := closedStar_dominates p hp b hb _ heq ⟨C, hinc, hext⟩
  intro j hj
  have h := hle j
  dsimp [b] at h
  simp only [hj, if_false, if_true, sub_zero] at h
  have ht1 : 0 < 1 + t := by linarith
  nlinarith

private lemma strict_openStar (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (β : Fin 4 → ℝ) (hn : ∀ j, 0 ≤ β j) (hs : ∑ j, β j = 1)
    (x : E) (hx : x = ∑ j, β j • p j) (hstrict : ∀ j ≠ 0, β j < β 0) :
    x ∈ openStar p := by
  classical
  have hmax : ∀ j, β j ≤ β 0 := fun j => by
    by_cases h : j = 0
    · simp [h]
    · exact (hstrict j h).le
  obtain ⟨π, hπ, hsort⟩ := sorted_flag β hmax
  let w := flagWeight β π
  have hw : ∀ k, 0 ≤ w k := by
    intro k
    have h01 := hsort (show (0 : Fin 4) ≤ 1 by decide)
    have h12 := hsort (show (1 : Fin 4) ≤ 2 by decide)
    have h23 := hsort (show (2 : Fin 4) ≤ 3 by decide)
    have h3 := hn (π 3)
    dsimp [Function.comp_def] at h01 h12 h23
    fin_cases k <;> simp [w, flagWeight] <;> linarith
  have hw0 : 0 < w 0 := by
    have h10 : π 1 ≠ 0 := by
      rw [← hπ]
      exact π.injective.ne (by decide)
    simpa [w, flagWeight, hπ] using sub_pos.mpr (hstrict _ h10)
  let S := Finset.univ.filter (fun k => 0 < w k)
  have hS0 : (0 : Fin 4) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw0⟩
  let C : FaceChain := {
    faces := S.image (prefixFace π)
    nonempty := (Finset.nonempty_iff_ne_empty.mpr (by
      intro h; simpa [h] using hS0)).image _
    face_nonempty := by
      intro F hF
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hF
      exact ⟨π k, Finset.mem_image.mpr ⟨k, Finset.mem_Iic.mpr le_rfl, rfl⟩⟩
    comparable := by
      intro F hF G hG
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hF
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hG
      exact (le_total k l).imp (prefix_mono π) (prefix_mono π) }
  have hsubsum : ∑ k ∈ S, w k = ∑ k, w k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    have hnot : ¬ 0 < w k := by simpa [S] using hk
    exact le_antisymm (le_of_not_gt hnot) (hw k)
  letI : Nonempty S := ⟨⟨0, hS0⟩⟩
  have hsS : ∑ k : S, w k = 1 := by
    rw [Finset.sum_coe_sort, hsubsum]
    exact (flag_reconstruction p β π).1.trans hs
  have hpos : ∀ k : S, 0 < w k := fun k => (Finset.mem_filter.mp k.property).2
  have hq := (flag_independent p hp π).subtype (S : Set (Fin 4))
  have hi := positive_mem_intrinsicInterior
    (fun k : S => barycenter p (prefixFace π k)) hq (fun k : S => w k) hpos hsS
  have hrange : Set.range (fun k : S => barycenter p (prefixFace π k)) =
      barycenter p '' (C.faces : Set (Finset (Fin 4))) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨prefixFace π k, Finset.mem_image.mpr ⟨k, k.property, rfl⟩, rfl⟩
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hF
      exact ⟨⟨k, hk⟩, rfl⟩
  have hxS : (∑ k : S, w k • barycenter p (prefixFace π k)) = x := by
    change (∑ k : S, (fun k => w k • barycenter p (prefixFace π k)) k) = x
    rw [Finset.sum_coe_sort (s := S) (f := fun k => w k • barycenter p (prefixFace π k))]
    calc
      ∑ k ∈ S, w k • barycenter p (prefixFace π k) =
          ∑ k, w k • barycenter p (prefixFace π k) := by
        apply Finset.sum_subset (Finset.subset_univ S)
        intro k _ hk
        have hnot : ¬ 0 < w k := by simpa [S] using hk
        rw [le_antisymm (le_of_not_gt hnot) (hw k), zero_smul]
      _ = x := (flag_reconstruction p β π).2.trans hx.symm
  refine ⟨C, ?_, ?_⟩
  · refine ⟨prefixFace π 0, Finset.mem_image.mpr ⟨0, hS0, rfl⟩, ?_⟩
    simpa [hπ] using prefix_barycenters p π 0
  · simpa only [hxS, hrange, chainHull] using hi

/-- Closed and all-face open stars in the actual barycentric subdivision of a tetrahedron. -/
theorem actual_closed_and_open_star_iff (p : Fin 4 → E) (hp : AffineIndependent ℝ p)
    (β : Fin 4 → ℝ) (hn : ∀ j, 0 ≤ β j) (hs : ∑ j, β j = 1)
    (x : E) (hx : x = ∑ j, β j • p j) :
    (x ∈ closedStar p ↔ ∀ j ≠ 0, β j ≤ β 0) ∧
    (x ∈ openStar p ↔ ∀ j ≠ 0, β j < β 0) := by
  constructor
  · constructor
    · intro hm j _
      exact closedStar_dominates p hp β hs x hx hm j
    · intro hm
      apply dominates_closedStar p β hn hs x hx
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · exact hm j hj
  · exact ⟨openStar_strict p hp β hs x hx,
      strict_openStar p hp β hn hs x hx⟩

end D5.S3.Geometry.Gluing.BarycentricSubdivisionStar
