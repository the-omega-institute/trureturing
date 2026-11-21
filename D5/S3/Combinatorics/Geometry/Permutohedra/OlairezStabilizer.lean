/- GID: D5/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Geometry/Permutohedra/OlairezStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The source dihedral permutohedron has intrinsic affine group S_n times C_2. -/
import D5.S3.Combinatorics.Geometry.Permutohedra.OlairezQ62
import Mathlib.Analysis.Convex.Extreme
import Mathlib.LinearAlgebra.AffineSpace.Centroid
import Mathlib.Data.Finite.Perm

/-! The signed wrap hull and the real affine action on Olairez's standard-basepoint orbit.

Voskresenskii and Klyachko, *Toroidal Fano Varieties and Root Systems* (1985), p. 238,
give the odd-`n` classification in the normalized del Pezzo model.
D’Alì, Juhnke-Kubitzke, and Koch, *On a Generalization of Symmetric Edge Polytopes
to Regular Matroids*, Theorems 3.2 and 4.3(v), give the regular-matroid lift and
the description of the antipodal vertices.

The source transfer uses the forward cyclic difference on the real affine span
and sends the literal paper label `j` to wrap index `1 - j` in cyclic indexing.
-/

namespace OlairezQ62

open Finset
open scoped BigOperators

noncomputable section

variable {n : ℕ} [NeZero n]

/-- The convex hull in cyclic-difference coordinates. -/
private def normalizedHull (n : ℕ) [NeZero n] : Set (sumZero n) :=
  convexHull ℝ (signedPoints n)

private def coord (i : ZMod n) : sumZero n →ₗ[ℝ] ℝ :=
  (LinearMap.proj i).comp (sumZero n).subtype

private theorem wrap_apply (k i : ZMod n) :
    (wrapPoint k).val i = 1 - (n : ℝ) * (if i = k then 1 else 0) := by
  simp [wrapPoint, basisVector, Pi.single_apply, eq_comm]

private theorem sum_wrap_coord (a : ZMod n → ℝ) (i : ZMod n) :
    coord i (∑ k, a k • wrapPoint k) = (∑ k, a k) - (n : ℝ) * a i := by
  classical
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  change (∑ k : ZMod n, a k * (wrapPoint k).val i) = _
  simp only [wrap_apply]
  simp_rw [mul_sub, mul_one, sum_sub_distrib]
  congr 1
  rw [sum_eq_single i]
  · simp [mul_comm]
  · intro k _ hki
    simp [Ne.symm hki]
  · simp

private theorem wrap_combination (x : sumZero n) :
    (∑ k : ZMod n, (-(x.val k) / (n : ℝ)) • wrapPoint k) = x := by
  apply Subtype.ext
  funext i
  change coord i (∑ k : ZMod n, (-(x.val k) / (n : ℝ)) • wrapPoint k) = x.val i
  rw [sum_wrap_coord, ← sum_div, sum_neg_distrib]
  have hx : ∑ k, x.val k = 0 := x.property
  rw [hx]
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp
  ring

/-- The only linear relations on the positive wrap vectors have constant coefficients. -/
private theorem wrap_dependence (a : ZMod n → ℝ) :
    (∑ k, a k • wrapPoint k) = 0 ↔ ∃ c : ℝ, ∀ k, a k = c := by
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  constructor
  · intro h
    refine ⟨(∑ k, a k) / (n : ℝ), fun k => (eq_div_iff hn).2 ?_⟩
    have hcoord := sum_wrap_coord a k
    rw [h, map_zero] at hcoord
    linarith
  · rintro ⟨c, hc⟩
    apply Subtype.ext
    funext i
    change coord i _ = 0
    rw [sum_wrap_coord]
    simp [hc, ZMod.card, nsmul_eq_mul]

private theorem sum_wrap : (∑ k : ZMod n, wrapPoint k) = 0 := by
  simpa using (wrap_dependence (n := n) (fun _ => 1)).2 ⟨1, fun _ => rfl⟩

private theorem wrap_span : Submodule.span ℝ (Set.range (wrapPoint (n := n))) = ⊤ := by
  apply top_unique
  intro x _
  rw [← wrap_combination x]
  exact Submodule.sum_mem _ fun k _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

private theorem wrap_mem (k : ZMod n) : wrapPoint k ∈ signedPoints n :=
  Or.inl ⟨k, rfl⟩

private theorem neg_wrap_mem (k : ZMod n) : -wrapPoint k ∈ signedPoints n :=
  Or.inr ⟨k, rfl⟩

private theorem normalized_affineSpan (n : ℕ) [NeZero n] :
    affineSpan ℝ (normalizedHull n) = ⊤ := by
  rw [normalizedHull, affineSpan_convexHull]
  have hzero : (0 : sumZero n) ∈ affineSpan ℝ (signedPoints n) := by
    have h := (convex_convexHull ℝ (signedPoints n)).midpoint_mem
      (subset_convexHull ℝ _ (wrap_mem (0 : ZMod n)))
      (subset_convexHull ℝ _ (neg_wrap_mem (0 : ZMod n)))
    simpa [midpoint_eq_smul_add] using convexHull_subset_affineSpan (𝕜 := ℝ) (signedPoints n) h
  rw [affineSpan_eq_span_iff_zero_mem.mpr hzero]
  apply top_unique
  intro x _
  change x ∈ Submodule.span ℝ (signedPoints n)
  apply Submodule.span_mono Set.subset_union_left
  rw [wrap_span]
  trivial

private theorem wrap_injective (hn : 3 ≤ n) : Function.Injective (wrapPoint (n := n)) := by
  intro i j h
  by_contra hne
  have hji : i ≠ j := hne
  have hi := congrArg (fun w : sumZero n => w.val i) h
  change (wrapPoint i).val i = (wrapPoint j).val i at hi
  simp [wrap_apply, hji] at hi
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

private theorem wrap_ne_neg (hn : 3 ≤ n) (i j : ZMod n) :
    wrapPoint i ≠ -wrapPoint j := by
  intro h
  have hi := congrArg (fun w : sumZero n => w.val i) h
  change (wrapPoint i).val i = -(wrapPoint j).val i at hi
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  by_cases hij : i = j
  · subst j
    simp [wrap_apply] at hi
    linarith
  · simp [wrap_apply, hij] at hi
    linarith

private theorem wrap_extreme (hn : 3 ≤ n) (k : ZMod n) :
    wrapPoint k ∈ (normalizedHull n).extremePoints ℝ := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let bound : ℝ := 1 - (n : ℝ)
  let cap : Set (sumZero n) := {x | x = wrapPoint k ∨ bound < coord k x}
  have hw : coord k (wrapPoint k) = bound := by
    change (wrapPoint k).val k = bound
    simp [wrap_apply, bound]
  have lower {x : sumZero n} (hx : x ∈ cap) : bound ≤ coord k x := by
    rcases hx with rfl | h
    · exact hw.ge
    · exact h.le
  have evalSegment {x y : sumZero n} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
      (hab : a + b = 1) (hx : x ∈ cap) (hy : y ∈ cap) :
      coord k (a • x + b • y) - bound =
        a * (coord k x - bound) + b * (coord k y - bound) := by
    simp only [map_add, map_smul, smul_eq_mul]
    linear_combination bound * hab
  have hconv : Convex ℝ cap := by
    rw [convex_iff_openSegment_subset]
    intro x hx y hy z hz
    rcases hz with ⟨a, b, ha, hb, hab, rfl⟩
    by_cases hxy : x = wrapPoint k ∧ y = wrapPoint k
    · rcases hxy with ⟨rfl, rfl⟩
      left
      rw [← add_smul, hab, one_smul]
    · right
      have hex : bound < coord k x ∨ bound < coord k y := by
        rcases hx with hx | hx <;> rcases hy with hy | hy
        · exact (hxy ⟨hx, hy⟩).elim
        · exact Or.inr hy
        · exact Or.inl hx
        · exact Or.inl hx
      have hdiff := evalSegment ha.le hb.le hab hx hy
      rcases hex with hx' | hy'
      · linarith [mul_pos ha (sub_pos.mpr hx'),
          mul_nonneg hb.le (sub_nonneg.mpr (lower hy))]
      · linarith [mul_nonneg ha.le (sub_nonneg.mpr (lower hx)),
          mul_pos hb (sub_pos.mpr hy')]
  have hsub : signedPoints n ⊆ cap := by
    intro x hx
    by_cases h : x = wrapPoint k
    · exact Or.inl h
    right
    have hne : x ∉ ({wrapPoint k} : Set (sumZero n)) := h
    change 1 - (n : ℝ) < x.val k
    rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have hkj : k ≠ j := fun h => hne (Set.mem_singleton_iff.mpr (congrArg wrapPoint h.symm))
      simp [wrap_apply, hkj]
      linarith
    · change 1 - (n : ℝ) < -(wrapPoint j).val k
      by_cases hkj : k = j
      · subst j
        simp [wrap_apply]
        linarith
      · simp [wrap_apply, hkj]
        linarith
  refine ⟨subset_convexHull ℝ _ (wrap_mem k), ?_⟩
  intro x hx y hy hxy
  have hx' := convexHull_min hsub hconv hx
  have hy' := convexHull_min hsub hconv hy
  rcases hxy with ⟨a, b, ha, hb, hab, h⟩
  have he := evalSegment ha.le hb.le hab hx' hy'
  rw [h, hw, sub_self] at he
  rcases hx' with hx' | hx'
  · exact hx'
  · linarith [mul_pos ha (sub_pos.mpr hx'),
      mul_nonneg hb.le (sub_nonneg.mpr (lower hy'))]

private theorem neg_image_signedPoints :
    (fun x : sumZero n => -x) '' signedPoints n = signedPoints n := by
  ext x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩ | ⟨k, rfl⟩, rfl⟩
    · exact neg_wrap_mem k
    · simpa using wrap_mem k
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨-wrapPoint k, neg_wrap_mem k, neg_neg _⟩
    · exact ⟨wrapPoint k, wrap_mem k, rfl⟩

private theorem normalized_extremePoints (hn : 3 ≤ n) :
    (normalizedHull n).extremePoints ℝ = signedPoints n := by
  refine extremePoints_convexHull_subset.antisymm ?_
  rintro x (⟨k, rfl⟩ | ⟨k, rfl⟩)
  · exact wrap_extreme hn k
  · let negEquiv : ↥(sumZero n) ≃ₗ[ℝ] ↥(sumZero n) := LinearEquiv.neg ℝ
    have hh : negEquiv '' normalizedHull n = normalizedHull n := by
      change negEquiv.toLinearMap '' convexHull ℝ _ = convexHull ℝ _
      rw [negEquiv.toLinearMap.image_convexHull]
      exact congrArg (convexHull ℝ) (neg_image_signedPoints (n := n))
    have h := Set.mem_image_of_mem negEquiv (wrap_extreme hn k)
    rw [image_extremePoints, hh] at h
    exact h

private def signedVertex : ZMod n ⊕ ZMod n → sumZero n :=
  Sum.elim wrapPoint (fun i => -wrapPoint i)

private theorem signedVertex_injective (hn : 3 ≤ n) :
    Function.Injective (signedVertex (n := n)) := by
  intro i j h
  rcases i with i | i <;> rcases j with j | j
  · exact congrArg Sum.inl (wrap_injective hn h)
  · exact (wrap_ne_neg hn i j h).elim
  · exact (wrap_ne_neg hn j i h.symm).elim
  · exact congrArg Sum.inr (wrap_injective hn (neg_injective h))

private theorem signedVertex_range : Set.range (signedVertex (n := n)) = signedPoints n := by
  ext x
  constructor
  · rintro ⟨i | i, rfl⟩
    · exact wrap_mem i
    · exact neg_wrap_mem i
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

private theorem centroid_weights :
    (∑ i : ZMod n ⊕ ZMod n, Finset.univ.centroidWeights ℝ i) = 1 :=
  Finset.univ.sum_centroidWeights_eq_one_of_card_ne_zero ℝ
    (Finset.card_ne_zero.mpr Finset.univ_nonempty)

private theorem normalized_centroid (n : ℕ) [NeZero n] :
    Finset.univ.centroid ℝ (signedVertex (n := n)) = 0 := by
  rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination _ _ _ centroid_weights]
  simp only [Finset.centroidWeights_apply, ← Finset.smul_sum]
  rw [Fintype.sum_sum_type]
  simp [signedVertex, sum_wrap]

/-- The subgroup of intrinsic affine bijections preserving a set. -/
def affineStabilizer {P V : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    (s : Set P) : Subgroup (P ≃ᵃ[ℝ] P) where
  carrier := {f | f '' s = s}
  one_mem' := Set.image_id s
  mul_mem' {f g} hf hg := by
    change f '' s = s at hf
    change g '' s = s at hg
    change (f ∘ g) '' s = s
    calc
      (f ∘ g) '' s = f '' (g '' s) := (Set.image_image (⇑f) (⇑g) s).symm
      _ = s := by rw [hg, hf]
  inv_mem' {f} hf := by
    change f '' s = s at hf
    change f.symm '' s = s
    calc
      f.symm '' s = f.symm '' (f '' s) := congrArg _ hf.symm
      _ = s := by
        rw [Set.image_image]
        simp

private theorem affine_image_extremePoints (f : sumZero n ≃ᵃ[ℝ] sumZero n)
    (s : Set (sumZero n)) :
    f '' s.extremePoints ℝ = (f '' s).extremePoints ℝ := by
  have imageSegment (x y : sumZero n) :
      f '' openSegment ℝ x y = openSegment ℝ (f x) (f y) :=
    image_openSegment ℝ f.toAffineMap x y
  apply Set.Subset.antisymm
  · rintro _ ⟨a, ha, rfl⟩
    refine ⟨⟨a, ha.1, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hseg
    rw [← imageSegment x y] at hseg
    obtain ⟨z, hz, hza⟩ := hseg
    have hza' : z = a := f.injective hza
    subst z
    exact congrArg f (ha.2 hx hy hz)
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := hb.1
    refine ⟨a, ⟨ha, ?_⟩, rfl⟩
    intro x hx y hy hseg
    apply f.injective
    apply hb.2 (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy)
    rw [← imageSegment x y]
    exact Set.mem_image_of_mem f hseg

private theorem preserves_signedPoints (hn : 3 ≤ n)
    (f : affineStabilizer (normalizedHull n)) :
    (f : sumZero n ≃ᵃ[ℝ] sumZero n) '' signedPoints n = signedPoints n := by
  have h : f.val '' normalizedHull n = normalizedHull n := f.property
  calc
    f.val '' signedPoints n = f.val '' (normalizedHull n).extremePoints ℝ :=
      congrArg (Set.image f.val) (normalized_extremePoints hn).symm
    _ = (f.val '' normalizedHull n).extremePoints ℝ := affine_image_extremePoints f.val _
    _ = signedPoints n := (congrArg (fun t : Set (sumZero n) => t.extremePoints ℝ) h).trans
      (normalized_extremePoints hn)

private theorem fixes_zero (hn : 3 ≤ n) (f : affineStabilizer (normalizedHull n)) :
    (f : sumZero n ≃ᵃ[ℝ] sumZero n) 0 = 0 := by
  let g := (f : sumZero n ≃ᵃ[ℝ] sumZero n)
  have hinj := signedVertex_injective hn
  have hcent :
      Finset.univ.centroid ℝ (g ∘ signedVertex) =
        Finset.univ.centroid ℝ (signedVertex (n := n)) := by
    apply Finset.univ.centroid_eq_of_inj_on_of_image_eq ℝ
    · exact fun _ _ _ _ h => hinj (g.injective h)
    · exact fun _ _ _ _ h => hinj h
    · simp only [Finset.coe_univ, Set.image_univ, Set.range_comp, signedVertex_range]
      exact preserves_signedPoints hn f
  calc
    g 0 = g (Finset.univ.centroid ℝ signedVertex) := congrArg (⇑g) (normalized_centroid n).symm
    _ = Finset.univ.centroid ℝ (g ∘ signedVertex) :=
      Finset.map_affineCombination Finset.univ signedVertex _ centroid_weights g.toAffineMap
    _ = Finset.univ.centroid ℝ signedVertex := hcent
    _ = 0 := normalized_centroid n

/-- The two real unit scalars whose square is one. -/
def Signs : Subgroup ℝˣ := (powMonoidHom 2 : ℝˣ →* ℝˣ).ker

/-- The real scalar associated to a common sign. -/
def signScalar (e : Signs) : ℝ := ((e : ℝˣ) : ℝ)

private theorem signScalar_injective : Function.Injective signScalar := by
  intro e d h
  exact Subtype.ext (Units.ext h)

@[simp] theorem signScalar_one : signScalar 1 = 1 := rfl

@[simp] theorem signScalar_mul (e d : Signs) :
    signScalar (e * d) = signScalar e * signScalar d := rfl

private theorem signScalar_cases (e : Signs) : signScalar e = 1 ∨ signScalar e = -1 := by
  apply sq_eq_one_iff.mp
  have h : (e : ℝˣ) ^ 2 = 1 := e.property
  have he := congrArg (fun u : ℝˣ => (u : ℝ)) h
  simpa [signScalar] using he

/-- The common sign that exchanges the two vertices of every pair. -/
def negativeSign : Signs := ⟨-1, by
  change (-1 : ℝˣ) ^ 2 = 1
  apply Units.ext
  norm_num⟩

@[simp] theorem signScalar_negativeSign : signScalar negativeSign = -1 := rfl

private theorem signed_wrap_eq (hn : 3 ≤ n) {e d : Signs} {i j : ZMod n}
    (h : signScalar e • wrapPoint i = signScalar d • wrapPoint j) :
    i = j ∧ e = d := by
  rcases signScalar_cases e with he | he <;> rcases signScalar_cases d with hd | hd
  · rw [he, hd, one_smul, one_smul] at h
    exact ⟨wrap_injective hn h, signScalar_injective (he.trans hd.symm)⟩
  · rw [he, hd, one_smul, neg_one_smul] at h
    exact (wrap_ne_neg hn i j h).elim
  · rw [he, hd, neg_one_smul, one_smul] at h
    exact (wrap_ne_neg hn j i h.symm).elim
  · rw [he, hd, neg_one_smul, neg_one_smul] at h
    exact ⟨wrap_injective hn (neg_injective h), signScalar_injective (he.trans hd.symm)⟩

private def permuteCoords (p : Equiv.Perm (ZMod n)) : ↥(sumZero n) ≃ₗ[ℝ] ↥(sumZero n) where
  toFun x := ⟨fun i => x.val (p.symm i), (p.symm.sum_comp x.val).trans x.property⟩
  invFun x := ⟨fun i => x.val (p i), (Equiv.sum_comp p x.val).trans x.property⟩
  left_inv x := Subtype.ext (funext fun i => by simp)
  right_inv x := Subtype.ext (funext fun i => by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem permuteCoords_wrap (p : Equiv.Perm (ZMod n)) (i : ZMod n) :
    permuteCoords p (wrapPoint i) = wrapPoint (p i) := by
  apply Subtype.ext
  funext j
  change (wrapPoint i).val (p.symm j) = (wrapPoint (p i)).val j
  simp only [wrap_apply, Equiv.symm_apply_eq]

private def signedCoords (p : Equiv.Perm (ZMod n)) (e : Signs) :
    ↥(sumZero n) ≃ₗ[ℝ] ↥(sumZero n) :=
  (permuteCoords p).trans (LinearEquiv.smulOfUnit (e : ℝˣ))

private theorem signedCoords_eval (p : Equiv.Perm (ZMod n)) (e : Signs) (x : sumZero n) :
    signedCoords p e x = signScalar e • permuteCoords p x := rfl

private theorem signedCoords_wrap (p : Equiv.Perm (ZMod n)) (e : Signs) (i : ZMod n) :
    signedCoords p e (wrapPoint i) = signScalar e • wrapPoint (p i) := by
  rw [signedCoords_eval, permuteCoords_wrap]

private theorem permute_image_signedPoints (p : Equiv.Perm (ZMod n)) :
    permuteCoords p '' signedPoints n = signedPoints n := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩ | ⟨i, rfl⟩, rfl⟩
    · rw [permuteCoords_wrap]
      exact wrap_mem _
    · rw [map_neg, permuteCoords_wrap]
      exact neg_wrap_mem _
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨wrapPoint (p.symm i), wrap_mem _, by simp [permuteCoords_wrap]⟩
    · exact ⟨-wrapPoint (p.symm i), neg_wrap_mem _, by simp [permuteCoords_wrap]⟩

private theorem signedCoords_image_hull (p : Equiv.Perm (ZMod n)) (e : Signs) :
    (signedCoords p e).toAffineEquiv '' normalizedHull n = normalizedHull n := by
  change (signedCoords p e).toLinearMap '' convexHull ℝ _ = convexHull ℝ _
  rw [LinearMap.image_convexHull]
  congr 1
  change (fun x => signedCoords p e x) '' signedPoints n = signedPoints n
  rcases signScalar_cases e with he | he
  · simp only [signedCoords_eval, he, one_smul]
    exact permute_image_signedPoints p
  · simp only [signedCoords_eval, he, neg_one_smul]
    calc
      (fun x => -permuteCoords p x) '' signedPoints n =
          (fun x : sumZero n => -x) '' (permuteCoords p '' signedPoints n) :=
        (Set.image_image _ _ _).symm
      _ = signedPoints n := by rw [permute_image_signedPoints, neg_image_signedPoints]

/-- Coordinate permutations and common signs give affine preservers of the normalized hull. -/
private def normalizedAction (n : ℕ) [NeZero n] :
    Equiv.Perm (ZMod n) × Signs →* affineStabilizer (normalizedHull n) where
  toFun g := ⟨(signedCoords g.1 g.2).toAffineEquiv, signedCoords_image_hull g.1 g.2⟩
  map_one' := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change signedCoords 1 1 x = x
    rw [signedCoords_eval, signScalar_one, one_smul]
    rfl
  map_mul' g h := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change signedCoords (g.1 * h.1) (g.2 * h.2) x =
      signedCoords g.1 g.2 (signedCoords h.1 h.2 x)
    simp only [signedCoords_eval, signScalar_mul, map_smul, smul_smul]
    rw [mul_comm (signScalar g.2) (signScalar h.2)]
    rfl

private theorem normalizedAction_wrap (g : Equiv.Perm (ZMod n) × Signs) (i : ZMod n) :
    ((normalizedAction n g).val) (wrapPoint i) = signScalar g.2 • wrapPoint (g.1 i) :=
  signedCoords_wrap g.1 g.2 i

private theorem normalizedAction_injective (hn : 3 ≤ n) :
    Function.Injective (normalizedAction n) := by
  intro g h he
  have hw (i : ZMod n) : g.1 i = h.1 i ∧ g.2 = h.2 := by
    apply signed_wrap_eq hn
    rw [← normalizedAction_wrap g i, ← normalizedAction_wrap h i, he]
  exact Prod.ext (Equiv.ext fun i => (hw i).1) (hw 0).2

private theorem stabilizer_apply_linear (hn : 3 ≤ n) (f : affineStabilizer (normalizedHull n))
    (x : sumZero n) : f.val x = f.val.linear x := by
  have h := f.val.map_vadd 0 x
  simpa [fixes_zero hn f] using h

private theorem normalizedAction_surjective (hn : 3 ≤ n) :
    Function.Surjective (normalizedAction n) := by
  intro f
  have he (i : ZMod n) : ∃ j : ZMod n, ∃ e : Signs,
      f.val (wrapPoint i) = signScalar e • wrapPoint j := by
    have hh := Set.mem_image_of_mem f.val (wrap_mem i)
    rw [preserves_signedPoints hn f] at hh
    rcases hh with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact ⟨j, 1, by simpa using hj.symm⟩
    · exact ⟨j, negativeSign, by simpa using hj.symm⟩
  choose j e he using he
  have hl (i : ZMod n) : f.val.linear (wrapPoint i) = signScalar (e i) • wrapPoint (j i) :=
    (stabilizer_apply_linear hn f _).symm.trans (he i)
  have hj : Function.Injective j := by
    intro i k hik
    have hi := hl i
    have hk := hl k
    rw [hik] at hi
    rcases signScalar_cases (e i) with ei | ei <;>
      rcases signScalar_cases (e k) with ek | ek <;>
      simp only [ei, ek, one_smul, neg_one_smul] at hi hk
    · exact wrap_injective hn (f.val.linear.injective (hi.trans hk.symm))
    · have hneg : wrapPoint (j k) = -(f.val.linear (wrapPoint k)) := by
        simpa only [neg_neg] using congrArg Neg.neg hk.symm
      have h := hi.trans hneg
      rw [← map_neg] at h
      exact (wrap_ne_neg hn i k (f.val.linear.injective h)).elim
    · have hneg : wrapPoint (j k) = -(f.val.linear (wrapPoint i)) := by
        simpa only [neg_neg] using congrArg Neg.neg hi.symm
      have h := hk.trans hneg
      rw [← map_neg] at h
      exact (wrap_ne_neg hn k i (f.val.linear.injective h)).elim
    · exact wrap_injective hn (f.val.linear.injective (hi.trans hk.symm))
  let p : Equiv.Perm (ZMod n) := Equiv.ofBijective j ⟨hj, Finite.surjective_of_injective hj⟩
  have hp (i : ZMod n) : p i = j i := rfl
  let coefficients : ZMod n → ℝ := fun k => signScalar (e (p.symm k))
  have hs : ∑ k, coefficients k • wrapPoint k = 0 := by
    calc
      (∑ k, coefficients k • wrapPoint k) =
          ∑ i, coefficients (p i) • wrapPoint (p i) := (Equiv.sum_comp p (fun k => coefficients k • wrapPoint k)).symm
      _ = ∑ i, f.val.linear (wrapPoint i) := by
        apply sum_congr rfl
        intro i _
        have heval : coefficients (p i) = signScalar (e i) := by
          simp only [coefficients, Equiv.symm_apply_apply]
        rw [heval, hp i, hl]
      _ = 0 := by rw [← map_sum, sum_wrap, map_zero]
  obtain ⟨c, hc⟩ := (wrap_dependence coefficients).mp hs
  have hcommon (i : ZMod n) : e i = e 0 := by
    apply signScalar_injective
    simpa only [coefficients, Equiv.symm_apply_apply] using (hc (p i)).trans (hc (p 0)).symm
  refine ⟨(p, e 0), ?_⟩
  apply Subtype.ext
  apply AffineEquiv.ext
  intro x
  rw [stabilizer_apply_linear hn f]
  change signedCoords p (e 0) x = f.val.linear x
  rw [← wrap_combination x]
  simp only [map_sum, map_smul]
  apply sum_congr rfl
  intro i _
  rw [signedCoords_wrap, hl, hp i, hcommon i]

/-- All affine preservers of the normalized hull, with composition as group multiplication. -/
private def normalizedStabilizerEquiv (hn : 3 ≤ n) :
    (Equiv.Perm (ZMod n) × Signs) ≃* affineStabilizer (normalizedHull n) :=
  MulEquiv.ofBijective (normalizedAction n)
    ⟨normalizedAction_injective hn, normalizedAction_surjective hn⟩

/-- The affine hyperplane through the orbit center with sum-zero direction. -/
def sourcePlane (n : ℕ) [NeZero n] : AffineSubspace ℝ (Coordinates n) :=
  AffineSubspace.mk' (center n) (sumZero n)

private theorem mem_sourcePlane (x : Coordinates n) :
    x ∈ sourcePlane n ↔ ∑ i, x i = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  change (∑ i : ZMod n, (x i - center n i)) = 0 ↔ _
  rw [sum_sub_distrib, sub_eq_zero]
  have hcenter : ∑ i : ZMod n, center n i = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    simp [center, ZMod.card, nsmul_eq_mul]
    ring
  rw [hcenter]

/-- The center as a point of the intrinsic affine hyperplane. -/
def sourceCenter (n : ℕ) [NeZero n] : sourcePlane n :=
  ⟨center n, AffineSubspace.self_mem_mk' _ _⟩

instance sourcePlane_nonempty (n : ℕ) [NeZero n] : Nonempty (sourcePlane n) :=
  ⟨sourceCenter n⟩

/-- Translate sum-zero vectors to the intrinsic source hyperplane. -/
private def centerChart (n : ℕ) [NeZero n] : ↥(sumZero n) ≃ᵃ[ℝ] ↥(sourcePlane n) :=
  (LinearEquiv.ofEq (sumZero n) (sourcePlane n).direction
    (AffineSubspace.direction_mk' (center n) (sumZero n)).symm).toAffineEquiv.trans
    (AffineEquiv.vaddConst ℝ (sourceCenter n))

private theorem centerChart_coe (x : sumZero n) :
    (centerChart n x).val = x.val + center n := rfl

/-- The original paper hull, as a set in its intrinsic affine hyperplane. -/
def sourceHull (n : ℕ) [NeZero n] : Set (sourcePlane n) :=
  (sourcePlane n).subtype ⁻¹' Q n

private theorem ambient_chart_image (hn : 3 ≤ n) :
    ((sourcePlane n).subtype : sourcePlane n → Coordinates n) ''
      (centerChart n '' centeredQ n) = Q n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _⟩ := source_coordinate_conjugacy n hn
  calc
    ((sourcePlane n).subtype : sourcePlane n → Coordinates n) ''
        (centerChart n '' centeredQ n) =
        (fun x : Coordinates n => x + center n) '' ((fun w : sumZero n => w.val) '' centeredQ n) := by
      rw [Set.image_image, Set.image_image]
      rfl
    _ = Q n := by
      rw [h, Set.image_image]
      simp

private theorem centerChart_image (hn : 3 ≤ n) :
    centerChart n '' centeredQ n = sourceHull n := by
  rw [sourceHull, ← ambient_chart_image hn]
  exact Set.preimage_image_eq _ Subtype.val_injective |>.symm

private theorem delta_image (hn : 3 ≤ n) :
    delta n '' centeredQ n = normalizedHull n := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩ := source_coordinate_conjugacy n hn
  exact h

private theorem centered_affineSpan (hn : 3 ≤ n) :
    affineSpan ℝ (centeredQ n) = ⊤ := by
  let e := (delta n).symm.toAffineEquiv
  have h : e.toAffineMap '' normalizedHull n = centeredQ n := by
    rw [← delta_image hn, Set.image_image]
    change (fun x => (delta n).symm (delta n x)) '' centeredQ n = _
    simp
  rw [← h]
  exact e.toAffineMap.span_eq_top_of_surjective e.surjective (normalized_affineSpan n)

private theorem source_affineSpan (hn : 3 ≤ n) :
    affineSpan ℝ (Q n) = sourcePlane n := by
  let g := (sourcePlane n).subtype.comp (centerChart n).toAffineMap
  have heq : g '' centeredQ n = Q n := by
    rw [← ambient_chart_image hn, Set.image_image]
    rfl
  rw [← heq, ← AffineSubspace.map_span g, centered_affineSpan hn]
  ext x
  change x ∈ g '' (Set.univ : Set (sumZero n)) ↔ x ∈ sourcePlane n
  constructor
  · rintro ⟨y, -, rfl⟩
    exact (centerChart n y).property
  · intro hx
    obtain ⟨y, hy⟩ := (centerChart n).surjective ⟨x, hx⟩
    exact ⟨y, Set.mem_univ _, congrArg Subtype.val hy⟩

/-- Center the source hull and take the forward cyclic difference. -/
private def sourceNormalize (n : ℕ) [NeZero n] : ↥(sourcePlane n) ≃ᵃ[ℝ] ↥(sumZero n) :=
  (centerChart n).symm.trans (delta n).toAffineEquiv

private theorem sourceNormalize_image (hn : 3 ≤ n) :
    sourceNormalize n '' sourceHull n = normalizedHull n := by
  rw [← centerChart_image hn, Set.image_image]
  change (fun x => delta n ((centerChart n).symm (centerChart n x))) '' centeredQ n = _
  simpa only [AffineEquiv.symm_apply_apply] using delta_image hn

private theorem sourceNormalize_chart (x : sumZero n) :
    sourceNormalize n (centerChart n x) = delta n x := by
  change delta n ((centerChart n).symm (centerChart n x)) = delta n x
  rw [AffineEquiv.symm_apply_apply]

private def transportStabilizer {P V P' V' : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    [AddCommGroup V'] [Module ℝ V'] [AddTorsor V' P']
    (e : P ≃ᵃ[ℝ] P') {s : Set P} {t : Set P'} (h : e '' s = t) :
    affineStabilizer s →* affineStabilizer t where
  toFun f := ⟨e.symm.trans (f.val.trans e), by
    change (fun x => e (f.val (e.symm x))) '' t = t
    calc
      (fun x => e (f.val (e.symm x))) '' t =
          (fun x => e (f.val (e.symm x))) '' (e '' s) := congrArg _ h.symm
      _ = e '' (f.val '' s) := by
        rw [Set.image_image, Set.image_image]
        simp only [AffineEquiv.symm_apply_apply]
      _ = e '' s := congrArg (Set.image e) f.property
      _ = t := h⟩
  map_one' := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change e (e.symm x) = x
    exact e.apply_symm_apply x
  map_mul' f g := by
    apply Subtype.ext
    apply AffineEquiv.ext
    intro x
    change e (f.val (g.val (e.symm x))) = e (f.val (e.symm (e (g.val (e.symm x)))))
    rw [AffineEquiv.symm_apply_apply]

private def stabilizerCongr {P V P' V' : Type*}
    [AddCommGroup V] [Module ℝ V] [AddTorsor V P]
    [AddCommGroup V'] [Module ℝ V'] [AddTorsor V' P']
    (e : P ≃ᵃ[ℝ] P') {s : Set P} {t : Set P'} (h : e '' s = t) :
    affineStabilizer s ≃* affineStabilizer t :=
  let hi : e.symm '' t = s := by
    rw [← h, Set.image_image]
    simp
  { transportStabilizer e h with
    invFun := transportStabilizer e.symm hi
    left_inv := fun f => by
      apply Subtype.ext
      apply AffineEquiv.ext
      intro x
      change e.symm (e (f.val (e.symm (e x)))) = f.val x
      simp
    right_inv := fun f => by
      apply Subtype.ext
      apply AffineEquiv.ext
      intro x
      change e (e.symm (f.val (e (e.symm x)))) = f.val x
      simp }

/-- The source rotation vertex bearing the literal paper label. -/
def sourceR (a : PaperLabels n) : sourcePlane n :=
  centerChart n (rCentered ((paperLabelsEquiv n).symm a))

/-- The source antipode bearing the same literal paper label. -/
def sourceF (a : PaperLabels n) : sourcePlane n :=
  centerChart n (fCentered ((paperLabelsEquiv n).symm a))

private theorem sourceR_coe (a : PaperLabels n) :
    (sourceR a).val = r (a.val : ZMod n) := by
  rw [sourceR, centerChart_coe]
  change r (a.val : ZMod n) - center n + center n = _
  exact sub_add_cancel _ _

private theorem sourceF_coe (a : PaperLabels n) :
    (sourceF a).val = f (a.val : ZMod n) := by
  rw [sourceF, centerChart_coe]
  change f (a.val : ZMod n) - center n + center n = _
  exact sub_add_cancel _ _

/-- The wrap index of the positive vertex with a given one-based paper label. -/
private def paperWrapIndex (n : ℕ) [NeZero n] : PaperLabels n ≃ ZMod n :=
  (paperLabelsEquiv n).symm.trans (reflection (1 : ZMod n))

private theorem sourceNormalize_vertices (hn : 3 ≤ n) (a : PaperLabels n) :
    sourceNormalize n (sourceR a) = wrapPoint (paperWrapIndex n a) ∧
    sourceNormalize n (sourceF a) = -wrapPoint (paperWrapIndex n a) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩ := source_coordinate_conjugacy n hn
  rw [sourceR, sourceF, sourceNormalize_chart, sourceNormalize_chart]
  exact h ((paperLabelsEquiv n).symm a)

private theorem sourceNormalize_center (n : ℕ) [NeZero n] :
    sourceNormalize n (sourceCenter n) = 0 := by
  have hz : centerChart n 0 = sourceCenter n := by
    apply Subtype.ext
    rw [centerChart_coe]
    exact zero_add _
  rw [← hz, sourceNormalize_chart, map_zero]

/-- Full real affine stabilizer of the source hull, indexed by the literal paper labels. -/
def sourceStabilizerEquiv (hn : 3 ≤ n) :
    (Equiv.Perm (PaperLabels n) × Signs) ≃* affineStabilizer (sourceHull n) :=
  let e := sourceNormalize n
  let h : e.symm '' normalizedHull n = sourceHull n := by
    have he : e '' sourceHull n = normalizedHull n := sourceNormalize_image hn
    rw [← he, Set.image_image]
    have hid : (fun x => e.symm (e x)) = id := funext e.symm_apply_apply
    rw [hid, Set.image_id]
  (MulEquiv.prodCongr (paperWrapIndex n).permCongrHom (MulEquiv.refl Signs)).trans
    ((normalizedStabilizerEquiv hn).trans (stabilizerCongr e.symm h))

private theorem sourceStabilizerEquiv_apply (hn : 3 ≤ n)
    (g : Equiv.Perm (PaperLabels n) × Signs) (x : sourcePlane n) :
    (sourceStabilizerEquiv hn g).val x =
      (sourceNormalize n).symm
        (signedCoords ((paperWrapIndex n).permCongr g.1) g.2 (sourceNormalize n x)) := rfl

private theorem source_stabilizer_normalized_vertices (hn : 3 ≤ n)
    (g : Equiv.Perm (PaperLabels n) × Signs) (a : PaperLabels n) :
    sourceNormalize n ((sourceStabilizerEquiv hn g).val (sourceR a)) =
      signScalar g.2 • wrapPoint (paperWrapIndex n (g.1 a)) ∧
    sourceNormalize n ((sourceStabilizerEquiv hn g).val (sourceF a)) =
      signScalar g.2 • (-wrapPoint (paperWrapIndex n (g.1 a))) := by
  let p := (paperWrapIndex n).permCongr g.1
  have hp : p (paperWrapIndex n a) = paperWrapIndex n (g.1 a) := by
    change paperWrapIndex n (g.1 ((paperWrapIndex n).symm (paperWrapIndex n a))) = _
    rw [Equiv.symm_apply_apply]
  constructor
  · rw [sourceStabilizerEquiv_apply, AffineEquiv.apply_symm_apply,
      (sourceNormalize_vertices hn a).1, signedCoords_wrap]
    exact congrArg (fun k => signScalar g.2 • wrapPoint k) hp
  · rw [sourceStabilizerEquiv_apply, AffineEquiv.apply_symm_apply,
      (sourceNormalize_vertices hn a).2, map_neg, signedCoords_wrap, smul_neg]
    exact congrArg (fun k => -(signScalar g.2 • wrapPoint k)) hp

/-- The source affine map acts by relabeling the pairs and one common sign. -/
private theorem source_stabilizer_action (hn : 3 ≤ n)
    (g : Equiv.Perm (PaperLabels n) × Signs) (a : PaperLabels n) :
    ((sourceStabilizerEquiv hn g).val (sourceR a)).val =
      center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n) ∧
    ((sourceStabilizerEquiv hn g).val (sourceF a)).val =
      center n + signScalar g.2 • ((sourceF (g.1 a)).val - center n) := by
  let R := rCentered ((paperLabelsEquiv n).symm (g.1 a))
  let F := fCentered ((paperLabelsEquiv n).symm (g.1 a))
  have normalized_r :
      delta n R = wrapPoint (paperWrapIndex n (g.1 a)) := by
    simpa only [sourceR, sourceNormalize_chart] using (sourceNormalize_vertices hn (g.1 a)).1
  have normalized_f :
      delta n F = -wrapPoint (paperWrapIndex n (g.1 a)) := by
    simpa only [sourceF, sourceNormalize_chart] using (sourceNormalize_vertices hn (g.1 a)).2
  have hr : (sourceStabilizerEquiv hn g).val (sourceR a) = centerChart n (signScalar g.2 • R) := by
    apply (sourceNormalize n).injective
    rw [(source_stabilizer_normalized_vertices hn g a).1, sourceNormalize_chart,
      map_smul, normalized_r]
  have hf : (sourceStabilizerEquiv hn g).val (sourceF a) = centerChart n (signScalar g.2 • F) := by
    apply (sourceNormalize n).injective
    rw [(source_stabilizer_normalized_vertices hn g a).2, sourceNormalize_chart,
      map_smul, normalized_f]
  constructor
  · rw [hr, sourceR, centerChart_coe, centerChart_coe, add_sub_cancel_right, add_comm]
    rfl
  · rw [hf, sourceF, centerChart_coe, centerChart_coe, add_sub_cancel_right, add_comm]
    rfl

private theorem source_parameters_unique (hn : 3 ≤ n)
    {g h : Equiv.Perm (PaperLabels n) × Signs}
    (he : ∀ a : PaperLabels n,
      ((sourceStabilizerEquiv hn g).val (sourceR a)).val =
        ((sourceStabilizerEquiv hn h).val (sourceR a)).val) : g = h := by
  have hparam (a : PaperLabels n) : g.1 a = h.1 a ∧ g.2 = h.2 := by
    have he' := congrArg (sourceNormalize n) (Subtype.ext (he a))
    rw [(source_stabilizer_normalized_vertices hn g a).1,
      (source_stabilizer_normalized_vertices hn h a).1] at he'
    obtain ⟨hi, hs⟩ := signed_wrap_eq hn he'
    exact ⟨(paperWrapIndex n).injective hi, hs⟩
  exact Prod.ext (Equiv.ext fun a => (hparam a).1) (hparam (paperLabelsEquiv n 0)).2

/-- The source rotations alone determine the affine preserver for a given pair action. -/
private theorem source_stabilizer_realization (hn : 3 ≤ n) (g : Equiv.Perm (PaperLabels n) × Signs) :
    ∃! T : affineStabilizer (sourceHull n), ∀ a : PaperLabels n,
      (T.val (sourceR a)).val = center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n) := by
  refine ⟨sourceStabilizerEquiv hn g, fun a => (source_stabilizer_action hn g a).1, ?_⟩
  intro T hT
  obtain ⟨h, rfl⟩ := (sourceStabilizerEquiv hn).surjective T
  have hh : h = g := source_parameters_unique hn
    (fun a => (hT a).trans (source_stabilizer_action hn g a).1.symm)
  rw [hh]

/-- Every intrinsic affine preserver has exactly one literal permutation and common sign. -/
private theorem source_stabilizer_exhaustion (hn : 3 ≤ n) (T : affineStabilizer (sourceHull n)) :
    ∃! g : Equiv.Perm (PaperLabels n) × Signs, ∀ a : PaperLabels n,
      (T.val (sourceR a)).val = center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n) := by
  obtain ⟨g, rfl⟩ := (sourceStabilizerEquiv hn).surjective T
  refine ⟨g, fun a => (source_stabilizer_action hn g a).1, ?_⟩
  intro h hh
  exact source_parameters_unique hn (fun a => (source_stabilizer_action hn h a).1.trans (hh a).symm)

private theorem source_stabilizer_fixes_center (hn : 3 ≤ n) (T : affineStabilizer (sourceHull n)) :
    T.val (sourceCenter n) = sourceCenter n := by
  obtain ⟨g, rfl⟩ := (sourceStabilizerEquiv hn).surjective T
  apply (sourceNormalize n).injective
  rw [sourceStabilizerEquiv_apply, AffineEquiv.apply_symm_apply, sourceNormalize_center, map_zero]

private theorem source_stabilizer_composition (hn : 3 ≤ n)
    (g h : Equiv.Perm (PaperLabels n) × Signs) (x : sourcePlane n) :
    (sourceStabilizerEquiv hn (g.1 * h.1, g.2 * h.2)).val x =
      (sourceStabilizerEquiv hn g).val ((sourceStabilizerEquiv hn h).val x) := by
  change (sourceStabilizerEquiv hn (g * h)).val x = _
  rw [map_mul]
  rfl

private theorem source_stabilizer_central_flip (hn : 3 ≤ n) (x : sourcePlane n) :
    ((sourceStabilizerEquiv hn (1, negativeSign)).val x).val = (2 : ℝ) • center n - x.val := by
  have ha :
      (sourceStabilizerEquiv hn (1, negativeSign)).val x =
        (sourceNormalize n).symm (-(sourceNormalize n x)) := by
    change (sourceNormalize n).symm
        (signedCoords ((paperWrapIndex n).permCongrHom 1) negativeSign (sourceNormalize n x)) = _
    rw [map_one, signedCoords_eval, signScalar_negativeSign, neg_one_smul]
    rfl
  rw [ha]
  obtain ⟨v, rfl⟩ := (centerChart n).surjective x
  rw [sourceNormalize_chart, ← map_neg]
  have hc : (sourceNormalize n).symm (delta n (-v)) = centerChart n (-v) := by
    apply (sourceNormalize n).injective
    rw [AffineEquiv.apply_symm_apply, sourceNormalize_chart]
  rw [hc, centerChart_coe, centerChart_coe]
  change -v.val + center n = (2 : ℝ) • center n - (v.val + center n)
  rw [two_smul]
  abel

private theorem signs_card : Nat.card Signs = 2 := by
  have hne : negativeSign ≠ (1 : Signs) := by
    intro h
    have he := congrArg signScalar h
    norm_num at he
  let e : Bool ≃ Signs := Equiv.ofBijective (fun b : Bool => if b then negativeSign else 1) (by
    constructor
    · intro b₁ b₂ h
      cases b₁ <;> cases b₂ <;> simp_all
    · intro s
      rcases signScalar_cases s with h | h
      · refine ⟨false, signScalar_injective ?_⟩
        simpa using h.symm
      · refine ⟨true, signScalar_injective ?_⟩
        simpa using h.symm)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  decide

private theorem source_stabilizer_card (hn : 3 ≤ n) :
    Nat.card (affineStabilizer (sourceHull n)) = 2 * Nat.factorial n := by
  let : Finite (PaperLabels n) := Finite.of_equiv (ZMod n) (paperLabelsEquiv n)
  have hlabels : Nat.card (PaperLabels n) = n := by
    rw [← Nat.card_congr (paperLabelsEquiv n), Nat.card_eq_fintype_card, ZMod.card]
  rw [← Nat.card_congr (sourceStabilizerEquiv hn).toEquiv,
    Nat.card_prod, Nat.card_perm, hlabels, signs_card]
  exact Nat.mul_comm _ _


/-- Question 6.2 on the source hull, including the action on both paper vertex families. -/
theorem result (n : ℕ) (hn : 3 ≤ n) :
    letI : NeZero n := ⟨by omega⟩
    affineSpan ℝ (Q n) = sourcePlane n ∧
    (∀ x : Coordinates n,
      x ∈ sourcePlane n ↔ ∑ i, x i = (n : ℝ) * ((n : ℝ) + 1) / 2) ∧
    (∀ a : PaperLabels n,
      (sourceR a).val = r (a.val : ZMod n) ∧ (sourceF a).val = f (a.val : ZMod n)) ∧
    (∀ (g : Equiv.Perm (PaperLabels n) × Signs) (a : PaperLabels n),
      ((sourceStabilizerEquiv hn g).val (sourceR a)).val =
        center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n) ∧
      ((sourceStabilizerEquiv hn g).val (sourceF a)).val =
        center n + signScalar g.2 • ((sourceF (g.1 a)).val - center n)) ∧
    (∀ g : Equiv.Perm (PaperLabels n) × Signs,
      ∃! T : affineStabilizer (sourceHull n), ∀ a : PaperLabels n,
        (T.val (sourceR a)).val =
          center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n)) ∧
    (∀ T : affineStabilizer (sourceHull n),
      ∃! g : Equiv.Perm (PaperLabels n) × Signs, ∀ a : PaperLabels n,
        (T.val (sourceR a)).val =
          center n + signScalar g.2 • ((sourceR (g.1 a)).val - center n)) ∧
    (∀ T : affineStabilizer (sourceHull n), T.val (sourceCenter n) = sourceCenter n) ∧
    (∀ (g h : Equiv.Perm (PaperLabels n) × Signs) (x : sourcePlane n),
      (sourceStabilizerEquiv hn (g.1 * h.1, g.2 * h.2)).val x =
        (sourceStabilizerEquiv hn g).val ((sourceStabilizerEquiv hn h).val x)) ∧
    (∀ x : sourcePlane n,
      ((sourceStabilizerEquiv hn (1, negativeSign)).val x).val = (2 : ℝ) • center n - x.val) ∧
    Nat.card (affineStabilizer (sourceHull n)) = 2 * Nat.factorial n := by
  letI : NeZero n := ⟨by omega⟩
  exact ⟨source_affineSpan hn, mem_sourcePlane, fun a => ⟨sourceR_coe a, sourceF_coe a⟩,
    source_stabilizer_action hn, source_stabilizer_realization hn,
    source_stabilizer_exhaustion hn, source_stabilizer_fixes_center hn,
    source_stabilizer_composition hn, source_stabilizer_central_flip hn,
    source_stabilizer_card hn⟩

end

end OlairezQ62
