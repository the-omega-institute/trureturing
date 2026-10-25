import D5.S3.Geometry.Hyperideal.LengthGramSideTrace
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate

noncomputable section
open Set
open scoped BigOperators
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
open D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private support_barycenter from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
open private endpoint_support from D5.S3.Geometry.Hyperideal.LengthGramSideTrace
set_option autoImplicit false
set_option maxRecDepth 10000

namespace CFMPCellIntersections435Transient

def mix {E : Type*} [AddCommMonoid E] [Module ℝ E] {k : ℕ}
    (w : Fin k → ℝ) (p : Fin k → E) : E := ∑ i, w i • p i

lemma mix_support {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (L : E →ₗ[ℝ] ℝ) (a : Fin (k+1) → ℝ) (p : Fin (k+1) → E) :
    L (mix a p) = a 0 * L (p 0) + ∑ i : Fin k, a i.succ * L (p i.succ) := by
  simp only [mix, Fin.sum_univ_succ, map_add, map_sum, map_smul, smul_eq_mul]

lemma strict_head_coefficient {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (L : E →ₗ[ℝ] ℝ) (p q : Fin (k+1) → E) (a b : Fin (k+1) → ℝ)
    (he : mix a p = mix b q) (hhead : p 0 = q 0)
    (hneg : L (p 0) < 0) (hp : ∀ i : Fin k, L (p i.succ) = 0)
    (hb : ∀ i, 0 < b i) (hq : ∀ i : Fin k, L (q i.succ) ≤ 0)
    (hstrict : ∃ i : Fin k, L (q i.succ) < 0) : b 0 < a 0 := by
  have htail : (∑ i : Fin k, b i.succ * L (q i.succ)) < 0 := by
    obtain ⟨i, hi⟩ := hstrict
    have h := Finset.sum_lt_sum
      (s := (Finset.univ : Finset (Fin k)))
      (f := fun j => b j.succ * L (q j.succ)) (g := fun _ => (0 : ℝ))
      (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hb j.succ).le (hq j))
      ⟨i, Finset.mem_univ i, mul_neg_of_pos_of_neg (hb i.succ) hi⟩
    simpa using h
  have h := congrArg L he
  rw [mix_support, mix_support] at h
  simp only [hp, mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [← hhead] at h
  exact (mul_lt_mul_right_of_neg hneg).mp (by linarith)

lemma equal_head_coefficient {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (L : E →ₗ[ℝ] ℝ) (p q : Fin (k+1) → E) (a b : Fin (k+1) → ℝ)
    (he : mix a p = mix b q) (hhead : p 0 = q 0)
    (hneg : L (p 0) < 0) (hp : ∀ i : Fin k, L (p i.succ) = 0)
    (hq : ∀ i : Fin k, L (q i.succ) = 0) : a 0 = b 0 := by
  have h := congrArg L he
  rw [mix_support, mix_support] at h
  simp only [hp, hq, mul_zero, Finset.sum_const_zero, add_zero] at h
  rw [← hhead] at h
  exact mul_right_cancel₀ hneg.ne h

lemma tails_equal {E : Type*} [AddCommGroup E] [Module ℝ E] {k : ℕ}
    (p q : Fin (k+1) → E) (a b : Fin (k+1) → ℝ)
    (he : mix a p = mix b q) (hhead : p 0 = q 0) (hw : a 0 = b 0) :
    mix (fun i : Fin k => a i.succ) (fun i => p i.succ) =
      mix (fun i : Fin k => b i.succ) (fun i => q i.succ) := by
  simp only [mix, Fin.sum_univ_succ] at he
  rw [hhead, hw] at he
  exact add_left_cancel he



def labels : Fin 20 → Fin 3 → Fin 4 × Fin 4 :=
  ![![(0,1), (0,2), (0,3)],
    ![(1,0), (1,2), (1,3)],
    ![(2,0), (2,1), (2,3)],
    ![(3,0), (3,1), (3,2)],
    ![(1,2), (2,1), (2,3)],
    ![(1,2), (2,3), (3,2)],
    ![(1,2), (3,2), (3,1)],
    ![(1,2), (3,1), (1,3)],
    ![(0,2), (2,0), (2,3)],
    ![(0,2), (2,3), (3,2)],
    ![(0,2), (3,2), (3,0)],
    ![(0,2), (3,0), (0,3)],
    ![(0,1), (1,0), (1,3)],
    ![(0,1), (1,3), (3,1)],
    ![(0,1), (3,1), (3,0)],
    ![(0,1), (3,0), (0,3)],
    ![(0,1), (1,0), (1,2)],
    ![(0,1), (1,2), (2,1)],
    ![(0,1), (2,1), (2,0)],
    ![(0,1), (2,0), (0,2)]]

lemma labels_ne (n : Fin 20) (j : Fin 3) : (labels n j).1 ≠ (labels n j).2 := by
  fin_cases n <;> fin_cases j <;> decide

lemma vertices_tail (l : Fin 6 → ℝ) (n : Fin 20) (j : Fin 3) :
    vertices l n j.succ = endpoint l (labels n j).1 (labels n j).2 := by
  fin_cases n <;> fin_cases j <;> rfl

lemma vertices_head (l : Fin 6 → ℝ) (n : Fin 20) : vertices l n 0 = barycenter := by
  fin_cases n <;> rfl

lemma own_facet_incident : ∀ n : Fin 20, ∀ j : Fin 3,
    incident (facet n) (labels n j).1 (labels n j).2 := by decide

lemma other_facet_strict : ∀ n : Fin 20, ∀ f : Support, f ≠ facet n →
    ∃ j : Fin 3, ¬incident f (labels n j).1 (labels n j).2 := by decide

lemma same_facet_roots : ∀ n m : Fin 20, n ≠ m → facet n = facet m →
    labels n 0 = labels m 0 := by decide

lemma same_facet_ridge : ∀ n m : Fin 20, n ≠ m → facet n = facet m →
    (¬incident (ridge n) (labels n 0).1 (labels n 0).2) ∧
    (∀ j : Fin 2, incident (ridge n) (labels n j.succ).1 (labels n j.succ).2) ∧
    (∃ j : Fin 2, ¬incident (ridge n) (labels m j.succ).1 (labels m j.succ).2) := by
  decide

lemma boundary_nonpos (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (f : Support) (j : Fin 3) : support l f (vertices l n j.succ) ≤ 0 := by
  rw [vertices_tail]
  by_cases h : incident f (labels n j).1 (labels n j).2
  · exact le_of_eq ((endpoint_support l hl f _ _ (labels_ne n j)).1 h)
  · exact ((endpoint_support l hl f _ _ (labels_ne n j)).2 h).le

lemma facet_zero (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (j : Fin 3) : support l (facet n) (vertices l n j.succ) = 0 := by
  rw [vertices_tail]
  exact (endpoint_support l hl _ _ _ (labels_ne n j)).1 (own_facet_incident n j)

lemma other_boundary_strict (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (f : Support) (hf : f ≠ facet n) :
    ∃ j : Fin 3, support l f (vertices l n j.succ) < 0 := by
  obtain ⟨j,hj⟩ := other_facet_strict n f hf
  refine ⟨j,?_⟩
  rw [vertices_tail]
  exact (endpoint_support l hl _ _ _ (labels_ne n j)).2 hj

lemma same_facet_root_eq (l : Fin 6 → ℝ) (n m : Fin 20)
    (hnm : n ≠ m) (hfacet : facet n = facet m) : vertices l n 1 = vertices l m 1 := by
  change vertices l n (0 : Fin 3).succ = vertices l m (0 : Fin 3).succ
  rw [vertices_tail,vertices_tail,same_facet_roots n m hnm hfacet]

theorem strict_combinations_disjoint (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n m : Fin 20) (hnm : n ≠ m) (a b : Fin 4 → ℝ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j) :
    mix a (vertices l n) ≠ mix b (vertices l m) := by
  intro he
  have hhead : vertices l n 0 = vertices l m 0 := by rw [vertices_head,vertices_head]
  have hfacet : facet n = facet m := by
    by_contra hf
    have hneg (r : Fin 20) : support l (facet r) (vertices l n 0) < 0 := by
      rw [vertices_head]
      exact support_barycenter l hl _
    have h1 := strict_head_coefficient (support l (facet n)) (vertices l n) (vertices l m)
      a b he hhead (hneg n) (facet_zero l hl n) hb (boundary_nonpos l hl m _)
      (other_boundary_strict l hl m _ hf)
    have h2 := strict_head_coefficient (support l (facet m)) (vertices l m) (vertices l n)
      b a he.symm hhead.symm (by rw [vertices_head]; exact support_barycenter l hl _)
      (facet_zero l hl m) ha (boundary_nonpos l hl n _)
      (other_boundary_strict l hl n _ (Ne.symm hf))
    linarith
  have hcoeff : a 0 = b 0 := equal_head_coefficient (support l (facet n))
    (vertices l n) (vertices l m) a b he hhead
    (by rw [vertices_head]; exact support_barycenter l hl _)
    (facet_zero l hl n) (by rw [hfacet]; exact facet_zero l hl m)
  have htail := tails_equal (vertices l n) (vertices l m) a b he hhead hcoeff
  have hroot := same_facet_root_eq l n m hnm hfacet
  have hbound (u v : Fin 20) (huv : u ≠ v) (hf : facet u = facet v)
      (A B : Fin 3 → ℝ) (hA : ∀ j, 0 < A j) (hB : ∀ j, 0 < B j)
      (h : mix A (fun j : Fin 3 => vertices l u j.succ) =
           mix B (fun j : Fin 3 => vertices l v j.succ)) : B 0 < A 0 := by
    obtain ⟨hr,he,hother⟩ := same_facet_ridge u v huv hf
    apply strict_head_coefficient (support l (ridge u))
      (fun j : Fin 3 => vertices l u j.succ) (fun j : Fin 3 => vertices l v j.succ)
      A B h (same_facet_root_eq l u v huv hf) ?_ ?_ hB ?_ ?_
    · rw [vertices_tail]
      exact (endpoint_support l hl _ _ _ (labels_ne u 0)).2 hr
    · intro j
      rw [vertices_tail]
      exact (endpoint_support l hl _ _ _ (labels_ne u j.succ)).1 (he j)
    · intro j
      exact boundary_nonpos l hl v _ j.succ
    · obtain ⟨j,hj⟩ := hother
      refine ⟨j,?_⟩
      rw [vertices_tail]
      exact (endpoint_support l hl _ _ _ (labels_ne v j.succ)).2 hj
  have h1 := hbound n m hnm hfacet (fun j => a j.succ) (fun j => b j.succ)
    (fun j => ha j.succ) (fun j => hb j.succ) htail
  have h2 := hbound m n hnm.symm hfacet.symm (fun j => b j.succ) (fun j => a j.succ)
    (fun j => hb j.succ) (fun j => ha j.succ) htail.symm
  linarith



lemma hull_weights {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Fin 4 → E) (x : E) (hx : x ∈ convexHull ℝ (range p)) :
    ∃ a : Fin 4 → ℝ, (∀ i, 0 ≤ a i) ∧ (∑ i, a i) = 1 ∧ mix a p = x := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hx
  obtain ⟨s,w,hw,hsum,he⟩ := hx
  let a : Fin 4 → ℝ := fun i => if i ∈ s then w i else 0
  have hsumA : ∑ i, a i = ∑ i ∈ s, w i := by
    calc
      _ = ∑ i ∈ s, a i := (Finset.sum_subset s.subset_univ (by
        intro i _ hi
        simp [a,hi])).symm
      _ = _ := Finset.sum_congr rfl (by intro i hi; simp [a,hi])
  refine ⟨a,?_,hsumA.trans hsum,?_⟩
  · intro i
    by_cases hi : i ∈ s
    · simpa [a,hi] using hw i hi
    · simp [a,hi]
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at he
    calc
      mix a p = ∑ i ∈ s, a i • p i := (Finset.sum_subset s.subset_univ (by
        intro i _ hi
        simp [a,hi])).symm
      _ = ∑ i ∈ s, w i • p i := Finset.sum_congr rfl (by intro i hi; simp [a,hi])
      _ = x := he

lemma zero_weight_face {E : Type*} [AddCommGroup E] [Module ℝ E]
    (p : Fin 4 → E) (a : Fin 4 → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hsum : (∑ i, a i) = 1) (i : Fin 4) (hi : a i = 0) :
    mix a p ∈ convexHull ℝ (range (fun j : Fin 3 => p (i.succAbove j))) := by
  have hsum' : ∑ j : Fin 3, a (i.succAbove j) = 1 := by
    rw [Fin.sum_univ_succAbove a i,hi,zero_add] at hsum
    exact hsum
  have hm : (∑ j : Fin 3, a (i.succAbove j) • p (i.succAbove j)) = mix a p := by
    unfold mix
    rw [Fin.sum_univ_succAbove _ i,hi,zero_smul,zero_add]
  exact mem_convexHull_of_exists_fintype _ _ (fun j => ha (i.succAbove j))
    hsum' (fun j => ⟨j,rfl⟩) hm

def face (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 4) : Set V :=
  convexHull ℝ (range (fun j : Fin 3 => vertices l n (i.succAbove j)))

theorem overlap_in_faces (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n m : Fin 20) (hnm : n ≠ m) :
    cell l n ∩ cell l m ⊆ (⋃ i, face l n i) ∪ (⋃ i, face l m i) := by
  intro x hx
  obtain ⟨a,ha,hsuma,heqa⟩ := hull_weights (vertices l n) x hx.1
  obtain ⟨b,hb,hsumb,heqb⟩ := hull_weights (vertices l m) x hx.2
  by_cases hapos : ∀ i, 0 < a i
  · by_cases hbpos : ∀ i, 0 < b i
    · exact ((strict_combinations_disjoint l hl n m hnm a b hapos hbpos)
        (heqa.trans heqb.symm)).elim
    · push_neg at hbpos
      obtain ⟨i,hi⟩ := hbpos
      refine Or.inr (mem_iUnion.mpr ⟨i,?_⟩)
      rw [← heqb]
      exact zero_weight_face _ _ hb hsumb i (le_antisymm hi (hb i))
  · push_neg at hapos
    obtain ⟨i,hi⟩ := hapos
    refine Or.inl (mem_iUnion.mpr ⟨i,?_⟩)
    rw [← heqa]
    exact zero_weight_face _ _ ha hsuma i (le_antisymm hi (ha i))

def drop : V →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x j := x j.castSucc
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma three_point_hull_null (p : Fin 3 → (Fin 3 → ℝ)) :
    MeasureTheory.volume (convexHull ℝ (range p)) = 0 := by
  apply MeasureTheory.measure_mono_null (convexHull_subset_affineSpan (𝕜 := ℝ) (range p))
  apply MeasureTheory.Measure.addHaar_affineSubspace
  exact affineSpan_range_ne_top_of_card_le_finrank ℝ (by simp) p

lemma projected_face_null (l : Fin 6 → ℝ) (n : Fin 20) (i : Fin 4) :
    MeasureTheory.volume (drop '' face l n i) = 0 := by
  rw [face,LinearMap.image_convexHull,← Set.range_comp]
  exact three_point_hull_null _

theorem intrinsic_overlap_null (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n m : Fin 20) (hnm : n ≠ m) :
    MeasureTheory.volume (drop '' (cell l n ∩ cell l m)) = 0 := by
  apply MeasureTheory.measure_mono_null (Set.image_mono (overlap_in_faces l hl n m hnm))
  rw [Set.image_union,Set.image_iUnion,Set.image_iUnion]
  apply MeasureTheory.measure_union_null
  · exact MeasureTheory.measure_iUnion_null (fun i => projected_face_null l n i)
  · exact MeasureTheory.measure_iUnion_null (fun i => projected_face_null l m i)



def lift (y : Fin 3 → ℝ) : V := ![y 0,y 1,y 2,1-y 0-y 1-y 2]

lemma lift_drop (x : V) (h : ∑ i, x i = 1) : lift (drop x) = x := by
  have hs : x 0 + x 1 + x 2 + x 3 = 1 := by simpa [Fin.sum_univ_four] using h
  funext i
  fin_cases i <;> simp [lift,drop]
  linarith

lemma vertex_mem_body (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (j : Fin 4) : vertices l n j ∈ cutBody l := by
  fin_cases n <;> fin_cases j
  all_goals first
    | exact (shared_radial_body l hl).2.1
    | exact ((cut_body_polytope l hl).2.2.2 _ _ (by decide)).1

lemma cell_sum_one (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n : Fin 20) (x : V) (hx : x ∈ cell l n) : ∑ i, x i = 1 := by
  have hsub : cell l n ⊆ (sumOne : Set V) := by
    apply convexHull_min _ sumOne.convex
    rintro z ⟨j,rfl⟩
    exact (vertex_mem_body l hl n j).1.2
  exact hsub hx

theorem chart_overlap_null (l : Fin 6 → ℝ) (hl : ∀ i, 0 < l i)
    (n m : Fin 20) (hnm : n ≠ m) :
    MeasureTheory.volume ((drop '' cell l n) ∩ (drop '' cell l m)) = 0 := by
  have he : (drop '' cell l n) ∩ (drop '' cell l m) = drop '' (cell l n ∩ cell l m) := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨x,hx,rfl⟩,⟨y,hy,he⟩⟩
      have hxy : y = x := by
        rw [← lift_drop y (cell_sum_one l hl m y hy),
          ← lift_drop x (cell_sum_one l hl n x hx),he]
      subst y
      exact ⟨x,⟨hx,hy⟩,rfl⟩
    · rintro z ⟨x,⟨hx,hy⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,⟨x,hy,rfl⟩⟩
  rw [he]
  exact intrinsic_overlap_null l hl n m hnm

end CFMPCellIntersections435Transient
