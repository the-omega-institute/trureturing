/- GID: D5/S3/Geometry/Hyperideal/LengthGramSideTrace
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/LengthGramSideTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Join]
   utility: none
   digest: The literal twenty closed tetrahedra in the original six-length coefficient body. -/

import D5.S3.Geometry.Hyperideal.LengthGramPolytope
import Mathlib.Analysis.Convex.Join
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-! The original coefficient body has exact cyclic supporting traces. -/
noncomputable section
open scoped BigOperators
open Set
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.Hyperideal.LengthGramPolytope
set_option autoImplicit false

namespace D5.S3.Geometry.Hyperideal.LengthGramSideTrace

abbrev V := Fin 4 → ℝ
abbrev Support := Fin 4 ⊕ Fin 4

def barycenter : V := fun _ => 1 / 4

/-- One fixed ambient affine space, shared by every cell. -/
def sumOne : AffineSubspace ℝ V where
  carrier := {x | ∑ i, x i = 1}
  smul_vsub_vadd_mem' c p q r hp hq hr := by
    change (∑ i : Fin 4, (c * (p i - q i) + r i)) = 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hp, hq, hr]
    ring

def support (l : Fin 6 → ℝ) : Support → V →ₗ[ℝ] ℝ
  | Sum.inl i => -(LinearMap.proj i)
  | Sum.inr i => ∑ j, lengthGram l i j • LinearMap.proj j

/-- Zero-incidence of the twelve original ordered endpoints with the eight supports. -/
def incident : Support → Fin 4 → Fin 4 → Prop
  | Sum.inl k, i, j => k ≠ i ∧ k ≠ j
  | Sum.inr k, i, _ => k = i

instance (f : Support) (i j : Fin 4) : Decidable (incident f i j) := by
  cases f <;> dsimp [incident] <;> infer_instance

/-- The original Scribe's twenty tuples, in its original order. -/
def vertices (l : Fin 6 → ℝ) : Fin 20 → Fin 4 → V :=
  ![![barycenter, endpoint l 0 1, endpoint l 0 2, endpoint l 0 3],
    ![barycenter, endpoint l 1 0, endpoint l 1 2, endpoint l 1 3],
    ![barycenter, endpoint l 2 0, endpoint l 2 1, endpoint l 2 3],
    ![barycenter, endpoint l 3 0, endpoint l 3 1, endpoint l 3 2],
    ![barycenter, endpoint l 1 2, endpoint l 2 1, endpoint l 2 3],
    ![barycenter, endpoint l 1 2, endpoint l 2 3, endpoint l 3 2],
    ![barycenter, endpoint l 1 2, endpoint l 3 2, endpoint l 3 1],
    ![barycenter, endpoint l 1 2, endpoint l 3 1, endpoint l 1 3],
    ![barycenter, endpoint l 0 2, endpoint l 2 0, endpoint l 2 3],
    ![barycenter, endpoint l 0 2, endpoint l 2 3, endpoint l 3 2],
    ![barycenter, endpoint l 0 2, endpoint l 3 2, endpoint l 3 0],
    ![barycenter, endpoint l 0 2, endpoint l 3 0, endpoint l 0 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 0, endpoint l 1 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 3, endpoint l 3 1],
    ![barycenter, endpoint l 0 1, endpoint l 3 1, endpoint l 3 0],
    ![barycenter, endpoint l 0 1, endpoint l 3 0, endpoint l 0 3],
    ![barycenter, endpoint l 0 1, endpoint l 1 0, endpoint l 1 2],
    ![barycenter, endpoint l 0 1, endpoint l 1 2, endpoint l 2 1],
    ![barycenter, endpoint l 0 1, endpoint l 2 1, endpoint l 2 0],
    ![barycenter, endpoint l 0 1, endpoint l 2 0, endpoint l 0 2]]

def cell (l : Fin 6 → ℝ) (n : Fin 20) : Set V :=
  convexHull ℝ (range (vertices l n))

def boundaryTriangle (l : Fin 6 → ℝ) (n : Fin 20) : Set V :=
  convexHull ℝ (range (fun j : Fin 3 => vertices l n j.succ))

def facet : Fin 20 → Support :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3,
    Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inl 0,
    Sum.inl 1, Sum.inl 1, Sum.inl 1, Sum.inl 1,
    Sum.inl 2, Sum.inl 2, Sum.inl 2, Sum.inl 2,
    Sum.inl 3, Sum.inl 3, Sum.inl 3, Sum.inl 3]

/-- The support of the opposite edge of each boundary triangle. -/
def ridge : Fin 20 → Support :=
  ![Sum.inl 1, Sum.inl 0, Sum.inl 0, Sum.inl 0,
    Sum.inr 2, Sum.inl 1, Sum.inr 3, Sum.inl 2,
    Sum.inr 2, Sum.inl 0, Sum.inr 3, Sum.inl 2,
    Sum.inr 1, Sum.inl 0, Sum.inr 3, Sum.inl 1,
    Sum.inr 1, Sum.inl 0, Sum.inr 2, Sum.inl 1]

def capIndex (i : Fin 4) : Fin 20 := ⟨i.val, by omega⟩
def sideIndex (k r : Fin 4) : Fin 20 := ⟨4 + 4 * k.val + r.val, by omega⟩

def sideOrder (k : Fin 4) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (![![0,1,2,3], ![1,0,2,3], ![2,0,1,3], ![3,0,1,2]] k)
    (by fin_cases k <;> decide)

/-- The four original six-vertex endpoint cycles, without changing any vertex. -/
def sideCycle (l : Fin 6 → ℝ) (k : Fin 4) : Fin 6 → V :=
  let σ := sideOrder k
  ![endpoint l (σ 1) (σ 2), endpoint l (σ 2) (σ 1),
    endpoint l (σ 2) (σ 3), endpoint l (σ 3) (σ 2),
    endpoint l (σ 3) (σ 1), endpoint l (σ 1) (σ 3)]

/-- Supporting traces of all six edges in each original cyclic order. -/
def cycleSupport (k : Fin 4) : Fin 6 → Support :=
  let σ := sideOrder k
  ![Sum.inl (σ 3), Sum.inr (σ 2), Sum.inl (σ 1),
    Sum.inr (σ 3), Sum.inl (σ 2), Sum.inr (σ 1)]


private lemma support_body (l : Fin 6 → ℝ) (x : V) (hx : x ∈ cutBody l)
    (f : Support) : support l f x ≤ 0 := by
  cases f with
  | inl i => exact neg_nonpos.mpr (hx.1.1 i)
  | inr i => simpa [support] using hx.2 i

private lemma support_barycenter (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) : support l f barycenter < 0 := by
  cases f with
  | inl i => norm_num [support, barycenter]
  | inr i => simpa [support, barycenter] using (shared_radial_body l hl).2.2.1 i

private lemma endpoint_support (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    (incident f i j → support l f (endpoint l i j) = 0) ∧
    (¬ incident f i j → support l f (endpoint l i j) < 0) := by
  obtain ⟨_, hi, hj, hz, hr, ho⟩ := (cut_body_polytope l hl).2.2.2 i j hij
  cases f with
  | inl k =>
    constructor
    · rintro ⟨hki, hkj⟩
      simpa [support] using congrArg Neg.neg (hz k hki hkj)
    · intro h
      by_cases hki : k = i
      · subst k; simpa [support] using neg_neg_of_pos hi
      · have hkj : k = j := by
          by_contra hkj
          exact h ⟨hki, hkj⟩
        subst k
        simpa [support] using neg_neg_of_pos hj
  | inr k =>
    constructor
    · intro h
      change k = i at h
      subst k
      simpa [support] using hr
    · intro h
      simpa [support] using ho k h

private lemma endpoint_support_zero_iff (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q)
    (f : Support) (i j : Fin 4) (hij : i ≠ j) :
    support l f (endpoint l i j) = 0 ↔ incident f i j := by
  constructor
  · intro he
    by_contra hn
    exact ((endpoint_support l hl f i j hij).2 hn).ne he
  · exact (endpoint_support l hl f i j hij).1

/-- Supporting traces select precisely the vertices whose support values vanish.
The nonzero-weight filter is necessary: zero-weight vertices need not lie on the trace. -/
private lemma zero_trace_hull {I : Type*} (s : Set V) (L : I → V →ₗ[ℝ] ℝ)
    (hs : ∀ p ∈ s, ∀ i, L i p ≤ 0) :
    convexHull ℝ {p ∈ s | ∀ i, L i p = 0} =
      {x ∈ convexHull ℝ s | ∀ i, L i x = 0} := by
  classical
  apply Subset.antisymm
  · apply convexHull_min
    · exact fun p hp => ⟨subset_convexHull ℝ s hp.1, hp.2⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ s) hx.1 hy.1 ha hb hab, ?_⟩
      intro i
      simp [map_add, map_smul, hx.2 i, hy.2 i]
  · rintro x ⟨hx, hzero⟩
    obtain ⟨J, _, w, z, hw, hsum, hz, he⟩ := mem_convexHull_iff_exists_fintype.mp hx
    have hterm (i : I) (j : J) : w j * L i (z j) = 0 := by
      have hh : ∑ j, w j * L i (z j) = 0 := by
        simpa only [map_sum, map_smul, smul_eq_mul, hzero i] using congrArg (L i) he
      exact (Finset.sum_eq_zero_iff_of_nonpos
        (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw j) (hs (z j) (hz j) i))).mp hh
          j (Finset.mem_univ j)
    let t : Finset J := Finset.univ.filter fun j => w j ≠ 0
    have ht_sum : ∑ j ∈ t, w j = 1 := by
      rw [show (∑ j ∈ t, w j) = ∑ j, w j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        by_contra hjw
        exact hjt (Finset.mem_filter.mpr ⟨hj, hjw⟩)]
      exact hsum
    have ht_vec : ∑ j ∈ t, w j • z j = x := by
      rw [show (∑ j ∈ t, w j • z j) = ∑ j, w j • z j by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hj hjt
        have hjw : w j = 0 := by
          by_contra hn
          exact hjt (Finset.mem_filter.mpr ⟨hj, hn⟩)
        simp [hjw]]
      exact he
    rw [← ht_vec]
    exact (convex_convexHull ℝ _).sum_mem
      (fun j _ => hw j) ht_sum (fun j hj => subset_convexHull ℝ _
        ⟨hz j, fun i => (mul_eq_zero.mp (hterm i j)).resolve_left
          (Finset.mem_filter.mp hj).2⟩)


set_option maxHeartbeats 2000000 in
/-- All six cyclic supporting traces are exactly the original closed edge segments. -/
theorem cycle_edge_hull (l : Fin 6 → ℝ) (hl : ∀ q, 0 < l q) (k : Fin 4) (r : Fin 6) :
    {x ∈ cutBody l | support l (Sum.inl k) x = 0 ∧
      support l (cycleSupport k r) x = 0} =
    segment ℝ (sideCycle l k r) (sideCycle l k (r + 1)) := by
  let P : Set V := range (fun p : EndpointLabel => endpoint l p.val.1 p.val.2)
  have hP : convexHull ℝ P = cutBody l := (cut_body_polytope l hl).2.1
  let L : Fin 2 → V →ₗ[ℝ] ℝ :=
    ![support l (Sum.inl k), support l (cycleSupport k r)]
  have hz := zero_trace_hull P L
    (by rintro p ⟨⟨⟨a,b⟩,hab⟩,rfl⟩ j
        fin_cases j
        · exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 (Sum.inl k)
        · exact support_body l _ ((cut_body_polytope l hl).2.2.2 a b hab).1 (cycleSupport k r))
  have hverts : {p ∈ P | ∀ j, L j p = 0} =
      {sideCycle l k r, sideCycle l k (r + 1)} := by
    ext x
    constructor
    · rintro ⟨⟨⟨⟨a,b⟩,hab⟩,rfl⟩,h⟩
      have h0 := (endpoint_support_zero_iff l hl (Sum.inl k) a b hab).mp (h 0)
      have h1 := (endpoint_support_zero_iff l hl (cycleSupport k r) a b hab).mp (h 1)
      fin_cases k <;> fin_cases r <;> fin_cases a <;> fin_cases b <;>
        simp_all [incident, cycleSupport, sideCycle, sideOrder] <;>
        try contradiction <;>
        try rfl
    · intro h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      rcases h with rfl | rfl
      all_goals
        refine ⟨?_, ?_⟩
        · fin_cases k <;> fin_cases r
          all_goals refine ⟨⟨(_, _), ?_⟩, rfl⟩ <;> decide
        · intro j
          fin_cases k <;> fin_cases r <;> fin_cases j <;>
            simp [L, cycleSupport, sideCycle, sideOrder]
          all_goals
            apply (endpoint_support l hl _ _ _ (by decide)).1
            decide
  have hbody : {x ∈ convexHull ℝ P | ∀ j, L j x = 0} =
      {x ∈ cutBody l | support l (Sum.inl k) x = 0 ∧
        support l (cycleSupport k r) x = 0} := by
    simp [hP, L, Fin.forall_fin_succ]
  rw [hverts, hbody, convexHull_pair] at hz
  exact hz.symm

end D5.S3.Geometry.Hyperideal.LengthGramSideTrace
