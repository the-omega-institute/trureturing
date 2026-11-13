/- GID: D5/S3/Geometry/AlgebraicBoundary/ConeMinimumBranch
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/ConeMinimumBranch
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual low-degree cone minima determine all-direction roots and the whole closed branch. -/

import D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation
import D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

noncomputable section

open Set Filter
open scoped Topology Pointwise

namespace D5.S3.Geometry.AlgebraicBoundary.ConeMinimumBranch

open private minimum_boundary_ideal
  from D5.S3.Geometry.AlgebraicBoundary.BoundaryPrincipalIdeal

open private exists_full_compact_base base_chart_geometry
  from D5.S3.Geometry.AlgebraicBoundary.ConeCompactBase

open private linePolynomial eval_linePolynomial eval_differentiable affineLinearPolynomial eval_affineLinearPolynomial hyperplane_factorization interior_zero_factor homogeneous_eval_smul linePolynomial_top_coeff cone_interior_add_positive cone_line_roots_and_branch
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

open private cone_vertex_frontier cone_boundary_component affinePullback eval_affinePullback chart_minimum_correspondence minimum_equation_squarefree exists_homogeneous_minimum
  from D5.S3.Geometry.AlgebraicBoundary.ConeBoundaryEquation

variable {ι : Type*} [Fintype ι]

private theorem minimum_cone_no_interior_zero [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) {d : ℕ} (hhom : p.IsHomogeneous d)
    (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∀ y ∈ interior (C : Set (ι → ℝ)), MvPolynomial.eval y p ≠ 0 := by
  classical
  obtain ⟨u, b, hu, hb, hbi, hKc, hKn, hint, hfront⟩ :=
    exists_full_compact_base C hs hfull
  let P : (ι → ℝ) →L[ℝ] u.ker :=
    (ContinuousLinearMap.id ℝ (ι → ℝ) - u.smulRight b).codRestrict u.ker
      (by intro x; simp [hb])
  have hP : ∀ x, (P x : ι → ℝ) = x - u x • b := fun _ => rfl
  let κ := Fin (Module.finrank ℝ u.ker)
  let k : u.ker ≃L[ℝ] (κ → ℝ) := (Module.finBasis ℝ u.ker).equivFunL
  let J : (κ → ℝ) →L[ℝ] (ι → ℝ) := u.ker.subtypeL.comp k.symm.toContinuousLinearMap
  let A : (ι → ℝ) →L[ℝ] (κ → ℝ) := k.toContinuousLinearMap.comp P
  have hJ : ∀ v, u (J v) = 0 := fun v => (k.symm v).property
  have hAb : A b = 0 := by
    have hh : P b = 0 := by apply Subtype.ext; simp [hP, hb]
    simp [A, hh]
  have hAJ : ∀ v, A (J v) = v := by
    intro v
    have hh : P (J v) = k.symm v := by
      apply Subtype.ext
      simp [hP, hJ, J]
    simp [A, hh]
  have hdecomp : ∀ x, J (A x) = x - u x • b := by
    intro x
    simpa [J, A] using hP x
  let K : Set u.ker := {v | b + (v : ι → ℝ) ∈ C}
  let B : Set (κ → ℝ) := {v | b + J v ∈ C}
  have hKB : k '' K = B := by
    ext v
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [B, J, K] using hw
    · intro hv
      exact ⟨k.symm v, hv, k.apply_symm_apply v⟩
  have hBc : IsCompact B := hKB ▸ hKc.image k.continuous
  have hBconv : Convex ℝ B := by
    intro x hx y hy a c ha hc hac
    change b + J (a • x + c • y) ∈ C
    have hh := C.convex hx hy ha hc hac
    have heq : b + J (a • x + c • y) = a • (b + J x) + c • (b + J y) := by
      simp only [map_add, map_smul, smul_add]
      calc
        b + (a • J x + c • J y) = (a + c) • b + (a • J x + c • J y) := by rw [hac, one_smul]
        _ = a • b + a • J x + (c • b + c • J y) := by module
    exact heq ▸ hh
  have hfr : ∀ v, v ∈ frontier B ↔ b + J v ∈ frontier (C : Set (ι → ℝ)) := by
    intro v
    have hh : frontier B = k '' frontier K := by
      rw [← hKB]
      exact (k.toHomeomorph.image_frontier K).symm
    rw [hh]
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [J] using (hfront w).mp hw
    · intro hv
      exact ⟨k.symm v, (hfront _).mpr hv, k.apply_symm_apply v⟩
  rcases subsingleton_or_nontrivial u.ker with hsub | hnontriv
  · have hx : ∀ x, x = u x • b := by
      intro x
      have hh : P x = 0 := Subsingleton.elim _ _
      have hh' := congrArg Subtype.val hh
      simpa [hP, sub_eq_zero] using hh'
    have hpb : MvPolynomial.eval b p ≠ 0 := by
      intro h
      apply hp
      apply MvPolynomial.funext
      intro x
      conv_lhs => rw [hx x, homogeneous_eval_smul p hhom, h, mul_zero]
      simp
    intro y hy hpy
    have hy0 : y ≠ 0 := by
      intro h
      have hz := (C.isClosed.frontier_eq ▸ cone_vertex_frontier C hs).2
      exact hz (h ▸ hy)
    rw [hx y, homogeneous_eval_smul p hhom] at hpy
    exact (mul_ne_zero (pow_ne_zero _ (hu y (interior_subset hy) hy0).ne') hpb) hpy
  · letI : Nontrivial u.ker := hnontriv
    letI : Nontrivial (κ → ℝ) := k.toEquiv.symm.nontrivial
    have hne : (frontier B).Nonempty := nonempty_frontier_iff.mpr
      ⟨⟨0, by simpa [B] using interior_subset hbi⟩, hBc.ne_univ⟩
    obtain ⟨hf, hdeg, hfv, hmf⟩ :=
      chart_minimum_correspondence C u hu b hb J A hJ hAb hAJ hdecomp hfr hne p hp hhom hvan hmin
    have hno : ∀ v ∈ interior B, MvPolynomial.eval v (affinePullback p b J) ≠ 0 := by
      intro v hv hpv
      obtain ⟨_, g, hg, _, hgd, hgv⟩ := interior_zero_factor hBconv hBc
        (affinePullback p b J) hf (hdeg ▸ hd) hfv hv hpv
      have hm := hmf g hg hgv
      omega
    intro y hy hpy
    have hy0 : y ≠ 0 := by
      intro h
      have hz := (C.isClosed.frontier_eq ▸ cone_vertex_frontier C hs).2
      exact hz (h ▸ hy)
    have huy := hu y (interior_subset hy) hy0
    let v := (u y)⁻¹ • A y
    have heq : b + J v = (u y)⁻¹ • y := by
      change b + J ((u y)⁻¹ • A y) = (u y)⁻¹ • y
      rw [map_smul, hdecomp, smul_sub, smul_smul, inv_mul_cancel₀ huy.ne', one_smul]
      module
    have hnorm : (u y)⁻¹ • y ∈ interior (C : Set (ι → ℝ)) := by
      have hh := cone_interior_add_positive C hy C.toPointedCone.zero_mem (inv_pos.mpr huy)
      simpa using hh
    have hv : v ∈ interior B := by
      have hh : interior B = k '' interior K := by
        rw [← hKB]
        exact (k.toHomeomorph.image_interior K).symm
      rw [hh]
      exact ⟨k.symm v, (hint _).mpr (by simpa [J] using heq.symm ▸ hnorm), k.apply_symm_apply v⟩
    apply hno v hv
    rw [eval_affinePullback, heq, homogeneous_eval_smul p hhom, hpy, mul_zero]

private theorem minimum_equation_homogeneous
    (C : ProperCone ℝ (ι → ℝ)) (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) : p.IsHomogeneous p.totalDegree := by
  classical
  have hcomp := cone_boundary_component (ContinuousLinearEquiv.refl ℝ (ι → ℝ)) C p hvan
  have hlow : ∀ k, k < p.totalDegree → MvPolynomial.homogeneousComponent k p = 0 := by
    intro k hk
    by_contra hn
    have hm := hmin _ hn (hcomp k)
    have hd := (MvPolynomial.homogeneousComponent_isHomogeneous k p).totalDegree_le
    omega
  have heq : MvPolynomial.homogeneousComponent p.totalDegree p = p := by
    have hh : (∑ k ∈ Finset.range (p.totalDegree + 1), MvPolynomial.homogeneousComponent k p) =
        MvPolynomial.homogeneousComponent p.totalDegree p := by
      apply Finset.sum_eq_single p.totalDegree
      · intro k hk hne
        exact hlow k (lt_of_le_of_ne (Nat.le_of_lt_succ (Finset.mem_range.mp hk)) hne)
      · simp
    exact hh.symm.trans (MvPolynomial.sum_homogeneousComponent p)
  have hh := MvPolynomial.homogeneousComponent_isHomogeneous p.totalDegree p
  rw [heq] at hh
  exact hh

private theorem minimum_homogeneous_scalar_unique [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p r : MvPolynomial ι ℝ) (hp : p ≠ 0) (hr : r ≠ 0) {d : ℕ}
    (hhom : p.IsHomogeneous d) (hrhom : r.IsHomogeneous d)
    (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hrvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * p := by
  obtain ⟨e, he⟩ := hfull
  have hpe := minimum_cone_no_interior_zero C hs ⟨e, he⟩ p hp hhom hd hvan hmin e he
  let a := MvPolynomial.eval e r / MvPolynomial.eval e p
  let q := r - MvPolynomial.C a * p
  have hqhom : q.IsHomogeneous d := hrhom.sub (hhom.C_mul a)
  have hqvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0 := by
    intro y hy
    simp [q, hvan y hy, hrvan y hy]
  have hqdeg : q.totalDegree ≤ p.totalDegree := by
    rw [hhom.totalDegree hp]
    exact hqhom.totalDegree_le
  have hqzero : q = 0 := by
    by_contra hq
    have hqmin : ∀ s : MvPolynomial ι ℝ, s ≠ 0 →
        (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y s = 0) →
          q.totalDegree ≤ s.totalDegree :=
      fun s hs hsv => hqdeg.trans (hmin s hs hsv)
    have hqe := minimum_cone_no_interior_zero C hs ⟨e, he⟩ q hq hqhom
      (hqdeg.trans hd) hqvan hqmin e he
    apply hqe
    simp [q, a, div_mul_cancel₀ _ hpe]
  have hrp : r = MvPolynomial.C a * p := sub_eq_zero.mp hqzero
  refine ⟨a, ?_, hrp⟩
  intro ha
  exact hr (by simpa [ha] using hrp)

private theorem minimum_scalar_unique [Nontrivial (ι → ℝ)]
    (C : ProperCone ℝ (ι → ℝ)) (hs : (C : ConvexCone ℝ (ι → ℝ)).Salient)
    (hfull : (interior (C : Set (ι → ℝ))).Nonempty)
    (p r : MvPolynomial ι ℝ) (hp : p ≠ 0) (hr : r ≠ 0)
    (hd : p.totalDegree ≤ 3) (hrd : r.totalDegree ≤ p.totalDegree)
    (hvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y p = 0)
    (hrvan : ∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y r = 0)
    (hmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        p.totalDegree ≤ q.totalDegree) :
    ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * p := by
  have heq : r.totalDegree = p.totalDegree := hrd.antisymm (hmin r hr hrvan)
  have hrmin : ∀ q : MvPolynomial ι ℝ, q ≠ 0 →
      (∀ y ∈ frontier (C : Set (ι → ℝ)), MvPolynomial.eval y q = 0) →
        r.totalDegree ≤ q.totalDegree := fun q hq hqv => hrd.trans (hmin q hq hqv)
  have hphom := minimum_equation_homogeneous C p hvan hmin
  have hrhom := minimum_equation_homogeneous C r hrvan hrmin
  rw [heq] at hrhom
  exact minimum_homogeneous_scalar_unique C hs hfull p r hp hr hphom hrhom hd hvan hrvan hmin

private theorem positive_finset_lower_bound (s : Finset ℝ) (hs : ∀ r ∈ s, 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r ∈ s, ε ≤ r := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨ε, hε, hεs⟩ := ih (fun r hr => hs r (Finset.mem_insert_of_mem hr))
    refine ⟨min a ε, lt_min (hs a (Finset.mem_insert_self _ _)) hε, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (hεs r hr)

/-- The converse uses the whole original root branch. A polynomial merely
covering the boundary does not supply this hypothesis. -/
private theorem whole_branch_boundary_vanishing {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ) {d : ℕ} (hp : p.IsHomogeneous d)
    {e : E} (he : e ∈ interior (C : Set E)) (hpe : MvPolynomial.eval (c e) p ≠ 0)
    (hbranch : {x : E | ∀ t : ℝ, (linePolynomial p (-c x) (c e)).eval t = 0 → 0 ≤ t} =
      (C : Set E)) :
    ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0 := by
  classical
  intro y hy
  by_contra hpy
  let q := linePolynomial p (-c y) (c e)
  have hq : q ≠ 0 := by
    intro h
    have hh := congrArg (fun Q : Polynomial ℝ => Q.coeff d) h
    rw [linePolynomial_top_coeff p hp] at hh
    exact hpe (by simpa using hh)
  have hq0 : q.eval 0 ≠ 0 := by
    rw [eval_linePolynomial]
    have hh : MvPolynomial.eval ((-1 : ℝ) • c y) p ≠ 0 := by
      rw [homogeneous_eval_smul p hp]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hpy
    simpa using hh
  have hyC : y ∈ C := (C.isClosed.frontier_eq ▸ hy).1
  have hroots : ∀ r ∈ q.roots.toFinset, 0 < r := by
    intro r hr
    have hr0 := (Polynomial.mem_roots hq).mp (Multiset.mem_toFinset.mp hr)
    have hnon : 0 ≤ r := (show y ∈ {x : E | ∀ t : ℝ,
        (linePolynomial p (-c x) (c e)).eval t = 0 → 0 ≤ t} from hbranch ▸ hyC) r hr0
    exact lt_of_le_of_ne hnon (by intro h; apply hq0; simpa [← h] using hr0)
  obtain ⟨ε, hε, hεroots⟩ := positive_finset_lower_bound q.roots.toFinset hroots
  have hshift : y - ε • e ∈ C := by
    change y - ε • e ∈ (C : Set E)
    rw [← hbranch]
    intro t ht
    have hroot : q.eval (t + ε) = 0 := by
      rw [eval_linePolynomial] at ht ⊢
      have heq : -c y + (t + ε) • c e = -c (y - ε • e) + t • c e := by
        rw [map_sub, map_smul]
        module
      rw [heq]
      exact ht
    have hmem : t + ε ∈ q.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hroot)
    linarith [hεroots (t + ε) hmem]
  have hinside := cone_interior_add_positive C he hshift hε
  have hyi : y ∈ interior (C : Set E) := by simpa using hinside
  exact (C.isClosed.frontier_eq ▸ hy).2 hyi

private theorem cone_component_and_closure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (c : E ≃L[ℝ] (ι → ℝ)) (C : ProperCone ℝ E)
    (p : MvPolynomial ι ℝ)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0)
    (hno : ∀ y ∈ interior (C : Set E), MvPolynomial.eval (c y) p ≠ 0)
    {e : E} (he : e ∈ interior (C : Set E)) :
    connectedComponentIn {x : E | MvPolynomial.eval (c x) p ≠ 0} e =
        interior (C : Set E) ∧
      closure (connectedComponentIn {x : E | MvPolynomial.eval (c x) p ≠ 0} e) =
        (C : Set E) := by
  let U : Set E := {x | MvPolynomial.eval (c x) p ≠ 0}
  let F := connectedComponentIn U e
  have heU : e ∈ U := hno e he
  have hUF : F ⊆ U := connectedComponentIn_subset U e
  have hcover : F ⊆ interior (C : Set E) ∪ (C : Set E)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior (C : Set E)
    · exact Or.inl hxi
    · right
      intro hxC
      have hxf : x ∈ frontier (C : Set E) := C.isClosed.frontier_eq ▸ ⟨hxC, hxi⟩
      exact hUF hx (hvan x hxf)
  have hFsub : F ⊆ interior (C : Set E) := by
    rcases isPreconnected_connectedComponentIn.subset_or_subset isOpen_interior
      C.isClosed.isOpen_compl (by
        apply Set.disjoint_left.mpr
        intro x hx hx'
        exact hx' (interior_subset hx)) hcover with h | h
    · exact h
    · exact False.elim ((h (mem_connectedComponentIn heU)) (interior_subset he))
  have hsubF : interior (C : Set E) ⊆ F :=
    C.convex.interior.isPreconnected.subset_connectedComponentIn he (fun x hx => hno x hx)
  have hF : F = interior (C : Set E) := hFsub.antisymm hsubF
  refine ⟨hF, ?_⟩
  change closure F = (C : Set E)
  rw [hF, C.convex.closure_interior_eq_closure_of_nonempty_interior ⟨e, he⟩,
    C.isClosed.closure_eq]

private theorem ray_boundary_ideal {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (hdim : Module.finrank ℝ E = 1) :
    ∃ (u : E →L[ℝ] ℝ) (b : E) (l : MvPolynomial ι ℝ),
      u b = 1 ∧ b ∈ interior (C : Set E) ∧
      (∀ x, x = u x • b) ∧ (∀ x, x ∈ C ↔ 0 ≤ u x) ∧
      frontier (C : Set E) = {0} ∧ l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l.totalDegree = 1 ∧
      (∀ x, MvPolynomial.eval (c x) l = u x) ∧
      (∀ q : MvPolynomial ι ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ↔ l ∣ q) := by
  classical
  letI : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ hdim
  obtain ⟨u, b, hu, hb, hbi, _⟩ := exists_full_compact_base C hs hfull
  have hb0 : b ≠ 0 := by intro h; simpa [h] using hb
  have hspan : ∀ x, x = u x • b := by
    intro x
    obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hdim hb0 x
    have hux : u x = a := by rw [← ha]; simp [hb]
    rw [hux, ha]
  have hcone : ∀ x, x ∈ C ↔ 0 ≤ u x := by
    intro x
    constructor
    · intro hx
      by_cases hx0 : x = 0
      · simp [hx0]
      · exact (hu x hx hx0).le
    · intro hx
      rw [hspan x]
      exact C.smul_mem (interior_subset hbi) hx
  have hfr : frontier (C : Set E) = {0} := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxC := (C.isClosed.frontier_eq ▸ hx).1
      by_contra hx0
      have hxne : x ≠ 0 := by simpa using hx0
      have hxi := cone_interior_add_positive C hbi C.toPointedCone.zero_mem (hu x hxC hxne)
      have hxi' : x ∈ interior (C : Set E) := by simpa [← hspan x] using hxi
      exact (C.isClosed.frontier_eq ▸ hx).2 hxi'
    · intro x hx
      have hx0 : x = 0 := hx
      simpa [hx0] using cone_vertex_frontier C hs
  let L : (ι → ℝ) →L[ℝ] ℝ := u.comp c.symm.toContinuousLinearMap
  have hL : L ≠ 0 := by
    intro h
    have hh : L (c b) = 1 := by simp [L, hb]
    simp [h] at hh
  let l := affineLinearPolynomial 0 L
  have hlhom : l.IsHomogeneous 1 := by
    apply MvPolynomial.IsHomogeneous.sum
    intro i hi
    simpa using MvPolynomial.isHomogeneous_C_mul_X (L (Pi.single i 1)) i
  have hleval : ∀ x, MvPolynomial.eval (c x) l = u x := by
    intro x
    simpa [l, L] using eval_affineLinearPolynomial 0 (c x) L
  have hl : l ≠ 0 := by
    intro h
    have hh := hleval b
    simp [h, hb] at hh
  refine ⟨u, b, l, hb, hbi, hspan, hcone, hfr, hl, hlhom, hlhom.totalDegree hl, hleval, ?_⟩
  intro q
  constructor
  · intro hq
    by_cases hq0 : q = 0
    · simp [hq0]
    obtain ⟨g, _, hqg, _⟩ := hyperplane_factorization q hq0 0 L hL (by
      intro z hz
      have hux : u (c.symm z) = 0 := by simpa [L] using hz
      have hx0 : c.symm z = 0 := by rw [hspan (c.symm z), hux, zero_smul]
      have hh := hq (c.symm z) (hfr ▸ (by simpa [hx0]))
      simpa using hh)
    exact ⟨g, hqg⟩
  · rintro ⟨g, rfl⟩ x hx
    have hx0 : x = 0 := by simpa [hfr] using hx
    rw [map_mul, hleval, hx0, map_zero, zero_mul]

/-- The selected minimum generates the actual entire-boundary ideal, and its
analytic conclusions retain all original directions and ambient vectors. -/
private theorem original_minimum_roots_and_branch {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] (c : E ≃L[ℝ] (ι → ℝ))
    (C : ProperCone ℝ E) (hs : (C : ConvexCone ℝ E).Salient)
    (hfull : (interior (C : Set E)).Nonempty)
    (p : MvPolynomial ι ℝ) (hp : p ≠ 0) (hd : p.totalDegree ≤ 3)
    (hvan : ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) p = 0) :
    ∃ (d : ℕ) (q : MvPolynomial ι ℝ), 0 < d ∧ d ≤ p.totalDegree ∧ q ≠ 0 ∧
      q.IsHomogeneous d ∧ Squarefree q ∧
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) q = 0) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      (∀ r : MvPolynomial ι ℝ,
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ q ∣ r) ∧
      (∀ y ∈ interior (C : Set E), 0 < MvPolynomial.eval (c y) q) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 → r.totalDegree ≤ d →
        (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) →
          ∃ a : ℝ, a ≠ 0 ∧ r = MvPolynomial.C a * q) ∧
      (Module.finrank ℝ E = 1 →
        ∃ (u : E →L[ℝ] ℝ) (b : E) (l : MvPolynomial ι ℝ),
          u b = 1 ∧ b ∈ interior (C : Set E) ∧
          (∀ x, x = u x • b) ∧ (∀ x, x ∈ C ↔ 0 ≤ u x) ∧
          frontier (C : Set E) = {0} ∧ l ≠ 0 ∧ l.IsHomogeneous 1 ∧ l.totalDegree = 1 ∧
          (∀ x, MvPolynomial.eval (c x) l = u x) ∧
          (∀ r : MvPolynomial ι ℝ,
            (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔ l ∣ r)) ∧
      (∀ (h : MvPolynomial ι ℝ) (k : ℕ) (e : E), h.IsHomogeneous k →
        e ∈ interior (C : Set E) → MvPolynomial.eval (c e) h ≠ 0 →
        {x : E | ∀ t : ℝ, (linePolynomial h (-c x) (c e)).eval t = 0 → 0 ≤ t} =
          (C : Set E) →
        ∃ r : MvPolynomial ι ℝ, r ≠ 0 ∧ r.totalDegree = h.totalDegree ∧
          ∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ∧
      ∀ e ∈ interior (C : Set E),
        (∀ x : E, (linePolynomial q (-c x) (c e)).natDegree = d ∧
          (linePolynomial q (-c x) (c e)).Splits ∧
          (∀ s : ℝ, x = s • e → linePolynomial q (-c x) (c e) =
            Polynomial.C (MvPolynomial.eval (c e) q) * (Polynomial.X - Polynomial.C s) ^ d)) ∧
        {x : E | ∀ t : ℝ, (linePolynomial q (-c x) (c e)).eval t = 0 → 0 ≤ t} =
          (C : Set E) ∧
        connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e =
          interior (C : Set E) ∧
        closure (connectedComponentIn {x : E | MvPolynomial.eval (c x) q ≠ 0} e) =
          (C : Set E) := by
  classical
  letI : Nontrivial (ι → ℝ) := c.toEquiv.symm.nontrivial
  let D := C.comap c.symm.toContinuousLinearMap
  have hi : interior (D : Set (ι → ℝ)) = c.symm ⁻¹' interior (C : Set E) :=
    (c.symm.toHomeomorph.preimage_interior (C : Set E)).symm
  have hf : frontier (D : Set (ι → ℝ)) = c.symm ⁻¹' frontier (C : Set E) :=
    (c.symm.toHomeomorph.preimage_frontier (C : Set E)).symm
  have hsD : (D : ConvexCone ℝ (ι → ℝ)).Salient := by
    intro x hx hx0 hneg
    apply hs (c.symm x) hx
    · intro h
      have hh := congrArg c h
      exact hx0 (by simpa using hh)
    · simpa [D] using hneg
  have hfullD : (interior (D : Set (ι → ℝ))).Nonempty := by
    obtain ⟨a, ha⟩ := hfull
    exact ⟨c a, by simpa [hi] using ha⟩
  have hboundary : ∀ r : MvPolynomial ι ℝ,
      (∀ y ∈ frontier (C : Set E), MvPolynomial.eval (c y) r = 0) ↔
        ∀ z ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval z r = 0 := by
    intro r
    constructor
    · intro h z hz
      simpa using h (c.symm z) (by simpa [hf] using hz)
    · intro h y hy
      exact h (c y) (by simpa [hf] using hy)
  obtain ⟨d, f, hdpos, hdp, hfn, hfhom, _, hfv, hfm⟩ :=
    exists_homogeneous_minimum D hsD p hp ((hboundary p).mp hvan)
  have hfd : f.totalDegree ≤ 3 := (hfhom.totalDegree hfn) ▸ hdp.trans hd
  have hfno := minimum_cone_no_interior_zero D hsD hfullD f hfn hfhom hfd hfv hfm
  have hcont : Continuous (fun x : ι → ℝ => MvPolynomial.eval x f) :=
    (eval_differentiable f).continuous
  have horient : ∃ q : MvPolynomial ι ℝ, q ≠ 0 ∧ q.IsHomogeneous d ∧
      (∀ y ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval y q = 0) ∧
      (∀ r : MvPolynomial ι ℝ, r ≠ 0 →
        (∀ y ∈ frontier (D : Set (ι → ℝ)), MvPolynomial.eval y r = 0) →
          q.totalDegree ≤ r.totalDegree) ∧
      ∀ y ∈ interior (D : Set (ι → ℝ)), 0 < MvPolynomial.eval y q := by
    rcases D.convex.interior.isPreconnected.mapsTo_Ioi_or_Iio hcont.continuousOn hfno with h | h
    · exact ⟨f, hfn, hfhom, hfv, hfm, h⟩
    · refine ⟨-f, neg_ne_zero.mpr hfn, hfhom.neg, ?_, ?_, ?_⟩
      · intro y hy
        simp [hfv y hy]
      · intro r hr hrv
        simpa using hfm r hr hrv
      · intro y hy
        have hh : MvPolynomial.eval y f < 0 := h hy
        simpa using neg_pos.mpr hh
  obtain ⟨q, hq, hqhom, hqv, hqm, hqpos⟩ := horient
  have hqd : q.totalDegree ≤ 3 := (hqhom.totalDegree hq) ▸ hdp.trans hd
  have hqvo := (hboundary q).mpr hqv
  have hqpo : ∀ y ∈ interior (C : Set E), 0 < MvPolynomial.eval (c y) q := by
    intro y hy
    exact hqpos (c y) (by simpa [hi] using hy)
  refine ⟨d, q, hdpos, hdp, hq, hqhom,
    minimum_equation_squarefree _ q hq hqv hqm, hqvo, ?_, ?_, hqpo, ?_, ?_, ?_, ?_⟩
  · intro r hr hrv
    exact hqm r hr ((hboundary r).mp hrv)
  · intro r
    exact (hboundary r).trans (minimum_boundary_ideal D hfullD q hq hdpos hqhom hqv hqm r)
  · intro r hr hrd hrv
    have hrd' : r.totalDegree ≤ q.totalDegree := by rwa [hqhom.totalDegree hq]
    exact minimum_scalar_unique D hsD hfullD q r hq hr hqd hrd'
      hqv ((hboundary r).mp hrv) hqm
  · intro hdim
    exact ray_boundary_ideal c C hs hfull hdim
  · intro h k e hhom he hhe hbranch
    refine ⟨h, ?_, rfl, whole_branch_boundary_vanishing c C h hhom he hhe hbranch⟩
    intro hz
    exact hhe (by rw [hz, map_zero])
  · intro e he
    obtain ⟨hline, hbranch⟩ := cone_line_roots_and_branch c C hs q hqhom (hdp.trans hd)
      hdpos hqvo (fun y hy => (hqpo y hy).ne') he
    obtain ⟨hcomp, hclosure⟩ := cone_component_and_closure c C q hqvo
      (fun y hy => (hqpo y hy).ne') he
    exact ⟨hline, hbranch, hcomp, hclosure⟩

end D5.S3.Geometry.AlgebraicBoundary.ConeMinimumBranch
