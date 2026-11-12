/- GID: D5/S3/Quantum/Foundation/LowAffineDimensionalBOnly
   generality: G
   mirror-B: none(waiver:registration-template-not-established)
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Whole-base balls and low-dimensional segment faces supply original antipodal effects. -/

import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import D5.S3.Quantum.Foundation.FinitePureSimplex
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Analysis.Convex.Radon
import Batteries.Tactic.OpenPrivate

/-!
The full-base and segment-face branches of the arbitrary-pure low-dimensional argument. The
coordinate functional is defined on the chart direction, extended as a linear
map on the original carrier, and then normalized with the original unit.  The
properness proof is on the whole original cone; no restricted effect space or
finite pure carrier is introduced.
-/

noncomputable section

namespace D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly

open CircuitBalancedConfirmation
open WholePairBallConfirmation
open FinitePureSimplex
open scoped RealInnerProductSpace

open private pair_extreme chart_sphere_pure from
  D5.S3.Quantum.Foundation.WholePairBallConfirmation
open private simplex_kernel_zero from
  D5.S3.Quantum.Foundation.FinitePureSimplex

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem chart_linear_injective {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : V} (b : BallChart C u p q) :
    Function.Injective b.param.linear := by
  intro x y hxy
  have hlin0 : b.param.linear (x - y) = 0 := by
    simpa [hxy] using b.param.linear_apply_vsub x y
  have hparam : b.param (x - y) - b.param 0 = 0 := by
    simpa [hlin0] using (b.param.linear_apply_vsub (x - y) 0).symm
  exact sub_eq_zero.mp (b.injective (sub_eq_zero.mp hparam))

private theorem chart_linear_coordinate {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    {p q : V} (b : BallChart C u p q) (n : EuclideanSpace ℝ (Fin b.dim))
    (hn : ‖n‖ = 1) :
    ∃ g : V →ₗ[ℝ] ℝ, ∀ s,
      g (b.param s - b.param 0) = ⟪n, s⟫ := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  let ℓ : E →ₗ[ℝ] ℝ := (InnerProductSpace.toDual ℝ E) n
  let e : E ≃ₗ[ℝ] LinearMap.range b.param.linear :=
    LinearEquiv.ofInjective b.param.linear (chart_linear_injective b)
  let f : LinearMap.range b.param.linear →ₗ[ℝ] ℝ :=
    ℓ.comp e.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, ?_⟩
  intro s
  have hmem : b.param.linear s ∈ LinearMap.range b.param.linear :=
    LinearMap.mem_range_self _ _
  have he : e s = ⟨b.param.linear s, hmem⟩ := rfl
  have hback : e.symm ⟨b.param.linear s, hmem⟩ = s := e.symm_apply_apply s
  have hgs : g (b.param.linear s) = ℓ s := by
    have hh := congrArg (fun k => k ⟨b.param.linear s, hmem⟩) hg
    change g (b.param.linear s) = ℓ (e.symm ⟨b.param.linear s, hmem⟩) at hh
    simpa [hback] using hh
  have hdiff : b.param s - b.param 0 = b.param.linear s := by
    simpa using (b.param.linear_apply_vsub s 0).symm
  rw [hdiff]
  simpa [ℓ, real_inner_comm] using hgs

/-- A whole-base ball chart gives the original proper effect separating every
coordinate antipodal pair.  The hypothesis `hwhole` is the full-base branch of
the source theorem: the selected entire pair face is the original base. -/
theorem ball_chart_antipodal_effect
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    {p q : V} (b : BallChart C u p q)
    (hwhole : pairBase C u p q = base C u)
    {n : EuclideanSpace ℝ (Fin b.dim)} (hn : ‖n‖ = 1) :
    ∃ f : V →ₗ[ℝ] ℝ,
      confirms C u (b.param n) f ∧ f (b.param (-n)) = 0 := by
  let E := EuclideanSpace ℝ (Fin b.dim)
  obtain ⟨g, hg⟩ := chart_linear_coordinate b n hn
  let α : ℝ := g (b.param 0)
  let f : V →ₗ[ℝ] ℝ :=
    (1 / 2 : ℝ) • u + (1 / 2 : ℝ) • g - (α / 2 : ℝ) • u
  have hchart (s : E) (hs : ‖s‖ ≤ 1) : b.param s ∈ base C u := by
    rw [← hwhole, ← b.whole]
    exact ⟨s, by simpa using hs, rfl⟩
  have hformula (s : E) (hs : ‖s‖ ≤ 1) :
      f (b.param s) = (1 + ⟪n, s⟫) / 2 := by
    have hsbase := hchart s hs
    have h0base := hchart 0 (by simp)
    have hu_s : u (b.param s) = 1 := hsbase.2
    have hu_0 : u (b.param 0) = 1 := h0base.2
    have hgs := hg s
    dsimp [f, α]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul, hu_s, hu_0]
    have hgdiff : g (b.param s) - g (b.param 0) = ⟪n, s⟫ := by
      simpa [map_sub] using hgs
    linarith
  have hbound (s : E) (hs : ‖s‖ ≤ 1) :
      0 ≤ f (b.param s) ∧ f (b.param s) ≤ 1 := by
    rw [hformula s hs]
    have hi : |⟪n, s⟫| ≤ 1 := by
      calc
        |⟪n, s⟫| ≤ ‖n‖ * ‖s‖ := abs_real_inner_le_norm n s
        _ ≤ 1 := by simpa [hn] using hs
    constructor <;> linarith [abs_le.mp hi]
  have hproper : proper C u f := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hux : 0 < u x := hstrict x hx hx0
    let z : V := (u x)⁻¹ • x
    have hz : z ∈ base C u := normalized_mem hstrict hx hx0
    rw [← hwhole] at hz
    rw [← b.whole] at hz
    obtain ⟨s, hs, hzs⟩ := hz
    have hs' : ‖s‖ ≤ 1 := by simpa using hs
    have hfz := hbound s hs'
    have hxz : x = u x • z := by
      dsimp [z]
      rw [smul_smul, mul_inv_cancel₀ hux.ne', one_smul]
    have hfx : f x = u x * f z := by
      calc
        f x = f (u x • z) := congrArg f hxz
        _ = u x • f z := map_smul f (u x) z
        _ = u x * f z := by rfl
    have hfz' : 0 ≤ f z ∧ f z ≤ 1 := by
      rw [← hzs]
      exact hfz
    rw [hfx]
    constructor
    · exact mul_nonneg hux.le hfz'.1
    · simpa [mul_one] using (mul_le_mul_of_nonneg_left hfz'.2 hux.le)
  have hplus : f (b.param n) = 1 := by
    rw [hformula n hn.le]
    rw [real_inner_self_eq_norm_sq, hn]
    norm_num
  have hminus : f (b.param (-n)) = 0 := by
    rw [hformula (-n) (by simpa [hn] using hn.le)]
    rw [inner_neg_right, real_inner_self_eq_norm_sq, hn]
    norm_num
  exact ⟨f, ⟨hproper, hplus⟩, hminus⟩

/-! The preceding effect is consumed by the original antipodal predicate. -/

theorem allAntipodes_of_full_pair_balls
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hB : ∀ (p q : pure C u), p ≠ q →
      ∃ b : BallChart C u p q, pairBase C u p q = base C u) :
    allAntipodes C u := by
  intro p q hpq b n hn _
  obtain ⟨_, hwhole⟩ := hB p q hpq
  obtain ⟨f, hf, hz⟩ := ball_chart_antipodal_effect C u hclosed hstrict b hwhole hn
  exact ⟨f, hf, hz⟩

private theorem small_pure_hull_face
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hseg : ∀ p q : pure C u, p ≠ q →
      pairBase C u p q = segment ℝ (p : V) (q : V))
    {ι : Type*} (f : ι → pure C u) (hf : Function.Injective f)
    (s : Finset ι) (hs : s.card ≤ 2) :
    IsExtreme ℝ (base C u) (convexHull ℝ ((fun i => (f i : V)) '' (s : Set ι))) ∧
    ∀ i, (f i : V) ∈ convexHull ℝ ((fun i => (f i : V)) '' (s : Set ι)) → i ∈ s := by
  classical
  have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases hcases with hzero | hone | htwo
  · have he : s = ∅ := Finset.card_eq_zero.mp hzero
    subst s
    simp only [Finset.coe_empty, Set.image_empty, convexHull_empty]
    exact ⟨⟨Set.empty_subset _, by simp⟩, by simp⟩
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
    simp only [Finset.coe_singleton, Set.image_singleton, convexHull_singleton]
    refine ⟨isExtreme_singleton.mpr (f i).property, ?_⟩
    intro j hj
    have he : f j = f i := Subtype.ext (Set.mem_singleton_iff.mp hj)
    simpa using hf he
  · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp htwo
    have hface := pair_extreme C u (f i) (f j)
    rw [hseg (f i) (f j) (fun h => hij (hf h))] at hface
    simp only [Finset.coe_pair, Set.image_pair, convexHull_pair]
    refine ⟨hface, ?_⟩
    intro k hk
    have he := (mem_extremePoints_iff_forall_segment.mp (f k).property).2
      (f i) (f i).property.1 (f j) (f j).property.1 hk
    rcases he with hi | hj
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inl (hf (Subtype.ext hi)).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (hf (Subtype.ext hj)).symm

private theorem small_pure_family_independent
    {C : PointedCone ℝ V} {u : V →ₗ[ℝ] ℝ}
    (hseg : ∀ p q : pure C u, p ≠ q →
      pairBase C u p q = segment ℝ (p : V) (q : V))
    {ι : Type*} [Fintype ι] (f : ι → pure C u) (hf : Function.Injective f)
    (hcard : Fintype.card ι ≤ 5) :
    AffineIndependent ℝ (fun i => (f i : V)) := by
  classical
  by_contra hdep
  obtain ⟨I, z, hzI, hzIc⟩ := Convex.radon_partition hdep
  have hside (J : Set ι) (hJ : J.toFinset.card ≤ 2)
      (hzJ : z ∈ convexHull ℝ ((fun i => (f i : V)) '' J))
      (hzJc : z ∈ convexHull ℝ ((fun i => (f i : V)) '' Jᶜ)) : False := by
    obtain ⟨hface, hvertices⟩ := small_pure_hull_face hseg f hf J.toFinset hJ
    simp only [Set.coe_toFinset] at hface hvertices
    have havoid : (fun i => (f i : V)) '' Jᶜ ⊆
        base C u \ convexHull ℝ ((fun i => (f i : V)) '' J) := by
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨(f i).property.1, fun h => hi (by simpa using hvertices i h)⟩
    exact (convexHull_min havoid (hface.convex_sdiff (base_convex C u)) hzJc).2 hzJ
  by_cases hI : I.toFinset.card ≤ 2
  · exact hside I hI hzI hzIc
  · have hIc : Iᶜ.toFinset.card ≤ 2 := by
      have hsum : I.toFinset.card + Iᶜ.toFinset.card = Fintype.card ι := by
        simpa using Finset.card_add_card_compl I.toFinset
      omega
    apply hside Iᶜ ?_ hzIc (by simpa using hzI)
    convert hIc using 1 <;> congr 1 <;> ext i <;> simp

/-- The segment-face branch of VII98.7 starts with the entire arbitrary pure
set. Radon forces it to be finite and affinely independent in affine dimension
at most three; the resulting original coordinate effects supply every chart
antipode. No finiteness or exposedness premise is used. -/
theorem segment_faces_lowdim_antipodes
    (C : PointedCone ℝ V) (u : V →ₗ[ℝ] ℝ)
    (hclosed : IsClosed (C : Set V))
    (hstrict : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hspan : Submodule.span ℝ (C : Set V) = ⊤)
    (hdim : Module.finrank ℝ (vectorSpan ℝ (base C u)) ≤ 3)
    (hseg : ∀ p q : pure C u, p ≠ q →
      pairBase C u p q = segment ℝ (p : V) (q : V)) :
    Finite (pure C u) ∧ simplex C u ∧
      Nat.card (pure C u) ≤ Module.finrank ℝ (vectorSpan ℝ (base C u)) + 1 ∧
      allAntipodes C u := by
  classical
  have hnofive (f : Fin 5 → pure C u) (hf : Function.Injective f) : False := by
    have hai := small_pure_family_independent hseg f hf (by simp)
    have hrank := hai.finrank_vectorSpan (by simp : Fintype.card (Fin 5) = 4 + 1)
    have hle : vectorSpan ℝ (Set.range (fun i => (f i : V))) ≤
        vectorSpan ℝ (base C u) :=
      vectorSpan_mono ℝ (by rintro _ ⟨i, rfl⟩; exact (f i).property.1)
    have := Submodule.finrank_mono hle
    omega
  have hfinite : Finite (pure C u) := by
    by_contra hn
    letI : Infinite (pure C u) := not_finite_iff_infinite.mp hn
    exact hnofive (fun i => Infinite.natEmbedding (pure C u) i.val)
      (fun _ _ h => Fin.ext ((Infinite.natEmbedding (pure C u)).injective h))
  letI : Finite (pure C u) := hfinite
  letI : Fintype (pure C u) := Fintype.ofFinite _
  have hcard : Fintype.card (pure C u) ≤ 4 := by
    by_contra hn
    have hle : Fintype.card (Fin 5) ≤ Fintype.card (pure C u) := by
      simp only [Fintype.card_fin]
      omega
    obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hle
    exact hnofive f f.injective
  have hai : AffineIndependent ℝ (fun p : pure C u => (p : V)) :=
    small_pure_family_independent hseg id Function.injective_id (by omega)
  have hbase : base C u = convexHull ℝ (pure C u) := by
    have hh := closure_convexHull_extremePoints (base_compact hclosed hstrict) (base_convex C u)
    change closure (convexHull ℝ (pure C u)) = base C u at hh
    rw [((Set.toFinite (pure C u)).isClosed_convexHull (𝕜 := ℝ)).closure_eq] at hh
    exact hh.symm
  have hS : simplex C u := ⟨hai, hbase⟩
  have hbound : Nat.card (pure C u) ≤
      Module.finrank ℝ (vectorSpan ℝ (base C u)) + 1 := by
    cases isEmpty_or_nonempty (pure C u) with
    | inl he => simp
    | inr he =>
      have hrank := hai.finrank_vectorSpan_add_one
      have hle : vectorSpan ℝ (Set.range (fun p : pure C u => (p : V))) ≤
          vectorSpan ℝ (base C u) :=
        vectorSpan_mono ℝ (by rintro _ ⟨p, rfl⟩; exact p.property.1)
      simpa [Nat.card_eq_fintype_card, ← hrank] using
        Nat.add_le_add_right (Submodule.finrank_mono hle) 1
  obtain ⟨e, he, hvalues, _, _, _⟩ :=
    zero_kernel_least_confirmation C u hclosed hstrict hspan (simplex_kernel_zero hS)
  refine ⟨hfinite, hS, hbound, ?_⟩
  intro p q hpq b n hn ha
  let a : pure C u := ⟨b.param n, ha⟩
  let r : pure C u := ⟨b.param (-n), chart_sphere_pure b (by simpa using hn)⟩
  have hra : r ≠ a := by
    intro h
    have hh := b.injective (congrArg Subtype.val h)
    have hzero : (2 : ℝ) • n = 0 := by
      have := congrArg (fun s => s + n) hh
      simpa [two_smul] using this.symm
    have : n = 0 := (smul_eq_zero.mp hzero).resolve_left (by norm_num)
    simp [this] at hn
  refine ⟨e a, he a, ?_⟩
  change e a (r : V) = 0
  simp [hvalues, hra]

end D5.S3.Quantum.Foundation.LowAffineDimensionalBOnly
