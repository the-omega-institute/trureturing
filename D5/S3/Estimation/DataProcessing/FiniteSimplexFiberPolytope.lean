/- GID: D5/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope
   generality: G
   mirror-B: D5/B/S3/Estimation/DataProcessing/FiniteSimplexFiberPolytope
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact linear slices of finite real probability simplexes are finite convex hulls. -/

import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

open Set
open scoped BigOperators

noncomputable section
set_option autoImplicit false

namespace D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope

variable {ι E : Type*} [Fintype ι]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]

def IsPolytope (C : Set (ι → ℝ)) : Prop :=
  ∃ V : Finset (ι → ℝ), convexHull ℝ (V : Set (ι → ℝ)) = C

def simplexFiber (A : (ι → ℝ) →ₗ[ℝ] E) (b : E) : Set (ι → ℝ) :=
  {x | x ∈ stdSimplex ℝ ι ∧ A x = b}

def positiveSupport (x : ι → ℝ) : Set ι := {i | 0 < x i}

/-- A finite positive floor, including a unit cap, for all positive coordinates. -/
private lemma positive_floor (x : ι → ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ i, 0 < x i → t ≤ x i := by
  classical
  let a : ι → ℝ := fun i => if 0 < x i then x i else 1
  let S : Finset ℝ := insert 1 (Finset.univ.image a)
  have hS : S.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let δ : ℝ := S.min' hS
  have hδpos : 0 < δ := by
    have hm : δ ∈ S := Finset.min'_mem S hS
    rcases Finset.mem_insert.mp hm with hm | hm
    · simpa only [hm] using (zero_lt_one : (0 : ℝ) < 1)
    · obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hm
      rw [← hia]
      dsimp [a]
      split_ifs with h
      · exact h
      · exact zero_lt_one
  have hδone : δ ≤ 1 := Finset.min'_le S 1 (Finset.mem_insert_self _ _)
  have hδx (i : ι) (hi : 0 < x i) : δ ≤ x i := by
    apply Finset.min'_le
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by simp [a, hi]⟩
  refine ⟨δ / 2, by positivity, by linarith, ?_⟩
  intro i hi
  linarith [hδx i hi]

/-- An extreme feasible vector admits no other feasible vector with smaller support. -/
lemma extreme_eq_of_support_subset (A : (ι → ℝ) →ₗ[ℝ] E) (b : E)
    {x y : ι → ℝ} (hx : x ∈ (simplexFiber A b).extremePoints ℝ)
    (hy : y ∈ simplexFiber A b)
    (hsub : positiveSupport y ⊆ positiveSupport x) : y = x := by
  classical
  have hxF : x ∈ simplexFiber A b := hx.1
  obtain ⟨t, ht0, ht1, htx⟩ := positive_floor x
  have hden : 0 < 1 - t := sub_pos.mpr ht1
  have hden0 : (1 - t) ≠ 0 := ne_of_gt hden
  let z : ι → ℝ := (1 - t)⁻¹ • (x - t • y)
  have hdiff (i : ι) : 0 ≤ x i - t * y i := by
    by_cases hxi : 0 < x i
    · have hyi := mem_Icc_of_mem_stdSimplex hy.1 i
      exact sub_nonneg.mpr (calc
        t * y i ≤ t * 1 := mul_le_mul_of_nonneg_left hyi.2 ht0.le
        _ = t := mul_one t
        _ ≤ x i := htx i hxi)
    · have hxzero : x i = 0 := le_antisymm (le_of_not_gt hxi) (hxF.1.1 i)
      have hyzero : y i = 0 := by
        apply le_antisymm
        · by_contra hn
          have hyp : 0 < y i := lt_of_not_ge hn
          have hxp : 0 < x i := hsub hyp
          exact hxi hxp
        · exact hy.1.1 i
      simp [hxzero, hyzero]
  have hzF : z ∈ simplexFiber A b := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i
      exact mul_nonneg (inv_nonneg.mpr hden.le) (hdiff i)
    · change (∑ i, (1 - t)⁻¹ * (x i - t * y i)) = 1
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hxF.1.2, hy.1.2]
      field_simp
    · change A ((1 - t)⁻¹ • (x - t • y)) = b
      rw [map_smul, map_sub, map_smul, hxF.2, hy.2]
      rw [show b - t • b = (1 - t) • b by rw [sub_smul, one_smul],
        smul_smul, inv_mul_cancel₀ hden0, one_smul]
  have hxseg : x ∈ openSegment ℝ y z := by
    refine ⟨t, 1 - t, ht0, hden, by ring, ?_⟩
    ext i
    change t * y i + (1 - t) * ((1 - t)⁻¹ * (x i - t * y i)) = x i
    field_simp
    ring
  exact (mem_extremePoints_iff_left.mp hx).2 y hy z hzF hxseg

lemma finite_extremePoints (A : (ι → ℝ) →ₗ[ℝ] E) (b : E) :
    ((simplexFiber A b).extremePoints ℝ).Finite := by
  classical
  let f : (simplexFiber A b).extremePoints ℝ → Set ι := fun x => positiveSupport x.val
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hsub : positiveSupport y.val ⊆ positiveSupport x.val := by
      change f y ⊆ f x
      rw [hxy]
    exact (extreme_eq_of_support_subset A b x.property y.property.1 hsub).symm
  let : Finite ((simplexFiber A b).extremePoints ℝ) := Finite.of_injective f hf
  exact Set.toFinite _

/-- Every exact linear slice of a finite real probability simplex is a finite convex hull.
The slice may be empty and masses may vanish; no rationality is assumed. -/
theorem simplexFiber_isPolytope (A : (ι → ℝ) →ₗ[ℝ] E) (b : E) :
    IsPolytope (simplexFiber A b) := by
  classical
  have hclosed : IsClosed {x : ι → ℝ | A x = b} :=
    isClosed_eq A.continuous_of_finiteDimensional continuous_const
  have hcompact : IsCompact (simplexFiber A b) :=
    (isCompact_stdSimplex ℝ ι).inter_right hclosed
  have hconv : Convex ℝ (simplexFiber A b) := by
    intro x hx y hy a c ha hc hac
    refine ⟨convex_stdSimplex ℝ ι hx.1 hy.1 ha hc hac, ?_⟩
    rw [map_add, map_smul, map_smul, hx.2, hy.2, ← add_smul, hac, one_smul]
  have hfin := finite_extremePoints A b
  have hhull : convexHull ℝ ((simplexFiber A b).extremePoints ℝ) = simplexFiber A b := by
    rw [← (hfin.isClosed_convexHull ℝ).closure_eq]
    exact closure_convexHull_extremePoints hcompact hconv
  refine ⟨hfin.toFinset, ?_⟩
  simpa only [hfin.coe_toFinset] using hhull

section DeclaredCoordinates

variable {W Z U : Type*} [Fintype W] [Fintype Z] [Fintype U]

/-- The actual deterministic pushforward on finite real mass coordinates. -/
def pushMass {V : Type*} [Fintype V] (f : W → V) : (W → ℝ) →ₗ[ℝ] (V → ℝ) := by
  classical
  exact {
    toFun := fun x v => ∑ w, if f w = v then x w else 0
    map_add' := by
      intro x y
      ext v
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro w hw
      split_ifs <;> ring
    map_smul' := by
      intro a x
      ext v
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w hw
      split_ifs <;> ring
  }

def outsideMass (A : Set W) : (W → ℝ) →ₗ[ℝ] (W → ℝ) := by
  classical
  exact {
    toFun := fun x w => if w ∈ A then 0 else x w
    map_add' := by intro x y; ext w; split_ifs <;> simp_all
    map_smul' := by intro a x; ext w; split_ifs <;> simp_all
  }

def declaredConstraint (label : W → Z) (source : W → U) (A : Set W) :
    (W → ℝ) →ₗ[ℝ] ((Z → ℝ) × (U → ℝ) × (W → ℝ)) :=
  (pushMass label).prod ((pushMass source).prod (outsideMass A))

def declaredCoordinateClass (label : W → Z) (source : W → U) (A : Set W)
    (Q : Z → ℝ) (ν : U → ℝ) : Set (W → ℝ) :=
  {x | x ∈ stdSimplex ℝ W ∧ pushMass label x = Q ∧
    pushMass source x = ν ∧ outsideMass A x = 0}

/-- Concrete exact label, joint-source and support constraints, with all carrier symbols. -/
theorem declaredCoordinateClass_isPolytope (label : W → Z) (source : W → U)
    (A : Set W) (Q : Z → ℝ) (ν : U → ℝ) :
    IsPolytope (declaredCoordinateClass label source A Q ν) := by
  have heq : declaredCoordinateClass label source A Q ν =
      simplexFiber (declaredConstraint label source A) (Q, ν, 0) := by
    ext x
    change (x ∈ stdSimplex ℝ W ∧ pushMass label x = Q ∧
      pushMass source x = ν ∧ outsideMass A x = 0) ↔
      x ∈ stdSimplex ℝ W ∧
        (pushMass label x, pushMass source x, outsideMass A x) = (Q, ν, 0)
    simp only [Prod.mk.injEq]
  rw [heq]
  exact simplexFiber_isPolytope _ _

end DeclaredCoordinates
end D5.S3.Estimation.DataProcessing.FiniteSimplexFiberPolytope
