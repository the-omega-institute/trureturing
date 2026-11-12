/- GID: D5/S3/Quantum/Foundation/OriginalHeptagonObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalHeptagonObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: certified-instance; basis=refutes=gid:D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.extensionClaim; result=D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.result; claim=D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.extensionClaim
   digest: The original seven-point cone obstructs full proper extension of its facet ruler. -/

import D5.S3.Quantum.Foundation.WeightedRelationConfirmation
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-! All effects are real linear maps on the original three-dimensional space.
The cone is the conical hull of all seven original rays; no effect is sampled.
The local domain is an actual normalized zero face, not a chosen subspace. -/

noncomputable section
open scoped BigOperators

namespace D5.S3.Quantum.Foundation.OriginalHeptagonObstruction

open CircuitBalancedConfirmation WeightedRelationConfirmation

abbrev V := Fin 3 → ℝ

/-- The original seven normalized rays in the order of the source. -/
def p : Fin 7 → V :=
  ![![1,10,0], ![1,6,8], ![1,-2,10], ![1,-9,4],
    ![1,-9,-4], ![1,-2,-10], ![1,6,-8]]

/-- The full original conical hull, including arbitrary nonnegative real mixtures. -/
def C : PointedCone ℝ V := PointedCone.hull ℝ (Set.range p)

/-- The original mass coordinate. -/
def u : V →ₗ[ℝ] ℝ := LinearMap.proj 0

/-- The entire original normalized base. -/
def K : Set V := base C u

private def form (c : V) : V →ₗ[ℝ] ℝ :=
  c 0 • LinearMap.proj 0 + c 1 • LinearMap.proj 1 + c 2 • LinearMap.proj 2

private theorem form_apply (c z : V) :
    form c z = c 0 * z 0 + c 1 * z 1 + c 2 * z 2 := rfl

/-- All seven normalized original facet effects. -/
def h : Fin 7 → (V →ₗ[ℝ] ℝ) :=
  ![form ![9/19,1/19,0], form ![82/174,6/174,7/174],
    form ![76/160,-2/160,8/160], form ![80/168,-8/168,4/168],
    form ![80/168,-8/168,-4/168], form ![76/160,-2/160,-8/160],
    form ![82/174,6/174,-7/174]]

/-- The proper edge mass effect on the unchanged carrier. -/
def edgeEffect : V →ₗ[ℝ] ℝ := form ![22/42,2/42,1/42]

/-- The actual zero face of the original p₀ facet effect. -/
def facet : Set V := {z | z ∈ K ∧ h 0 z = 0}

/-- The endpoint ruler on that entire face, represented homogeneously. -/
def ruler : V →ₗ[ℝ] ℝ := (87/28 : ℝ) • h 1

/-- The specified projection, with the original complementary ray p₄. -/
def edgeProjection : V →ₗ[ℝ] V :=
  (((551/196 : ℝ) • (h 0 - (15/19 : ℝ) • h 1)).smulRight (p 0)) +
  (((551/196 : ℝ) • (h 1 - (71/87 : ℝ) • h 0)).smulRight (p 1))

/-- Existence of a proper extension of the specified ruler on the whole original face. -/
def extensionClaim : Prop :=
  ∃ f : V →ₗ[ℝ] ℝ, proper C u f ∧ ∀ z ∈ facet, f z = ruler z

private theorem p_mem (i : Fin 7) : p i ∈ C := PointedCone.subset_hull ⟨i,rfl⟩

private theorem unit_p (i : Fin 7) : u (p i) = 1 := by
  fin_cases i <;> norm_num [u,p]

private theorem p_base (i : Fin 7) : p i ∈ K := ⟨p_mem i,unit_p i⟩

private theorem cone_weights {z : V} (hz : z ∈ C) :
    ∃ w : Fin 7 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i • p i = z := by
  obtain ⟨w,hw⟩ := (Submodule.mem_span_range_iff_exists_fun (R := {r : ℝ // 0 ≤ r})).mp hz
  exact ⟨fun i => (w i : ℝ),fun i => (w i).property,hw⟩

private theorem weights_cone (w : Fin 7 → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i • p i ∈ C :=
  C.sum_mem (fun i _ => C.smul_mem (hw i) (p_mem i))

private theorem base_weights {z : V} (hz : z ∈ K) :
    ∃ w : Fin 7 → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ ∑ i, w i • p i = z := by
  obtain ⟨w,hw,rfl⟩ := cone_weights hz.1
  refine ⟨w,hw,?_,rfl⟩
  simpa [map_sum,map_smul,unit_p] using hz.2

private theorem base_hull : K = convexHull ℝ (Set.range p) := by
  apply Set.Subset.antisymm
  · intro z hz
    obtain ⟨w,hw,hs,rfl⟩ := base_weights hz
    exact (convex_convexHull ℝ (Set.range p)).sum_mem
      (fun i _ => hw i) hs (fun i _ => subset_convexHull ℝ (Set.range p) ⟨i,rfl⟩)
  · exact convexHull_min (by rintro _ ⟨i,rfl⟩; exact p_base i) (base_convex C u)

private theorem proper_of_vertices (f : V →ₗ[ℝ] ℝ)
    (hf : ∀ i, 0 ≤ f (p i) ∧ f (p i) ≤ 1) : proper C u f := by
  intro z hz
  obtain ⟨w,hw,rfl⟩ := cone_weights hz
  simp only [map_sum,map_smul,smul_eq_mul]
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hf i).1)
  · apply Finset.sum_le_sum
    intro i _
    rw [unit_p]
    exact mul_le_mul_of_nonneg_left (hf i).2 (hw i)

private theorem h_proper (i : Fin 7) : proper C u (h i) := by
  apply proper_of_vertices
  intro j
  fin_cases i <;> fin_cases j <;> norm_num [h,p,form_apply]

private theorem h_self (i : Fin 7) : h i (p i) = 1 := by
  fin_cases i <;> norm_num [h,p,form_apply]

private theorem linear_coordinates (f : V →ₗ[ℝ] ℝ) (z : V) :
    f z = z 0 * f (Pi.single 0 1) + z 1 * f (Pi.single 1 1) + z 2 * f (Pi.single 2 1) := by
  have hz : z = z 0 • Pi.single 0 1 + z 1 • Pi.single 1 1 + z 2 • Pi.single 2 1 := by
    ext k
    fin_cases k <;> simp
  conv_lhs => rw [hz]
  simp [map_add,map_smul,smul_eq_mul]

/-- Universal domination supplies the full mixed exclusion argument. The input f
is arbitrary in the entire proper interval, not one of the seven facet effects. -/
private theorem confirmer_bound (i j : Fin 7) (f : V →ₗ[ℝ] ℝ)
    (hf : confirms C u (p i) f) : h i (p j) ≤ 100 * f (p j) := by
  have h0 := hf.1 (p 0) (p_mem 0)
  have h1 := hf.1 (p 1) (p_mem 1)
  have h2 := hf.1 (p 2) (p_mem 2)
  have h3 := hf.1 (p 3) (p_mem 3)
  have h4 := hf.1 (p 4) (p_mem 4)
  have h5 := hf.1 (p 5) (p_mem 5)
  have h6 := hf.1 (p 6) (p_mem 6)
  have hc := hf.2
  rw [linear_coordinates f (p 0)] at h0
  rw [linear_coordinates f (p 1)] at h1
  rw [linear_coordinates f (p 2)] at h2
  rw [linear_coordinates f (p 3)] at h3
  rw [linear_coordinates f (p 4)] at h4
  rw [linear_coordinates f (p 5)] at h5
  rw [linear_coordinates f (p 6)] at h6
  rw [linear_coordinates f (p i)] at hc
  rw [linear_coordinates f (p j)]
  fin_cases i <;> fin_cases j <;>
    norm_num [h,p,u,form_apply] at * <;> linarith

private theorem exclusion_zero (i : Fin 7) {z : V} (hz : z ∈ C)
    (he : ∃ f, confirms C u (p i) f ∧ f z = 0) : h i z = 0 := by
  obtain ⟨f,hf,hfz⟩ := he
  apply le_antisymm _ ((h_proper i z hz).1)
  obtain ⟨w,hw,rfl⟩ := cone_weights hz
  have hb : ∑ j, w j * h i (p j) ≤ ∑ j, w j * (100 * f (p j)) :=
    Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (confirmer_bound i j f hf) (hw j))
  have heq : (∑ j, w j * (100 * f (p j))) = 100 * f (∑ j, w j • p j) := by
    simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
    congr 1
    ext j
    ring
  rw [heq,hfz,mul_zero] at hb
  simpa [map_sum,map_smul,smul_eq_mul] using hb

/-- Zero gluing holds for every original pure point and every actual pair of mixed states. -/
theorem whole_mixed_zero_gluing : zeroGluing C u := by
  intro q x y hx hy he hf
  have hq : (q : V) ∈ Set.range p := by
    apply extremePoints_convexHull_subset
    simpa only [pure,← base_hull] using q.property
  obtain ⟨i,hi⟩ := hq
  have he' : h i x = 0 := exclusion_zero i hx.1 (by simpa [hi] using he)
  have hf' : h i y = 0 := exclusion_zero i hy.1 (by simpa [hi] using hf)
  exact ⟨h i,⟨h_proper i,by simpa [hi] using h_self i⟩,
    by simp [map_smul,map_add,he',hf']⟩

private theorem edge_proper : proper C u edgeEffect := by
  apply proper_of_vertices
  intro i
  fin_cases i <;> norm_num [edgeEffect,p,form_apply]

private theorem facet_endpoints : p 3 ∈ facet ∧ p 4 ∈ facet := by
  constructor <;> refine ⟨p_base _,?_⟩ <;> norm_num [h,p,form_apply]

private theorem extensions_exhaustive (f : V →ₗ[ℝ] ℝ) :
    (∀ z ∈ facet, f z = ruler z) ↔ ∃ μ : ℝ, f = ruler + μ • h 0 := by
  constructor
  · intro hf
    have h3 := hf (p 3) facet_endpoints.1
    have h4 := hf (p 4) facet_endpoints.2
    refine ⟨19 * (f (Pi.single 0 1) - ruler (Pi.single 0 1)) / 9,?_⟩
    ext z
    rw [linear_coordinates f (p 3)] at h3
    rw [linear_coordinates f (p 4)] at h4
    rw [linear_coordinates f z]
    norm_num [ruler,h,p,form_apply] at h3 h4
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    norm_num [ruler,h,form_apply,Pi.single_apply]
    linear_combination (z 2 / 8 - z 1 / 18) * h3 + (-z 2 / 8 - z 1 / 18) * h4
  · rintro ⟨μ,rfl⟩ z hz
    simp [hz.2]

private theorem no_extension : ¬ extensionClaim := by
  rintro ⟨f,hf,he⟩
  obtain ⟨μ,rfl⟩ := (extensions_exhaustive f).mp he
  have hp := (hf (p 5) (p_mem 5)).1
  have hq := (hf (p 1) (p_mem 1)).2
  norm_num [ruler,h,p,u,form_apply] at hp hq
  linarith

private theorem projection_formula (z : V) :
    edgeProjection z =
      ((h 0 z - (15/19 : ℝ) * h 1 z) / (196/551 : ℝ)) • p 0 +
      ((h 1 z - (71/87 : ℝ) * h 0 z) / (196/551 : ℝ)) • p 1 := by
  simp [edgeProjection,div_eq_mul_inv,mul_comm]

private theorem projection_mass (z : V) : u (edgeProjection z) = edgeEffect z := by
  rw [projection_formula]
  simp only [map_add,map_smul,smul_eq_mul,unit_p,mul_one]
  norm_num [h,edgeEffect,form_apply]
  ring

private theorem projection_not_positive : edgeProjection (p 5) ∉ C := by
  intro hp
  have hb := (h_proper 6 _ hp).1
  rw [projection_formula] at hb
  norm_num [map_add,map_smul,h,p,form_apply] at hb

/-- The original facet ruler has no proper real linear extension. -/
theorem result : ¬ extensionClaim := no_extension

end D5.S3.Quantum.Foundation.OriginalHeptagonObstruction
