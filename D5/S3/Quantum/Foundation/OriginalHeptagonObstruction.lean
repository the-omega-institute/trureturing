/- GID: D5/S3/Quantum/Foundation/OriginalHeptagonObstruction
   generality: I
   mirror-B: D5/B/S3/Quantum/Foundation/OriginalHeptagonObstruction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: certified-instance; basis=refutes=gid:D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.extensionClaim; result=D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.result; claim=D5/S3/Quantum/Foundation/OriginalHeptagonObstruction.extensionClaim
   digest: The original seven-point cone obstructs full proper extension of its facet ruler. -/

import D5.S3.Quantum.Foundation.FinitePureSimplex
import D5.S3.Quantum.Foundation.WholePairBallConfirmation
import Mathlib.Analysis.Convex.Combination
import Mathlib.LinearAlgebra.AffineSpace.Restrict
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

set_option maxHeartbeats 2000000 in
-- The seven symbolic confirmer polyhedra require seven-by-seven linear checks.
/-- Universal domination uses arbitrary proper real linear confirmers. -/
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

private theorem confirmer_bound_cone (i : Fin 7) (f : V →ₗ[ℝ] ℝ)
    (hf : confirms C u (p i) f) {z : V} (hz : z ∈ C) : h i z ≤ 100 * f z := by
  obtain ⟨w,hw,rfl⟩ := cone_weights hz
  calc
    h i (∑ j, w j • p j) = ∑ j, w j * h i (p j) := by
      simp [map_sum,map_smul,smul_eq_mul]
    _ ≤ ∑ j, w j * (100 * f (p j)) :=
      Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (confirmer_bound i j f hf) (hw j))
    _ = 100 * f (∑ j, w j • p j) := by
      simp only [map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
      congr 1
      ext j
      ring

private theorem exclusion_zero (i : Fin 7) {z : V} (hz : z ∈ C)
    (he : ∃ f, confirms C u (p i) f ∧ f z = 0) : h i z = 0 := by
  obtain ⟨f,hf,hfz⟩ := he
  apply le_antisymm _ ((h_proper i z hz).1)
  simpa only [hfz,mul_zero] using confirmer_bound_cone i f hf hz

private theorem comparison_zero_iff (i : Fin 7) (z : V) (hz : z ∈ C) :
    comparison C u (p i) z = 0 ↔ ∃ f, confirms C u (p i) f ∧ f z = 0 := by
  let R := {r : ℝ | ∃ f, confirms C u (p i) f ∧ f z = r}
  have hne : R.Nonempty := ⟨h i z,h i,⟨h_proper i,h_self i⟩,rfl⟩
  have hb : BddBelow R := ⟨0,by rintro r ⟨f,hf,rfl⟩; exact (hf.1 z hz).1⟩
  have hn : 0 ≤ sInf R := le_csInf hne (by
    rintro r ⟨f,hf,rfl⟩
    exact (hf.1 z hz).1)
  constructor
  · intro he
    have hl : h i z / 100 ≤ sInf R := by
      apply le_csInf hne
      rintro r ⟨f,hf,rfl⟩
      have hh := confirmer_bound_cone i f hf hz
      linarith
    change sInf R = 0 at he
    rw [he] at hl
    exact ⟨h i,⟨h_proper i,h_self i⟩,le_antisymm (by linarith) (h_proper i z hz).1⟩
  · rintro ⟨f,hf,hfz⟩
    exact le_antisymm (csInf_le hb ⟨f,hf,hfz⟩) hn

private theorem self_fiber (i : Fin 7) (z : V) (hz : z ∈ K)
    (he : h i z = 1) : z = p i := by
  obtain ⟨w,hw,hs,rfl⟩ := base_weights hz
  have hn (j : Fin 7) : 0 ≤ 1-h i (p j) := by
    simpa only [unit_p,sub_nonneg] using (h_proper i _ (p_mem j)).2
  have ht : ∑ j, w j * (1-h i (p j)) = 0 := by
    simp only [mul_sub,mul_one,Finset.sum_sub_distrib]
    rw [hs]
    simpa [map_sum,map_smul,smul_eq_mul] using sub_eq_zero.mpr he.symm
  have hj0 : ∀ j, j ≠ i → w j = 0 := by
    intro j hji
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hw j) (hn j))).mp ht j (Finset.mem_univ j)
    have hne : 1-h i (p j) ≠ 0 := by
      fin_cases i <;> fin_cases j <;> norm_num [h,p,form_apply] at *
    exact (mul_eq_zero.mp hh).resolve_right hne
  have hwi : w i = 1 := by
    calc
      w i = ∑ j, w j := by
        symm
        exact Finset.sum_eq_single i (fun j _ hji => hj0 j hji) (by simp)
      _ = 1 := hs
  rw [Finset.sum_eq_single i]
  · simp [hwi]
  · intro j _ hji
    simp [hj0 j hji]
  · simp

private theorem pure_family : pure C u = Set.range p := by
  apply Set.Subset.antisymm
  · intro q hq
    apply extremePoints_convexHull_subset (𝕜 := ℝ)
    rw [← base_hull]
    exact hq
  · rintro _ ⟨i,rfl⟩
    refine ⟨p_base i,?_⟩
    intro x hx y hy hseg
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    have he' := congrArg (h i) he
    simp only [map_add,map_smul,smul_eq_mul,h_self] at he'
    have hx' := (h_proper i x hx.1).2
    have hy' := (h_proper i y hy.1).2
    rw [hx.2] at hx'
    rw [hy.2] at hy'
    apply self_fiber i x hx
    nlinarith

/-- Zero gluing holds for every original pure point and every actual pair of mixed states. -/
theorem whole_mixed_zero_gluing : zeroGluing C u := by
  intro q x y hx hy he hf
  have hq : (q : V) ∈ Set.range p := by
    apply extremePoints_convexHull_subset (𝕜 := ℝ)
    rw [← base_hull]
    exact q.property
  obtain ⟨i,hi⟩ := hq
  have he' : h i x = 0 := exclusion_zero i hx.1 (by simpa [hi] using he)
  have hf' : h i y = 0 := exclusion_zero i hy.1 (by simpa [hi] using hf)
  exact ⟨h i,⟨h_proper i,by simpa [hi] using h_self i⟩,
    by simp [map_smul,map_add,he',hf']⟩

private theorem edge_proper : proper C u edgeEffect := by
  apply proper_of_vertices
  intro i
  fin_cases i <;> norm_num [edgeEffect,p,form_apply]

private theorem zero_slice (f : V →ₗ[ℝ] ℝ) (i j : Fin 7) (hij : i ≠ j)
    (hf : ∀ k, 0 ≤ f (p k))
    (hz : ∀ k, f (p k) = 0 ↔ k = i ∨ k = j) :
    {z | z ∈ K ∧ f z = 0} = segment ℝ (p i) (p j) := by
  ext z
  constructor
  · rintro ⟨hk,hfz⟩
    obtain ⟨w,hw,hs,rfl⟩ := base_weights hk
    have ht : ∀ k, w k * f (p k) = 0 := by
      have he : ∑ k, w k * f (p k) = 0 := by
        simpa [map_sum,map_smul,smul_eq_mul] using hfz
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (hw k) (hf k))).mp he
        |> fun hh k => hh k (Finset.mem_univ k)
    have hwz : ∀ k, k ≠ i → k ≠ j → w k = 0 := by
      intro k hki hkj
      exact (mul_eq_zero.mp (ht k)).resolve_right (by simpa [hz k,hki,hkj])
    have sum_restrict (g : Fin 7 → ℝ) : ∑ k, w k * g k = w i * g i + w j * g j := by
      rw [← Finset.sum_subset (Finset.subset_univ ({i,j} : Finset (Fin 7)))]
      · simp [hij]
      · intro k _ hk
        have hk' : k ≠ i ∧ k ≠ j := by simpa using hk
        simp [hwz k hk'.1 hk'.2]
    have sum_vec : ∑ k, w k • p k = w i • p i + w j • p j := by
      ext k
      simpa [Finset.sum_apply,Pi.smul_apply,Pi.add_apply,smul_eq_mul] using
        sum_restrict (fun a => p a k)
    refine ⟨w i,w j,hw i,hw j,?_,sum_vec.symm⟩
    simpa using (sum_restrict (fun _ => 1)).symm.trans (by simpa using hs)
  · rintro ⟨a,b,ha,hb,hab,rfl⟩
    refine ⟨base_convex C u (p_base i) (p_base j) ha hb hab,?_⟩
    simp [map_add,map_smul,(hz i).mpr (Or.inl rfl),(hz j).mpr (Or.inr rfl)]

private theorem facet_slices (i : Fin 7) :
    {z | z ∈ K ∧ h i z = 0} = segment ℝ (p (i+3)) (p (i+4)) := by
  apply zero_slice (h i) (i+3) (i+4)
  · fin_cases i <;> decide
  · intro k
    exact (h_proper i _ (p_mem k)).1
  · intro k
    fin_cases i <;> fin_cases k <;> norm_num [h,p,form_apply]

private theorem entire_exclusion_face (i : Fin 7) (z : V) (hz : z ∈ K) :
    (∃ f, confirms C u (p i) f ∧ f z = 0) ↔
      z ∈ segment ℝ (p (i+3)) (p (i+4)) := by
  rw [← facet_slices]
  constructor
  · exact fun he => ⟨hz,exclusion_zero i hz.1 he⟩
  · exact fun he => ⟨h i,⟨h_proper i,h_self i⟩,he.2⟩

private theorem facet_segment : facet = segment ℝ (p 3) (p 4) := facet_slices 0

private theorem edge_one_face : {z | z ∈ K ∧ edgeEffect z = 1} =
    segment ℝ (p 0) (p 1) := by
  have he := zero_slice (u-edgeEffect) 0 1 (by decide)
    (fun k => by have hh := (edge_proper _ (p_mem k)).2
                 simpa [unit_p,sub_nonneg] using hh)
    (by intro k; fin_cases k <;> norm_num [u,edgeEffect,p,form_apply])
  calc
    {z | z ∈ K ∧ edgeEffect z = 1} = {z | z ∈ K ∧ (u-edgeEffect) z = 0} := by
      ext z
      constructor <;> rintro ⟨hz,he⟩ <;> refine ⟨hz,?_⟩
      · simp [LinearMap.sub_apply,hz.2,he]
      · have hh : 1-edgeEffect z = 0 := by
          simpa only [LinearMap.sub_apply,hz.2] using he
        linarith
    _ = _ := he

private theorem ruler_local (z : V) (hz : z ∈ facet) : 0 ≤ ruler z ∧ ruler z ≤ 1 := by
  rw [facet_segment] at hz
  obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
  rw [map_add,map_smul,map_smul]
  norm_num [ruler,h,p,form_apply]
  exact ⟨ha,by linarith⟩

private theorem facet_maximum : IsGreatest ((h 1) '' facet) (28/87 : ℝ) := by
  constructor
  · exact ⟨p 3,by rw [facet_segment]; exact left_mem_segment ..,
      by norm_num [h,p,form_apply]⟩
  · rintro _ ⟨z,hz,rfl⟩
    have hb := (ruler_local z hz).2
    simp only [ruler,LinearMap.smul_apply,smul_eq_mul] at hb
    linarith

private theorem facet_endpoints : p 3 ∈ facet ∧ p 4 ∈ facet := by
  constructor <;> refine ⟨p_base _,?_⟩ <;> norm_num [h,p,form_apply]

private def zeroCone (f : V →ₗ[ℝ] ℝ) : PointedCone ℝ V :=
  C ⊓ (LinearMap.ker f : Submodule ℝ V)

private theorem zero_cone_face (f : V →ₗ[ℝ] ℝ) (hf : ∀ z ∈ C, 0 ≤ f z) :
    (zeroCone f).IsFaceOf C := by
  refine ⟨inf_le_left,?_⟩
  intro x y a hx hy ha hh
  refine ⟨hx,?_⟩
  have he : a * f x + f y = 0 := by
    simpa [zeroCone,map_add,map_smul,smul_eq_mul] using hh.2
  change f x = 0
  nlinarith [hf x hx,hf y hy]

private theorem whole_facet_pair :
    FinitePureSimplex.wholePairBase C u (p 3) (p 4) = facet := by
  ext z
  constructor
  · rintro ⟨hz,he⟩
    exact ⟨hz,(he (zeroCone (h 0)) (zero_cone_face (h 0) (fun z hz =>
      (h_proper 0 z hz).1))
      ⟨p_mem 3,facet_endpoints.1.2⟩ ⟨p_mem 4,facet_endpoints.2.2⟩).2⟩
  · intro hz
    refine ⟨hz.1,?_⟩
    rw [facet_segment] at hz
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hz
    intro F hF h3 h4
    exact F.add_mem (F.smul_mem ha h3) (F.smul_mem hb h4)

private theorem edge_is_pair :
    FinitePureSimplex.wholePairBase C u (p 0) (p 1) = segment ℝ (p 0) (p 1) := by
  ext z
  constructor
  · rintro ⟨hz,he⟩
    rw [← edge_one_face]
    refine ⟨hz,?_⟩
    have hp := he (zeroCone (u-edgeEffect))
      (zero_cone_face _ (fun z hz => sub_nonneg.mpr (edge_proper z hz).2))
      ⟨p_mem 0,by norm_num [u,edgeEffect,p,form_apply]⟩
      ⟨p_mem 1,by norm_num [u,edgeEffect,p,form_apply]⟩
    have hp' : u z - edgeEffect z = 0 := hp.2
    rw [hz.2] at hp'
    linarith
  · rintro ⟨a,b,ha,hb,hab,rfl⟩
    exact ⟨base_convex C u (p_base 0) (p_base 1) ha hb hab,
      fun F _ h0 h1 => F.add_mem (F.smul_mem ha h0) (F.smul_mem hb h1)⟩

private theorem extensions_exhaustive (f : V →ₗ[ℝ] ℝ) :
    (∀ z ∈ facet, f z = ruler z) ↔ ∃ μ : ℝ, f = ruler + μ • h 0 := by
  constructor
  · intro hf
    have h3 := hf (p 3) facet_endpoints.1
    have h4 := hf (p 4) facet_endpoints.2
    refine ⟨19 * (f (Pi.single 0 1) - ruler (Pi.single 0 1)) / 9,?_⟩
    apply LinearMap.ext
    intro z
    rw [linear_coordinates f (p 3)] at h3
    rw [linear_coordinates f (p 4)] at h4
    rw [linear_coordinates f z]
    norm_num [ruler,h,p,form_apply] at h3 h4
    simp only [LinearMap.add_apply,LinearMap.smul_apply,smul_eq_mul]
    norm_num [ruler,h,form_apply,Pi.single_apply]
    linear_combination (z 2 / 8 - z 1 / 18) * h3 + (-z 2 / 8 - z 1 / 18) * h4
  · rintro ⟨μ,rfl⟩ z hz
    simp [hz.2]

/-- The original facet ruler has no proper real linear extension. -/
theorem result : ¬ extensionClaim := by
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
  have hb := (h_proper 3 _ hp).1
  rw [projection_formula] at hb
  norm_num [map_add,map_smul,h,p,form_apply] at hb

private theorem projection_split (z : V) :
    z = edgeProjection z + (u z - edgeEffect z) • p 4 := by
  rw [projection_formula]
  ext k
  fin_cases k <;> norm_num [h,p,u,edgeEffect,form_apply] <;> ring

private theorem projection_on_generators :
    edgeProjection (p 0) = p 0 ∧ edgeProjection (p 1) = p 1 ∧
      edgeProjection (p 4) = 0 := by
  constructor
  · rw [projection_formula]
    norm_num [h,p,form_apply]
  constructor
  · rw [projection_formula]
    norm_num [h,p,form_apply]
  · rw [projection_formula]
    norm_num [h,p,form_apply]

private theorem complementary_face :
    {z | z ∈ K ∧ h 0 z = 0 ∧ h 1 z = 0} = {p 4} := by
  ext z
  constructor
  · rintro ⟨hz,h0,h1⟩
    have hs : z ∈ facet := ⟨hz,h0⟩
    rw [facet_segment] at hs
    obtain ⟨a,b,ha,hb,hab,rfl⟩ := hs
    norm_num [map_add,map_smul,h,p,form_apply] at h1
    have ha0 : a = 0 := by linarith
    have hb1 : b = 1 := by linarith
    simp [ha0,hb1]
  · rintro rfl
    refine ⟨p_base 4,?_,?_⟩ <;> norm_num [h,p,form_apply]

/-- The global affine coordinate plane uses the original normalized hyperplane. -/
def spatial : V →ₗ[ℝ] (Fin 2 → ℝ) :=
  LinearMap.pi ![LinearMap.proj 1,LinearMap.proj 2]

/-- Homogenization keeps the original unit t rather than changing the carrier. -/
def homogenize (g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ) : V →ₗ[ℝ] ℝ :=
  form ![g 0,g.linear (Pi.single 0 1),g.linear (Pi.single 1 1)]

private theorem homogenize_value (g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ)
    (z : V) (hz : u z = 1) : homogenize g z = g (spatial z) := by
  have he : spatial z = z 1 • Pi.single 0 1 + z 2 • Pi.single 1 1 := by
    ext k
    fin_cases k <;> simp [spatial]
  have hg : g (spatial z) = g.linear (spatial z) + g 0 :=
    congrFun g.decomp (spatial z)
  have hl : g.linear (spatial z) =
      z 1 * g.linear (Pi.single 0 1) + z 2 * g.linear (Pi.single 1 1) := by
    rw [he,map_add,map_smul,map_smul]
    rfl
  rw [hl] at hg
  change z 0 = 1 at hz
  norm_num [homogenize,form_apply,hz]
  linarith

private theorem linear_unique_on_base (f g : V →ₗ[ℝ] ℝ)
    (he : ∀ z ∈ K, f z = g z) : f = g := by
  let d := f-g
  have h0 : d (p 0) = 0 := sub_eq_zero.mpr (he _ (p_base 0))
  have h1 : d (p 1) = 0 := sub_eq_zero.mpr (he _ (p_base 1))
  have h4 : d (p 4) = 0 := sub_eq_zero.mpr (he _ (p_base 4))
  rw [linear_coordinates d (p 0)] at h0
  rw [linear_coordinates d (p 1)] at h1
  rw [linear_coordinates d (p 4)] at h4
  norm_num [p] at h0 h1 h4
  have a : d (Pi.single 0 1) = 0 := by linarith
  have b : d (Pi.single 1 1) = 0 := by linarith
  have c : d (Pi.single 2 1) = 0 := by linarith
  apply LinearMap.ext
  intro z
  have heq := linear_coordinates d z
  simp only [a,b,c,mul_zero,add_zero] at heq
  exact sub_eq_zero.mp heq

private theorem original_affine_span :
    (affineSpan ℝ K : Set V) = {z | u z = 1} := by
  let H : AffineSubspace ℝ V :=
    { carrier := {z | u z = 1}
      smul_vsub_vadd_mem' := by
        intro a x y z hx hy hz
        change u x = 1 at hx
        change u y = 1 at hy
        change u z = 1 at hz
        change u (a • (x-y)+z) = 1
        simp [map_add,map_smul,map_sub,hx,hy,hz] }
  have hle : affineSpan ℝ K ≤ H := affineSpan_le.mpr (fun z hz => hz.2)
  ext z
  constructor
  · exact fun hz => hle hz
  · intro hz
    have h0 := mem_affineSpan ℝ (p_base 0)
    have h1 := mem_affineSpan ℝ (p_base 1)
    have h4 := mem_affineSpan ℝ (p_base 4)
    let a := (19*z 2 - 4*(z 1-10*z 0))/168
    let b := (-8*(z 1-10*z 0)-4*z 2)/168
    have hm := (affineSpan ℝ K).smul_vsub_vadd_mem b h4 h0
      ((affineSpan ℝ K).smul_vsub_vadd_mem a h1 h0 h0)
    have he : z = b • (p 4 -ᵥ p 0) +ᵥ a • (p 1 -ᵥ p 0) +ᵥ p 0 := by
      ext k
      change z 0 = 1 at hz
      fin_cases k <;> norm_num [a,b,p,hz] <;> ring
    rw [he]
    exact hm

private theorem affine_homogeneous_bridge (g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ) :
    ∃! f : V →ₗ[ℝ] ℝ, ∀ z ∈ K, f z = g (spatial z) := by
  refine ⟨homogenize g,fun z hz => homogenize_value g z hz.2,?_⟩
  intro f hf
  exact linear_unique_on_base f _ (fun z hz => (hf z hz).trans
    (homogenize_value g z hz.2).symm)

private instance plane_nonempty : Nonempty (affineSpan ℝ K) :=
  ⟨⟨p 0,mem_affineSpan ℝ (p_base 0)⟩⟩

private def normalizedEmbedding : (Fin 2 → ℝ) →ᵃ[ℝ] V :=
  (LinearMap.pi ![0,LinearMap.proj 0,LinearMap.proj 1]).toAffineMap +
    AffineMap.const ℝ (Fin 2 → ℝ) (![1,0,0] : V)

private def planeParam : (Fin 2 → ℝ) →ᵃ[ℝ] (affineSpan ℝ K) :=
  (normalizedEmbedding.restrict (E := ⊤) (F := affineSpan ℝ K) (by
    rintro z ⟨x,_,rfl⟩
    rw [← SetLike.mem_coe,original_affine_span]
    norm_num [normalizedEmbedding,u,LinearMap.pi_apply,Matrix.vecHead])).comp
      (AffineSubspace.topEquiv ℝ (Fin 2 → ℝ) (Fin 2 → ℝ)).symm.toAffineMap

private theorem plane_param_inverse (z : affineSpan ℝ K) :
    planeParam (spatial (z : V)) = z := by
  apply Subtype.ext
  have hz : u (z : V) = 1 := by
    have hh := z.property
    change (z : V) ∈ (affineSpan ℝ K : Set V) at hh
    rw [original_affine_span] at hh
    exact hh
  change (z : V) 0 = 1 at hz
  ext k
  fin_cases k <;> simp [planeParam,normalizedEmbedding,spatial,hz,LinearMap.pi_apply]

private theorem actual_affine_bridge (g : (affineSpan ℝ K) →ᵃ[ℝ] ℝ) :
    ∃! f : V →ₗ[ℝ] ℝ, ∀ z : affineSpan ℝ K, f z = g z := by
  refine ⟨homogenize (g.comp planeParam),?_,?_⟩
  · intro z
    have hz : u (z : V) = 1 := by
      have hh := z.property
      change (z : V) ∈ (affineSpan ℝ K : Set V) at hh
      rw [original_affine_span] at hh
      exact hh
    rw [homogenize_value _ _ hz]
    change g (planeParam (spatial (z : V))) = g z
    rw [plane_param_inverse]
  · intro f hf
    apply linear_unique_on_base
    intro z hz
    rw [homogenize_value _ _ hz.2]
    exact (hf ⟨z,mem_affineSpan ℝ hz⟩).trans
      (congrArg g (plane_param_inverse ⟨z,mem_affineSpan ℝ hz⟩)).symm

private theorem no_actual_affine_extension :
    ¬ ∃ g : (affineSpan ℝ K) →ᵃ[ℝ] ℝ,
      (∀ z : affineSpan ℝ K, (z : V) ∈ K → 0 ≤ g z ∧ g z ≤ 1) ∧
      ∀ z : affineSpan ℝ K, (z : V) ∈ facet → g z = ruler z := by
  rintro ⟨g,hg,he⟩
  obtain ⟨f,hf,_⟩ := actual_affine_bridge g
  apply result
  refine ⟨f,proper_of_vertices _ (fun i => ?_),?_⟩
  · rw [hf ⟨p i,mem_affineSpan ℝ (p_base i)⟩]
    exact hg _ (p_base i)
  · intro z hz
    rw [hf ⟨z,mem_affineSpan ℝ hz.1⟩]
    exact he _ hz

private theorem no_affine_extension :
    ¬ ∃ g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ,
      (∀ z ∈ K, 0 ≤ g (spatial z) ∧ g (spatial z) ≤ 1) ∧
      ∀ z ∈ facet, g (spatial z) = ruler z := by
  rintro ⟨g,hg,he⟩
  apply result
  refine ⟨homogenize g,proper_of_vertices _ (fun i => ?_),?_⟩
  · simpa only [homogenize_value g _ (unit_p i)] using hg _ (p_base i)
  · intro z hz
    rw [homogenize_value g z hz.1.2]
    exact he z hz

private def localParam : EuclideanSpace ℝ (Fin 1) →ᵃ[ℝ] V :=
  ((EuclideanSpace.projₗ 0).smulRight (![0,0,4] : V)).toAffineMap +
    AffineMap.const ℝ (EuclideanSpace ℝ (Fin 1)) (![1,-9,0] : V)

private theorem local_param_apply (s : EuclideanSpace ℝ (Fin 1)) :
    localParam s = (![1,-9,4*s 0] : V) := by
  ext k
  fin_cases k <;> simp [localParam,mul_comm]

private theorem pair_base_agrees (a b : V) :
    WholePairBallConfirmation.pairBase C u a b =
      FinitePureSimplex.wholePairBase C u a b := by
  ext z
  constructor
  · rintro ⟨hz,hf⟩
    exact ⟨hz,fun F hF ha hb => hf ⟨F,hF⟩ ha hb⟩
  · rintro ⟨hz,hf⟩
    exact ⟨hz,fun F ha hb => hf F F.isFaceOf ha hb⟩

private def localBallChart : WholePairBallConfirmation.BallChart C u (p 3) (p 4) where
  dim := 1
  dim_pos := by norm_num
  param := localParam
  injective := by
    intro s t he
    have hh := congrArg (fun z => z 2) he
    rw [local_param_apply,local_param_apply] at hh
    norm_num at hh
    apply PiLp.ext
    intro i
    fin_cases i
    simpa using hh
  whole := by
    rw [pair_base_agrees,whole_facet_pair,facet_segment]
    ext z
    constructor
    · rintro ⟨s,hs,rfl⟩
      have hn0 : ‖s 0‖ ≤ ‖s‖ := PiLp.norm_apply_le s 0
      have hn : |s 0| ≤ 1 := by
        rw [Real.norm_eq_abs] at hn0
        exact hn0.trans (by simpa using hs)
      have hb := abs_le.mp hn
      refine ⟨(1+s 0)/2,(1-s 0)/2,by linarith,by linarith,by ring,?_⟩
      rw [local_param_apply]
      ext k
      fin_cases k <;> norm_num [p] <;> ring
    · rintro ⟨a,b,ha,hb,hab,rfl⟩
      refine ⟨PiLp.single 2 0 (a-b),?_,?_⟩
      · rw [Metric.mem_closedBall,dist_zero_right,PiLp.norm_single,Real.norm_eq_abs]
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      · rw [local_param_apply]
        ext k
        fin_cases k <;> norm_num [p,PiLp.single_apply] <;> linarith

private theorem comparison_upper : comparison C u (p 0) (p 5) ≤ (4/21 : ℝ) := by
  have hb : BddBelow {r : ℝ | ∃ f, confirms C u (p 0) f ∧ f (p 5) = r} := by
    refine ⟨0,?_⟩
    rintro r ⟨f,hf,rfl⟩
    exact (hf.1 _ (p_mem 5)).1
  have he : confirms C u (p 0) edgeEffect :=
    ⟨edge_proper,by norm_num [edgeEffect,p,form_apply]⟩
  exact csInf_le hb ⟨edgeEffect,he,by norm_num [edgeEffect,p,form_apply]⟩

private theorem unit_strict {z : V} (hz : z ∈ C) (hne : z ≠ 0) : 0 < u z := by
  obtain ⟨w,hw,rfl⟩ := cone_weights hz
  have hn : 0 ≤ ∑ i, w i := Finset.sum_nonneg (fun i _ => hw i)
  have hp : 0 < ∑ i, w i := by
    by_contra hh
    have hs : ∑ i, w i = 0 := le_antisymm (le_of_not_gt hh) hn
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hw i)).mp hs
    apply hne
    apply Finset.sum_eq_zero
    intro i hi
    simp [hz i hi]
  simpa [map_sum,map_smul,unit_p] using hp

private theorem cone_salient : (C : ConvexCone ℝ V).Salient := by
  intro z hz hne hneg
  have hp := unit_strict hz hne
  have hn := unit_strict hneg (neg_ne_zero.mpr hne)
  rw [map_neg] at hn
  linarith

private theorem cone_generating : Submodule.span ℝ (C : Set V) = ⊤ := by
  apply top_unique
  intro z _
  let a := (19*z 2 - 4*(z 1-10*z 0))/168
  let b := (-8*(z 1-10*z 0)-4*z 2)/168
  have he : z = (z 0-a-b) • p 0 + a • p 1 + b • p 4 := by
    ext k
    fin_cases k <;> norm_num [a,b,p] <;> ring
  rw [he]
  exact Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (p_mem 0)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (p_mem 1))))
    (Submodule.smul_mem _ _ (Submodule.subset_span (p_mem 4)))

private theorem cone_closed : IsClosed (C : Set V) := by
  apply IsSeqClosed.isClosed
  intro v z hv ht
  choose w hw he using fun n => cone_weights (hv n)
  have hmass : ∀ n, ∑ i, w n i = u (v n) := by
    intro n
    rw [← he n]
    simp [map_sum,map_smul,unit_p]
  have htu := u.continuous_of_finiteDimensional.tendsto z |>.comp ht
  obtain ⟨M,hM⟩ := (Metric.isBounded_range_of_tendsto (fun n => u (v n)) htu).exists_norm_le
  have hbox (n : ℕ) : w n ∈ Set.Icc (0 : Fin 7 → ℝ) (fun _ => M) := by
    refine ⟨hw n,fun i => ?_⟩
    calc
      w n i ≤ ∑ j, w n j := Finset.single_le_sum (fun j _ => hw n j) (Finset.mem_univ i)
      _ = u (v n) := hmass n
      _ ≤ ‖u (v n)‖ := le_abs_self _
      _ ≤ M := hM _ ⟨n,rfl⟩
  obtain ⟨a,ha,φ,hφ,hta⟩ := isCompact_Icc.tendsto_subseq hbox
  have hc : Continuous (fun a : Fin 7 → ℝ => ∑ i, a i • p i) := by fun_prop
  have hlim := hc.continuousAt.tendsto.comp hta
  have hlim' := ht.comp hφ.tendsto_atTop
  have hea : ∑ i, a i • p i = z := tendsto_nhds_unique hlim (by
    simpa only [Function.comp_def,he] using hlim')
  rw [← hea]
  exact C.sum_mem (fun i _ => C.smul_mem (ha.1 i) (p_mem i))

private theorem nonadjacent_pair_whole :
    FinitePureSimplex.wholePairBase C u (p 0) (p 2) = K := by
  apply Set.Subset.antisymm (fun _ hz => hz.1)
  intro z hz
  refine ⟨hz,?_⟩
  intro F hF h0 h2
  let w : Fin 7 → ℝ := ![759/4760,2901/4760,136/4760,556/4760,
    136/4760,136/4760,136/4760]
  have hw : ∀ i, 0 < w i := by intro i; fin_cases i <;> norm_num [w]
  have he : ∑ i, w i • p i = (1/2 : ℝ) • p 0 + (1/2 : ℝ) • p 2 := by
    ext k
    fin_cases k <;> norm_num [w,p,Fin.sum_univ_succ]
  have hm : ∑ i, w i • p i ∈ F := by
    rw [he]
    exact F.add_mem (F.smul_mem (by norm_num) h0) (F.smul_mem (by norm_num) h2)
  have hall (i : Fin 7) : p i ∈ F :=
    hF.mem_of_sum_smul_mem p_mem (fun i => (hw i).le) hm i (hw i)
  obtain ⟨a,ha,rfl⟩ := cone_weights hz.1
  exact F.sum_mem (fun i _ => F.smul_mem (ha i) (hall i))

private theorem no_center : ¬ ∃ c : V, ∀ z ∈ K, (2 : ℝ) • c - z ∈ K := by
  rintro ⟨c,hc⟩
  have h0 := hc (p 0) (p_base 0)
  have h3 := hc (p 3) (p_base 3)
  have h4 := hc (p 4) (p_base 4)
  have ht : c 0 = 1 := by
    have hh := h0.2
    norm_num [u,p,Pi.smul_apply,smul_eq_mul,Matrix.vecHead] at hh
    linarith
  have hl := (h_proper 0 _ h0.1).1
  have hu := (h_proper 0 _ h3.1).2
  norm_num [h,p,u,form_apply,Pi.smul_apply,smul_eq_mul,Matrix.vecHead,
    Matrix.vecTail,ht] at hl hu
  have hx : c 1 = (1/2 : ℝ) := by linarith
  have he3 := self_fiber 0 _ h3 (by
    norm_num [h,p,form_apply,Pi.smul_apply,smul_eq_mul,Matrix.vecHead,Matrix.vecTail,ht,hx])
  have he4 := self_fiber 0 _ h4 (by
    norm_num [h,p,form_apply,Pi.smul_apply,smul_eq_mul,Matrix.vecHead,Matrix.vecTail,ht,hx])
  have he := congrArg (fun z => z 2) (he3.trans he4.symm)
  norm_num [p] at he
  linarith

private theorem no_whole_ball :
    ¬ Nonempty (WholePairBallConfirmation.BallChart C u (p 0) (p 2)) := by
  rintro ⟨b⟩
  apply no_center
  refine ⟨b.param 0,?_⟩
  intro z hz
  have hz' : z ∈ b.param '' Metric.closedBall 0 1 := by
    rw [b.whole,pair_base_agrees,nonadjacent_pair_whole]
    exact hz
  obtain ⟨s,hs,rfl⟩ := hz'
  have hneg : b.param (-s) ∈ K := by
    rw [← nonadjacent_pair_whole,← pair_base_agrees,← b.whole]
    exact ⟨-s,by simpa using hs,rfl⟩
  have he : (2 : ℝ) • b.param 0 - b.param s = b.param (-s) := by
    have hn : b.param (-s) = - b.param.linear s + b.param 0 := by
      rw [congrFun b.param.decomp (-s),map_neg]
    rw [hn,congrFun b.param.decomp s]
    module
  rw [he]
  exact hneg

private theorem universal_ball_failure : ¬ WholePairBallConfirmation.wholePairBalls C u := by
  intro hB
  have hpure (i : Fin 7) : p i ∈ pure C u := by rw [pure_family]; exact ⟨i,rfl⟩
  apply no_whole_ball
  apply hB ⟨p 0,hpure 0⟩ ⟨p 2,hpure 2⟩
  intro he
  have hh := congrArg (fun q : pure C u => (q : V) 1) he
  norm_num [p] at hh

/-- A complete original effect obstruction unit: full mixed zero gluing, all
mixed exclusion faces, the actual local minimal face, all real linear extensions,
proper edge mass, and failure of positivity of the specified split. -/
theorem original_effect_obstruction :
    K = convexHull ℝ (Set.range p) ∧
    zeroGluing C u ∧
    (∀ (i : Fin 7) (z : V), z ∈ K →
      ((∃ f, confirms C u (p i) f ∧ f z = 0) ↔
        z ∈ segment ℝ (p (i+3)) (p (i+4)))) ∧
    facet = segment ℝ (p 3) (p 4) ∧
    FinitePureSimplex.wholePairBase C u (p 3) (p 4) = facet ∧
    FinitePureSimplex.wholePairBase C u (p 0) (p 1) = segment ℝ (p 0) (p 1) ∧
    (∀ z ∈ facet, 0 ≤ ruler z ∧ ruler z ≤ 1) ∧
    IsGreatest ((h 1) '' facet) (28/87 : ℝ) ∧
    (∀ f : V →ₗ[ℝ] ℝ,
      (∀ z ∈ facet, f z = ruler z) ↔ ∃ μ : ℝ, f = ruler + μ • h 0) ∧
    ¬ extensionClaim ∧
    proper C u edgeEffect ∧
    (∀ z, u (edgeProjection z) = edgeEffect z) ∧
    p 5 ∈ C ∧ edgeProjection (p 5) ∉ C ∧
    u (edgeProjection (p 5)) = (4/21 : ℝ) ∧
    comparison C u (p 0) (p 5) ≤ (4/21 : ℝ) ∧
    (4/21 : ℝ) < h 0 (p 5) ∧
    (∀ z, z = edgeProjection z + (u z - edgeEffect z) • p 4) ∧
    edgeProjection (p 0) = p 0 ∧ edgeProjection (p 1) = p 1 ∧
    edgeProjection (p 4) = 0 ∧
    {z | z ∈ K ∧ h 0 z = 0 ∧ h 1 z = 0} = {p 4} ∧
    (∀ g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ,
      ∃! f : V →ₗ[ℝ] ℝ, ∀ z ∈ K, f z = g (spatial z)) ∧
    (¬ ∃ g : (Fin 2 → ℝ) →ᵃ[ℝ] ℝ,
      (∀ z ∈ K, 0 ≤ g (spatial z) ∧ g (spatial z) ≤ 1) ∧
      ∀ z ∈ facet, g (spatial z) = ruler z) ∧
    (∀ i : Fin 7, edgeEffect (p i) = (![1,1,2/3,4/21,0,4/21,13/21] : Fin 7 → ℝ) i) ∧
    (∀ i : Fin 7, i ≠ 0 → i ≠ 1 → (196/551 : ℝ) * (1-edgeEffect (p i)) > 0) ∧
    (∀ z, edgeEffect z = (76/147 : ℝ) * h 0 z + (29/49 : ℝ) * h 1 z ∧
      edgeEffect z = u z-h 4 z) ∧
    edgeProjection (p 5) = (29/28 : ℝ) • p 0 - (71/84 : ℝ) • p 1 ∧
    pure C u = Set.range p ∧
    (affineSpan ℝ K : Set V) = {z | u z = 1} ∧
    (∀ (i : Fin 7) (z : V), z ∈ C →
      (comparison C u (p i) z = 0 ↔ ∃ f, confirms C u (p i) f ∧ f z = 0)) ∧
    Nonempty (WholePairBallConfirmation.BallChart C u (p 3) (p 4)) ∧
    IsClosed (C : Set V) ∧
    (∀ z ∈ C, z ≠ 0 → 0 < u z) ∧
    (C : ConvexCone ℝ V).Salient ∧
    Submodule.span ℝ (C : Set V) = ⊤ ∧
    FinitePureSimplex.wholePairBase C u (p 0) (p 2) = K ∧
    ¬ Nonempty (WholePairBallConfirmation.BallChart C u (p 0) (p 2)) ∧
    ¬ WholePairBallConfirmation.wholePairBalls C u ∧
    (∀ g : (affineSpan ℝ K) →ᵃ[ℝ] ℝ,
      ∃! f : V →ₗ[ℝ] ℝ, ∀ z : affineSpan ℝ K, f z = g z) ∧
    (¬ ∃ g : (affineSpan ℝ K) →ᵃ[ℝ] ℝ,
      (∀ z : affineSpan ℝ K, (z : V) ∈ K → 0 ≤ g z ∧ g z ≤ 1) ∧
      ∀ z : affineSpan ℝ K, (z : V) ∈ facet → g z = ruler z) ∧
    ruler (p 3) = 1 ∧ ruler (p 4) = 0 ∧ p 1 ∉ facet ∧ (0 : ℝ) < 4/21 := by
  exact ⟨base_hull,whole_mixed_zero_gluing,entire_exclusion_face,facet_segment,
    whole_facet_pair,edge_is_pair,ruler_local,facet_maximum,extensions_exhaustive,
    result,edge_proper,projection_mass,p_mem 5,projection_not_positive,
    by rw [projection_mass]; norm_num [edgeEffect,p,form_apply],comparison_upper,
    by norm_num [h,p,form_apply],projection_split,
    projection_on_generators.1,projection_on_generators.2.1,projection_on_generators.2.2,
    complementary_face,affine_homogeneous_bridge,no_affine_extension,
    by intro i; fin_cases i <;> norm_num [edgeEffect,p,form_apply],
    by intro i hi hj; fin_cases i <;> norm_num [edgeEffect,p,form_apply] at *,
    by intro z; constructor <;> norm_num [h,u,edgeEffect,form_apply] <;> ring,
    by rw [projection_formula]; norm_num [h,p,form_apply]; ext k; fin_cases k <;> norm_num,
    pure_family,original_affine_span,comparison_zero_iff,⟨localBallChart⟩,
    cone_closed,fun _ hz hne => unit_strict hz hne,cone_salient,cone_generating,
    nonadjacent_pair_whole,no_whole_ball,universal_ball_failure,
    actual_affine_bridge,no_actual_affine_extension,
    by norm_num [ruler,h,p,form_apply],by norm_num [ruler,h,p,form_apply],
    by rintro ⟨_,hh⟩; norm_num [h,p,form_apply] at hh,by norm_num⟩

end D5.S3.Quantum.Foundation.OriginalHeptagonObstruction
