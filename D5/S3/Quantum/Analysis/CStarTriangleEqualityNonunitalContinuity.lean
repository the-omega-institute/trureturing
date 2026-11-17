/- GID: D5/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity
   generality: G
   mirror-B: D5/B/S3/Quantum/Analysis/CStarTriangleEqualityNonunitalContinuity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Triangle-equality rigidity for complex C-star algebras. -/

/-
admission_basis: escape-witness
escape_witness: spectral_three_points_lipschitz
Direct frozen dependencies: none.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/27516
Declarations (definition rows carry no proof-shape claim):
unitCorner: definition; consumers: inr_unitCorner, nine_corners_bound, sum_unitCorner, unitCorner_norm_le, unitCorner_orthogonal.
inr_unitCorner: proof_shape: bind-only; consumers: sum_unitCorner, unitCorner_norm_le, unitCorner_orthogonal.
unitCorner_norm_le: proof_shape: bind-only; consumers: nine_corners_bound.
sum_unitCorner: proof_shape: bind-only; consumers: nine_corners_bound.
unitCorner_orthogonal: proof_shape: bind-only; consumers: nine_corners_bound.
nine_corners_bound: proof_shape: content; consumers: spectral_three_points_lipschitz.
exists_scalar_cutoff_triple: proof_shape: content; consumers: spectral_three_points_lipschitz.
spectral_three_points_lipschitz: proof_shape: content; consumers: seminorm_nonunital_lipschitz.
finite_spectrum_support_projection: proof_shape: content; consumers: exists_orthogonal_projection_of_finite_spectra.
exists_nonzero_selfadjoint_orthogonal_to_projection: proof_shape: content; consumers: exists_orthogonal_projection_of_finite_spectra.
exists_orthogonal_projection_of_finite_spectra: proof_shape: content; consumers: exists_three_orthogonal_projections_of_finite_spectra.
exists_three_orthogonal_projections_of_finite_spectra: proof_shape: content; consumers: nonunital_exists_three_real_spectral_values.
real_quasispectrum_of_nonzero_eigenvector: proof_shape: bind-only; consumers: three_real_spectral_values_of_orthogonal_projections.
three_real_spectral_values_of_orthogonal_projections: proof_shape: content; consumers: nonunital_exists_three_real_spectral_values.
nonunital_exists_three_real_spectral_values: proof_shape: content; consumers: seminorm_nonunital_lipschitz.
seminorm_nonunital_lipschitz: proof_shape: content; consumers: D5.S3.Quantum.Analysis.CStarTriangleEqualityPreservers.seminorm_rigidity.
-/

import D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane
import Mathlib.Analysis.CStarAlgebra.Unitization
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing

namespace D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity

section

open scoped BigOperators
variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- A multiplier corner, retained in the original algebra. -/
private def unitCorner (u v : Unitization ℂ A) (a : A) : A :=
  (u * (a : Unitization ℂ A) * v).snd

private theorem inr_unitCorner (u v : Unitization ℂ A) (a : A) :
    ((unitCorner u v a : A) : Unitization ℂ A) = u * (a : Unitization ℂ A) * v := by
  apply Unitization.ext <;> simp [unitCorner]

private theorem unitCorner_norm_le (u v : Unitization ℂ A) (a : A)
    (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) : ‖unitCorner u v a‖ ≤ ‖a‖ := by
  rw [← Unitization.norm_inr (𝕜 := ℂ), inr_unitCorner (A := A) u v a]
  calc
    ‖u * (a : Unitization ℂ A) * v‖ ≤ ‖u * (a : Unitization ℂ A)‖ * ‖v‖ := norm_mul_le _ _
    _ ≤ (‖u‖ * ‖a‖) * ‖v‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg v)
      simpa only [Unitization.norm_inr] using norm_mul_le u (a : Unitization ℂ A)
    _ ≤ (1 * ‖a‖) * 1 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right hu (norm_nonneg a)) hv
        (norm_nonneg v) (by positivity)
    _ = ‖a‖ := by ring

private theorem sum_unitCorner {n : ℕ} (e : Fin n → Unitization ℂ A)
    (he : ∑ i, e i = 1) (a : A) : ∑ i, ∑ j, unitCorner (e i) (e j) a = a := by
  apply Unitization.inr_injective (R := ℂ)
  have hmap (f : Fin n → A) :
      ((∑ i, f i : A) : Unitization ℂ A) = ∑ i, (f i : Unitization ℂ A) :=
    map_sum (Unitization.inrHom ℂ ℂ A) f Finset.univ
  simp only [hmap, inr_unitCorner (A := A), ← Finset.mul_sum, ← Finset.sum_mul, he, one_mul, mul_one]

private theorem unitCorner_orthogonal (u v : Unitization ℂ A) (a g : A)
    (hu : IsSelfAdjoint u) (hv : IsSelfAdjoint v) (hg : IsSelfAdjoint g)
    (hug : u * (g : Unitization ℂ A) = 0) (hvg : v * (g : Unitization ℂ A) = 0) :
    star (unitCorner u v a) * g = 0 ∧ unitCorner u v a * star g = 0 := by
  constructor
  · apply Unitization.inr_injective (R := ℂ)
    simp only [Unitization.inr_mul, Unitization.inr_star, Unitization.inr_zero,
      inr_unitCorner (A := A), star_mul, hu.star_eq, hv.star_eq]
    simp only [mul_assoc, hug, mul_zero]
  · apply Unitization.inr_injective (R := ℂ)
    simp only [Unitization.inr_mul, Unitization.inr_star, Unitization.inr_zero,
      inr_unitCorner (A := A), hg.star_eq]
    simp only [mul_assoc, hvg, mul_zero]

/-- Three synchronized bumps and a contractive partition in the unitization give continuity. -/
private theorem nine_corners_bound (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b)
    (g : Fin 3 → A) (hg : ∀ k, ‖g k‖ = 1) (hgsa : ∀ k, IsSelfAdjoint (g k))
    (hgg : ∀ i j, i ≠ j → g i * g j = 0)
    (e : Fin 3 → Unitization ℂ A) (he : ∑ i, e i = 1)
    (hen : ∀ i, ‖e i‖ ≤ 1) (hesa : ∀ i, IsSelfAdjoint (e i))
    (heg : ∀ i k, i ≠ k → e i * (g k : Unitization ℂ A) = 0) (a : A) :
    p a ≤ 9 * p (g 0) * ‖a‖ := by
  classical
  have hscale (k : Fin 3) : p (g k) = p (g 0) := by
    by_cases hk : k = 0
    · rw [hk]
    · apply D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.seminorm_orthogonal_axes p hp (g k) (g 0) (hg k) (hg 0)
      · simpa only [(hgsa k).star_eq] using hgg k 0 hk
      · simpa only [(hgsa 0).star_eq] using hgg k 0 hk
  have hc (i j : Fin 3) : p (unitCorner (e i) (e j) a) ≤ p (g 0) * ‖a‖ := by
    obtain ⟨k, hki, hkj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by decide : 2 < 3)
    have ho := unitCorner_orthogonal (e i) (e j) a (g k) (hesa i) (hesa j) (hgsa k)
      (heg i k hki.symm) (heg j k hkj.symm)
    rw [D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.seminorm_orthogonal_unit_scale p hp _ _ (hg k) ho.1 ho.2, hscale k]
    exact mul_le_mul_of_nonneg_left (unitCorner_norm_le _ _ a (hen i) (hen j))
      (apply_nonneg p _)
  have hsum (f : Fin 3 → A) : p (∑ i, f i) ≤ ∑ i, p (f i) := by
    letI : SeminormedAddCommGroup A := p.toAddGroupSeminorm.toSeminormedAddCommGroup
    exact norm_sum_le Finset.univ f
  calc
    p a = p (∑ i, ∑ j, unitCorner (e i) (e j) a) := by rw [sum_unitCorner e he]
    _ ≤ ∑ i, p (∑ j, unitCorner (e i) (e j) a) := hsum _
    _ ≤ ∑ i, ∑ j, p (unitCorner (e i) (e j) a) :=
      Finset.sum_le_sum fun i _ => hsum _
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, p (g 0) * ‖a‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hc i j
    _ = 9 * p (g 0) * ‖a‖ := by simp; ring

end

section
end

section

open Function Set
open scoped BigOperators

/-- Three distinct nonzero real points admit disjoint bumps and a contractive partition. -/
private theorem exists_scalar_cutoff_triple (x : Fin 3 → ℝ) (hinj : Injective x)
    (hx0 : ∀ i, x i ≠ 0) :
    ∃ G E : Fin 3 → C(ℝ, ℝ),
      (∀ i, G i 0 = 0) ∧ (∀ i, G i (x i) = 1) ∧
      (∀ i t, G i t ∈ Icc (0 : ℝ) 1) ∧
      (∀ i j, i ≠ j → ∀ t, G i t * G j t = 0) ∧
      (∀ t, ∑ i, E i t = 1) ∧ (∀ i t, E i t ∈ Icc (0 : ℝ) 1) ∧
      (∀ i k, i ≠ k → ∀ t, E i t * G k t = 0) := by
  classical
  let S : Set ℝ := insert 0 (range x)
  have hS : S.Finite := (finite_range x).insert 0
  obtain ⟨U, hU, hUD⟩ := hS.t2_separation
  have hxS (i : Fin 3) : x i ∈ S := mem_insert_of_mem 0 (mem_range_self i)
  have hUDx (i j : Fin 3) (hij : i ≠ j) : Disjoint (U (x i)) (U (x j)) :=
    hUD (hxS i) (hxS j) (fun he => hij (hinj he))
  have hzeroU (i : Fin 3) : (0 : ℝ) ∉ U (x i) := by
    intro hz
    have hdis := hUD (by simp [S]) (hxS i) (Ne.symm (hx0 i))
    exact Set.disjoint_left.mp hdis (hU 0).1 hz
  have hG (i : Fin 3) := exists_continuousMap_one_of_isCompact_subset_isOpen
    (K := {x i}) isCompact_singleton (hU (x i)).2
    (singleton_subset_iff.mpr (hU (x i)).1)
  choose G hGp hGc hGs hGb using hG
  have hF (i : Fin 3) := exists_continuousMap_one_of_isCompact_subset_isOpen
    (hGc i) (hU (x i)).2 (hGs i)
  choose F hFp hFc hFs hFb using hF
  have hG0 (i : Fin 3) : G i 0 = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hzeroU i (hGs i h))
  have hGpeak (i : Fin 3) : G i (x i) = 1 := hGp i (by simp)
  have hFF (i j : Fin 3) (hij : i ≠ j) (t : ℝ) : F i t * F j t = 0 := by
    by_cases hi : F i t = 0
    · rw [hi, zero_mul]
    · have ht : t ∈ U (x i) := hFs i (subset_tsupport _ hi)
      have hj : t ∉ tsupport (F j) := fun hj =>
        Set.disjoint_left.mp (hUDx i j hij) ht (hFs j hj)
      rw [image_eq_zero_of_notMem_tsupport hj, mul_zero]
  have hGG (i j : Fin 3) (hij : i ≠ j) (t : ℝ) : G i t * G j t = 0 := by
    by_cases hi : G i t = 0
    · rw [hi, zero_mul]
    · have ht : t ∈ U (x i) := hGs i (subset_tsupport _ hi)
      have hj : t ∉ tsupport (G j) := fun hj =>
        Set.disjoint_left.mp (hUDx i j hij) ht (hGs j hj)
      rw [image_eq_zero_of_notMem_tsupport hj, mul_zero]
  have hFG (i j : Fin 3) (hij : i ≠ j) (t : ℝ) : F i t * G j t = 0 := by
    by_cases hi : F i t = 0
    · rw [hi, zero_mul]
    · have ht : t ∈ U (x i) := hFs i (subset_tsupport _ hi)
      have hj : t ∉ tsupport (G j) := fun hj =>
        Set.disjoint_left.mp (hUDx i j hij) ht (hGs j hj)
      rw [image_eq_zero_of_notMem_tsupport hj, mul_zero]
  have hFGself (i : Fin 3) (t : ℝ) : F i t * G i t = G i t := by
    by_cases hi : G i t = 0
    · rw [hi, mul_zero]
    · rw [hFp i (subset_tsupport _ hi), Pi.one_apply, one_mul]
  have hsum (t : ℝ) : (∑ i, F i t) ∈ Icc (0 : ℝ) 1 := by
    have h0 := hFb 0 t
    have h1 := hFb 1 t
    have h2 := hFb 2 t
    have h01 := hFF 0 1 (by decide) t
    have h02 := hFF 0 2 (by decide) t
    have h12 := hFF 1 2 (by decide) t
    simp only [Fin.sum_univ_three]
    constructor
    · linarith [h0.1, h1.1, h2.1]
    · by_cases hz0 : F 0 t = 0
      · rw [hz0, zero_add]
        by_cases hz1 : F 1 t = 0
        · simpa only [hz1, zero_add] using h2.2
        · have hz2 : F 2 t = 0 := (mul_eq_zero.mp h12).resolve_left hz1
          simpa only [hz2, add_zero] using h1.2
      · have hz1 : F 1 t = 0 := (mul_eq_zero.mp h01).resolve_left hz0
        have hz2 : F 2 t = 0 := (mul_eq_zero.mp h02).resolve_left hz0
        simpa only [hz1, hz2, add_zero] using h0.2
  let E : Fin 3 → C(ℝ, ℝ) := fun i =>
    ⟨fun t => F i t + (1 - ∑ j, F j t) / 3, by fun_prop⟩
  refine ⟨G, E, hG0, hGpeak, hGb, hGG, ?_, ?_, ?_⟩
  · intro t
    simp only [E, ContinuousMap.coe_mk, Fin.sum_univ_three]
    ring
  · intro i t
    have hi := hFb i t
    have hs := hsum t
    have hle : F i t ≤ ∑ j, F j t := Finset.single_le_sum
      (fun j _ => (hFb j t).1) (Finset.mem_univ i)
    change 0 ≤ F i t + (1 - ∑ j, F j t) / 3 ∧
      F i t + (1 - ∑ j, F j t) / 3 ≤ 1
    constructor <;> linarith [hi.1, hi.2, hs.2]
  · intro i k hik t
    change (F i t + (1 - ∑ j, F j t) / 3) * G k t = 0
    rw [add_mul, hFG i k hik t, zero_add, div_mul_eq_mul_div]
    have heq : (∑ j, F j t) * G k t = G k t := by
      calc
        (∑ j, F j t) * G k t = ∑ j, F j t * G k t := by rw [Finset.sum_mul]
        _ = F k t * G k t := Finset.sum_eq_single k
          (fun j _ hjk => hFG j k hjk t)
          (fun hk => (hk (Finset.mem_univ k)).elim)
        _ = G k t := hFGself k t
    rw [sub_mul, one_mul, heq, sub_self, zero_div]

end

section

open scoped BigOperators

/-- Three distinct nonzero real spectral values imply automatic seminorm continuity. -/
private theorem spectral_three_points_lipschitz {A : Type*} [NonUnitalCStarAlgebra A]
    (d : A) (hd : IsSelfAdjoint d) (x : Fin 3 → ℝ)
    (hx : ∀ i, x i ∈ quasispectrum ℝ d)
    (hinj : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b) :
    ∃ C : NNReal, LipschitzWith C p := by
  classical
  obtain ⟨G, E, hG0, hGpeak, hGb, hGG, hE1, hEb, hEG⟩ :=
    exists_scalar_cutoff_triple x hinj hx0
  let g : Fin 3 → A := fun i => cfcₙ (G i) d
  let e : Fin 3 → Unitization ℂ A := fun i => cfc (E i) (d : Unitization ℂ A)
  have hd' : IsSelfAdjoint (d : Unitization ℂ A) := Unitization.isSelfAdjoint_inr.mpr hd
  have hgN (i : Fin 3) : ‖g i‖ = 1 := by
    apply le_antisymm
    · apply norm_cfcₙ_le
      intro t ht
      rw [Real.norm_eq_abs, abs_of_nonneg (hGb i t).1]
      exact (hGb i t).2
    · have ht := norm_apply_le_norm_cfcₙ (G i) d (hx i)
        (G i).continuous.continuousOn (hG0 i) hd
      simpa only [hGpeak i, norm_one, g] using ht
  have hgsa (i : Fin 3) : IsSelfAdjoint (g i) := cfcₙ_predicate (G i) d
  have hgg (i j : Fin 3) (hij : i ≠ j) : g i * g j = 0 := by
    change cfcₙ (G i) d * cfcₙ (G j) d = 0
    rw [← cfcₙ_mul (G i) (G j) d (G i).continuous.continuousOn (hG0 i)
      (G j).continuous.continuousOn (hG0 j)]
    have heq : (fun t => G i t * G j t) = (fun _ : ℝ => 0) := funext (hGG i j hij)
    rw [heq, cfcₙ_const_zero]
  have he : ∑ i, e i = 1 := by
    change (∑ i, cfc (E i) (d : Unitization ℂ A)) = 1
    rw [← cfc_sum_univ (fun i => (E i : ℝ → ℝ)) (d : Unitization ℂ A)
      (fun i => (E i).continuous.continuousOn)]
    have heq : (∑ i, (E i : ℝ → ℝ)) = (fun _ : ℝ => 1) := by
      exact Function.ext_iff_mulSupport_union.mpr fun x a => hE1 x
    rw [heq, cfc_const_one ℝ (d : Unitization ℂ A) (ha := hd')]
  have hen (i : Fin 3) : ‖e i‖ ≤ 1 := by
    apply norm_cfc_le (by norm_num : (0 : ℝ) ≤ 1)
    intro t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (hEb i t).1]
    exact (hEb i t).2
  have hesa (i : Fin 3) : IsSelfAdjoint (e i) := cfc_predicate (E i) (d : Unitization ℂ A)
  have heg (i k : Fin 3) (hik : i ≠ k) : e i * (g k : Unitization ℂ A) = 0 := by
    change cfc (E i) (d : Unitization ℂ A) *
      ((cfcₙ (G k) d : A) : Unitization ℂ A) = 0
    rw [Unitization.real_cfcₙ_eq_cfc_inr d (G k) (hG0 k),
      ← cfc_mul (E i) (G k) (d : Unitization ℂ A)
        (E i).continuous.continuousOn (G k).continuous.continuousOn]
    have heq : (fun t => E i t * G k t) = (fun _ : ℝ => 0) := funext (hEG i k hik)
    rw [heq, cfc_const_zero]
  have hbound (a : A) : p a ≤ 9 * p (g 0) * ‖a‖ :=
    nine_corners_bound p hp g hgN hgsa hgg e he hen hesa heg a
  refine ⟨⟨9 * p (g 0), mul_nonneg (by norm_num) (apply_nonneg p _)⟩, ?_⟩
  apply lipschitzWith_iff_dist_le_mul.mpr
  intro a b
  rw [dist_eq_norm, dist_eq_norm]
  exact (p.norm_sub_map_le_sub a b).trans (hbound (a - b))

end

section

open scoped BigOperators

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Every finite-spectrum selfadjoint element has its support projection inside the algebra. -/
private theorem finite_spectrum_support_projection (d : A) (hd : IsSelfAdjoint d)
    (hfin : (quasispectrum ℝ d).Finite) :
    ∃ q : A, IsSelfAdjoint q ∧ q * q = q ∧ q * d = d ∧ d * q = d ∧
      ∃ v : A, q = d * v := by
  classical
  let f : ℝ → ℝ := fun t => if t = 0 then 0 else 1
  let g : ℝ → ℝ := fun t => if t = 0 then 0 else t⁻¹
  have hf : ContinuousOn f (quasispectrum ℝ d) := hfin.continuousOn f
  have hg : ContinuousOn g (quasispectrum ℝ d) := hfin.continuousOn g
  have hf0 : f 0 = 0 := by exact ite_eq_left rfl
  have hg0 : g 0 = 0 := by exact ite_eq_left rfl
  let q : A := cfcₙ f d
  have hq : IsSelfAdjoint q := cfcₙ_predicate f d
  have hsq : q * q = q := by
    change cfcₙ f d * cfcₙ f d = cfcₙ f d
    rw [← cfcₙ_mul f f d hf hf0 hf hf0]
    apply cfcₙ_congr
    intro t ht
    dsimp [f]
    split_ifs <;> norm_num
  have hqd : q * d = d := by
    calc
      q * d = cfcₙ f d * cfcₙ (id : ℝ → ℝ) d := by rw [cfcₙ_id ℝ d (ha := hd)]
      _ = cfcₙ (fun t => f t * t) d :=
        (cfcₙ_mul f id d hf hf0 continuous_id.continuousOn rfl).symm
      _ = cfcₙ (id : ℝ → ℝ) d := by
        apply cfcₙ_congr
        intro t ht
        by_cases ht0 : t = 0 <;> simp [f, ht0]
      _ = d := cfcₙ_id ℝ d (ha := hd)
  have hdq : d * q = d := by
    have h := congrArg star hqd
    simpa only [star_mul, hq.star_eq, hd.star_eq] using h
  refine ⟨q, hq, hsq, hqd, hdq, cfcₙ g d, ?_⟩
  have hgf : (fun t => t * g t) = f := by
    funext t
    by_cases ht : t = 0 <;> simp [f, g, ht]
  change cfcₙ f d = d * cfcₙ g d
  rw [← hgf]
  calc
    cfcₙ (fun t => t * g t) d = cfcₙ (id : ℝ → ℝ) d * cfcₙ g d :=
      cfcₙ_mul id g d continuous_id.continuousOn rfl hg hg0
    _ = d * cfcₙ g d := by rw [cfcₙ_id ℝ d (ha := hd)]

/-- A projection cannot exhaust a genuinely nonunital C*-algebra. -/
private theorem exists_nonzero_selfadjoint_orthogonal_to_projection
    (hnu : ¬ ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a)
    (q : A) (hq : IsSelfAdjoint q) (hqq : q * q = q) :
    ∃ d : A, IsSelfAdjoint d ∧ d ≠ 0 ∧ q * d = 0 ∧ d * q = 0 := by
  classical
  have hnot : ¬ ∀ a : A, q * a = a := by
    intro h
    apply hnu
    refine ⟨q, fun a => ⟨h a, ?_⟩⟩
    have hs := congrArg star (h (star a))
    simpa only [star_mul, star_star, hq.star_eq] using hs
  obtain ⟨a, ha⟩ := not_forall.mp hnot
  let x : A := a - q * a
  have hx : x ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hqx : q * x = 0 := by
    change q * (a - q * a) = 0
    rw [mul_sub, ← mul_assoc, hqq, sub_self]
  let d : A := x * star x
  have hd : IsSelfAdjoint d := .mul_star_self x
  have hd0 : d ≠ 0 := by
    intro hz
    have hn := congrArg norm hz
    rw [CStarRing.norm_self_mul_star, norm_zero] at hn
    have hxn := norm_pos_iff.mpr hx
    nlinarith
  have hqd : q * d = 0 := by
    change q * (x * star x) = 0
    rw [← mul_assoc, hqx, zero_mul]
  have hdq : d * q = 0 := by
    have hs := congrArg star hqd
    simpa only [star_mul, hq.star_eq, hd.star_eq, star_zero] using hs
  exact ⟨d, hd, hd0, hqd, hdq⟩

/-- Finite real spectra provide a new orthogonal nonzero projection. -/
private theorem exists_orthogonal_projection_of_finite_spectra
    (hnu : ¬ ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a)
    (hfin : ∀ d : A, IsSelfAdjoint d → (quasispectrum ℝ d).Finite)
    (q : A) (hq : IsSelfAdjoint q) (hqq : q * q = q) :
    ∃ r : A, IsSelfAdjoint r ∧ r * r = r ∧ r ≠ 0 ∧ q * r = 0 ∧ r * q = 0 := by
  obtain ⟨d, hd, hd0, hqd, hdq⟩ :=
    exists_nonzero_selfadjoint_orthogonal_to_projection hnu q hq hqq
  obtain ⟨r, hr, hrr, hrd, hdr, v, hrv⟩ :=
    finite_spectrum_support_projection d hd (hfin d hd)
  have hr0 : r ≠ 0 := by
    intro hz
    apply hd0
    simpa only [hz, zero_mul] using hrd.symm
  have hqr : q * r = 0 := by rw [hrv, ← mul_assoc, hqd, zero_mul]
  have hrq : r * q = 0 := by
    have hs := congrArg star hqr
    simpa only [star_mul, hq.star_eq, hr.star_eq, star_zero] using hs
  exact ⟨r, hr, hrr, hr0, hqr, hrq⟩

end

section

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- Three nonzero orthogonal projections can be found if all selfadjoint spectra are finite. -/
private theorem exists_three_orthogonal_projections_of_finite_spectra
    (hnu : ¬ ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a)
    (hfin : ∀ d : A, IsSelfAdjoint d → (quasispectrum ℝ d).Finite) :
    ∃ q : Fin 3 → A, (∀ i, IsSelfAdjoint (q i)) ∧ (∀ i, q i * q i = q i) ∧
      (∀ i, q i ≠ 0) ∧ ∀ i j, i ≠ j → q i * q j = 0 := by
  classical
  obtain ⟨q₁, hsa₁, h₁₁, h₁0, _, _⟩ :=
    exists_orthogonal_projection_of_finite_spectra hnu hfin 0 (by simp [IsSelfAdjoint]) (by simp)
  obtain ⟨q₂, hsa₂, h₂₂, h₂0, h₁₂, h₂₁⟩ :=
    exists_orthogonal_projection_of_finite_spectra hnu hfin q₁ hsa₁ h₁₁
  have hs : (q₁ + q₂) * (q₁ + q₂) = q₁ + q₂ := by
    simp only [add_mul, mul_add, h₁₁, h₂₂, h₁₂, h₂₁, add_zero, zero_add]
  obtain ⟨q₃, hsa₃, h₃₃, h₃0, hs₃, h₃s⟩ :=
    exists_orthogonal_projection_of_finite_spectra hnu hfin (q₁ + q₂) (hsa₁.add hsa₂) hs
  have h₁₃ : q₁ * q₃ = 0 := by
    calc
      q₁ * q₃ = (q₁ * (q₁ + q₂)) * q₃ := by rw [mul_add, h₁₁, h₁₂, add_zero]
      _ = q₁ * ((q₁ + q₂) * q₃) := mul_assoc _ _ _
      _ = 0 := by rw [hs₃, mul_zero]
  have h₂₃ : q₂ * q₃ = 0 := by
    calc
      q₂ * q₃ = (q₂ * (q₁ + q₂)) * q₃ := by rw [mul_add, h₂₁, h₂₂, zero_add]
      _ = q₂ * ((q₁ + q₂) * q₃) := mul_assoc _ _ _
      _ = 0 := by rw [hs₃, mul_zero]
  have h₃₁ : q₃ * q₁ = 0 := by
    simpa only [star_mul, hsa₁.star_eq, hsa₃.star_eq, star_zero] using congrArg star h₁₃
  have h₃₂ : q₃ * q₂ = 0 := by
    simpa only [star_mul, hsa₂.star_eq, hsa₃.star_eq, star_zero] using congrArg star h₂₃
  refine ⟨![q₁, q₂, q₃], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> simp_all
  · intro i
    fin_cases i <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- A nonzero algebraic eigenvector detects a real quasispectral value. -/
private theorem real_quasispectrum_of_nonzero_eigenvector (d q : A) (hq : q ≠ 0)
    (r : ℝ) (heig : d * q = r • q) : r ∈ quasispectrum ℝ d := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ ℂ d, spectrum.mem_iff]
  intro hu
  have hz : (algebraMap ℝ (Unitization ℂ A) r - (d : Unitization ℂ A)) *
      (q : Unitization ℂ A) = 0 := by
    rw [sub_mul, Algebra.algebraMap_eq_smul_one, smul_one_mul,
      ← Unitization.inr_mul, heig, Unitization.inr_smul, sub_self]
  have hq' : (q : Unitization ℂ A) = 0 :=
    hu.mul_left_cancel (by simpa only [mul_zero] using hz)
  apply hq
  exact Unitization.inr_injective (R := ℂ) (by simpa using hq')

/-- Orthogonal projections give three distinct nonzero real spectral values. -/
private theorem three_real_spectral_values_of_orthogonal_projections
    (q : Fin 3 → A) (hsa : ∀ i, IsSelfAdjoint (q i))
    (hqq : ∀ i, q i * q i = q i) (hq0 : ∀ i, q i ≠ 0)
    (horth : ∀ i j, i ≠ j → q i * q j = 0) :
    ∃ d : A, IsSelfAdjoint d ∧ ∃ x : Fin 3 → ℝ,
      (∀ i, x i ∈ quasispectrum ℝ d) ∧ Function.Injective x ∧ ∀ i, x i ≠ 0 := by
  classical
  let x : Fin 3 → ℝ := fun i => (i.val : ℝ) + 1
  let d : A := ∑ i, x i • q i
  have hd : IsSelfAdjoint d := by
    change star d = d
    simp only [d, star_sum, star_smul, star_trivial]
    exact Finset.sum_congr rfl fun i _ => congrArg (x i • ·) (hsa i).star_eq
  have heig (j : Fin 3) : d * q j = x j • q j := by
    change (∑ i, x i • q i) * q j = x j • q j
    rw [Finset.sum_mul, Finset.sum_eq_single j]
    · rw [smul_mul_assoc, hqq]
    · intro i hi hij
      rw [smul_mul_assoc, horth i j hij, smul_zero]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  refine ⟨d, hd, x, fun i => real_quasispectrum_of_nonzero_eigenvector d (q i) (hq0 i) (x i) (heig i), ?_, ?_⟩
  · intro i j hij
    apply Fin.ext
    have he : (i.val : ℝ) = (j.val : ℝ) := add_right_cancel hij
    exact_mod_cast he
  · intro i
    change (i.val : ℝ) + 1 ≠ 0
    positivity

/-- Every genuinely nonunital C*-algebra has a selfadjoint element with three nonzero spectral values. -/
private theorem nonunital_exists_three_real_spectral_values
    (hnu : ¬ ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a) :
    ∃ d : A, IsSelfAdjoint d ∧ ∃ x : Fin 3 → ℝ,
      (∀ i, x i ∈ quasispectrum ℝ d) ∧ Function.Injective x ∧ ∀ i, x i ≠ 0 := by
  classical
  by_cases hfin : ∀ d : A, IsSelfAdjoint d → (quasispectrum ℝ d).Finite
  · obtain ⟨q, hsa, hqq, hq0, horth⟩ :=
      exists_three_orthogonal_projections_of_finite_spectra hnu hfin
    exact three_real_spectral_values_of_orthogonal_projections q hsa hqq hq0 horth
  · simp only [not_forall] at hfin
    obtain ⟨d, hd, hinf⟩ := hfin
    let S : Set ℝ := quasispectrum ℝ d \ {0}
    have hS : S.Infinite := Set.Infinite.diff hinf (Set.finite_singleton 0)
    let f : ℕ ↪ S := Set.Infinite.natEmbedding S hS
    let x : Fin 3 → ℝ := fun i => (f i.val).val
    refine ⟨d, hd, x, ?_, ?_, ?_⟩
    · intro i
      exact (f i.val).property.1
    · intro i j hij
      exact Fin.ext (f.injective (Subtype.ext hij))
    · intro i
      have hz := (f i.val).property.2
      simpa only [Set.mem_singleton_iff] using hz

end

section

/-- A finite complex seminorm additive on TEA pairs is continuous on a genuinely nonunital C*-algebra. -/
theorem seminorm_nonunital_lipschitz {A : Type*} [NonUnitalCStarAlgebra A]
    (hnu : ¬ ∃ q : A, ∀ a : A, q * a = a ∧ a * q = a)
    (p : Seminorm ℂ A)
    (hp : ∀ a b : A, D5.S3.Quantum.Analysis.CStarTriangleEqualityPlane.TEAPair a b → p (a + b) = p a + p b) :
    ∃ C : NNReal, LipschitzWith C p := by
  obtain ⟨d, hd, x, hx, hinj, hx0⟩ := nonunital_exists_three_real_spectral_values hnu
  exact spectral_three_points_lipschitz d hd x hx hinj hx0 p hp

end

end D5.S3.Quantum.Analysis.CStarTriangleEqualityNonunitalContinuity
