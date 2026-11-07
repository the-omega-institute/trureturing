/- GID: D5/S3/VertexAlgebra/Analysis/OriginalEnergyBasis
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Analysis/OriginalEnergyBasis
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual completed original energy grades give the Sobolev Hilbert bases. -/

import D5.S3.VertexAlgebra.Analysis.OriginalSobolev
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
stdOrthonormalBasis acts on the ACTUAL
Hm energy norm of each completedGrade, not on the monomial coefficient metric.
The lattice/Sugawara suppliers retain Bakalov--Kac and original full-frame metric
attributions. Mathlib Hilbert-basis/completion machinery is Apache 2.0. This
module assumes no spectral theorem, generator, trace or Hamiltonian domain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators InnerProductSpace Topology VertexOperator
namespace D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open LatticeGeneratingFieldLocality LatticePositiveEnergy LatticeSugawaraCurrents
open Lattice.OriginalChargedEnergy SourceBPZ.OriginalMatterHermitian
open Model
variable (M : Model)

/-- The original completion pairing at every order, with the full within-grade form. -/
private theorem sobolev_embed_inner (k : ℕ) (u v : Carrier M.D) :
    ⟪M.embed k u, M.embed k v⟫_ℂ =
      Hm ((M.energyOperator ^ k) u) ((M.energyOperator ^ k) v) := by
  change ⟪((u : M.Finite k) : M.Sobolev k),
    ((v : M.Finite k) : M.Sobolev k)⟫_ℂ = _
  rw [UniformSpace.Completion.inner_coe (E := M.Finite k) (𝕜 := ℂ)]
  rfl

private theorem sobolev_grades_inner_zero (k : ℕ) (E F : ℤ) (hEF : E ≠ F)
    (u v : Carrier M.D) (hu : u ∈ grade M.D E) (hv : v ∈ grade M.D F) :
    ⟪M.embed k u, M.embed k v⟫_ℂ = 0 := by
  rw [sobolev_embed_inner,
    energy_power_grade M.inverse M.inverse_left M.inverse_right E u hu k,
    energy_power_grade M.inverse M.inverse_left M.inverse_right F v hv k,
    Hm_smul_left, Hm_smul_right,
    Hm_grade_orthogonal M.inverse M.inverse_left M.inverse_right E F hEF u v hu hv,
    mul_zero, mul_zero]

private theorem completed_energy_orthogonal (k : ℕ) :
    OrthogonalFamily ℂ (fun E : ℤ => M.completedGrade k E)
      (fun E => (M.completedGrade k E).subtypeₗᵢ) := by
  intro E F hEF x y
  obtain ⟨u, hu⟩ := x.property
  obtain ⟨v, hv⟩ := y.property
  change M.embed k (u : Carrier M.D) = (x : M.Sobolev k) at hu
  change M.embed k (v : Carrier M.D) = (y : M.Sobolev k) at hv
  change ⟪(x : M.Sobolev k), (y : M.Sobolev k)⟫_ℂ = 0
  rw [← hu, ← hv]
  exact sobolev_grades_inner_zero M k E F hEF u v u.property v.property

/-- Actual positivity makes every negative completed original grade zero. -/
theorem completedGrade_negative (k : ℕ) (E : ℤ) (hE : E < 0) :
    M.completedGrade k E = ⊥ := by
  apply le_antisymm ?_ bot_le
  rintro x ⟨v, rfl⟩
  have hv : (v : Carrier M.D) = 0 :=
    negative_grade_eq_zero M.positive E hE v v.property
  change M.embed k (v : Carrier M.D) = 0
  rw [hv, map_zero]

/-- Each fiber is the dimension of the actual completed Hm grade, including empty fibers. -/
def Model.energyIndex (k : ℕ) : Type :=
  Σ E : ℤ, Fin (Module.finrank ℂ (M.completedGrade k E))

def Model.energyGradeBasis (k : ℕ) (E : ℤ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (M.completedGrade k E)))
      ℂ (M.completedGrade k E) :=
  stdOrthonormalBasis ℂ (M.completedGrade k E)

def Model.energyVector (k : ℕ) (i : M.energyIndex k) : M.Sobolev k :=
  (M.completedGrade k i.1).subtype (M.energyGradeBasis k i.1 i.2)

private theorem energyVector_mem_core (k : ℕ) (i : M.energyIndex k) :
    M.energyVector k i ∈ (M.embed k).range := by
  obtain ⟨v, hv⟩ := (M.energyGradeBasis k i.1 i.2).property
  exact ⟨(v : Carrier M.D), hv⟩

private theorem original_grade_mem_energy_span (k : ℕ) (E : ℤ) (v : grade M.D E) :
    M.embed k (v : Carrier M.D) ∈
      Submodule.span ℂ (Set.range (M.energyVector k)) := by
  let x : M.completedGrade k E := ⟨M.embed k (v : Carrier M.D), ⟨v, rfl⟩⟩
  have hx : x ∈ Submodule.span ℂ (Set.range (M.energyGradeBasis k E)) := by
    rw [← OrthonormalBasis.coe_toBasis, (M.energyGradeBasis k E).toBasis.span_eq]
    exact Submodule.mem_top
  change (x : M.Sobolev k) ∈ Submodule.span ℂ (Set.range (M.energyVector k))
  refine Submodule.span_induction (p := fun (z : M.completedGrade k E) _ =>
      (z : M.Sobolev k) ∈ Submodule.span ℂ (Set.range (M.energyVector k)))
    ?_ ?_ ?_ ?_ hx
  · rintro z ⟨j, rfl⟩
    exact Submodule.subset_span ⟨⟨E, j⟩, rfl⟩
  · exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    exact Submodule.smul_mem _ c ha

private theorem original_core_eq_energy_span (k : ℕ) :
    (M.embed k).range = Submodule.span ℂ (Set.range (M.energyVector k)) := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    rw [← sum_gradeProjections M.D v, map_sum]
    exact Submodule.sum_mem _ fun E _ => original_grade_mem_energy_span M k E
      ⟨gradeProjection M.D E v, gradeProjection_mem M.D E v⟩
  · apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    exact energyVector_mem_core M k i

private theorem original_energy_span_dense (k : ℕ) :
    (⊤ : Submodule ℂ (M.Sobolev k)) ≤
      (Submodule.span ℂ (Set.range (M.energyVector k))).topologicalClosure := by
  intro x _
  change x ∈ closure ((Submodule.span ℂ (Set.range (M.energyVector k))) :
    Set (M.Sobolev k))
  rw [← original_core_eq_energy_span M k]
  exact embed_dense M k x

/-- Constructed from finite original grades and their dense actual finite span. -/
def Model.energyBasis (k : ℕ) : HilbertBasis (M.energyIndex k) ℂ (M.Sobolev k) :=
  HilbertBasis.mk
    (show Orthonormal ℂ (M.energyVector k) from
      (completed_energy_orthogonal M k).orthonormal_sigma_orthonormal
        (fun E => (M.energyGradeBasis k E).orthonormal))
    (original_energy_span_dense M k)

/-- The constructed basis really consists of the original completed-grade vectors. -/
theorem energyBasis_coe (k : ℕ) :
    (M.energyBasis k : M.energyIndex k → M.Sobolev k) = M.energyVector k := by
  funext i
  simp only [Model.energyBasis, HilbertBasis.coe_mk]

/-- The algebraic span is precisely the original finite carrier image. -/
theorem finiteCore_eq_energyBasis_span (k : ℕ) :
    (M.embed k).range =
      Submodule.span ℂ (Set.range (M.energyBasis k : M.energyIndex k → M.Sobolev k)) := by
  rw [energyBasis_coe M k]
  exact original_core_eq_energy_span M k

/-- Empty negative fibers are proved from positivity, without removing rank zero. -/
theorem energyIndex_nonnegative (k : ℕ) (i : M.energyIndex k) : 0 ≤ i.1 := by
  by_contra hn
  have hbot := completedGrade_negative M k i.1 (lt_of_not_ge hn)
  have hdim : Module.finrank ℂ (M.completedGrade k i.1) = 0 := by
    rw [hbot]
    simp
  have hi := i.2.isLt
  omega

private theorem grade_embed_norm (k : ℕ) (E : ℤ) (hE : 0 ≤ E)
    (v : Carrier M.D) (hv : v ∈ grade M.D E) :
    ‖M.embed k v‖ = ((E : ℝ) + 1) ^ k * normD v := by
  have hc : (E.toNat : ℤ) = E := Int.toNat_of_nonneg hE
  have hcR : (E.toNat : ℝ) = (E : ℝ) := by exact_mod_cast hc
  have h := sobolev_grade_norm M k E.toNat v (by rw [hc]; exact hv)
  rw [embed_norm]
  simpa only [hcR] using h

/-- Finite Pythagoras with full original within-grade quadratic forms and Sobolev weights. -/
theorem finite_grade_quadratic (k : ℕ) (F : Finset ℤ)
    (u : ℤ → Carrier M.D) (b : ℤ → ℂ)
    (hu : ∀ E ∈ F, u E ∈ grade M.D E) :
    ‖M.embed k (∑ E ∈ F, b E • u E)‖^2 =
      ∑ E ∈ F, ‖b E‖^2 * ((E : ℝ) + 1) ^ (2*k) * normD (u E)^2 := by
  classical
  rw [embed_norm, map_sum]
  rw [normD_orthogonal_sum M.positive F
    (fun E => (M.energyOperator ^ k) (b E • u E)) (by
      intro E hEF G hGF hEG
      apply Hm_grade_orthogonal M.inverse M.inverse_left M.inverse_right E G hEG
      · rw [map_smul, energy_power_grade M.inverse M.inverse_left M.inverse_right
          E (u E) (hu E hEF) k, smul_smul]
        exact (grade M.D E).smul_mem _ (hu E hEF)
      · rw [map_smul, energy_power_grade M.inverse M.inverse_left M.inverse_right
          G (u G) (hu G hGF) k, smul_smul]
        exact (grade M.D G).smul_mem _ (hu G hGF))]
  apply Finset.sum_congr rfl
  intro E hEF
  rw [← embed_norm, map_smul, norm_smul]
  by_cases hE : 0 ≤ E
  · rw [grade_embed_norm M k E hE (u E) (hu E hEF), Nat.mul_comm 2 k, pow_mul]
    ring
  · have hz : u E = 0 := negative_grade_eq_zero M.positive E (lt_of_not_ge hE)
      (u E) (hu E hEF)
    have hzero : normD (0 : Carrier M.D) = 0 := by
      have h := embed_norm M 0 (0 : Carrier M.D)
      simpa only [map_zero, norm_zero, pow_zero, Module.End.one_apply] using h.symm
    rw [hz, map_zero, norm_zero, hzero]
    ring

/-- The finite original-grade quadratic certificate, used for smoothing and tails. -/
private theorem finite_energy_quadratic (j : ℕ) (v : Carrier M.D) :
    ‖M.embed j v‖^2 = ∑ E ∈ stateEnergies M.D v,
      ((E : ℝ) + 1) ^ (2*j) * normD (gradeProjection M.D E v)^2 := by
  have h := finite_grade_quadratic M j (stateEnergies M.D v)
    (fun E => gradeProjection M.D E v) (fun _ => (1 : ℂ))
    (fun E _ => gradeProjection_mem M.D E v)
  simpa only [one_smul, sum_gradeProjections, norm_one, one_pow, one_mul] using h

/-- A scalar comparison controls the ACTUAL original norm, not a coordinate replacement. -/
theorem finite_multiplier_bound (j k : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (v : Carrier M.D) (b : ℤ → ℂ)
    (hb : ∀ E ∈ stateEnergies M.D v,
      ‖b E‖ * ((E : ℝ) + 1) ^ k ≤ B * ((E : ℝ) + 1) ^ j) :
    ‖M.embed k (∑ E ∈ stateEnergies M.D v, b E • gradeProjection M.D E v)‖ ≤
      B * ‖M.embed j v‖ := by
  have hs := finite_grade_quadratic M k (stateEnergies M.D v)
    (fun E => gradeProjection M.D E v) b
    (fun E _ => gradeProjection_mem M.D E v)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  rw [hs, mul_pow, finite_energy_quadratic, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro E hE
  have h0 : (0 : ℝ) ≤ (E : ℝ) + 1 := by
    have h := stateEnergies_nonneg M.positive v E hE
    have : (0 : ℝ) ≤ (E : ℝ) := by exact_mod_cast h
    linarith
  have hh := (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (pow_nonneg h0 k))
    (mul_nonneg hB (pow_nonneg h0 j))).mpr (hb E hE)
  have hh' := mul_le_mul_of_nonneg_right hh
    (sq_nonneg (normD (gradeProjection M.D E v)))
  simpa only [mul_pow, ← pow_mul, Nat.mul_comm 2, mul_assoc] using hh'

end D5.S3.VertexAlgebra.Analysis.OriginalSmearing
