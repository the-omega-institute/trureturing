/- GID: D5/S3/Observer/Hilbert/FiniteSynthesisSpectralCut
   generality: G
   mirror-B: D5/B/S3/Observer/Hilbert/FiniteSynthesisSpectralCut
   mirror-E: none(waiver:universal-hilbert-theorem)
   anchors: []
   utility: none
   digest: Finite synthesis admits spectral cuts on its original arbitrary Hilbert ambient space. -/

import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import D5.S3.SpectralTopology.HermitianEigenvaluePerturbation
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-! Spectral truncation of finite synthesis into an arbitrary complete Hilbert space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut

open Module
open scoped InnerProductSpace
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open D5.S3.SpectralTopology.HermitianEigenvaluePerturbation

variable {E H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restriction of the codomain, with no assumption on the ambient dimension. -/
def rangeMap (T : E →L[ℂ] H) : E →ₗ[ℂ] T.range := T.toLinearMap.rangeRestrict

/-- Singular values are computed in the finite synthesis range. -/
def singular (T : E →L[ℂ] H) : ℕ → ℝ := (rangeMap T).singularValues

/-- The right singular basis of the finite-range restriction. -/
def rightBasis (T : E →L[ℂ] H) : OrthonormalBasis (Fin (finrank ℂ E)) ℂ E :=
  rightSingularBasis (rangeMap T)

private theorem synthesis_energy (T : E →L[ℂ] H) (z : E) :
    ‖T z‖ ^ 2 = ∑ i : Fin (finrank ℂ E),
      singular T i ^ 2 * ‖(rightBasis T).repr z i‖ ^ 2 := by
  have h := re_inner_apply_self_eq_sum_eigenvalues_mul_sq
    (rangeMap T).isSymmetric_adjoint_comp_self rfl z
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq] at h
  change ‖T z‖ ^ 2 = _ at h
  simpa only [singular, rightBasis, rightSingularBasis,
    LinearMap.sq_singularValues_fin] using h

private theorem singular_top_ge_one (T : E →L[ℂ] H)
    (hT : ∃ z : E, ‖z‖ = 1 ∧ 1 ≤ ‖T z‖) :
    1 ≤ singular T 0 := by
  obtain ⟨z, hz, htz⟩ := hT
  have henergy := synthesis_energy T z
  have hbound : ‖T z‖ ^ 2 ≤ singular T 0 ^ 2 * ‖z‖ ^ 2 := by
    rw [henergy, ← sum_sq_norm_repr_eq_sq_norm (rightBasis T), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact pow_le_pow_left₀ ((rangeMap T).singularValues_nonneg i)
      ((rangeMap T).singularValues_antitone (Nat.zero_le i)) 2
  have hs := (rangeMap T).singularValues_nonneg 0
  rw [hz] at hbound
  dsimp only [singular] at *
  nlinarith

private theorem first_geometric_gap (σ : ℕ → ℝ) (n : ℕ)
    (hσ : ∀ i, 0 ≤ σ i) (hzero : σ n = 0) (hone : 1 ≤ σ 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ k < n, σ (k + 1) ≤ η * σ k ∧ η ^ k ≤ σ k := by
  have hn : 0 < n := by
    by_contra h
    have : n = 0 := by omega
    subst n
    linarith
  have hex : ∃ k, k < n ∧ σ (k + 1) ≤ η * σ k := by
    refine ⟨n - 1, by omega, ?_⟩
    rw [Nat.sub_add_cancel (by omega), hzero]
    exact mul_nonneg hη.le (hσ _)
  let k := Nat.find hex
  have hk := Nat.find_spec hex
  have hchain : ∀ i ≤ k, η ^ i ≤ σ i := by
    intro i hi
    induction i with
    | zero => simpa using hone
    | succ i ih =>
      have hik : i < k := by omega
      have hprev : η * σ i < σ (i + 1) := by
        have hh := Nat.find_min hex hik
        push Not at hh
        exact hh (by omega)
      calc
        η ^ (i + 1) = η * η ^ i := by rw [pow_succ, mul_comm]
        _ ≤ η * σ i := mul_le_mul_of_nonneg_left (ih (by omega)) hη.le
        _ ≤ σ (i + 1) := hprev.le
  exact ⟨k, hk.1, hk.2, hchain k le_rfl⟩

/-- The domain spectral subspace through the zero-based index `k`. -/
def sourceCut (T : E →L[ℂ] H) (k : Fin (finrank ℂ E)) : Submodule ℂ E :=
  Submodule.span ℂ (rightBasis T '' (Finset.Iic k : Set (Fin (finrank ℂ E))))

/-- Its image in the original ambient Hilbert space. -/
def imageCut (T : E →L[ℂ] H) (k : Fin (finrank ℂ E)) : Submodule ℂ H :=
  (sourceCut T k).map T.toLinearMap

private theorem source_cut_lower (T : E →L[ℂ] H) (k : Fin (finrank ℂ E))
    {z : E} (hz : z ∈ sourceCut T k) :
    singular T k * ‖z‖ ≤ ‖T z‖ := by
  have hsq : singular T k ^ 2 * ‖z‖ ^ 2 ≤ ‖T z‖ ^ 2 := by
    have h := le_re_inner_apply_self_of_mem_spanIndices
      (rangeMap T).isSymmetric_adjoint_comp_self rfl
      (s := (Finset.Iic k : Set (Fin (finrank ℂ E))))
      (c := singular T k ^ 2) (fun i hi => by
        rw [← LinearMap.sq_singularValues_fin]
        exact pow_le_pow_left₀ ((rangeMap T).singularValues_nonneg k)
          ((rangeMap T).singularValues_antitone (by simpa using hi)) 2)
      (show z ∈ Submodule.span ℂ
        ((rangeMap T).isSymmetric_adjoint_comp_self.eigenvectorBasis rfl ''
          (Finset.Iic k : Set (Fin (finrank ℂ E)))) from hz)
    rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, inner_self_eq_norm_sq] at h
    exact h
  apply le_of_sq_le_sq _ (norm_nonneg _)
  simpa only [singular, mul_pow] using hsq

private theorem gram_preserves_source_cut (T : E →L[ℂ] H)
    (k : Fin (finrank ℂ E)) {z : E} (hz : z ∈ sourceCut T k) :
    ((rangeMap T).adjoint.comp (rangeMap T)) z ∈ sourceCut T k := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, hi, rfl⟩ := hz
    rw [show rightBasis T i = rightSingularBasis (rangeMap T) i from rfl,
      adjointCompSelf_apply_rightSingularBasis]
    exact (sourceCut T k).smul_mem _ (Submodule.subset_span ⟨i, hi, rfl⟩)
  | zero => simp
  | add x y hx hy ihx ihy => simpa only [map_add] using (sourceCut T k).add_mem ihx ihy
  | smul c x hx ih => simpa only [map_smul] using (sourceCut T k).smul_mem c ih

instance imageCut_finiteDimensional (T : E →L[ℂ] H) (k : Fin (finrank ℂ E)) :
    FiniteDimensional ℂ (imageCut T k) := by
  letI : FiniteDimensional ℂ (sourceCut T k) := inferInstance
  dsimp [imageCut]
  exact Module.Finite.map (sourceCut T k) T.toLinearMap

private theorem image_cut_projection (T : E →L[ℂ] H)
    (k : Fin (finrank ℂ E)) (z : E) :
    (imageCut T k).starProjection (T z) = T ((sourceCut T k).starProjection z) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨_, (sourceCut T k).starProjection_apply_mem z, rfl⟩
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_sub]
    change inner ℂ ((rangeMap T) (z - (sourceCut T k).starProjection z))
      ((rangeMap T) y) = 0
    rw [← LinearMap.adjoint_inner_right]
    exact (Submodule.mem_orthogonal' _ _).mp
      ((sourceCut T k).sub_starProjection_mem_orthogonal z) _
      (gram_preserves_source_cut T k hy)

private theorem source_cut_tail (T : E →L[ℂ] H) (k : Fin (finrank ℂ E))
    {z : E} (hz : z ∈ (sourceCut T k)ᗮ) :
    ‖T z‖ ≤ singular T (k + 1) * ‖z‖ := by
  have hsq : ‖T z‖ ^ 2 ≤ singular T (k + 1) ^ 2 * ‖z‖ ^ 2 := by
    rw [synthesis_energy, ← sum_sq_norm_repr_eq_sq_norm (rightBasis T), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases hi : i ≤ k
    · have hm : rightBasis T i ∈ sourceCut T k :=
        Submodule.subset_span ⟨i, by simpa using hi, rfl⟩
      have he : (rightBasis T).repr z i = 0 := by
        rw [(rightBasis T).repr_apply_apply]
        exact hz _ hm
      rw [he]
      simp
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact pow_le_pow_left₀ ((rangeMap T).singularValues_nonneg i)
        ((rangeMap T).singularValues_antitone (by omega)) 2
  apply le_of_sq_le_sq _ (mul_nonneg ((rangeMap T).singularValues_nonneg _) (norm_nonneg _))
  simpa only [singular, mul_pow] using hsq

/-- A spectral cut is selected from the data; no spectral-gap hypothesis is required.
The finite rank belongs to a subspace of the original ambient Hilbert space. -/
theorem exists_spectral_cut (T : E →L[ℂ] H)
    (hT : ∃ z : E, ‖z‖ = 1 ∧ 1 ≤ ‖T z‖)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : Fin (finrank ℂ E),
      η ^ (finrank ℂ E - 1) ≤ singular T k ∧
      singular T (k + 1) ≤ η * singular T k ∧
      1 ≤ finrank ℂ (imageCut T k) ∧
      finrank ℂ (imageCut T k) ≤ finrank ℂ E ∧
      (∀ z ∈ sourceCut T k, singular T k * ‖z‖ ≤ ‖T z‖) ∧
      (∀ z : E, (imageCut T k).starProjection (T z) =
        T ((sourceCut T k).starProjection z)) ∧
      (∀ z : E, ‖T z - (imageCut T k).starProjection (T z)‖ ≤
        singular T (k + 1) * ‖z‖) := by
  obtain ⟨j, hj, hgap, hlow⟩ := first_geometric_gap (singular T) (finrank ℂ E)
    (rangeMap T).singularValues_nonneg
    ((rangeMap T).singularValues_of_finrank_le le_rfl)
    (singular_top_ge_one T hT) η hη
  let k : Fin (finrank ℂ E) := ⟨j, hj⟩
  have hpos : 0 < singular T k := (pow_pos hη j).trans_le hlow
  have hnonzero : T (rightBasis T k) ≠ 0 := by
    intro hz
    have hm : rightBasis T k ∈ sourceCut T k :=
      Submodule.subset_span ⟨k, by simp, rfl⟩
    have hl := source_cut_lower T k hm
    rw [(rightBasis T).orthonormal.1 k, hz, norm_zero, mul_one] at hl
    exact (not_le_of_gt hpos) hl
  refine ⟨k, ?_, hgap, ?_, ?_, fun z hz => source_cut_lower T k hz,
    image_cut_projection T k, ?_⟩
  · exact (pow_le_pow_of_le_one hη.le hη1.le (by omega : j ≤ finrank ℂ E - 1)).trans hlow
  · apply Submodule.one_le_finrank_iff.mpr
    intro hbot
    have hm : T (rightBasis T k) ∈ imageCut T k :=
      ⟨_, Submodule.subset_span ⟨k, by simp, rfl⟩, rfl⟩
    rw [hbot, Submodule.mem_bot] at hm
    exact hnonzero hm
  · exact (Submodule.finrank_map_le T.toLinearMap (sourceCut T k)).trans
      (sourceCut T k).finrank_le
  · intro z
    rw [image_cut_projection, ← map_sub]
    have hn := source_cut_tail T k ((sourceCut T k).sub_starProjection_mem_orthogonal z)
    exact hn.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Submodule.starProjection_orthogonal_val] using
        (sourceCut T k)ᗮ.norm_starProjection_apply_le z)
      ((rangeMap T).singularValues_nonneg _))

/-- Normalized left singular vectors, only on the selected positive part. -/
def cutFrame (T : E →L[ℂ] H) (k : Fin (finrank ℂ E))
    (i : ↥(Finset.Iic k)) : H :=
  ((singular T i : ℂ)⁻¹) • T (rightBasis T i)

private theorem cut_frame_orthonormal (T : E →L[ℂ] H)
    (k : Fin (finrank ℂ E)) (hk : 0 < singular T k) :
    Orthonormal ℂ (cutFrame T k) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hinner : inner ℂ (T (rightBasis T i)) (T (rightBasis T j)) =
      ((singular T j ^ 2 : ℝ) : ℂ) *
        inner ℂ (rightBasis T i) (rightBasis T j) :=
    inner_apply_rightSingularBasis (rangeMap T) i j
  have hifin : (i : Fin (finrank ℂ E)) ≤ k := Finset.mem_Iic.mp i.property
  have hiNat : (i : Fin (finrank ℂ E)).val ≤ k.val := hifin
  have hi : singular T i ≠ 0 := ne_of_gt
    (hk.trans_le ((rangeMap T).singularValues_antitone hiNat))
  have hiC : (singular T i : ℂ) ≠ 0 := by exact_mod_cast hi
  simp only [cutFrame, inner_smul_left, inner_smul_right, hinner,
    orthonormal_iff_ite.mp (rightBasis T).orthonormal]
  by_cases hij : i = j
  · subst j
    simp [hiC, pow_two]
  · have hij' : (i : Fin (finrank ℂ E)) ≠ j := fun h => hij (Subtype.ext h)
    simp [hij, hij']

/-- On the cut, the loss of invariance is bounded by the intertwining defect.
The same selected subspace works simultaneously for all operators `U` and `M`. -/
theorem exists_cut_intertwining_bound (T : E →L[ℂ] H)
    (hT : ∃ z : E, ‖z‖ = 1 ∧ 1 ≤ ‖T z‖)
    (η : ℝ) (hη : 0 < η) (hη1 : η < 1) :
    ∃ k : Fin (finrank ℂ E),
      1 ≤ finrank ℂ (imageCut T k) ∧
      finrank ℂ (imageCut T k) ≤ finrank ℂ E ∧
      Orthonormal ℂ (cutFrame T k) ∧
      ∀ (U : H →L[ℂ] H) (M : E →L[ℂ] E) (y : H), y ∈ imageCut T k →
        ‖U y - (imageCut T k).starProjection (U y)‖ ≤
          (η * ‖M‖ + (η ^ (finrank ℂ E - 1))⁻¹ * ‖U.comp T - T.comp M‖) * ‖y‖ := by
  obtain ⟨k, hlow, hgap, hr1, hrn, hsource, hproj, htail⟩ :=
    exists_spectral_cut T hT η hη hη1
  have hpow := pow_pos hη (finrank ℂ E - 1)
  have hk : 0 < singular T k := hpow.trans_le hlow
  refine ⟨k, hr1, hrn, cut_frame_orthonormal T k hk, ?_⟩
  intro U M y hy
  obtain ⟨z, hz, rfl⟩ := hy
  let P := (imageCut T k).starProjection
  let Q := (imageCut T k)ᗮ.starProjection
  let Z := U.comp T - T.comp M
  have heq : Q (U (T z)) = Q (T (M z)) + Q (Z z) := by
    change Q (U (T z)) = Q (T (M z)) + Q (U (T z) - T (M z))
    rw [map_sub]
    abel
  have htail' : ‖Q (T (M z))‖ ≤ singular T (k + 1) * ‖M z‖ := by
    simpa only [Q, Submodule.starProjection_orthogonal_val] using htail (M z)
  have hZ : ‖Q (Z z)‖ ≤ ‖Z‖ * ‖z‖ :=
    ((imageCut T k)ᗮ.norm_starProjection_apply_le _).trans (Z.le_opNorm z)
  have hbound : ‖Q (U (T z))‖ ≤ (η * singular T k * ‖M‖ + ‖Z‖) * ‖z‖ := by
    calc
      ‖Q (U (T z))‖ ≤ ‖Q (T (M z))‖ + ‖Q (Z z)‖ := by rw [heq]; exact norm_add_le _ _
      _ ≤ singular T (k + 1) * ‖M z‖ + ‖Z‖ * ‖z‖ := add_le_add htail' hZ
      _ ≤ η * singular T k * (‖M‖ * ‖z‖) + ‖Z‖ * ‖z‖ := by
        gcongr
        exact M.le_opNorm z
      _ = (η * singular T k * ‖M‖ + ‖Z‖) * ‖z‖ := by ring
  have hsource' := hsource z hz
  have hinv : (singular T k)⁻¹ ≤ (η ^ (finrank ℂ E - 1))⁻¹ := inv_anti₀ hpow hlow
  have hzbound : ‖z‖ ≤ (singular T k)⁻¹ * ‖T z‖ := by
    exact (le_inv_mul_iff₀ hk).2 hsource'
  change ‖U (T z) - P (U (T z))‖ ≤ _
  have hq : U (T z) - P (U (T z)) = Q (U (T z)) := by
    simp only [Q, P, Submodule.starProjection_orthogonal_val]
  rw [hq]
  calc
    ‖Q (U (T z))‖ ≤ (η * singular T k * ‖M‖ + ‖Z‖) *
        ((singular T k)⁻¹ * ‖T z‖) := hbound.trans (by gcongr)
    _ = (η * ‖M‖ + (singular T k)⁻¹ * ‖Z‖) * ‖T z‖ := by field_simp
    _ ≤ (η * ‖M‖ + (η ^ (finrank ℂ E - 1))⁻¹ * ‖Z‖) * ‖T z‖ := by gcongr

#print axioms exists_spectral_cut
#print axioms exists_cut_intertwining_bound

end D5.S3.Observer.Hilbert.FiniteSynthesisSpectralCut
