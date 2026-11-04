/- GID: D5/S3/Quantum/Entanglement/Rectangular/FiniteSectorRectangularAttainment
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Rectangular/FiniteSectorRectangularAttainment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Attaining orthonormal pairs for finite rectangular Ky Fan sums. -/

/- Extracted with its proof unchanged from sector_pair in FiniteSectorPassivePair.
The existing finite-sector attribution and license notices apply:
https://github.com/AIQ-Kitware/aiq-dkps-formalization,
revision 64e234954217f3ca907ac980c8cbde2900109a66.
Copyright (c) 2026 Kitware, Inc. Released under the Apache 2.0 license.
Authors: Jon Crall, Claude Fable 5.
The full license and notice chain are retained in
docs/reports/licenses/finite-sector-channel-third-party.md.
-/
import D5.S3.Quantum.Entanglement.FiniteSectorRectangularVariational

noncomputable section
universe u
namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
open Module (finrank)
open scoped InnerProductSpace

theorem exists_orthonormal_re_sum_inner_map_eq_ky_fan_sum {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) {k : ℕ} (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) = kyFanSum k A := by
  classical
  set hS := A.isSymmetric_adjoint_comp_self with hSdef
  set b := hS.eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) with hbdef
  set v : Fin k → E := fun i => b (Fin.castLE hkE i) with hvdef
  have hv : Orthonormal 𝕜 v := b.orthonormal.comp _ (Fin.castLE_injective hkE)
  -- the Gram relation of the singular directions
  have hgram : ∀ i j : Fin k, ⟪A (v i), A (v j)⟫_𝕜
      = ((A.singularValues (i : ℕ) ^ 2 : ℝ) : 𝕜) * (if i = j then (1 : 𝕜) else 0) := by
    intro i j
    have h1 : ⟪A (v i), A (v j)⟫_𝕜 = ⟪(A.adjoint ∘ₗ A) (v i), v j⟫_𝕜 := by
      rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
    have h2 : (A.adjoint ∘ₗ A) (v i)
        = ((hS.eigenvalues rfl (Fin.castLE hkE i) : ℝ) : 𝕜) • v i :=
      hS.apply_eigenvectorBasis (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    have h3 : (A.singularValues (i : ℕ) ^ 2 : ℝ)
        = hS.eigenvalues rfl (Fin.castLE hkE i) :=
      A.sq_singularValues_fin (rfl : finrank 𝕜 E = finrank 𝕜 E) (Fin.castLE hkE i)
    rw [h1, h2, inner_smul_left, RCLike.conj_ofReal, h3]
    rw [orthonormal_iff_ite.mp hv i j]
  -- norms of the images
  have hnorm : ∀ i : Fin k, ‖A (v i)‖ = A.singularValues (i : ℕ) := by
    intro i
    have h := hgram i i
    rw [if_pos rfl, mul_one] at h
    have h2 : ‖A (v i)‖ ^ 2 = A.singularValues (i : ℕ) ^ 2 := by
      have := congrArg (RCLike.re (K := 𝕜)) h
      rw [inner_self_eq_norm_sq_to_K] at this
      simpa using this
    have := A.singularValues_nonneg (i : ℕ)
    nlinarith [norm_nonneg (A (v i))]
  -- the codomain family, defined on the indices with a nonzero singular value
  set w : Fin (finrank 𝕜 F) → F := fun j =>
    if h : (j : ℕ) < k then ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, h⟩) else 0
    with hwdef
  set s : Set (Fin (finrank 𝕜 F)) :=
    {j | (j : ℕ) < k ∧ A.singularValues (j : ℕ) ≠ 0} with hsdef
  have hws : Orthonormal 𝕜 (s.domRestrict w) := by
    rw [orthonormal_iff_ite]
    rintro ⟨j, hj⟩ ⟨j', hj'⟩
    obtain ⟨hjk, hjne⟩ := hj
    obtain ⟨hj'k, hj'ne⟩ := hj'
    have hwj : w j = ((A.singularValues (j : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j, hjk⟩) := by
      simp [hwdef, hjk]
    have hwj' : w j' = ((A.singularValues (j' : ℕ) : ℝ) : 𝕜)⁻¹ • A (v ⟨j', hj'k⟩) := by
      simp [hwdef, hj'k]
    change ⟪w j, w j'⟫_𝕜 = _
    rw [hwj, hwj', inner_smul_left, inner_smul_right, hgram ⟨j, hjk⟩ ⟨j', hj'k⟩]
    have hj0 : ((A.singularValues (j : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hjne
    rcases eq_or_ne j j' with hjj | hjj
    · subst hjj
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
    · have h1 : (⟨(j : ℕ), hjk⟩ : Fin k) ≠ ⟨(j' : ℕ), hj'k⟩ := by
        simp only [ne_eq, Fin.mk.injEq]
        exact fun hh => hjj (Fin.ext hh)
      simp [h1, hjj, Subtype.ext_iff]
  obtain ⟨c, hc⟩ := hws.exists_orthonormalBasis_extension_of_card_eq
    (Fintype.card_fin _).symm
  set u : Fin k → F := fun i => c (Fin.castLE hkF i) with hudef
  have hu : Orthonormal 𝕜 u := c.orthonormal.comp _ (Fin.castLE_injective hkF)
  refine ⟨u, v, hu, hv, ?_⟩
  have hterm : ∀ i : Fin k, ⟪u i, A (v i)⟫_𝕜 = ((A.singularValues (i : ℕ) : ℝ) : 𝕜) := by
    intro i
    by_cases hz : A.singularValues (i : ℕ) = 0
    · have hA0 : A (v i) = 0 := by
        have h := hnorm i
        rw [hz] at h
        exact norm_eq_zero.mp h
      rw [hA0, inner_zero_right, hz, RCLike.ofReal_zero]
    · have hlt : ((Fin.castLE hkF i : Fin (finrank 𝕜 F)) : ℕ) < k := i.isLt
      have hmem : (Fin.castLE hkF i) ∈ s := ⟨hlt, hz⟩
      have hwv : w (Fin.castLE hkF i) = ((A.singularValues (i : ℕ) : ℝ) : 𝕜)⁻¹ • A (v i) := by
        simp only [hwdef, dif_pos hlt]
        rfl
      have h0 : ((A.singularValues (i : ℕ) : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hz
      change ⟪c (Fin.castLE hkF i), A (v i)⟫_𝕜 = _
      rw [hc _ hmem, hwv, inner_smul_left, hgram i i]
      simp only [map_inv₀, RCLike.conj_ofReal]
      push_cast
      field_simp
  rw [Finset.sum_congr rfl fun (i : Fin k) (_ : i ∈ Finset.univ) => hterm i]
  rw [show (∑ i : Fin k, ((A.singularValues (i : ℕ) : ℝ) : 𝕜))
      = ((∑ i : Fin k, A.singularValues (i : ℕ) : ℝ) : 𝕜) by push_cast; rfl,
    RCLike.ofReal_re]
  rfl

end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
