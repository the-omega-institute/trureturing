/- GID: D5/S3/Zeros/GRH/New/Rows/RowVolume
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Rows/RowVolume
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Rows.RowVolume. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Rows/RowVolume.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Trace.GoodFormTransfer
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: The rows repay the cost of the idle directions (see New.Rows.LiftVolumeHeight).

This file: Volume of the chain on rows factors into volumes of single lifts. -/

open Finset Fint LinearMap Module

variable {U V} [NormedAddCommGroup U] [InnerProductSpace ℂ U]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [Module.Finite ℂ V] {P} (D : Data P)

/-- Let u: U → V be a linear map of finite-dimensional complex Hilbert spaces and S an
endomorphism of U with ⟨ux, uy⟩ = a⟨x, Sy⟩ for all x, y. Then det(u*u) = a^D·det S, D = dim
U. -/
lemma normDet_sq_eq_pow_mul_det [Module.Finite ℂ U]
    (u : U →ₗ[ℂ] V) (S : End ℂ U) {a} (h : ∀ x y, inner ℂ (u x) (u y) =
  a * inner ℂ x (S y)) : u.normDet ^ 2 = a ^ finrank ℂ U * S.det := by
  rw [← det_smul]; convert u.normDet_sq; simp
  ext; simp [ext_iff_inner_left ℂ, adjoint_inner_right, inner_smul_right, h]

/-- For an m-fold twist ϑ, the volume det(u*u) of u = θ_j^* for the twist ϑ^j, restricted to the
good forms on U(W_j). -/
noncomputable def Data.liftVolume (ϑ : D.MFoldTwist) j := ((D.goodLift (ϑ.pow j) j).normDet : ℂ) ^ 2

/-- The lift Θ_ϑ: the composite `Data.iotaAtLevel` of the m theta lifts for the twist ϑ, restricted
to the rows. -/
noncomputable abbrev Data.Θ (ϑ : D.MFoldTwist) := D.iotaAtLevel ϑ ∘ₗ D.rows.subtype

/-- The volume 𝔷(ϑ) = det(u*u) of u = ι_ϑ (`Data.iotaAtLevel`) restricted to the space of rows. -/
noncomputable def Data.𝔷 ϑ := ((D.Θ ϑ).normDet : ℂ) ^ 2

/-- There are c(ϑ) with 0 ≠ 𝔷(ϑ) = |c(ϑ)|^D ∏_{j=1}^m λ_j(ϑ^j), D = `Data.rowDim`, for all ϑ whose
first m powers are twists; under `Data.IsFitFamily`, |c(θ(ι))/c(1)|^{−2} has height at most
2m²t·x^999. Here λ_j(ϑ^j) is `Data.liftVolume` ϑ j.

The rows repay the cost of the idle directions. -/
lemma Data.volume_iota_eq_prod_liftVolume : ∃ c, D.CostsSquares (D.m * D.m) c ∧ ∀ ϑ, D.𝔷 ϑ ≠ 0 ∧
  D.𝔷 ϑ = ‖c ϑ‖ ^ D.rowDim * ∏ j ∈ Icc 1 D.m, D.liftVolume ϑ j := by
  choose! A n H using (@auxLift_injective_and_hasSum_inner _ D ⟨·, ·⟩)
  choose! C _ g using D.hasSum_inner_triLift false
  choose! p e e' using fun (ϑ : D.MFoldTwist) i h ↦
    D.exists_common_hecke_rallis (ϑ.pow _) _ (a' := _ * (D.auxPair ϑ 1).gramFactor)
    (V := D.spaceY 0) (fun _ ↦ (g i h ϑ · _)) (H (i + 1) (by simpa) _).2
  choose _ k _ t K using (exists_isTriangle ..).choose_spec.inner_weightedChain_eq rfl (fun ϑ i ↦
    C i • D.heckeOnGood _ _)
    (fun i h ϑ x ↦ (e ϑ i h x ·.1 |>.trans (inner_smul_right ..).symm)) _ _ (zero_add _)
  refine D.stdLevelIndex_lastResLevel_eq.elim fun γ ⟨l, H⟩ ↦
    ⟨_, k.mul (.of_norm_sq_eq_mul_card_zpow (c := fun ϑ ↦ (∏ i : Fin D.m, C i /
    A i.succ) * Nat.card (WeylIndex (D.Y D.m) D.columnsY) * γ * Nat.card (D.𝔪 ϑ 0).ResRing ^ l) 0 _
    (l * 2) (by simp [mul_pow, zpow_mul]; rfl)) .refl, fun ϑ ↦ ⟨by simp [𝔷, ker_eq_bot,
    normDet_eq_zero_iff_ker_ne_bot], prod_Ico_add' (D.liftVolume ϑ) 0 _ 1 ▸ ?_⟩⟩
  obtain ⟨L, Z⟩ := fun i ↦ congr((‖$(normDet_sq_eq_pow_mul_det (goodLift ..) (D.heckeOnGood _ _)
    fun _ _ ↦ e' ϑ _ (Fin.isLt i) ..)‖ : ℂ)), congr((‖$(normDet_sq_eq_pow_mul_det (D.Θ ϑ) _ fun x
    y ↦ by erw [inner_iotaAtLevel, K, ← mul_assoc]; rfl)‖ : ℂ))
  simp [𝔷, liftVolume, prod_range, D.det_heckeOnGood_eq (hasRigidLabels_spaceW _ ⟨_,
    _⟩) D.hasRigidLabels_spaceY_zero, ← D.finrank_rows_eq_finrank_goodForms ⟨_, _⟩, *] at L Z ⊢
  simp [*, univ.prod_pow, div_pow, prod_eq_zero_iff, div_eq_iff, mul_div,
    div_mul_eq_mul_div, eq_div_iff]; ring

/-- For a representation f of the group algebra and a good tuple of labels c
(`Data.goodTupleFamilies`), the image of the idempotent of c lies in the image of `Data.e₀`. -/
lemma Data.range_tupleIdem_le {f : _ →ₐ[ℂ] End ℂ U} {c} (h : c ∈ D.goodTupleFamilies) :
    (f (tupleIdem _ c)).range ≤ (f D.e₀).range := by
  erw [← tupleIdem_orthogonal.mul_sum_of_mem h, D.isCentralProj_e₀.2.commute, map_mul]
  apply range_comp_le_range

lemma Data.groupAlgAction_auxLift {ϑ} {j : D.LiftIndex} {x} y :
  D.auxLift ϑ j ((D.principalRep _).asAlgebraHom x y) = (D.auxPair ϑ j).groupAlgAction x (D.auxLift
  ϑ j y) := by erw [AuxPair.groupAlgAction, asAlgebraHom_eq_sum,
  asAlgebraHom_eq_sum]; simp [auxLift_principalRep]; rfl

/-- For 1 ≤ j ≤ m, a subspace N that contains θ_{j,ϑ}^* y for every good form y on U(W_j) with a
Hecke eigensystem whose lift lies in the image of the idempotent of one good tuple contains all
lifts of good forms (the range of `Data.goodLift`). -/
lemma Data.range_goodLift_le {ϑ} {j : D.LiftIndex} {N} (h : ∀ p, ∀ y ∈ D.goodForms _ ⊓ D.eigenPart _
  p, ∀ c ∈ D.goodTupleFamilies, D.auxLift ϑ j y ∈ (AuxPair.groupAlgAction _ (tupleIdem _ c)).range →
  D.auxLift ϑ j y ∈ N) : (D.goodLift ϑ j).range ≤ N := by
  erw [range_domRestrict, ← range_comp, range_le_iff_comap, eq_top_iff, ← iSup_eigenPart,
    iSup_le_iff]
  simp_intro p y a [e₀]
  exact sum_mem fun c k ↦ h p _ ⟨D.range_tupleIdem_le k ⟨y, rfl⟩,
    principalRep_mem_eigenPart _ _ a _⟩ c k ⟨_, (D.groupAlgAction_auxLift y).symm⟩
