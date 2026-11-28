/- GID: D5/S3/Zeros/GRH/New/Filling/ColumnCoords
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/Filling/ColumnCoords
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.Filling.ColumnCoords. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/Filling/ColumnCoords.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.Filling.PoincareSeries
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Set-up for this proof: dictionaries between two encodings of the same objects.

This file: Dictionary between adelic groups and frame coordinates; columns in orthonormal
coordinates. -/
seal Finset.univ Finset.sum Finset.prod

open Equiv Grading Matrix

namespace Filling.Fits

attribute [local simp] adelicEquiv adelicToFin inclHFin basisScale inclX Shape.besselIndexEquiv
  U.map U.reindex U.sum Units.ext_iff toBesselH

variable {E 𝔰} [Field E] [CMType E] {S : Filling E 𝔰} {ε l kw V Y η} [Frame 𝔰 ε]
  (h : S.Fits V l kw Y η)

lemma mem_unipotent_iff {g} : (g ∈ Y.unipotent ↔ h.adelicEquiv g ∈ besselU) ∧ (g ∈ Y.besselGroup ↔
  h.adelicEquiv g ∈ besselS) := by constructor <;> apply forall₂_congr <;> simp! [h.index_eq,
  gradeOf, FI.level, Functor.map, Space.ratCoordMatrix] <;> grind-ring -linarith

lemma adelicToFin_adelicEquiv_inclX a : S.adelicToFin (h.adelicEquiv (Y.inclX a)) =
  S.inclHFin a.2 := by
  simp [← ext_iff, h.index_eq, apply_ite Prod.snd]; and_intros <;> intros <;> first | rfl | grind

lemma finiteEquiv_inclX a : h.finiteEquiv (Y.inclX a).2 = S.inclHFin a.2 := by
  rw [finiteEquiv_eq_adelicToFin, adelicToFin_adelicEquiv_inclX, ((h.5 _).map _).inv_mul_cancel]

lemma adelicToInf_inclX a : S.adelicToInf (h.adelicEquiv (Y.inclX a)) = (toBesselH 𝔰 1 ⟨a.1 ·,
  @signMatrix_one .. ▸ (a.1 _).2⟩) := by
  ext _ (_ | (_ | _) | _) (_ | (_ | _) | _) <;>
    simp [h.index_eq, adelicToInf_apply, one_apply, apply_ite Prod.fst, ite_apply] <;>
    first | rfl | lia | (split_ifs <;> simp_all; lia)

/-- A linear isomorphism A from Weyl coordinates of type kw to Bessel coordinates with Av·W(gy)
= A(S_kw(gᵀ)v)·W(y) for g in ∏_v U(X₀), W the Bessel function, S_kw the Schur matrix. -/
noncomputable def weylBesselEquiv : {A : _ ≃ₗ[ℂ] _ // ∀ (g : _ → _) y v, A v ⬝ᵥ S.besselFn
  ((toBesselH 𝔰 1 <| g ·) * y) = A (schur kw (g · |>.1.1ᵀ) *ᵥ v) ⬝ᵥ S.besselFn y} := by
  choose A A' _ _ t using (h.1 · |>.2)
  let e := (funUnique Unit (WeylIndex 𝔰.κ kw)).symm.trans (piComm _)
  use toLinearEquivRight'OfInv (?_ : (kroneckerPi A').submatrix id e * (kroneckerPi A).submatrix e
    id = 1) ?_ <;> simp [← coe_refl, ← kroneckerPi_mul, *]
  intros; rw [← vecMul_transpose]; repeat erw [← dotProduct_mulVec]
  congr 1; ext; simpa [mulVec_eq_sum, Fintype.prod_sum, reindex_equiv e,
    schur_apply_eq_prod (κ := kw)] using! congr(∏ v, $(t v ..) _)

/-- The isomorphism from algebraic forms of weight (kw, 0) and level Kc on U(X₀) to ℓ²(classes ×
coordinates): evaluate at class representatives, then change coordinates by
`Filling.Fits.weylBesselEquiv`. -/
noncomputable def columnCoords : levelSpace (algFormRep kw 0) S.columnLevel ≃ₗ[ℂ] EuclideanSpace ℂ
  (S.Classes × S.BesselCoord) := freeLevelEquiv _ _ 1 S.aut_columnLevel ≪≫ₗ .piCongrRight (fun _ ↦
  h.weylBesselEquiv.1) ≪≫ₗ .symm (WithLp.linearEquiv .. ≪≫ₗ .curry ..)
