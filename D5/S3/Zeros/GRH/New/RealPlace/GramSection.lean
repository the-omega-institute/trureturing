/- GID: D5/S3/Zeros/GRH/New/RealPlace/GramSection
   generality: G
   mirror-B: D5/B/S3/Zeros/GRH/New/RealPlace/GramSection
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compact Dirichlet GRH proof, upstream module New.RealPlace.GramSection. -/

-- Source: https://github.com/lsernau/grh-lean/blob/72fead102f663d5c7a407964a13dc0cf9d977207/grh-compact/src/New/RealPlace/GramSection.lean
-- Apache 2.0 license, notice and attribution: docs/reports/third-party/grh-lean/
import D5.S3.Zeros.GRH.New.RealPlace.GramSectionBounds
-- Adapted imports and elaboration settings for D5.
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.mathlibStandardSet false

/-! Part of: Real-place Bessel integrals: band limits, energy and open-cell bound (see
New.Filling.FillingData).

This file: Explicit section is unitary and represents every double coset of the open cell. -/


open Matrix Complex Fin IsHermInvolution MatMul
variable {𝔰 : Shape} {Z : 𝔰.FrameMat} (h : Z ∈ 𝔰.openCell)
attribute [local simp] sum_univ_castSucc diagonal_apply Matrix.mul_apply actOnCols diagLast
  splitGram middleGram inclMatrix cornerDefect_pos Real.sqrt_eq_zero' frameGram prod_univ_castSucc
  conjTranspose_nonsing_inv Fin.ne_of_gt isUnit_iff_isUnit_det forall_fin_succ'
attribute [local simp ←] ext_iff
attribute [-simp] fromCols_mul_fromBlocks conjTranspose_fromCols_eq_fromRows_conjTranspose

lemma sectionMatrix_mul_frameCols : sectionMatrix Z * 𝔰.frameCols =
  sectionFrame Z := by simp [sectionMatrix]

lemma frameCols_gram_sectionMatrix : 𝔰.frameColsᴴ * 𝔰.J₁ * (sectionMatrix Z * 𝔰.frameCols) =
  Z := by simp [↓sectionMatrix_mul_frameCols, sectionFrame]; simp [sectionCoeff]

/-- The section γ_Z: the element of G₁ with matrix `sectionMatrix` at Z if Z lies in
`Shape.openCell` (det Z ≠ 0, |ξ| < 1), and the identity otherwise. -/
noncomputable def gramSection (Z : 𝔰.FrameMat) : 𝔰.G₁ :=
  U.of isUnit (if Z ∈ 𝔰.openCell then sectionMatrix Z else 1) (by
  split_ifs with h; swap; simp
  let C := fromCols 𝔰.frameCols 𝔰.dualFrameCols; let J := Cᴴ * 𝔰.J₁ * C; let Δ :=
    @diagLast 𝔰 (√(cornerDefect Z))⁻¹
  obtain ⟨d, a, b⟩ := cornerDefect_pos h, (by simp [C, J]; lia : Cᴴ * C = 1 ∧ 𝔰.J₁ = actOnCols C J)
  let x := fromBlocks Z⁻¹ (sectionCoeff Zᴴ Z * Δ) 0 (1 : 𝔰.FrameMat)
  let y := fromBlocks (sectionCoeff Z) (Zᴴ⁻¹ * Δ) (diagLast √(cornerDefect Z)) 0; have e :
    yᴴ * J * y = xᴴ * J * x := by
                           simp +zetaDelta [sectionCoeff, map_ofNat, ← ofReal_pow, d.le, d.ne',
                             ← conjTranspose_nonsing_inv, field]
                           simp [cornerDefect, invCorner]; grind [conj_mul']
  rw [(by simp [x, y, C, Δ, inv_fromBlocks_zero₂₁_of_isUnit_iff', h, h.1, -ext_iff, sectionMatrix,
    sectionFrame, conjTranspose_fromCols_eq_fromRows_conjTranspose]; abel : sectionMatrix _ =
    actOnCols C (y * x⁻¹))]
  simpa [↓b, mul_mul_eq_of_mul_eq a, x, h.1, -ext_iff] using congr(actOnCols C (x⁻¹ᴴ * $e * x⁻¹)))

@[fun_prop] lemma measurable_gramSection : Measurable (@gramSection 𝔰) :=
  .subtype_mk (measurable_comap_iff.2 (by
  exact ContinuousOn.measurable_piecewise (@differentiableAt_sectionMatrix _ · ·
    |>.continuousAt.continuousWithinAt) (by fun_prop) isOpen_openCell.measurableSet))

include h

lemma diagLast_sqrt_mul_inv :
  @diagLast 𝔰 √(cornerDefect Z) * diagLast (√(cornerDefect Z))⁻¹ = 1 := by aesop

/-- For Z in the open set Ω (Z invertible, with last diagonal entry of Z⁻¹ of absolute value
less than 1), the matrix underlying the section γ_Z ∈ G₁ equals the explicit matrix
`sectionMatrix` at Z. -/
lemma coe_gramSection : (gramSection Z).1.1 = sectionMatrix Z := ite_eq_left h

lemma gramSection_eventuallyEq : (gramSection ·|>.1.1) =ᶠ[nhds Z] sectionMatrix :=
  .mono (isOpen_openCell.mem_nhds h) (@coe_gramSection _)

/-- For Z in Ω, the element γ_Z of G₁ has frame matrix Z(γ_Z) = Z. -/
lemma realFrameGram_gramSection : realFrameGram (gramSection Z) =
  Z := by simpa [coe_gramSection h] using frameCols_gram_sectionMatrix (Z := Z)

/-- If γ ∈ G₁ has Z(γ) in Ω, then γ = u h γ_{Z(γ)} h' u' with u, u' in the frame-fixing
unipotent group U⁰ and h, h' in the image of U(κ). -/
lemma exists_eq_mul_gramSection_mul {γ} (y : realFrameGram γ = Z) :
    ∃ q k r l, γ = unipotentOf q * embedH k * gramSection Z * (unipotentOf r * embedH l)⁻¹ := by
  have A {s} (z : realFrameGram s = Z) : (framePair s)ᴴ * 𝔰.J₁ * framePair s =
    fromBlocks (diagLast 0 - 1) Z Zᴴ
    (diagLast 0 - 1) := by simpa [← z] using congr(submatrix $(s.2) 𝔰.besselFrame 𝔰.besselFrame)
  have B {s} z := HasLeftInv.of_isUnit_gram (isUnit_of_mul_isUnit_right (x := fromBlocks 0 Zᴴ⁻¹
    Z⁻¹ 0) (by rw [@A s z]; simp [h.1]; rw [det_of_isUpperTriangular] <;> simp [BlockTriangular,
    conj_mul', ← conjTranspose_nonsing_inv] <;> norm_cast <;> grind [cornerDefect_pos h,
    cornerDefect, invCorner]))
  obtain ⟨g, e⟩ := witt ⟨I, by simp⟩ isHermitian isUnit (B y) (B (realFrameGram_gramSection h)) (A
    (realFrameGram_gramSection h) ▸ A y)
  simp [fromCols_ext_iff, ← mul_inclMatrix, -inclMatrix, -ext_iff] at e
  obtain ⟨⟨q, k, a⟩, p, l, b⟩ := exists_embedH_eq_of_fix_frameCols e.1,
    @exists_embedH_eq_of_fix_frameCols _ ((gramSection Z)⁻¹ * g * γ) (by simp [e, -inclMatrix])
  use q, k⁻¹, p, l⁻¹, by simp_rw [map_inv, ← a, ← b]; group
