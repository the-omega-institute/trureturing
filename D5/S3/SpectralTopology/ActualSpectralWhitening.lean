/- GID: D5/S3/SpectralTopology/ActualSpectralWhitening
   generality: G
   mirror-B: D5/B/S3/SpectralTopology/ActualSpectralWhitening
   mirror-E: none(waiver:general-analytic-proof)
   anchors: []
   utility: none
   digest: Actual support, zero-on-kernel inverse square root, and square root are smooth on constant-rank PSD families. -/

/-
admission_basis: escape-witness
escape_witness: sqrt_localInverse_identification on the live proof path of
  actual_constant_rank_whitening_smooth, via positive_matrix_sqrt_smooth.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/18787
No compiled Reg mirror or declared_validated registration is claimed.
The actual CFC square root is identified with the smooth local inverse of the
Hermitian square map. The derivative YV+VY is invertible for positive Y.
All dimensions and ranks are arbitrary naturals; the manifold may be empty.
This general analytic result does not complete the global ST37 tensor geometry.

Direct frozen dependencies (module GID and statement_id):
D5/S3/Geometry/AlphaGeometry/HermitianCubeDerivative
  sha256:a383e2db6be9c84f4e80ed43b63887591371cd913a3b081fa4061b193249fcec
D5/S3/Geometry/ProjectionRange/Prebundle
  sha256:faf7f9a933abd59f15d9aa684b4a659e912ba46502138e3a726da325239fb476
D5/S3/Quantum/Recovery/SpectralTransposeRecovery
  sha256:511237a5d20ff1beb474456cd2c9cc427fe528454ace0586e89dc9a4a4362cd6

Per-declaration classification after inlining the new helpers:
Herm: definition, used throughout the Hermitian square-root construction.
positive_jordan_injective: bind-only; directly consumes the existing
  Traces.jordan_conjugation and Traces.diagonal_conjugated_jordan;
  consumer positiveJordanEquiv.
positiveJordanEquiv: constructed derivative equivalence; consumed by
  square_strict_derivative and positive_hermitian_sqrt_contDiffAt.
positiveSqrt: definition; consumers positiveSqrt_posdef, positiveSqrt_square,
  square_positiveSqrt, sqrt_localInverse_identification and the smoothness proof.
positiveSqrt_posdef: bind-only; consumer positive_hermitian_sqrt_contDiffAt.
positiveSqrt_square: bind-only; consumer sqrt_localInverse_identification.
square_positiveSqrt: bind-only; consumer positive_hermitian_sqrt_contDiffAt.
square_strict_derivative: bind-only; consumers squareLocalEquiv and
  sqrt_localInverse_identification.
squareLocalEquiv: definition; consumer sqrt_localInverse_identification.
sqrt_localInverse_identification: content; consumer
  positive_hermitian_sqrt_contDiffAt; escape witness is the local identification.
positive_hermitian_sqrt_contDiffAt: content after inlining its live helpers;
  consumer positive_matrix_sqrt_smooth.
support_range: bind-only; consumer gram_is_actual_support.
gram_is_actual_support: bind-only; consumer actual_constant_rank_support_smooth.
actual_constant_rank_support_smooth: bind-only; consumer
  actual_constant_rank_whitening_smooth.
positive_matrix_sqrt_smooth: content after inlining the new Hermitian root proof;
  consumer actual_constant_rank_whitening_smooth.
actual_whitening_extension: bind-only; consumer actual_constant_rank_whitening_smooth.
actual_constant_rank_whitening_smooth: content endpoint, with the same live
  square-root local-inverse witness; no separate novelty claim.
All declarations have utility kind none: these are symbolic analytic statements
for arbitrary matrices and smooth manifolds, not finite certified instances,
enumeration, checkers or numerical reductions.
-/

import D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative
import D5.S3.Geometry.ProjectionRange.Prebundle
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery

/-! Actual spectral functions on smooth constant-rank positive semidefinite families. -/

noncomputable section
open Filter Set
open scoped BigOperators Matrix MatrixOrder ComplexOrder Topology Manifold ContDiff
  Matrix.Norms.Elementwise
open D5.S3.Geometry.AlphaGeometry.HermitianCubeDerivative
open D5.S3.Geometry.AlphaGeometry.HermitianDensityCoordinates
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Original8340Global

abbrev Herm (n : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin n) (Fin n) ℂ)

private lemma positive_jordan_injective {n : ℕ} (Y : Herm n) (hY : Y.val.PosDef) :
    Function.Injective (jordan Y) := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro V hV
  have hV' : jordan Y V = 0 := hV
  let e := Unitary.conjStarAlgAut ℂ (Matrix (Fin n) (Fin n) ℂ)
    hY.isHermitian.eigenvectorUnitary
  let ec := Traces.hermitianConj e
  let D := Traces.diagonalH hY.isHermitian.eigenvalues
  have hEY : ec D = Y := by
    apply Subtype.ext
    exact hY.isHermitian.spectral_theorem.symm
  let z := ec.symm V
  have hzker : jordan D z = 0 := by
    apply ec.injective
    have hc := congrArg (fun f : Herm n →ₗ[ℝ] Herm n => f V)
      (Traces.jordan_conjugation e D)
    change ec (jordan D (ec.symm V)) = jordan (ec D) V at hc
    rw [hEY, hV'] at hc
    simpa only [map_zero] using hc
  let c := Traces.readoutEquiv n
  have he := congrArg
    (fun f : (Fin n × Fin n → ℝ) →ₗ[ℝ] (Fin n × Fin n → ℝ) => f (c z))
    (Traces.diagonal_conjugated_jordan hY.isHermitian.eigenvalues)
  change c (jordan D (c.symm (c z))) = _ at he
  rw [c.symm_apply_apply, hzker, map_zero] at he
  have hcz : c z = 0 := by
    ext ⟨i,j⟩
    have hij := congrFun he (i,j)
    have hij' : (hY.isHermitian.eigenvalues i + hY.isHermitian.eigenvalues j) *
        c z (i,j) = 0 := by
      simpa [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.diagonal] using hij.symm
    exact (mul_eq_zero.mp hij').resolve_left
      (ne_of_gt (add_pos (hY.eigenvalues_pos i) (hY.eigenvalues_pos j)))
  have hz : z = 0 := c.injective (by simpa only [map_zero] using hcz)
  exact ec.symm.injective (by simpa only [map_zero] using hz)

private def positiveJordanEquiv {n : ℕ} (Y : Herm n) (hY : Y.val.PosDef) :
    Herm n ≃L[ℝ] Herm n :=
  (LinearEquiv.ofInjectiveEndo (jordan Y).toLinearMap
    (positive_jordan_injective Y hY)).toContinuousLinearEquiv

private def positiveSqrt {n : ℕ} (A : Herm n) : Herm n :=
  ⟨CFC.sqrt A.val, (Matrix.LE.le.posSemidef (CFC.sqrt_nonneg A.val)).isHermitian⟩

private lemma positiveSqrt_posdef {n : ℕ} (A : Herm n) (hA : A.val.PosDef) :
    (positiveSqrt A).val.PosDef := by
  change (CFC.sqrt A.val).PosDef
  rw [CFC.sqrt_eq_rpow]
  exact Matrix.IsStrictlyPositive.posDef
    (IsStrictlyPositive.rpow A.val (1 / 2 : ℝ) hA.isStrictlyPositive)

private lemma positiveSqrt_square {n : ℕ} (A : Herm n) (hA : A.val.PosDef) :
    positiveSqrt (square A) = A := by
  apply Subtype.ext
  exact CFC.sqrt_sq A.val hA.posSemidef.nonneg

private lemma square_positiveSqrt {n : ℕ} (A : Herm n) (hA : A.val.PosDef) :
    square (positiveSqrt A) = A := by
  apply Subtype.ext
  exact CFC.sq_sqrt A.val hA.posSemidef.nonneg

private lemma square_strict_derivative {n : ℕ} (Y : Herm n) (hY : Y.val.PosDef) :
    HasStrictFDerivAt square (positiveJordanEquiv Y hY : Herm n →L[ℝ] Herm n) Y := by
  apply (square_contDiff n).contDiffAt.hasStrictFDerivAt' _ (by simp)
  exact square_hasFDerivAt Y

private def squareLocalEquiv {n : ℕ} (Y : Herm n) (hY : Y.val.PosDef) :
    OpenPartialHomeomorph (Herm n) (Herm n) :=
  (square_strict_derivative Y hY).toOpenPartialHomeomorph square

private lemma sqrt_localInverse_identification {n : ℕ} (Y : Herm n)
    (hY : Y.val.PosDef) :
    positiveSqrt =ᶠ[𝓝 (square Y)] (squareLocalEquiv Y hY).symm := by
  apply (square_strict_derivative Y hY).localInverse_unique
  filter_upwards [(hermitian_posdef_open n).mem_nhds hY] with X hX
  exact positiveSqrt_square X hX

theorem positive_hermitian_sqrt_contDiffAt {n : ℕ} (A : Herm n)
    (hA : A.val.PosDef) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun X : Herm n => CFC.sqrt X.val) A := by
  let Y := positiveSqrt A
  have hY : Y.val.PosDef := positiveSqrt_posdef A hA
  have hf : HasFDerivAt square (positiveJordanEquiv Y hY : Herm n →L[ℝ] Herm n) Y :=
    square_hasFDerivAt Y
  have hc := (square_contDiff n).contDiffAt.to_localInverse hf
    (by simp : (↑(⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) positiveSqrt (square Y) :=
    hc.congr_of_eventuallyEq (sqrt_localInverse_identification Y hY)
  have hsA : ContDiffAt ℝ (⊤ : ℕ∞) positiveSqrt A := by
    simpa only [Y, square_positiveSqrt A hA] using hs
  exact (Herm n).subtypeL.contDiff.contDiffAt.comp A hsA




set_option maxHeartbeats 3000000 in
-- The finite spectral identities and local Gram patch are elaborated together.
theorem support_range {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.PosSemidef) :
    LinearMap.range (spectralSupport Q).toEuclideanLin = LinearMap.range Q.toEuclideanLin ∧
    (spectralSupport Q).IsHermitian ∧
    spectralSupport Q * spectralSupport Q = spectralSupport Q := by
  let p := spectralSupport Q
  let z := cfc (fun t : ℝ => t⁻¹) Q
  have hc (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ Q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have hmul (f g : ℝ → ℝ) : cfc f Q * cfc g Q = cfc (fun t => f t * g t) Q :=
    (cfc_mul f g Q (hc f) (hc g)).symm
  have hp : p.IsHermitian := (cfc_predicate _ Q : IsSelfAdjoint p).isHermitian
  have hpq : p * Q = Q := by
    calc
      _ = cfc (fun t : ℝ => if t = 0 then 0 else 1) Q * cfc (fun t : ℝ => t) Q := by
        rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]; rfl
      _ = cfc (fun t : ℝ => (if t = 0 then 0 else 1) * t) Q := hmul _ _
      _ = cfc (fun t : ℝ => t) Q := by
        apply cfc_congr
        intro t ht
        by_cases hz : t = 0 <;> simp [hz]
      _ = Q := cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint
  have hqz : Q * z = p := by
    calc
      _ = cfc (fun t : ℝ => t) Q * cfc (fun t : ℝ => t⁻¹) Q := by
        rw [cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint]
      _ = cfc (fun t : ℝ => t * t⁻¹) Q := hmul _ _
      _ = p := by
        apply cfc_congr
        intro t ht
        by_cases hz : t = 0 <;> simp [hz]
  have hpp : p * p = p := by
    change cfc _ Q * cfc _ Q = cfc _ Q
    rw [hmul]
    apply cfc_congr
    intro t ht
    by_cases hz : t = 0 <;> simp [hz]
  have hlinPQ : p.toEuclideanLin.comp Q.toEuclideanLin = Q.toEuclideanLin := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg Matrix.toEuclideanLin hpq
  have hlinQZ : Q.toEuclideanLin.comp z.toEuclideanLin = p.toEuclideanLin := by
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg Matrix.toEuclideanLin hqz
  refine ⟨?_, hp, hpp⟩
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    exact ⟨z.toEuclideanLin u, congrArg (fun f => f u) hlinQZ⟩
  · rintro v ⟨u, rfl⟩
    exact ⟨Q.toEuclideanLin u, congrArg (fun f => f u) hlinPQ⟩

set_option maxHeartbeats 3000000 in
-- The Gram projection is identified by its actual Euclidean range.
private theorem gram_is_actual_support {n r : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q.PosSemidef)
    (C : Matrix (Fin n) (Fin r) ℂ) (hC : IsUnit (Cᴴ * C))
    (hspan : Submodule.span ℂ (Set.range C.col) =
      Submodule.span ℂ (Set.range Q.col)) :
    C * (Cᴴ * C)⁻¹ * Cᴴ = spectralSupport Q := by
  let G := C * (Cᴴ * C)⁻¹ * Cᴴ
  have hGC : G * C = C := by
    change (C * (Cᴴ * C)⁻¹ * Cᴴ) * C = C
    calc
      _ = C * ((Cᴴ * C)⁻¹ * (Cᴴ * C)) := by simp only [Matrix.mul_assoc]
      _ = C := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hC), Matrix.mul_one]
  have hGs : G.IsHermitian := by
    change (C * (Cᴴ * C)⁻¹ * Cᴴ)ᴴ = C * (Cᴴ * C)⁻¹ * Cᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  have hGG : G * G = G := by
    calc
      _ = (G * C) * (Cᴴ * C)⁻¹ * Cᴴ := by dsimp [G]; simp only [Matrix.mul_assoc]
      _ = G := by rw [hGC]
  have hGproj : G.toEuclideanLin.IsSymmetricProjection := by
    refine ⟨?_, Matrix.isSymmetric_toEuclideanLin_iff.mpr hGs⟩
    change G.toEuclideanLin.comp G.toEuclideanLin = G.toEuclideanLin
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg Matrix.toEuclideanLin hGG
  obtain ⟨hPrange, hPs, hPP⟩ := support_range Q hQ
  have hPproj : (spectralSupport Q).toEuclideanLin.IsSymmetricProjection := by
    refine ⟨?_, Matrix.isSymmetric_toEuclideanLin_iff.mpr hPs⟩
    change (spectralSupport Q).toEuclideanLin.comp (spectralSupport Q).toEuclideanLin = _
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
      congrArg Matrix.toEuclideanLin hPP
  have hrangeG : LinearMap.range G.toEuclideanLin = LinearMap.range C.toEuclideanLin := by
    apply le_antisymm
    · rintro v ⟨u, rfl⟩
      refine ⟨((Cᴴ * C)⁻¹ * Cᴴ).toEuclideanLin u, ?_⟩
      have he : C.toEuclideanLin.comp ((Cᴴ * C)⁻¹ * Cᴴ).toEuclideanLin = G.toEuclideanLin := by
        simp only [G, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_assoc]
      exact congrArg (fun f => f u) he
    · rintro v ⟨u, rfl⟩
      refine ⟨C.toEuclideanLin u, ?_⟩
      have he : G.toEuclideanLin.comp C.toEuclideanLin = C.toEuclideanLin := by
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using
          congrArg Matrix.toEuclideanLin hGC
      exact congrArg (fun f => f u) he
  apply Matrix.toEuclideanLin.injective
  apply hGproj.ext hPproj
  exact hrangeG.trans ((ProjectionRange.euclidean_range_eq_of_span_eq C Q hspan).trans hPrange.symm)

set_option maxHeartbeats 3000000 in
-- The finite spectral identities and local Gram patch are elaborated together.
theorem actual_constant_rank_support_smooth
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {n r : ℕ} (Q : B → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ Q)
    (hPSD : ∀ x, (Q x).PosSemidef) (hrank : ∀ x, (Q x).rank = r) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞
      (fun x => spectralSupport (Q x)) := by
  classical
  intro x
  have hr : ∀ᶠ y in 𝓝[univ] x,
      Module.finrank ℂ (LinearMap.range (Q y).mulVecLin) =
      Module.finrank ℂ (LinearMap.range (Q x).mulVecLin) :=
    Eventually.of_forall fun y => (hrank y).trans (hrank x).symm
  have hcert := exact_original_local_gram_certificate Q univ x (mem_univ _)
    (fun y _ => hPSD y) hQ.continuous.continuousAt.continuousWithinAt hr
  dsimp only at hcert
  obtain ⟨J, hJ, U, hU, hx, hcert⟩ := hcert
  let C : B → Matrix (Fin n)
      (Fin (Module.finrank ℂ (LinearMap.range (Q x).mulVecLin))) ℂ := fun y i j => Q y i (J j)
  have hCs : ContMDiffAt I 𝓘(ℝ, Matrix (Fin n)
      (Fin (Module.finrank ℂ (LinearMap.range (Q x).mulVecLin))) ℂ) ∞ C x := by
    apply contMDiffAt_pi_space.mpr
    intro i
    apply contMDiffAt_pi_space.mpr
    intro j
    exact contMDiffAt_pi_space.mp (contMDiffAt_pi_space.mp (hQ x) i) (J j)
  have hGr := ProjectionRange.smooth_mul (ProjectionRange.smooth_adj hCs) hCs
  have hunit : IsUnit ((C x)ᴴ * C x) := (hcert x hx).2.1
  have hs := ProjectionRange.smooth_mul
    (ProjectionRange.smooth_mul hCs (ProjectionRange.smooth_inv hGr hunit))
    (ProjectionRange.smooth_adj hCs)
  apply hs.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx.1] with y hy
  exact (gram_is_actual_support (Q y) (hPSD y) (C y)
    (hcert y ⟨hy, mem_univ _⟩).2.1 (hcert y ⟨hy, mem_univ _⟩).2.2).symm



set_option maxHeartbeats 3000000 in
-- Matrix CFC composition and dependent manifold instances need this elaboration budget.
theorem positive_matrix_sqrt_smooth
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {n : ℕ} (Q : B → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ Q)
    (hPD : ∀ x, (Q x).PosDef) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => CFC.sqrt (Q x)) := by
  let T := selfAdjointPartL ℝ (Matrix (Fin n) (Fin n) ℂ)
  let q : B → Herm n := fun x => T (Q x)
  have he (x : B) : (q x).val = Q x :=
    (hPD x).isHermitian.isSelfAdjoint.coe_selfAdjointPart_apply ℝ
  have hq : ContMDiff I 𝓘(ℝ, Herm n) ∞ q :=
    T.contDiff.comp_contMDiff hQ
  intro x
  have hpos : (q x).val.PosDef := by rw [he]; exact hPD x
  have hs := (positive_hermitian_sqrt_contDiffAt (q x) hpos).comp_contMDiffAt (hq x)
  apply hs.congr_of_eventuallyEq
  exact Eventually.of_forall fun y => by
    change CFC.sqrt (Q y) = CFC.sqrt (q y).val
    rw [he y]

set_option maxHeartbeats 3000000 in
-- Matrix CFC composition and dependent manifold instances need this elaboration budget.
theorem actual_whitening_extension {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q.PosSemidef) :
    let P := spectralSupport Q
    let H := Q + 1 - P
    H.PosDef ∧
    spectralInverseSqrt Q = P * (CFC.sqrt H)⁻¹ ∧
    CFC.sqrt Q = P * CFC.sqrt H := by
  let chi : ℝ → ℝ := fun t => if t = 0 then 0 else 1
  let f := fun t : ℝ => t + 1 - chi t
  let P := spectralSupport Q
  let H := Q + 1 - P
  have hc (g : ℝ → ℝ) : ContinuousOn g (spectrum ℝ Q) := by
    rw [continuousOn_iff_continuous_domRestrict]
    fun_prop
  have hmul (g h : ℝ → ℝ) : cfc g Q * cfc h Q = cfc (fun t => g t * h t) Q :=
    (cfc_mul g h Q (hc g) (hc h)).symm
  have hHcfc : cfc f Q = H := by
    dsimp only [f, H, P, spectralSupport]
    rw [cfc_sub _ _ Q (hc _) (hc _),
      cfc_add Q (fun t : ℝ => t) (fun _ : ℝ => 1) (hc _) (hc _),
      cfc_id' ℝ Q hQ.isHermitian.isSelfAdjoint, cfc_const_one ℝ Q]
  have hfpos : ∀ t ∈ spectrum ℝ Q, 0 < f t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at ht
      obtain ⟨i, rfl⟩ := ht
      exact hQ.eigenvalues_nonneg i
    by_cases hz : t = 0
    · simp [f, chi, hz]
    · simpa [f, chi, hz] using lt_of_le_of_ne ht0 (Ne.symm hz)
  have hH : H.PosDef := by
    rw [← hHcfc]
    exact Matrix.IsStrictlyPositive.posDef
      ((cfc_isStrictlyPositive_iff f Q (hc f) hQ.isHermitian.isSelfAdjoint).mpr hfpos)
  have hRcf : CFC.sqrt H = cfc (fun t : ℝ => Real.sqrt (f t)) Q := by
    rw [CFC.sqrt_eq_real_sqrt H hH.posSemidef.nonneg, cfcₙ_eq_cfc]
    rw [← hHcfc]
    exact (cfc_comp Real.sqrt f Q hQ.isHermitian.isSelfAdjoint
      Real.continuous_sqrt.continuousOn (hc f)).symm
  let Z := cfc (fun t : ℝ => (Real.sqrt (f t))⁻¹) Q
  have hRZ : CFC.sqrt H * Z = 1 := by
    rw [hRcf]
    change cfc _ Q * cfc _ Q = 1
    rw [hmul]
    calc
      _ = cfc (fun _ : ℝ => 1) Q := by
        apply cfc_congr
        intro t ht
        exact mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (hfpos t ht)))
      _ = 1 := cfc_const_one ℝ Q
  have hInv : (CFC.sqrt H)⁻¹ = Z := Matrix.inv_eq_right_inv hRZ
  refine ⟨hH, ?_, ?_⟩
  · rw [hInv]
    change cfc (fun t : ℝ => (Real.sqrt t)⁻¹) Q = cfc chi Q * cfc _ Q
    rw [hmul]
    apply cfc_congr
    intro t ht
    by_cases hz : t = 0 <;> simp [chi, f, hz]
  · rw [hRcf, CFC.sqrt_eq_real_sqrt Q hQ.nonneg, cfcₙ_eq_cfc]
    change cfc Real.sqrt Q = cfc chi Q * cfc _ Q
    rw [hmul]
    apply cfc_congr
    intro t ht
    by_cases hz : t = 0 <;> simp [chi, f, hz]

set_option maxHeartbeats 3000000 in
-- Matrix CFC composition and dependent manifold instances need this elaboration budget.
theorem actual_constant_rank_whitening_smooth
    {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] [TopologicalSpace B] [ChartedSpace H B]
    (I : ModelWithCorners ℝ E H) [IsManifold I ∞ B]
    {n r : ℕ} (Q : B → Matrix (Fin n) (Fin n) ℂ)
    (hQ : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ Q)
    (hPSD : ∀ x, (Q x).PosSemidef) (hrank : ∀ x, (Q x).rank = r) :
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => spectralSupport (Q x)) ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => spectralInverseSqrt (Q x)) ∧
    ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ (fun x => CFC.sqrt (Q x)) := by
  have hp := actual_constant_rank_support_smooth I Q hQ hPSD hrank
  let H := fun x => Q x + 1 - spectralSupport (Q x)
  have hH : ContMDiff I 𝓘(ℝ, Matrix (Fin n) (Fin n) ℂ) ∞ H :=
    (hQ.add contMDiff_const).sub hp
  have hPD (x : B) : (H x).PosDef := (actual_whitening_extension (Q x) (hPSD x)).1
  have hR := positive_matrix_sqrt_smooth I H hH hPD
  refine ⟨hp, ?_, ?_⟩
  · intro x
    have hr : IsUnit (CFC.sqrt (H x)) := by
      have hpD : (CFC.sqrt (H x)).PosDef := by
        rw [CFC.sqrt_eq_rpow]
        exact Matrix.IsStrictlyPositive.posDef
          (IsStrictlyPositive.rpow (H x) (1 / 2 : ℝ) (hPD x).isStrictlyPositive)
      exact hpD.isUnit
    have hs := ProjectionRange.smooth_mul (hp x) (ProjectionRange.smooth_inv (hR x) hr)
    apply hs.congr_of_eventuallyEq
    exact Eventually.of_forall fun y => (actual_whitening_extension (Q y) (hPSD y)).2.1
  · intro x
    have hs := ProjectionRange.smooth_mul (hp x) (hR x)
    apply hs.congr_of_eventuallyEq
    exact Eventually.of_forall fun y => (actual_whitening_extension (Q y) (hPSD y)).2.2



end Original8340Global
