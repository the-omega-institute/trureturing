/- GID: D5/S3/Quantum/Entanglement/FiniteSectorRectangularVariational
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/FiniteSectorRectangularVariational
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rectangular singular-value variational bounds for passive sector tests. -/

import D5.S3.Quantum.Entanglement.FiniteSectorChannelModel
import D5.S3.Weil.ZetaLinear.Sylvester
import D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Trace
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic

/-
Selected variational proofs adapted from AIQ-Kitware/aiq-dkps-formalization,
revision 64e234954217f3ca907ac980c8cbde2900109a66.
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Authors: Jon Crall, Claude Fable 5, Claude Opus 4.8,
GPT-5.6 Thinking, GPT-5.6 High.
Modified for this repository's pinned Lean v4.33.0 and Mathlib.
License and provenance: docs/reports/licenses/finite-sector-channel-third-party.md.
Retire when this repository's pinned Mathlib contains equivalent declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality

open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Observer.Hilbert.FiniteMoorePenroseInverse
open Matrix RHLinalg
open _root_.LinearMap
open Module (finrank)
open scoped BigOperators CStarAlgebra ComplexOrder MatrixOrder Matrix Kronecker InnerProductSpace

def kyFanSum {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (k : ℕ) (A : E →ₗ[𝕜] F) : ℝ :=
  ∑ i : Fin k, A.singularValues (i : ℕ)






set_option maxHeartbeats 400000 in
theorem re_sum_inner_map_le_ky_fan_sum {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
    {A : E →ₗ[𝕜] F} {k : ℕ} (hk : k ≤ finrank 𝕜 E)
    {u : Fin k → F} {v : Fin k → E}
    (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ kyFanSum k A := by
  classical
  let spectralSqrt {𝕜 : Type} {E : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsPositive) :
      E →ₗ[𝕜] E :=
    ∑ i : Fin (finrank 𝕜 E),
      ((Real.sqrt (hT.isSymmetric.eigenvalues rfl i) : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜 (hT.isSymmetric.eigenvectorBasis rfl i)
          (hT.isSymmetric.eigenvectorBasis rfl i)).toLinearMap

  let operatorAbs {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
    spectralSqrt (LinearMap.isPositive_adjoint_comp_self A)

  let zeroExtensionProd {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) :
      (E × F) →ₗ[𝕜] (E × F) :=
    { toFun := fun z => (0, A z.1)
      map_add' := by intro x y; ext <;> simp
      map_smul' := by intro c x; ext <;> simp }

  let zeroExtension {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F) :
      WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
      zeroExtensionProd A ∘ₗ
        (WithLp.linearEquiv 2 𝕜 (E × F)).toLinearMap

  let zeroExtensionInl {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
      E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
        LinearMap.inl 𝕜 E F)).isometryOfInner (by
      intro x y
      simp [WithLp.prod_inner_apply])

  let zeroExtensionInr {𝕜 : Type} {E F : Type u} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] :
      F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
    (((WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ
        LinearMap.inr 𝕜 E F)).isometryOfInner (by
      intro x y
      simp [WithLp.prod_inner_apply])

  let H := WithLp 2 (E × F)
  have sortedSpectrum {S : H →ₗ[𝕜] H} {n : ℕ}
      (hS : S.IsSymmetric) (hn : finrank 𝕜 H = n)
      (w : OrthonormalBasis (Fin n) 𝕜 H) {μ : Fin n → ℝ}
      (hμ : Antitone μ) (hw : ∀ i, S (w i) = (μ i : 𝕜) • w i) :
      hS.eigenvalues hn = μ := by
    have hmatrix : S.toMatrix w.toBasis w.toBasis =
        Matrix.diagonal (RCLike.ofReal ∘ μ) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [LinearMap.toMatrix_apply, hw,
          RCLike.real_smul_eq_coe_mul]
      · simp [LinearMap.toMatrix_apply, hw, hij]
    have hchar : S.charpoly = ∏ i, (Polynomial.X - Polynomial.C (μ i : 𝕜)) := by
      rw [← S.charpoly_toMatrix w.toBasis, hmatrix, Matrix.charpoly_diagonal]
      rfl
    have hroots : S.charpoly.roots =
        Multiset.map (RCLike.ofReal ∘ μ) Finset.univ.val := by
      rw [hchar, Polynomial.roots_prod _ _ (by
        simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero])]
      simp
    rw [← List.ofFn_inj, ← hS.sort_roots_charpoly_eq_eigenvalues hn]
    simp_rw [hroots, Fin.univ_val_map, Multiset.map_coe, List.map_ofFn,
      Function.comp_def, RCLike.ofReal_re, Multiset.coe_sort]
    convert! List.mergeSort_of_pairwise ?_
    simp_rw [decide_eq_true_eq, ← List.sortedGE_iff_pairwise]
    exact hμ.sortedGE_ofFn

  have sqrtPositive {T : H →ₗ[𝕜] H} (hT : T.IsPositive) :
      (spectralSqrt hT).IsPositive := by
    unfold spectralSqrt
    refine isPositive_sum _ fun i _ => ?_
    refine IsPositive.smul_of_nonneg ?_ (RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _))
    exact (InnerProductSpace.isPositive_rankOne_self _).toLinearMap

  have sqrtApply {T : H →ₗ[𝕜] H} (hT : T.IsPositive)
      (j : Fin (finrank 𝕜 H)) :
      spectralSqrt hT (hT.isSymmetric.eigenvectorBasis rfl j) =
        (Real.sqrt (hT.isSymmetric.eigenvalues rfl j) : 𝕜) •
          hT.isSymmetric.eigenvectorBasis rfl j := by
    unfold spectralSqrt
    rw [LinearMap.sum_apply]
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro i _ hij
      simp [InnerProductSpace.rankOne_apply,
        orthonormal_iff_ite.mp (hT.isSymmetric.eigenvectorBasis rfl).orthonormal i j,
        if_neg hij]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
    · simp [InnerProductSpace.rankOne_apply]

  have sqrtSquare {T : H →ₗ[𝕜] H} (hT : T.IsPositive) :
      spectralSqrt hT ∘ₗ spectralSqrt hT = T := by
    apply (hT.isSymmetric.eigenvectorBasis rfl).toBasis.ext
    intro k
    have hnn := hT.nonneg_eigenvalues rfl k
    simp only [OrthonormalBasis.coe_toBasis, LinearMap.comp_apply, sqrtApply,
      map_smul, smul_smul, hT.isSymmetric.apply_eigenvectorBasis]
    rw [← RCLike.ofReal_mul, Real.mul_self_sqrt hnn]


  have sqrtNormSq {T : H →ₗ[𝕜] H} (hT : T.IsPositive) (x : H) :
      ‖spectralSqrt hT x‖ ^ 2 = RCLike.re ⟪T x, x⟫_𝕜 := by
    have hss : spectralSqrt hT (spectralSqrt hT x) = T x := by
      rw [← LinearMap.comp_apply, sqrtSquare hT]
    rw [norm_sq_eq_re_inner (𝕜 := 𝕜), (sqrtPositive hT).isSymmetric x (spectralSqrt hT x), hss,
      ← hT.isSymmetric x x]

  have sqrtKer {T : H →ₗ[𝕜] H} (hT : T.IsPositive) :
      ker (spectralSqrt hT) = ker T := by
    have h := LinearMap.ker_adjoint_comp_self (spectralSqrt hT)
    rw [(sqrtPositive hT).adjoint_eq, sqrtSquare hT] at h
    exact h.symm

  have absPositive (A : H →ₗ[𝕜] H) : (operatorAbs A).IsPositive :=
    sqrtPositive (LinearMap.isPositive_adjoint_comp_self A)
  have absSquare (A : H →ₗ[𝕜] H) :
      operatorAbs A ∘ₗ operatorAbs A = A.adjoint ∘ₗ A :=
    sqrtSquare (LinearMap.isPositive_adjoint_comp_self A)

  have normAbs (A : H →ₗ[𝕜] H) (x : H) : ‖operatorAbs A x‖ = ‖A x‖ := by
    have hsq : ‖operatorAbs A x‖ ^ 2 = ‖A x‖ ^ 2 :=
      (sqrtNormSq (LinearMap.isPositive_adjoint_comp_self A) x).trans <| by
        rw [LinearMap.comp_apply, LinearMap.adjoint_inner_left, ← norm_sq_eq_re_inner (𝕜 := 𝕜)]
    rw [← Real.sqrt_sq (norm_nonneg (operatorAbs A x)), ← Real.sqrt_sq (norm_nonneg (A x)), hsq]

  have kerAbs (A : H →ₗ[𝕜] H) : ker (operatorAbs A) = ker A :=
    (sqrtKer (LinearMap.isPositive_adjoint_comp_self A)).trans
      (LinearMap.ker_adjoint_comp_self A)

  have rangeAbs (A : H →ₗ[𝕜] H) : range (operatorAbs A) = (ker A)ᗮ := by
    rw [← kerAbs A, LinearMap.orthogonal_ker, (absPositive A).adjoint_eq]

  have absMem (A : H →ₗ[𝕜] H) (x : H) :
      operatorAbs A x ∈ (ker A)ᗮ := by
    rw [← rangeAbs A]
    exact LinearMap.mem_range_self (operatorAbs A) x

  let absRestrict (A : H →ₗ[𝕜] H) : ↥((ker A)ᗮ) ≃ₗ[𝕜] ↥((ker A)ᗮ) :=
    LinearEquiv.ofBijective
        ((operatorAbs A).restrict fun x _ => absMem A x) <| by
      have hinj : Function.Injective
          ((operatorAbs A).restrict (p := (ker A)ᗮ)
            fun x _ => absMem A x) := by
        intro y z hyz
        have habs : operatorAbs A ↑y = operatorAbs A ↑z := congrArg Subtype.val hyz
        have hker : (↑y - ↑z : H) ∈ ker (operatorAbs A) := by
          rw [LinearMap.mem_ker, map_sub, habs, sub_self]
        rw [kerAbs A] at hker
        have hmem : (↑y - ↑z : H) ∈ (ker A)ᗮ := Submodule.sub_mem _ y.2 z.2
        exact Subtype.ext <| sub_eq_zero.mp <|
          Submodule.disjoint_def.mp (Submodule.orthogonal_disjoint (ker A)) _ hker hmem
      exact ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩

  let polarFactor (A : H →ₗ[𝕜] H) : H →ₗ[𝕜] H :=
    A ∘ₗ ((ker A)ᗮ).subtype ∘ₗ (absRestrict A).symm.toLinearMap
      ∘ₗ (((ker A)ᗮ).orthogonalProjectionOnto : H →L[𝕜] ↥((ker A)ᗮ)).toLinearMap

  have polarAction (A : H →ₗ[𝕜] H) (x : H) :
      polarFactor A (operatorAbs A x) = A x := by
    have habs : operatorAbs A x ∈ (ker A)ᗮ := absMem A x
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto (operatorAbs A x) = ⟨operatorAbs A x, habs⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨operatorAbs A x, habs⟩
    -- states the goal with the definition unfolded, in the shape the next step needs;
    -- there is no `_apply` lemma to rewrite with here.
    change A ↑((absRestrict A).symm
      (((ker A)ᗮ).orthogonalProjectionOnto (operatorAbs A x))) = A x
    rw [hproj]
    have h1 : operatorAbs A ↑((absRestrict A).symm ⟨operatorAbs A x, habs⟩)
        = operatorAbs A x :=
      congrArg Subtype.val ((absRestrict A).apply_symm_apply ⟨operatorAbs A x, habs⟩)
    have hker : (↑((absRestrict A).symm ⟨operatorAbs A x, habs⟩) - x : H)
        ∈ ker (operatorAbs A) := by
      rw [LinearMap.mem_ker, map_sub, h1, sub_self]
    rw [kerAbs A] at hker
    have h2 := LinearMap.mem_ker.mp hker
    rwa [map_sub, sub_eq_zero] at h2

  have polarNorm {A : H →ₗ[𝕜] H} {x : H} (hx : x ∈ (ker A)ᗮ) :
      ‖polarFactor A x‖ = ‖x‖ := by
    have hproj : ((ker A)ᗮ).orthogonalProjectionOnto x = ⟨x, hx⟩ :=
      Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ⟨x, hx⟩
    -- names the application so the norm bound applies to it directly.
    change ‖A ↑((absRestrict A).symm (((ker A)ᗮ).orthogonalProjectionOnto x))‖ = ‖x‖
    rw [hproj, ← normAbs,
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      show operatorAbs A ↑((absRestrict A).symm ⟨x, hx⟩) = x from
        congrArg Subtype.val ((absRestrict A).apply_symm_apply ⟨x, hx⟩)]

  let polarIsometry (A : H →ₗ[𝕜] H) :
      ↥((ker A)ᗮ) →ₗᵢ[𝕜] H := {
    toLinearMap := (polarFactor A) ∘ₗ ((ker A)ᗮ).subtype
    norm_map' := fun x => polarNorm x.2 }

  let polarUnitary (A : H →ₗ[𝕜] H) : H ≃ₗᵢ[𝕜] H :=
    LinearIsometryEquiv.ofSurjective (polarIsometry A).extend
      (LinearMap.injective_iff_surjective.mp (polarIsometry A).extend.injective)

  have unitaryAction (A : H →ₗ[𝕜] H) (x : H) :
      polarUnitary A (operatorAbs A x) = A x := by
    have hmem : operatorAbs A x ∈ (ker A)ᗮ := absMem A x
    dsimp only [polarUnitary]
    rw [LinearIsometryEquiv.coe_ofSurjective,
      -- states the goal with the definition unfolded, in the shape the next step needs;
      -- there is no `_apply` lemma to rewrite with here.
      show operatorAbs A x = ((⟨operatorAbs A x, hmem⟩ : ↥((ker A)ᗮ)) : H) from rfl,
      LinearIsometry.extend_apply]
    exact polarAction A x

  have cardFilter {n k : ℕ} (hk : k ≤ n) :
      (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k)).card = k := by
    classical
    rcases lt_or_eq_of_le hk with hlt | rfl
    · have h : (Finset.univ.filter (fun j : Fin n => (j : ℕ) < k))
          = Finset.Iio (⟨k, hlt⟩ : Fin n) := by
        ext j; simp [Fin.lt_def]
      rw [h, Fin.card_Iio]
    · have h : (Finset.univ.filter (fun j : Fin k => (j : ℕ) < k)) = Finset.univ := by
        ext j; simp
      rw [h, Finset.card_univ, Fintype.card_fin]

  have quad {T : H →ₗ[𝕜] H} {n : ℕ}
      (hT : T.IsSymmetric) (hn : finrank 𝕜 H = n) (x : H) :
      RCLike.re ⟪T x, x⟫_𝕜
        = ∑ i : Fin n, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
    have key : ⟪T x, x⟫_𝕜
        = ((∑ i : Fin n,
            hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [← (hT.eigenvectorBasis hn).repr.inner_map_map (T x) x, PiLp.inner_apply]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [RCLike.inner_apply, hT.eigenvectorBasis_apply_self_apply, map_mul, RCLike.conj_ofReal,
        mul_left_comm, RCLike.mul_conj]
    rw [key, RCLike.ofReal_re]

  have sum_mul_le_sum_top {n k : ℕ} (hk : k ≤ n) {lam c : Fin n → ℝ}
      (hlam : Antitone lam) (h0 : ∀ j, 0 ≤ c j) (h1 : ∀ j, c j ≤ 1)
      (hsum : ∑ j, c j = k) :
      ∑ j, lam j * c j
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j := by
    rcases lt_or_eq_of_le hk with hkn | rfl
    · set t := lam ⟨k, hkn⟩ with ht
      have hhead : ∀ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
          lam j * c j ≤ lam j + t * (c j - 1) := by
        intro j hj
        have hjk : (j : ℕ) < k := (Finset.mem_filter.mp hj).2
        have hle : t ≤ lam j := hlam (Fin.le_def.mpr hjk.le)
        nlinarith [mul_nonneg (sub_nonneg.mpr hle) (sub_nonneg.mpr (h1 j))]
      have htail : ∀ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k),
          lam j * c j ≤ t * c j := by
        intro j hj
        have hjk : ¬ (j : ℕ) < k := (Finset.mem_filter.mp hj).2
        have hle : lam j ≤ t := hlam (Fin.le_def.mpr (Nat.le_of_not_lt hjk))
        nlinarith [mul_nonneg (sub_nonneg.mpr hle) (h0 j)]
      have hsplit := (Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun j : Fin n => (j : ℕ) < k) (fun j => lam j * c j)).symm
      have hhead_eq : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
          (lam j + t * (c j - 1))
          = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j
            + t * (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), c j) - t * k := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
          Finset.sum_const, cardFilter hk, nsmul_eq_mul, mul_one]
        ring
      have htail_eq : ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), t * c j
          = t * ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), c j :=
        (Finset.mul_sum _ _ _).symm
      have hcsplit : ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), c j
          + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), c j = k := by
        rw [Finset.sum_filter_add_sum_filter_not]; exact hsum
      have hmul := congrArg (fun z => t * z) hcsplit
      simp only [mul_add] at hmul
      calc ∑ j, lam j * c j
          = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j * c j
            + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), lam j * c j := hsplit
        _ ≤ (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k),
              (lam j + t * (c j - 1)))
            + ∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬ (j : ℕ) < k), t * c j :=
            add_le_add (Finset.sum_le_sum hhead) (Finset.sum_le_sum htail)
        _ = ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), lam j := by
            rw [hhead_eq, htail_eq]
            linarith [hmul]
    · have hall : ∀ j, c j = 1 := by
        intro j
        by_contra hne
        have hlt : c j < 1 := lt_of_le_of_ne (h1 j) hne
        have hstrict : ∑ j', c j' < k := by
          calc ∑ j', c j' < ∑ _j' : Fin k, (1 : ℝ) :=
                Finset.sum_lt_sum (fun j' _ => h1 j') ⟨j, Finset.mem_univ j, hlt⟩
            _ = k := by
                rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
        rw [hsum] at hstrict
        exact lt_irrefl _ hstrict
      have hfilter : (Finset.univ.filter (fun j : Fin k => (j : ℕ) < k)) = Finset.univ := by
        ext j; simp
      rw [hfilter]
      exact le_of_eq (Finset.sum_congr rfl fun j _ => by rw [hall j, mul_one])

  have traceUpper {S : H →ₗ[𝕜] H} (hS : S.IsSymmetric)
      {n : ℕ} (hn : finrank 𝕜 H = n) {k : ℕ} (hk : k ≤ n) {w : Fin k → H}
      (hw : Orthonormal 𝕜 w) :
      ∑ i, RCLike.re ⟪S (w i), w i⟫_𝕜
        ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), hS.eigenvalues hn j := by
    set b := hS.eigenvectorBasis hn with hb
    set c : Fin n → ℝ := fun j => ∑ i : Fin k, ‖b.repr (w i) j‖ ^ 2 with hc
    have hswap : ∑ i, RCLike.re ⟪S (w i), w i⟫_𝕜 = ∑ j, hS.eigenvalues hn j * c j := by
      have hdiag : ∀ i, RCLike.re ⟪S (w i), w i⟫_𝕜
          = ∑ j : Fin n, hS.eigenvalues hn j * ‖b.repr (w i) j‖ ^ 2 := fun i =>
        quad hS hn (w i)
      simp_rw [hdiag, hc, Finset.mul_sum]
      exact Finset.sum_comm
    rw [hswap]
    refine sum_mul_le_sum_top hk (hS.eigenvalues_antitone hn)
      (fun j => Finset.sum_nonneg fun i _ => sq_nonneg _) (fun j => ?_) ?_
    · -- Bessel: the `j`-th column mass is at most `‖b j‖² = 1`.
      have hcontr : ∑ i : Fin k, ‖⟪w i, b j⟫_𝕜‖ ^ 2 ≤ 1 := by
        simpa [b.orthonormal.norm_eq_one j] using
          Orthonormal.sum_inner_products_le (b j) (s := Finset.univ) hw
      calc c j = ∑ i : Fin k, ‖⟪w i, b j⟫_𝕜‖ ^ 2 :=
            Finset.sum_congr rfl fun i _ => by rw [b.repr_apply_apply, ← norm_inner_symm]
        _ ≤ 1 := hcontr
    · -- Parseval: the total mass is `k`.
      have hcomm : ∑ j, c j = ∑ i : Fin k, ∑ j : Fin n, ‖b.repr (w i) j‖ ^ 2 := by
        rw [hc]; exact Finset.sum_comm
      have hone : ∀ i : Fin k, ∑ j : Fin n, ‖b.repr (w i) j‖ ^ 2 = 1 := by
        intro i
        simp_rw [b.repr_apply_apply]
        rw [b.sum_sq_norm_inner_right (w i), hw.1 i, one_pow]
      rw [hcomm, Finset.sum_congr rfl fun i _ => hone i]
      simp

  have absEigenvalues (A : H →ₗ[𝕜] H) :
      (absPositive A).isSymmetric.eigenvalues rfl
        = fun i : Fin (finrank 𝕜 H) => A.singularValues (i : ℕ) := by
    refine sortedSpectrum _ rfl
      (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl)
      (fun i j hij => A.singularValues_antitone (by exact_mod_cast hij))
      fun i => ?_
    rw [show operatorAbs A = spectralSqrt (LinearMap.isPositive_adjoint_comp_self A) from rfl,
      sqrtApply (LinearMap.isPositive_adjoint_comp_self A) i,
      A.singularValues_fin rfl i]

  have sumFilter {n k : ℕ} (hk : k ≤ n) (f : ℕ → ℝ) :
      ∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ)
        = ∑ i : Fin k, f (i : ℕ) := by
    rw [show (∑ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < k), f (j : ℕ))
        = ∑ j : Fin n, if (j : ℕ) < k then f (j : ℕ) else 0 from Finset.sum_filter _ _,
      Fin.sum_univ_eq_sum_range (fun m => if m < k then f m else 0) n,
      Fin.sum_univ_eq_sum_range (fun m => f m) k, ← Finset.sum_filter]
    congr 1
    ext m
    simp only [Finset.mem_filter, Finset.mem_range]
    omega

  have squareUpper {A : H →ₗ[𝕜] H} {k : ℕ}
      (hk : k ≤ finrank 𝕜 H) {u v : Fin k → H}
      (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
      RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜) ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := by
    set W := polarUnitary A with hW
    set R := spectralSqrt (absPositive A) with hR
    have hRsymm : R.IsSymmetric := (sqrtPositive (absPositive A)).isSymmetric
    have hRR : R ∘ₗ R = operatorAbs A := sqrtSquare (absPositive A)
    -- Pull the polar unitary across and split `|A|` symmetrically.
    have hterm : ∀ i, ⟪u i, A (v i)⟫_𝕜 = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := by
      intro i
      have h1 : A (v i) = W (operatorAbs A (v i)) := by
        have h := LinearMap.congr_fun (show A = (polarUnitary A : H →ₗ[𝕜] H) ∘ₗ operatorAbs A by ext x; exact (unitaryAction A x).symm) (v i)
        rw [LinearMap.comp_apply] at h
        exact h.trans rfl
      calc ⟪u i, A (v i)⟫_𝕜 = ⟪W (W.symm (u i)), W (operatorAbs A (v i))⟫_𝕜 := by
            rw [W.apply_symm_apply, ← h1]
        _ = ⟪W.symm (u i), operatorAbs A (v i)⟫_𝕜 := W.inner_map_map _ _
        _ = ⟪W.symm (u i), R (R (v i))⟫_𝕜 := by
            rw [← hRR]; rfl
        _ = ⟪R (W.symm (u i)), R (v i)⟫_𝕜 := (hRsymm (W.symm (u i)) (R (v i))).symm
    have hquad : ∀ x : H, ‖R x‖ ^ 2 = RCLike.re ⟪operatorAbs A x, x⟫_𝕜 := fun x =>
      sqrtNormSq (absPositive A) x
    have hterm_le : ∀ i, RCLike.re ⟪u i, A (v i)⟫_𝕜
        ≤ RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
          + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2 := by
      intro i
      rw [hterm i, ← hquad, ← hquad]
      have h1 : RCLike.re ⟪R (W.symm (u i)), R (v i)⟫_𝕜 ≤ ‖R (W.symm (u i))‖ * ‖R (v i)‖ :=
        (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      nlinarith [sq_nonneg (‖R (W.symm (u i))‖ - ‖R (v i)‖)]
    have hu' : Orthonormal 𝕜 (fun i => W.symm (u i)) := by
      rw [orthonormal_iff_ite] at hu ⊢
      intro i j
      rw [W.symm.inner_map_map]
      exact hu i j
    have htr1 := traceUpper (absPositive A).isSymmetric rfl hk hu'
    have htr2 := traceUpper (absPositive A).isSymmetric rfl hk hv
    rw [absEigenvalues A] at htr1 htr2
    rw [sumFilter hk (fun j => A.singularValues j)] at htr1 htr2
    calc RCLike.re (∑ i, ⟪u i, A (v i)⟫_𝕜)
        = ∑ i, RCLike.re ⟪u i, A (v i)⟫_𝕜 := map_sum _ _ _
      _ ≤ ∑ i, (RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜 / 2
            + RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜 / 2) :=
          Finset.sum_le_sum fun i _ => hterm_le i
      _ = (∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜) / 2
          + (∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
      _ ≤ (∑ i : Fin k, A.singularValues (i : ℕ)) / 2
          + (∑ i : Fin k, A.singularValues (i : ℕ)) / 2 := by
          have h1 : ∑ i, RCLike.re ⟪operatorAbs A (W.symm (u i)), W.symm (u i)⟫_𝕜
              ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr1
          have h2 : ∑ i, RCLike.re ⟪operatorAbs A (v i), v i⟫_𝕜
              ≤ ∑ i : Fin k, A.singularValues (i : ℕ) := htr2
          linarith
      _ = ∑ i : Fin k, A.singularValues (i : ℕ) := by ring


  have adjointApply (ι : E →ₗᵢ[𝕜] H) (x : E) :
      LinearMap.adjoint ι.toLinearMap (ι x) = x :=
    ext_inner_right 𝕜 fun y => by
      rw [LinearMap.adjoint_inner_left]
      exact ι.inner_map_map x y

  have adjointZero (ι : E →ₗᵢ[𝕜] H) {y : H}
      (hy : y ∈ (LinearMap.range ι.toLinearMap)ᗮ) :
      LinearMap.adjoint ι.toLinearMap y = 0 :=
    ext_inner_right 𝕜 fun z => by
      rw [LinearMap.adjoint_inner_left, inner_zero_left]
      exact Submodule.inner_left_of_mem_orthogonal
        (LinearMap.mem_range.mpr ⟨z, rfl⟩) hy
  have finrank_le_of_linearIsometry (ι : E →ₗᵢ[𝕜] H) :
      finrank 𝕜 E ≤ finrank 𝕜 H := by
    have hdimU : finrank 𝕜 (LinearMap.range ι.toLinearMap) = finrank 𝕜 E :=
      LinearMap.finrank_range_of_inj ι.injective
    have hsum := Submodule.finrank_add_finrank_orthogonal (LinearMap.range ι.toLinearMap)
    omega

  have finrank_orthogonal_range_linearIsometry (ι : E →ₗᵢ[𝕜] H) :
      finrank 𝕜 ((LinearMap.range ι.toLinearMap)ᗮ : Submodule 𝕜 H)
        = finrank 𝕜 H - finrank 𝕜 E := by
    have hdimU : finrank 𝕜 (LinearMap.range ι.toLinearMap) = finrank 𝕜 E :=
      LinearMap.finrank_range_of_inj ι.injective
    have hsum := Submodule.finrank_add_finrank_orthogonal (LinearMap.range ι.toLinearMap)
    omega

  let isometryPad (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) : Fin (finrank 𝕜 H) → H := fun i =>
    if h : (i : ℕ) < finrank 𝕜 E then ι (v ⟨(i : ℕ), h⟩)
    else
      (stdOrthonormalBasis 𝕜 ((LinearMap.range ι.toLinearMap)ᗮ : Submodule 𝕜 H)
        (Fin.cast (finrank_orthogonal_range_linearIsometry ι).symm
          ⟨(i : ℕ) - finrank 𝕜 E, by have := i.isLt; omega⟩) : H)

  have isometryPad_of_lt (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) {i : Fin (finrank 𝕜 H)}
      (h : (i : ℕ) < finrank 𝕜 E) : isometryPad ι v i = ι (v ⟨(i : ℕ), h⟩) :=
    dif_pos h

  have isometryPad_of_ge (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) {i : Fin (finrank 𝕜 H)}
      (h : ¬ (i : ℕ) < finrank 𝕜 E) :
      isometryPad ι v i
        = (stdOrthonormalBasis 𝕜 ((LinearMap.range ι.toLinearMap)ᗮ : Submodule 𝕜 H)
            (Fin.cast (finrank_orthogonal_range_linearIsometry ι).symm
              ⟨(i : ℕ) - finrank 𝕜 E, by have := i.isLt; omega⟩) : H) :=
    dif_neg h

  have isometryPad_mem_range (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) {i : Fin (finrank 𝕜 H)}
      (h : (i : ℕ) < finrank 𝕜 E) : isometryPad ι v i ∈ LinearMap.range ι.toLinearMap := by
    rw [isometryPad_of_lt ι v h]; exact ⟨_, rfl⟩

  have isometryPad_mem_orthogonal (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) {i : Fin (finrank 𝕜 H)}
      (h : ¬ (i : ℕ) < finrank 𝕜 E) :
      isometryPad ι v i ∈ (LinearMap.range ι.toLinearMap)ᗮ := by
    rw [isometryPad_of_ge ι v h]; exact SetLike.coe_mem _

  have orthonormal_isometryPad (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) : Orthonormal 𝕜 (isometryPad ι v) := by
    classical
    rw [orthonormal_iff_ite]
    intro i j
    by_cases hi : (i : ℕ) < finrank 𝕜 E
    · by_cases hj : (j : ℕ) < finrank 𝕜 E
      · rw [isometryPad_of_lt ι v hi, isometryPad_of_lt ι v hj, ι.inner_map_map,
          orthonormal_iff_ite.mp v.orthonormal]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (fun hc => hij (Fin.ext (by simpa using congrArg Fin.val hc))),
            if_neg hij]
      · rw [if_neg (fun hc : i = j => hj (hc ▸ hi))]
        exact Submodule.inner_right_of_mem_orthogonal (isometryPad_mem_range ι v hi)
          (isometryPad_mem_orthogonal ι v hj)
    · by_cases hj : (j : ℕ) < finrank 𝕜 E
      · rw [if_neg (fun hc : i = j => hi (hc ▸ hj))]
        exact Submodule.inner_left_of_mem_orthogonal (isometryPad_mem_range ι v hj)
          (isometryPad_mem_orthogonal ι v hi)
      · rw [isometryPad_of_ge ι v hi, isometryPad_of_ge ι v hj, ← Submodule.coe_inner,
          orthonormal_iff_ite.mp (stdOrthonormalBasis 𝕜
            ((LinearMap.range ι.toLinearMap)ᗮ : Submodule 𝕜 H)).orthonormal]
        by_cases hij : i = j
        · subst hij; rw [if_pos rfl, if_pos rfl]
        · rw [if_neg (fun hc => ?_), if_neg hij]
          rw [Fin.cast_inj] at hc
          have hval : (i : ℕ) - finrank 𝕜 E = (j : ℕ) - finrank 𝕜 E := by
            simpa using congrArg Fin.val hc
          have hi' := i.isLt
          have hj' := j.isLt
          exact hij (Fin.ext (by omega))

  let isometryPadBasis (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) :
      OrthonormalBasis (Fin (finrank 𝕜 H)) 𝕜 H :=
    OrthonormalBasis.mk (orthonormal_isometryPad ι v) (by
      refine (Submodule.eq_top_of_finrank_eq ?_).ge
      rw [finrank_span_eq_card (orthonormal_isometryPad ι v).linearIndependent,
        Fintype.card_fin])

  have isometryPadBasis_apply (ι : E →ₗᵢ[𝕜] H)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (i : Fin (finrank 𝕜 H)) :
      isometryPadBasis ι v i = isometryPad ι v i :=
    congrFun (OrthonormalBasis.coe_mk _ _) i

  have antitone_padZero {n m : ℕ} {μ : Fin n → ℝ} (hanti : Antitone μ)
      (hnonneg : ∀ i, 0 ≤ μ i) :
      Antitone (fun i : Fin m => if h : (i : ℕ) < n then μ ⟨(i : ℕ), h⟩ else 0) := by
    intro i j hij
    have hvij : (i : ℕ) ≤ (j : ℕ) := hij
    dsimp only
    by_cases hj : (j : ℕ) < n
    · have hi : (i : ℕ) < n := lt_of_le_of_lt hvij hj
      rw [dif_pos hi, dif_pos hj]
      exact hanti (Fin.mk_le_mk.mpr hvij)
    · rw [dif_neg hj]
      by_cases hi : (i : ℕ) < n
      · rw [dif_pos hi]; exact hnonneg _
      · rw [dif_neg hi]

  have isometryPadBasis_conj_apply (ι : E →ₗᵢ[𝕜] H)
      (G : E →ₗ[𝕜] E)
      (v : OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E) (μ : Fin (finrank 𝕜 E) → ℝ)
      (hv : ∀ j, G (v j) = ((μ j : ℝ) : 𝕜) • v j) (i : Fin (finrank 𝕜 H)) :
      (ι.toLinearMap ∘ₗ (G ∘ₗ LinearMap.adjoint ι.toLinearMap)) (isometryPadBasis ι v i)
        = (((if h : (i : ℕ) < finrank 𝕜 E then μ ⟨(i : ℕ), h⟩ else 0 : ℝ)) : 𝕜)
            • isometryPadBasis ι v i := by
    classical
    rw [isometryPadBasis_apply]
    by_cases h : (i : ℕ) < finrank 𝕜 E
    · simp only [dif_pos h, isometryPad_of_lt ι v h, LinearMap.comp_apply,
        adjointApply, hv, map_smul, LinearIsometry.coe_toLinearMap]
    · simp only [dif_neg h, isometryPad_of_ge ι v h, LinearMap.comp_apply,
        adjointZero ι (SetLike.coe_mem _),
        map_zero, zero_smul]

  have singularPad
      (ι : E →ₗᵢ[𝕜] H) (X : E →ₗ[𝕜] F) :
      (X ∘ₗ LinearMap.adjoint ι.toLinearMap).singularValues = X.singularValues := by
    classical
    set Y : H →ₗ[𝕜] F := X ∘ₗ LinearMap.adjoint ι.toLinearMap with hYdef
    -- the gram operator of `Y` is that of `X`, conjugated onto the range of `ι`
    have hgram : LinearMap.adjoint Y ∘ₗ Y =
        ι.toLinearMap ∘ₗ ((LinearMap.adjoint X ∘ₗ X) ∘ₗ LinearMap.adjoint ι.toLinearMap) := by
      rw [hYdef, LinearMap.adjoint_comp, LinearMap.adjoint_adjoint]
      ext x
      simp only [LinearMap.comp_apply]
    have hGX : (LinearMap.adjoint X ∘ₗ X).IsSymmetric := X.isSymmetric_adjoint_comp_self
    -- push its eigenbasis into `H` along `ι`, padding the complement with zeros
    have heq := sortedSpectrum
      Y.isSymmetric_adjoint_comp_self rfl (isometryPadBasis ι (hGX.eigenvectorBasis rfl))
      (antitone_padZero (hGX.eigenvalues_antitone rfl)
        (fun i => X.isPositive_adjoint_comp_self.nonneg_eigenvalues rfl i))
      (fun i => by
        rw [hgram]
        exact isometryPadBasis_conj_apply ι _ _ (hGX.eigenvalues rfl)
          (fun j => hGX.apply_eigenvectorBasis rfl j) i)
    -- three ranges of the index: inside `E`, the padding, and past `H`
    refine Finsupp.ext fun i => ?_
    rcases lt_or_ge i (finrank 𝕜 E) with hid | hid
    · have hin : i < finrank 𝕜 H := lt_of_lt_of_le hid (finrank_le_of_linearIsometry ι)
      rw [Y.singularValues_of_lt rfl hin, X.singularValues_of_lt rfl hid, heq]
      simp only [dif_pos hid]
    · rcases lt_or_ge i (finrank 𝕜 H) with hin | hin
      · rw [Y.singularValues_of_lt rfl hin, X.singularValues_of_finrank_le hid, heq]
        simp only [dif_neg (not_lt.mpr hid)]
        exact Real.sqrt_zero
      · rw [Y.singularValues_of_finrank_le hin, X.singularValues_of_finrank_le hid]

  have singularLeft (ι : F →ₗᵢ[𝕜] H) (X : H →ₗ[𝕜] F) :
      (ι.toLinearMap ∘ₗ X).singularValues = X.singularValues := by
    have hgram : (ι.toLinearMap ∘ₗ X).adjoint ∘ₗ (ι.toLinearMap ∘ₗ X) =
        X.adjoint ∘ₗ X := by
      ext x
      apply ext_inner_right 𝕜
      intro y
      simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_left]
      exact ι.inner_map_map (X x) (X y)
    have heigen :
        (ι.toLinearMap ∘ₗ X).isSymmetric_adjoint_comp_self.eigenvalues rfl =
          X.isSymmetric_adjoint_comp_self.eigenvalues rfl := by
      congr 1
    refine Finsupp.ext fun i => ?_
    rcases lt_or_ge i (finrank 𝕜 H) with hi | hi
    · rw [(ι.toLinearMap ∘ₗ X).singularValues_of_lt rfl hi,
        X.singularValues_of_lt rfl hi, heigen]
    · rw [(ι.toLinearMap ∘ₗ X).singularValues_of_finrank_le hi,
        X.singularValues_of_finrank_le hi]

  have zeroExtension_apply (A : E →ₗ[𝕜] F)
      (z : WithLp 2 (E × F)) :
      zeroExtension A z = WithLp.toLp 2 (0, A (WithLp.ofLp z).1) := rfl
  have zeroExtensionInr_apply (y : F) :
      zeroExtensionInr (𝕜 := 𝕜) (E := E) y = WithLp.toLp 2 (0, y) := rfl
  have zeroExtensionInl_adjoint_apply (z : WithLp 2 (E × F)) :
      LinearMap.adjoint (zeroExtensionInl (𝕜 := 𝕜) (F := F)).toLinearMap z = z.fst := by
    apply ext_inner_right 𝕜
    intro x
    rw [LinearMap.adjoint_inner_left]
    simp [zeroExtensionInl, WithLp.prod_inner_apply]

  have zeroSingular (A : E →ₗ[𝕜] F) :
      (zeroExtension A).singularValues = A.singularValues := by
    let ιE : E →ₗᵢ[𝕜] WithLp 2 (E × F) :=
      zeroExtensionInl (𝕜 := 𝕜) (E := E) (F := F)
    let ιF : F →ₗᵢ[𝕜] WithLp 2 (E × F) :=
      zeroExtensionInr (𝕜 := 𝕜) (E := E) (F := F)
    have hfactor : zeroExtension A =
        ιF.toLinearMap ∘ₗ
          (A ∘ₗ LinearMap.adjoint ιE.toLinearMap) := by
      ext z
      simp only [LinearMap.comp_apply, zeroExtension_apply, ιE, ιF,
        LinearIsometry.coe_toLinearMap, zeroExtensionInr_apply,
        zeroExtensionInl_adjoint_apply, WithLp.ofLp_fst]
    rw [hfactor]
    calc
      (ιF.toLinearMap ∘ₗ
          (A ∘ₗ LinearMap.adjoint ιE.toLinearMap)).singularValues =
          (A ∘ₗ LinearMap.adjoint ιE.toLinearMap).singularValues :=
        singularLeft ιF _
      _ = A.singularValues :=
        singularPad ιE A
  let u' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (0, u i)
  let v' : Fin k → WithLp 2 (E × F) :=
    fun i => WithLp.toLp 2 (v i, 0)
  have hu' : Orthonormal 𝕜 u' := by
    rw [orthonormal_iff_ite] at hu ⊢
    intro i j
    simpa [u', WithLp.prod_inner_apply] using hu i j
  have hv' : Orthonormal 𝕜 v' := by
    rw [orthonormal_iff_ite] at hv ⊢
    intro i j
    simpa [v', WithLp.prod_inner_apply] using hv i j
  have hfin : finrank 𝕜 (WithLp 2 (E × F)) =
      finrank 𝕜 E + finrank 𝕜 F := by
    calc
      finrank 𝕜 (WithLp 2 (E × F)) = finrank 𝕜 (E × F) :=
        (WithLp.linearEquiv 2 𝕜 (E × F)).finrank_eq
      _ = finrank 𝕜 E + finrank 𝕜 F := by
        simp [Module.finrank_prod]
  have hk' : k ≤ finrank 𝕜 (WithLp 2 (E × F)) := by
    rw [hfin]
    omega
  have h := squareUpper
    (A := zeroExtension A) hk' hu' hv'
  dsimp only [H] at h
  simpa [u', v', zeroExtension_apply, WithLp.prod_inner_apply,
    kyFanSum, zeroSingular] using h


end D5.S3.Quantum.Entanglement.FiniteSectorChannelOptimality
