/- GID: D5/S3/Quantum/Recovery/PointwiseTensorGeometry
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PointwiseTensorGeometry
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Explicit matrix units construct the canonical tensor isometry and a positive trace-one invertible multiplicity operator. -/

import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder TensorProduct
namespace Original8340PointwiseGeometry
set_option autoImplicit false
set_option relaxedAutoImplicit false
variable {n d : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
  [Fintype d] [DecidableEq d]

set_option maxHeartbeats 3000000 in
/-- Canonical tensor geometry and positive multiplicity operator of a matrix-unit system. -/
theorem matrix_unit_pointwise_tensor
    (F : d → d → EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n)
    (P Q R : Matrix n n ℂ) (NX : Matrix d d ℂ → Matrix n n ℂ) (v : d)
    (hFmul : ∀ i j k l, (F i j).comp (F k l) = if j = k then F i l else 0)
    (hFadj : ∀ i j, LinearMap.adjoint (F i j) = F j i)
    (hFsum : (∑ i, F i i) = P.toEuclideanLin)
    (hPF : ∀ i j, P.toEuclideanLin.comp (F i j) = F i j)
    (hPself : Pᴴ = P) (hPid : P * P = P) (hQ : Q.PosSemidef)
    (hQF : ∀ i j x, Q.toEuclideanLin (F i j x) = F i j (Q.toEuclideanLin x))
    (hQR : Q * R = P) (hRQ : R * Q = P)
    (hRF : ∀ x, F v v (R.toEuclideanLin x) = R.toEuclideanLin (F v v x))
    (hTraceQF : LinearMap.trace ℂ (EuclideanSpace ℂ n)
      (Q.toEuclideanLin.comp (F v v)) = 1)
    (hNF : ∀ T, (NX T).toEuclideanLin =
      Q.toEuclideanLin.comp (∑ i, ∑ j, T i j • F i j)) :
    let E0 := LinearMap.range P.toEuclideanLin
    let K0 := LinearMap.range (F v v)
    letI : NormedAddCommGroup (K0 ⊗[ℂ] EuclideanSpace ℂ d) :=
      TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ d)
    letI : InnerProductSpace ℂ (K0 ⊗[ℂ] EuclideanSpace ℂ d) :=
      TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ d)
    ∃ Theta : K0 ⊗[ℂ] EuclideanSpace ℂ d ≃ₗᵢ[ℂ] E0,
      ∃ B : EuclideanSpace ℂ n →ₗ[ℂ] (d → K0),
      ∃ sigma sigmaInv : K0 →ₗ[ℂ] K0,
      (∀ (w : K0) (i : d),
        (Theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) : EuclideanSpace ℂ n) = F i v w) ∧
      (∀ x : E0, Theta.symm x = ∑ i, B x i ⊗ₜ[ℂ] EuclideanSpace.single i 1) ∧
      (∀ (y : EuclideanSpace ℂ n) (i : d), (B y i : EuclideanSpace ℂ n) = F v i y) ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := E0) Theta.toLinearMap) = Theta.symm.toLinearMap ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := E0) (F := EuclideanSpace ℂ n) E0.subtype).comp E0.subtype = LinearMap.id ∧
      E0.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := E0) (F := EuclideanSpace ℂ n) E0.subtype) = P.toEuclideanLin ∧
      (LinearMap.adjoint (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ n) K0.subtype).comp K0.subtype = LinearMap.id ∧
      K0.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ n) K0.subtype) = F v v ∧
      (∀ w : K0, (sigma w : EuclideanSpace ℂ n) = Q.toEuclideanLin w) ∧
      LinearMap.IsPositive (𝕜 := ℂ) (E := K0) sigma ∧
      (∀ w : K0, w ≠ 0 → 0 < (inner ℂ w (sigma w)).re) ∧
      sigma.comp sigmaInv = LinearMap.id ∧
      sigmaInv.comp sigma = LinearMap.id ∧
      LinearMap.trace ℂ K0 sigma = 1 ∧
      (∀ z : K0 ⊗[ℂ] EuclideanSpace ℂ d,
        Q.toEuclideanLin (Theta z : EuclideanSpace ℂ n) =
        (Theta (TensorProduct.map sigma LinearMap.id z) : EuclideanSpace ℂ n)) ∧
      (let U : K0 ⊗[ℂ] EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ n :=
        E0.subtype.comp Theta.toLinearMap
       ∀ T : Matrix d d ℂ,
         (NX T).toEuclideanLin =
         (U.comp (TensorProduct.map sigma T.toEuclideanLin)).comp (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := EuclideanSpace ℂ n) U)) ∧
      (∀ w : K0, (sigmaInv w : EuclideanSpace ℂ n) = R.toEuclideanLin w) := by
  let E0 := LinearMap.range P.toEuclideanLin
  let K0 := LinearMap.range (F v v)
  let : NormedAddCommGroup (K0 ⊗[ℂ] EuclideanSpace ℂ d) :=
    TensorProduct.instNormedAddCommGroup (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ d)
  let : InnerProductSpace ℂ (K0 ⊗[ℂ] EuclideanSpace ℂ d) :=
    TensorProduct.instInnerProductSpace (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ d)
  have hF_into_E (i j : d) (x : EuclideanSpace ℂ n) : F i j x ∈ E0 := by
    refine ⟨F i j x, ?_⟩
    exact congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f x) (hPF i j)
  let col : d → K0 →ₗ[ℂ] E0 := fun i =>
    ((F i v).codRestrict E0 (hF_into_E i v)).comp K0.subtype
  let C : K0 ⊗[ℂ] EuclideanSpace ℂ d ≃ₗ[ℂ] (d → K0) :=
    (TensorProduct.congr (LinearEquiv.refl ℂ K0)
      (EuclideanSpace.equiv d ℂ).toLinearEquiv).trans
      (TensorProduct.piScalarRight ℂ ℂ K0 d)
  let S : (d → K0) →ₗ[ℂ] E0 := ∑ i, (col i).comp (LinearMap.proj i)
  have hcolMap (j : d) :
      E0.subtype.comp (col j) = (F j v).comp K0.subtype := by
    dsimp only [col]
    rw [← LinearMap.comp_assoc, LinearMap.subtype_comp_codRestrict]
  have hcolApply (j : d) (u : K0) :
      (col j u : EuclideanSpace ℂ n) = F j v (u : EuclideanSpace ℂ n) := by
    have h := congrArg (fun f : K0 →ₗ[ℂ] EuclideanSpace ℂ n => f u) (hcolMap j)
    simpa only [LinearMap.comp_apply, Submodule.subtype_apply] using h
  have hSsingle (i : d) (w : K0) : S (Pi.single i w) = col i w := by
    simp only [S, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
    · intro j hj hji
      simp [hji]
    · simp
  have hC (w : K0) (i : d) : C (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) = Pi.single i w := by
    ext j
    by_cases hji : j = i
    · subst j
      simp [C]
    · simp [C, hji]
  have hPAdj : (LinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ n) (F := EuclideanSpace ℂ n) P.toEuclideanLin) = P.toEuclideanLin := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hPself]
  have hPfix (x : E0) : P.toEuclideanLin (x : EuclideanSpace ℂ n) = x := by
    obtain ⟨y, hy⟩ := x.property
    change P.toEuclideanLin y = (x : EuclideanSpace ℂ n) at hy
    have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin y) hPid
    simp only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply] at h
    change P.toEuclideanLin (P.toEuclideanLin y) = P.toEuclideanLin y at h
    simpa only [hy] using h
  have hKfix (w : K0) : F v v (w : EuclideanSpace ℂ n) = w := by
    obtain ⟨y, hy⟩ := w.property
    have h := congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f y)
      (hFmul v v v v)
    simpa only [LinearMap.comp_apply, ite_true, hy] using h
  have hKintoE (w : K0) : (w : EuclideanSpace ℂ n) ∈ E0 := by
    obtain ⟨y, hy⟩ := w.property
    exact hy ▸ hF_into_E v v y
  have hFintoK (i : d) (x : EuclideanSpace ℂ n) : F v i x ∈ K0 := by
    refine ⟨F v i x, ?_⟩
    have h := congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f x)
      (hFmul v v v i)
    simpa only [LinearMap.comp_apply, ite_true] using h
  let back : d → EuclideanSpace ℂ n →ₗ[ℂ] K0 := fun i =>
    (F v i).codRestrict K0 (hFintoK i)
  let B : EuclideanSpace ℂ n →ₗ[ℂ] (d → K0) := LinearMap.pi back
  have hB (x : EuclideanSpace ℂ n) (i : d) :
      (B x i : EuclideanSpace ℂ n) = F v i x := by
    simp only [B, LinearMap.pi_apply, back, LinearMap.codRestrict_apply]
  have hS (f : d → K0) : (S f : EuclideanSpace ℂ n) =
      ∑ i, F i v (f i : EuclideanSpace ℂ n) := by
    have h : S f = ∑ i, col i (f i) := by
      simp only [S, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [h, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun i _ => hcolApply i (f i)
  have hBS (f : d → K0) : B (S f : EuclideanSpace ℂ n) = f := by
    funext i
    apply Subtype.ext
    rw [hB, hS, map_sum]
    calc
      (∑ j, F v i (F j v (f j : EuclideanSpace ℂ n))) =
          ∑ j, if i = j then (f j : EuclideanSpace ℂ n) else 0 := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [← LinearMap.comp_apply, hFmul]
        by_cases hij : i = j
        · subst j
          simp only [ite_true, hKfix]
        · simp only [hij, ite_false, LinearMap.zero_apply]
      _ = (f i : EuclideanSpace ℂ n) := by simp
  have hSB (x : E0) : S (B (x : EuclideanSpace ℂ n)) = x := by
    apply Subtype.ext
    rw [hS]
    calc
      _ = ∑ i, F i i (x : EuclideanSpace ℂ n) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hB, ← LinearMap.comp_apply, hFmul]
        simp only [ite_true]
      _ = (∑ i, F i i) (x : EuclideanSpace ℂ n) := by simp only [LinearMap.sum_apply]
      _ = (x : EuclideanSpace ℂ n) := by rw [hFsum, hPfix]
  have hCinv (f : d → K0) : C.symm f =
      ∑ i, f i ⊗ₜ[ℂ] EuclideanSpace.single i 1 := by
    apply C.injective
    rw [C.apply_symm_apply, map_sum]
    simp_rw [hC]
    ext j
    simp
  have hExpand (z : K0 ⊗[ℂ] EuclideanSpace ℂ d) :
      z = ∑ i, C z i ⊗ₜ[ℂ] EuclideanSpace.single i 1 := by
    simpa only [C.symm_apply_apply] using hCinv (C z)
  let theta := S.comp C.toLinearMap
  let psi := C.symm.toLinearMap.comp (B.comp E0.subtype)
  have htheta (w : K0) (i : d) : theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) = col i w := by
    simp only [theta, LinearMap.comp_apply, LinearEquiv.coe_coe, hC, hSsingle]
  have hPsiTheta (z : K0 ⊗[ℂ] EuclideanSpace ℂ d) : psi (theta z) = z := by
    simp only [psi, theta, LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
      hBS, C.symm_apply_apply]
  have hThetaPsi (x : E0) : theta (psi x) = x := by
    simp only [psi, theta, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, C.apply_symm_apply, hSB]
  have hColInner (i j : d) (w u : K0) :
      inner ℂ (col i w) (col j u) = if i = j then inner ℂ w u else 0 := by
    change inner ℂ (col i w : EuclideanSpace ℂ n)
      (col j u : EuclideanSpace ℂ n) = _
    rw [hcolApply, hcolApply, ← LinearMap.adjoint_inner_right, hFadj,
      ← LinearMap.comp_apply, hFmul]
    by_cases hij : i = j
    · subst j
      simp only [ite_true, hKfix]
      rfl
    · simp only [hij, ite_false, LinearMap.zero_apply, inner_zero_right]
  let e : d → EuclideanSpace ℂ d := fun i => EuclideanSpace.single i (1 : ℂ)
  have hInner (z z' : K0 ⊗[ℂ] EuclideanSpace ℂ d) :
      inner ℂ (theta z) (theta z') = inner ℂ z z' := by
    have ht (x : K0 ⊗[ℂ] EuclideanSpace ℂ d) : theta x = ∑ i, col i (C x i) := by
      simp only [theta, LinearMap.comp_apply, S, LinearMap.sum_apply,
        LinearMap.proj_apply, LinearEquiv.coe_coe]
    have hThetaCoeff : inner ℂ (theta z) (theta z') =
        ∑ i, inner ℂ (C z i) (C z' i) := by
      calc
        _ = inner ℂ (∑ i, col i (C z i)) (∑ j, col j (C z' j)) :=
          congrArg₂ (inner ℂ) (ht z) (ht z')
        _ = ∑ i, inner ℂ (col i (C z i)) (∑ j, col j (C z' j)) :=
          sum_inner (𝕜 := ℂ) (E := E0) Finset.univ _ _
        _ = ∑ i, ∑ j, inner ℂ (col i (C z i)) (col j (C z' j)) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact inner_sum (𝕜 := ℂ) (E := E0) Finset.univ _ _
        _ = ∑ i, inner ℂ (C z i) (C z' i) := by
          simp_rw [hColInner]
          simp
    have hTensorCoeff : inner ℂ z z' =
        ∑ i, inner ℂ (C z i) (C z' i) := by
      calc
        _ = inner ℂ (∑ i, C z i ⊗ₜ[ℂ] e i) (∑ j, C z' j ⊗ₜ[ℂ] e j) :=
          congrArg₂ (inner ℂ) (hExpand z) (hExpand z')
        _ = ∑ i, inner ℂ (C z i ⊗ₜ[ℂ] e i) (∑ j, C z' j ⊗ₜ[ℂ] e j) :=
          sum_inner (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) Finset.univ _ _
        _ = ∑ i, ∑ j, inner ℂ (C z i ⊗ₜ[ℂ] e i) (C z' j ⊗ₜ[ℂ] e j) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact inner_sum (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) Finset.univ _ _
        _ = ∑ i, ∑ j, inner ℂ (C z i) (C z' j) * inner ℂ (e i) (e j) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact TensorProduct.inner_tmul (E := K0) (F := EuclideanSpace ℂ d)
            ℂ (C z i) (C z' j) (e i) (e j)
        _ = ∑ i, inner ℂ (C z i) (C z' i) := by
          have he (i j : d) : inner ℂ (e i) (e j) = if i = j then 1 else 0 := by
            simp only [e, EuclideanSpace.inner_single_left, map_one, one_mul,
              PiLp.single_apply]
          simp_rw [he]
          simp
    exact hThetaCoeff.trans hTensorCoeff.symm
  let eqv : K0 ⊗[ℂ] EuclideanSpace ℂ d ≃ₗ[ℂ] E0 :=
    { theta with invFun := psi, left_inv := hPsiTheta, right_inv := hThetaPsi }
  let Theta : K0 ⊗[ℂ] EuclideanSpace ℂ d ≃ₗᵢ[ℂ] E0 :=
    LinearEquiv.isometryOfInner (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d)
      (E' := E0) eqv (by
        intro x y
        change inner ℂ (theta x) (theta y) = inner ℂ x y
        exact hInner x y)
  have hThetaMap : Theta.toLinearMap = theta := rfl
  have hThetaInv : Theta.symm.toLinearMap = psi := rfl
  have hAdjTheta : (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := E0) Theta.toLinearMap) = Theta.symm.toLinearMap :=
    Theta.adjoint_toLinearMap_eq_symm
  let pE : EuclideanSpace ℂ n →ₗ[ℂ] E0 := P.toEuclideanLin.rangeRestrict
  let pK : EuclideanSpace ℂ n →ₗ[ℂ] K0 := (F v v).rangeRestrict
  have hpE (x : EuclideanSpace ℂ n) : (pE x : EuclideanSpace ℂ n) = P.toEuclideanLin x := rfl
  have hpK (x : EuclideanSpace ℂ n) : (pK x : EuclideanSpace ℂ n) = F v v x := rfl
  have hAdjE : (LinearMap.adjoint (𝕜 := ℂ) (E := E0) (F := EuclideanSpace ℂ n) E0.subtype) = pE := by
    symm
    apply (LinearMap.eq_adjoint_iff pE E0.subtype).mpr
    intro x y
    change inner ℂ (pE x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ n) = _
    rw [hpE, ← LinearMap.adjoint_inner_right, hPAdj, hPfix]
    rfl
  have hAdjK : (LinearMap.adjoint (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ n) K0.subtype) = pK := by
    symm
    apply (LinearMap.eq_adjoint_iff pK K0.subtype).mpr
    intro x y
    change inner ℂ (pK x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ n) = _
    rw [hpK, ← LinearMap.adjoint_inner_right, hFadj, hKfix]
    rfl
  have hEleft : (LinearMap.adjoint (𝕜 := ℂ) (E := E0) (F := EuclideanSpace ℂ n) E0.subtype).comp E0.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [hAdjE, LinearMap.comp_apply, LinearMap.id_apply,
      Submodule.subtype_apply, hpE, hPfix]
  have hEright : E0.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := E0) (F := EuclideanSpace ℂ n) E0.subtype) = P.toEuclideanLin := by
    apply LinearMap.ext
    intro x
    simp only [hAdjE, LinearMap.comp_apply, Submodule.subtype_apply, hpE]
  have hKleft : (LinearMap.adjoint (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ n) K0.subtype).comp K0.subtype = LinearMap.id := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp only [hAdjK, LinearMap.comp_apply, LinearMap.id_apply,
      Submodule.subtype_apply, hpK, hKfix]
  have hKright : K0.subtype.comp (LinearMap.adjoint (𝕜 := ℂ) (E := K0) (F := EuclideanSpace ℂ n) K0.subtype) = F v v := by
    apply LinearMap.ext
    intro x
    simp only [hAdjK, LinearMap.comp_apply, Submodule.subtype_apply, hpK]
  have hQintoK (w : K0) : Q.toEuclideanLin (w : EuclideanSpace ℂ n) ∈ K0 := by
    refine ⟨Q.toEuclideanLin (w : EuclideanSpace ℂ n), ?_⟩
    rw [← hQF, hKfix]
  let sigma : K0 →ₗ[ℂ] K0 :=
    (Q.toEuclideanLin.comp K0.subtype).codRestrict K0 hQintoK
  have hSigma (w : K0) : (sigma w : EuclideanSpace ℂ n) = Q.toEuclideanLin w := rfl
  have hQpositive : LinearMap.IsPositive (𝕜 := ℂ) (E := EuclideanSpace ℂ n) Q.toEuclideanLin := Matrix.isPositive_toEuclideanLin_iff.mpr hQ
  have hSigmaPositive : LinearMap.IsPositive (𝕜 := ℂ) (E := K0) sigma := by
    constructor
    · intro x y
      change inner ℂ (sigma x : EuclideanSpace ℂ n) (y : EuclideanSpace ℂ n) =
        inner ℂ (x : EuclideanSpace ℂ n) (sigma y : EuclideanSpace ℂ n)
      rw [hSigma, hSigma]
      exact hQpositive.isSymmetric x y
    · intro x
      change 0 ≤ (inner ℂ (sigma x : EuclideanSpace ℂ n) (x : EuclideanSpace ℂ n)).re
      rw [hSigma]
      exact hQpositive.re_inner_nonneg_left x
  have hRintoK (w : K0) : R.toEuclideanLin (w : EuclideanSpace ℂ n) ∈ K0 := by
    refine ⟨R.toEuclideanLin (w : EuclideanSpace ℂ n), ?_⟩
    rw [hRF, hKfix]
  let sigmaInv : K0 →ₗ[ℂ] K0 :=
    (R.toEuclideanLin.comp K0.subtype).codRestrict K0 hRintoK
  have hSigmaInv (w : K0) : (sigmaInv w : EuclideanSpace ℂ n) =
      R.toEuclideanLin w := rfl
  have hInvRight : sigma.comp sigmaInv = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hSigma, hSigmaInv]
    calc
      _ = P.toEuclideanLin (w : EuclideanSpace ℂ n) := by
        have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin (w : EuclideanSpace ℂ n)) hQR
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
      _ = _ := hPfix ⟨w, hKintoE w⟩
  have hInvLeft : sigmaInv.comp sigma = LinearMap.id := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hSigma, hSigmaInv]
    calc
      _ = P.toEuclideanLin (w : EuclideanSpace ℂ n) := by
        have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin (w : EuclideanSpace ℂ n)) hRQ
        simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply] using h
      _ = _ := hPfix ⟨w, hKintoE w⟩
  have hStrict (w : K0) (hw : w ≠ 0) : 0 < (inner ℂ w (sigma w)).re := by
    have hn := hSigmaPositive.re_inner_nonneg_right w
    apply lt_of_le_of_ne hn
    intro hz
    have hr : (inner ℂ w (sigma w)).re = 0 := hz.symm
    have hi : inner ℂ w (sigma w) = 0 := by
      apply Complex.ext
      · exact hr
      · exact (RCLike.nonneg_iff (K := ℂ)).mp (hSigmaPositive.inner_nonneg_right w) |>.2
    have hqzero : Q.toEuclideanLin (w : EuclideanSpace ℂ n) = 0 := by
      have hc : inner ℂ (w : EuclideanSpace ℂ n) (Q.toEuclideanLin w) = 0 := by
        change inner ℂ (w : EuclideanSpace ℂ n) (sigma w : EuclideanSpace ℂ n) = 0 at hi
        simpa only [hSigma] using hi
      have hc' : star (w : EuclideanSpace ℂ n).ofLp ⬝ᵥ
          (Q *ᵥ (w : EuclideanSpace ℂ n).ofLp) = 0 := by
        simpa only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin,
          Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct_comm] using hc
      have hz' := (hQ.dotProduct_mulVec_zero_iff (x := (w : EuclideanSpace ℂ n).ofLp)).mp hc'
      ext i
      have h := congrFun hz' i
      simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply] using h
    have hs : sigma w = 0 := by apply Subtype.ext; simpa only [hSigma, Submodule.coe_zero] using hqzero
    have h := congrArg (fun f : K0 →ₗ[ℂ] K0 => f w) hInvLeft
    simp only [LinearMap.comp_apply, LinearMap.id_apply, hs, map_zero] at h
    exact hw h.symm
  have hTrace : LinearMap.trace ℂ K0 sigma = 1 := by
    calc
      _ = LinearMap.trace ℂ K0 ((sigma.comp pK).comp K0.subtype) := by
        rw [LinearMap.comp_assoc, ← hAdjK, hKleft, LinearMap.comp_id]
      _ = LinearMap.trace ℂ (EuclideanSpace ℂ n) (K0.subtype.comp (sigma.comp pK)) :=
        LinearMap.trace_comp_comm' _ _
      _ = LinearMap.trace ℂ (EuclideanSpace ℂ n) (Q.toEuclideanLin.comp (F v v)) := rfl
      _ = 1 := hTraceQF
  have hthetaGeneral (w : K0) (z : EuclideanSpace ℂ d) :
      (theta (w ⊗ₜ[ℂ] z) : EuclideanSpace ℂ n) = ∑ i, z i • F i v w := by
    rw [show theta (w ⊗ₜ[ℂ] z) = S (C (w ⊗ₜ[ℂ] z)) from rfl, hS]
    apply Finset.sum_congr rfl
    intro i hi
    have hcoord : C (w ⊗ₜ[ℂ] z) i = z i • w := by simp [C]
    rw [hcoord, Submodule.coe_smul, map_smul]
  let U : K0 ⊗[ℂ] EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ n :=
        E0.subtype.comp Theta.toLinearMap
  have hU (z : K0 ⊗[ℂ] EuclideanSpace ℂ d) : U z = (theta z : EuclideanSpace ℂ n) := rfl
  have hUadj (y : EuclideanSpace ℂ n) : (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := EuclideanSpace ℂ n) U) y = C.symm (B y) := by
    rw [LinearMap.adjoint_comp, hAdjTheta, hAdjE]
    simp only [hThetaInv, psi, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply]
    congr 1
    funext i
    apply Subtype.ext
    rw [hB, hpE, hB]
    have hFP : (F v i).comp P.toEuclideanLin = F v i := by
      have h := congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => LinearMap.adjoint f) (hPF i v)
      simpa only [LinearMap.adjoint_comp, hPAdj, hFadj] using h
    exact congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f y) hFP
  have hIntertwine (z : K0 ⊗[ℂ] EuclideanSpace ℂ d) :
      Q.toEuclideanLin (U z) = U (TensorProduct.map sigma LinearMap.id z) := by
    have hb (w : K0) (i : d) :
        Q.toEuclideanLin (U (w ⊗ₜ[ℂ] EuclideanSpace.single i 1)) =
        U (TensorProduct.map sigma LinearMap.id (w ⊗ₜ[ℂ] EuclideanSpace.single i 1)) := by
      simp only [TensorProduct.map_tmul, LinearMap.id_apply, hU, htheta,
        hcolApply, hSigma, hQF]
    calc
      _ = ∑ i, Q.toEuclideanLin (U (C z i ⊗ₜ[ℂ] EuclideanSpace.single i 1)) := by
        conv_lhs => rw [hExpand z]
        rw [map_sum, map_sum]
      _ = ∑ i, U (TensorProduct.map sigma LinearMap.id
          (C z i ⊗ₜ[ℂ] EuclideanSpace.single i 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hb (C z i) i
      _ = U (TensorProduct.map sigma LinearMap.id z) := by
        conv_rhs => rw [hExpand z]
        rw [map_sum, map_sum]
  have hFactor (T : Matrix d d ℂ) :
      (NX T).toEuclideanLin = (U.comp (TensorProduct.map sigma T.toEuclideanLin)).comp (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := EuclideanSpace ℂ n) U) := by
    apply LinearMap.ext
    intro y
    symm
    simp only [LinearMap.comp_apply]
    rw [hUadj, hCinv, map_sum, map_sum]
    simp only [TensorProduct.map_tmul, hU]
    simp_rw [hthetaGeneral, hSigma, hB]
    have he (j i : d) : T.toEuclideanLin (EuclideanSpace.single j 1) i = T i j := by
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
        dotProduct, EuclideanSpace.single]
    simp_rw [he]
    calc
      _ = ∑ j, ∑ i, T i j • Q.toEuclideanLin (F i j y) := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro i hi
        have hm : F i v (F v j y) = F i j y := by
          have h := congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f y)
            (hFmul i v v j)
          simpa only [LinearMap.comp_apply, ite_true] using h
        exact congrArg (fun x : EuclideanSpace ℂ n => T i j • x)
          ((hQF i v (F v j y)).symm.trans (congrArg Q.toEuclideanLin hm))
      _ = Q.toEuclideanLin (∑ i, ∑ j, T i j • F i j y) := by
        rw [Finset.sum_comm]
        simp only [map_sum, map_smul]
      _ = (NX T).toEuclideanLin y := by
        have h := congrArg (fun f : EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n => f y) (hNF T)
        simpa only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h.symm
  refine ⟨Theta, B, sigma, sigmaInv, ?_, ?_, hB, hAdjTheta,
    hEleft, hEright, hKleft, hKright, hSigma, hSigmaPositive, hStrict,
    hInvRight, hInvLeft, hTrace, ?_, hFactor, hSigmaInv⟩
  · intro w i
    rw [show Theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) =
      theta (w ⊗ₜ[ℂ] EuclideanSpace.single i 1) from rfl, htheta, hcolApply]
  · intro x
    exact hCinv (B x)
  · exact hIntertwine

end Original8340PointwiseGeometry
