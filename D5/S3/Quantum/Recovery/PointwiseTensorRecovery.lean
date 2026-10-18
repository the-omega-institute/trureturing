/- GID: D5/S3/Quantum/Recovery/PointwiseTensorRecovery
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/PointwiseTensorRecovery
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: An actual finite Kraus left inverse yields the full canonical pointwise tensor recovery factorization on the spectral support. -/

import D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
import D5.S3.Quantum.Recovery.PointwiseTensorGeometry
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.InnerProductSpace.Positive

noncomputable section
open scoped Matrix BigOperators ComplexOrder MatrixOrder TensorProduct
namespace Original8340InheritedCoreAttempt
open D5.S3.Quantum.Recovery.SpectralRecoveryCorrectness
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
open D5.S3.Quantum.Recovery.KrausLeftInverseNecessity
set_option autoImplicit false
set_option relaxedAutoImplicit false
variable {s t n d : Type*} [Fintype s] [DecidableEq s] [Fintype t]
  [Fintype n] [DecidableEq n] [Nonempty n] [Fintype d] [DecidableEq d]

set_option maxHeartbeats 3000000 in
theorem whole_pointwise_core_attempt (E : s → Matrix n d ℂ)
    (hTP : (∑ a, (E a)ᴴ * E a) = 1)
    (A : t → Matrix d n ℂ) (hA : (∑ b, (A b)ᴴ * A b) = 1)
    (hleft : ∀ X : Matrix d d ℂ,
      (∑ b, A b * (∑ a, E a * X * (E a)ᴴ) * (A b)ᴴ) = X)
    (v r : d) :
    let Q := ∑ a, E a * (E a)ᴴ
    let P := spectralSupport Q
    let W := spectralInverseSqrt Q
    let pi := fun T : Matrix d d ℂ => W * (∑ a, E a * T * (E a)ᴴ) * W
    let F := fun i j : d => (pi (Matrix.single i j 1)).toEuclideanLin
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
         (∑ a, E a * T * (E a)ᴴ).toEuclideanLin =
         (U.comp (TensorProduct.map sigma T.toEuclideanLin)).comp (LinearMap.adjoint (𝕜 := ℂ) (E := K0 ⊗[ℂ] EuclideanSpace ℂ d) (F := EuclideanSpace ℂ n) U)) := by
  let Q := ∑ a, E a * (E a)ᴴ
  let P := spectralSupport Q
  let W := spectralInverseSqrt Q
  let Y := fun T : Matrix d d ℂ => leftInverseObservable A T
  let NX := fun T : Matrix d d ℂ => ∑ a, E a * T * (E a)ᴴ
  have hQ : Q.PosSemidef := Matrix.nonneg_iff_posSemidef.mp
    (Finset.sum_nonneg fun a _ => (Matrix.posSemidef_self_mul_conjTranspose (E a)).nonneg)
  obtain ⟨hYE, hEY, hQY, hYQ, hWY, hSandwich, hWN, hPE, hPN⟩ :=
    kraus_left_inverse_spectral_relations E A hA hleft v
  have hcomm (T : Matrix d d ℂ) : Commute Q (Y T) :=
    (hQY T).trans (hYQ T).symm
  obtain ⟨hWs, hPs, hPP, hNorm⟩ := spectral_decoder_normalization E
  have hWself : Wᴴ = W := hWs
  have hPself : Pᴴ = P := hPs
  have hPid : P * P = P := hPP
  let pi := fun T : Matrix d d ℂ => W * NX T * W
  have hpi (T : Matrix d d ℂ) : pi T = P * Y T := hWN T
  have hPY (T : Matrix d d ℂ) : P * Y T = Y T * P :=
    ((hcomm T).cfc_real (fun x : ℝ => if x = 0 then 0 else 1)).eq
  have hpiP (T : Matrix d d ℂ) : pi T * P = pi T := by
    rw [hpi T]
    calc
      P * Y T * P = P * (Y T * P) := Matrix.mul_assoc _ _ _
      _ = P * (P * Y T) := by rw [← hPY T]
      _ = P * Y T := by rw [← Matrix.mul_assoc, hPP]
  have hPpi (T : Matrix d d ℂ) : P * pi T = pi T := by
    rw [hpi T, ← Matrix.mul_assoc, hPP]
  have hNY (T U : Matrix d d ℂ) : NX T * Y U = NX (T * U) := by
    have hEYprime (a : s) : (E a)ᴴ * Y U = U * (E a)ᴴ := by
      change (E a)ᴴ * leftInverseObservable A U = U * (E a)ᴴ
      exact hEY U a
    simp only [NX, Matrix.sum_mul, Matrix.mul_assoc]
    apply Finset.sum_congr rfl
    intro a ha
    exact congrArg (fun M : Matrix d n ℂ => E a * (T * M)) (hEYprime a)
  have hpiY (T U : Matrix d d ℂ) : pi (T * U) = pi T * Y U := by
    change W * NX (T * U) * W = (W * NX T * W) * Y U
    rw [← hNY T U]
    calc
      W * (NX T * Y U) * W = W * NX T * (Y U * W) := by
        simp only [Matrix.mul_assoc]
      _ = W * NX T * (W * Y U) := by rw [← hWY U]
      _ = (W * NX T * W) * Y U := by simp only [Matrix.mul_assoc]
  have hpi_mul (T U : Matrix d d ℂ) : pi T * pi U = pi (T * U) := by
    rw [hpi U, ← Matrix.mul_assoc, hpiP T, ← hpiY T U]
  let F := fun i j : d => (pi (Matrix.single i j 1)).toEuclideanLin
  let piL : Matrix d d ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := pi
      map_add' := by
        intro T U
        simp [pi, NX, Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c T
        change W * (∑ a, E a * (c • T) * (E a)ᴴ) * W =
          c • (W * NX T * W)
        simp only [NX, Matrix.mul_smul, Matrix.smul_mul]
        rw [← Finset.smul_sum, Matrix.mul_smul, Matrix.smul_mul] }
  have hpi0 : pi 0 = 0 := map_zero piL
  have hFmul (i j k l : d) :
      (F i j).comp (F k l) = if j = k then F i l else 0 := by
    have h := congrArg Matrix.toEuclideanLin
      (hpi_mul (Matrix.single i j 1) (Matrix.single k l 1))
    by_cases hjk : j = k
    · subst k
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        Matrix.single_mul_single_same, one_mul, ite_true, F] using h
    · have hz : Matrix.single i j (1 : ℂ) * Matrix.single k l (1 : ℂ) = 0 :=
        Matrix.single_mul_single_of_ne (c := (1 : ℂ)) (i := i) (j := j)
          (k := k) (h := hjk) (d := (1 : ℂ))
      simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
        hz, hpi0, map_zero, ite_false, F, hjk] using h
  have hFadj (i j : d) : (LinearMap.adjoint (𝕜 := ℂ) (E := EuclideanSpace ℂ n) (F := EuclideanSpace ℂ n) (F i j)) = F j i := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    congr 1
    simp only [pi, NX, Matrix.conjTranspose_mul, Matrix.conjTranspose_sum,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_single, star_one, hWself]
    simp only [Matrix.mul_assoc]
  have hFsum : (∑ i, F i i) = P.toEuclideanLin := by
    calc
      _ = (piL (∑ i, Matrix.single i i 1)).toEuclideanLin := by
        simp only [map_sum]; rfl
      _ = P.toEuclideanLin := by
        rw [Matrix.sum_single_one]
        change (pi (1 : Matrix d d ℂ)).toEuclideanLin = P.toEuclideanLin
        congr 1
        simpa only [pi, NX, Matrix.mul_one] using hSandwich
  have hPF (i j : d) : P.toEuclideanLin.comp (F i j) = F i j := by
    have h := congrArg Matrix.toEuclideanLin (hPpi (Matrix.single i j 1))
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, F] using h
  have hPQ : P * Q = Q := by
    have hPEprime (a : s) : P * E a = E a := by
      change spectralSupport (∑ a, E a * (E a)ᴴ) * E a = E a
      exact hPE a
    simp only [Q, Matrix.mul_sum, ← Matrix.mul_assoc]
    apply Finset.sum_congr rfl
    intro a ha
    exact congrArg (fun M : Matrix n d ℂ => M * (E a)ᴴ) (hPEprime a)
  have hQP : Q * P = Q := by
    have h := congrArg Matrix.conjTranspose hPQ
    simpa only [Matrix.conjTranspose_mul, hQ.isHermitian.eq, hPself] using h
  have hQpi (T : Matrix d d ℂ) : Q * pi T = NX T := by
    rw [hpi, ← Matrix.mul_assoc, hQP, hQY]
  have hpiQ (T : Matrix d d ℂ) : pi T * Q = NX T := by
    rw [hpi, Matrix.mul_assoc, hYQ, hPN]
  have hQF (i j : d) (x : EuclideanSpace ℂ n) :
      Q.toEuclideanLin (F i j x) = F i j (Q.toEuclideanLin x) := by
    have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin x)
      ((hQpi (Matrix.single i j 1)).trans (hpiQ (Matrix.single i j 1)).symm)
    simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same, LinearMap.comp_apply, F] using h
  have hWQ : W * Q = Q * W :=
    ((Commute.refl Q).cfc_real (fun q : ℝ => (Real.sqrt q)⁻¹)).eq
  have hQWW : Q * (W * W) = P := by
    rw [← Matrix.mul_assoc, ← hWQ, Matrix.mul_assoc, ← Matrix.mul_assoc W Q W, hSandwich]
  have hWWQ : (W * W) * Q = P := by
    rw [Matrix.mul_assoc, hWQ, ← Matrix.mul_assoc, hSandwich]
  have hRF (x : EuclideanSpace ℂ n) :
      F v v ((W * W).toEuclideanLin x) = (W * W).toEuclideanLin (F v v x) := by
    have hc : Commute Q (pi (Matrix.single v v 1)) :=
      (hQpi _).trans (hpiQ _).symm
    have hw : W * pi (Matrix.single v v 1) = pi (Matrix.single v v 1) * W :=
      (hc.cfc_real (fun q : ℝ => (Real.sqrt q)⁻¹)).eq
    have hmm : pi (Matrix.single v v 1) * (W * W) =
        (W * W) * pi (Matrix.single v v 1) := by
      calc
        _ = (pi (Matrix.single v v 1) * W) * W := (Matrix.mul_assoc _ _ _).symm
        _ = (W * pi (Matrix.single v v 1)) * W :=
          congrArg (fun M : Matrix n n ℂ => M * W) hw.symm
        _ = W * (pi (Matrix.single v v 1) * W) := Matrix.mul_assoc _ _ _
        _ = W * (W * pi (Matrix.single v v 1)) :=
          congrArg (fun M : Matrix n n ℂ => W * M) hw.symm
        _ = _ := (Matrix.mul_assoc _ _ _).symm
    have h := congrArg (fun M : Matrix n n ℂ => M.toEuclideanLin x) hmm
    simpa only [F, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same,
      LinearMap.comp_apply] using h
  have hNtrace (T : Matrix d d ℂ) : Matrix.trace (NX T) = Matrix.trace T := by
    calc
      _ = ∑ a, Matrix.trace (((E a)ᴴ * E a) * T) := by
        simp only [NX, Matrix.trace_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
      _ = Matrix.trace ((∑ a, (E a)ᴴ * E a) * T) := by
        simp only [Matrix.sum_mul, Matrix.trace_sum]
      _ = Matrix.trace T := by rw [hTP, Matrix.one_mul]
  have hTraceQF : LinearMap.trace ℂ (EuclideanSpace ℂ n)
      (Q.toEuclideanLin.comp (F v v)) = 1 := by
    have hh : Q.toEuclideanLin.comp (F v v) = (NX (Matrix.single v v 1)).toEuclideanLin := by
      have h := congrArg Matrix.toEuclideanLin (hQpi (Matrix.single v v 1))
      simpa only [F, Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h
    rw [hh, Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq, hNtrace]
    simp
  have hpiExpand (T : Matrix d d ℂ) (x : EuclideanSpace ℂ n) :
      (pi T).toEuclideanLin x = ∑ i, ∑ j, T i j • F i j x := by
    have hs (i j : d) : Matrix.single i j (T i j) = T i j • Matrix.single i j 1 := by simp
    have ht : T = ∑ i, ∑ j, T i j • Matrix.single i j 1 := by
      calc
        T = ∑ i, ∑ j, Matrix.single i j (T i j) := Matrix.matrix_eq_sum_single T
        _ = _ := by simp_rw [hs]
    calc
      _ = (piL (∑ i, ∑ j, T i j • Matrix.single i j 1)).toEuclideanLin x :=
        congrArg (fun M : Matrix d d ℂ => (piL M).toEuclideanLin x) ht
      _ = ∑ i, ∑ j, T i j • (piL (Matrix.single i j 1)).toEuclideanLin x := by
        simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
      _ = ∑ i, ∑ j, T i j • (pi (Matrix.single i j 1)).toEuclideanLin x := by
        rfl
      _ = _ := by
        rfl
  have hNF (T : Matrix d d ℂ) : (NX T).toEuclideanLin =
      Q.toEuclideanLin.comp (∑ i, ∑ j, T i j • F i j) := by
    have hx : (pi T).toEuclideanLin = ∑ i, ∑ j, T i j • F i j := by
      apply LinearMap.ext
      intro x
      simpa only [LinearMap.sum_apply, LinearMap.smul_apply] using hpiExpand T x
    rw [← hx]
    have h := congrArg Matrix.toEuclideanLin (hQpi T)
    exact (by simpa only [Matrix.toEuclideanLin, Matrix.toLpLin_mul_same] using h.symm)
  exact Original8340PointwiseGeometry.matrix_unit_pointwise_tensor F P Q (W * W) NX v
    hFmul hFadj hFsum hPF hPself hPid hQ hQF hQWW hWWQ hRF hTraceQF hNF

#print axioms whole_pointwise_core_attempt
end Original8340InheritedCoreAttempt
