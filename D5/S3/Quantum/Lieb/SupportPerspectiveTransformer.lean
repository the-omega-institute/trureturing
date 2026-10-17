/- GID: D5/S3/Quantum/Lieb/SupportPerspectiveTransformer
   generality: G
   mirror-B: D5/B/S3/Quantum/Lieb/SupportPerspectiveTransformer
   mirror-E: none(waiver:finite-spectral-proof)
   anchors: []
   utility: none
   digest: The supported spectral perspective contracts under every finite complex-linear positive map with exact kernel inclusion. -/



import D5.S3.Quantum.Lieb.SupportPerspectiveTransport
import Mathlib.LinearAlgebra.Complex.Module

/-!
Source candidate; current elaboration, kernel and axiom checks are pending.

The analytic supplier is the existing attributed Physlib transplant by
Kei Tsukamoto, Kento Mori and Hayata Yamasaki, revision
b9043cc548ef6d63a28454cf3a57fb12a0c2e142, Apache-2.0. Its license is retained
at docs/reports/inoutbalance/physlib-LICENSE.txt. The finite spectral-effect
Jensen and support-corner arguments are classical; no novelty is claimed.
The exact endpoint includes empty ambient carriers, singular A and B, and
zero output support. Kernel inclusion is converted to reconstruction; the
signed sandwich support theorem cancels the ambient compensation. The actual
all-Hilbert operator-convex supplier and continuity remain explicit premises.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Lieb.PositiveMapJensen
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

namespace D5.S3.Quantum.Lieb.SupportPerspectiveTransformer

variable {n : Type u} {m : Type v}
  [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Mixed products of the actual square root and zero-on-kernel spectral
inverse root give the actual support. The support also fixes the inverse root.
Only finite spectral multiplication is added to the existing normalization. -/
private theorem spectral_sqrt_inverse_products (Q : Matrix n n ℂ) (hQ : Q.PosSemidef) :
    let R := CFC.sqrt Q
    let W := spectralInverseSqrt Q
    let P := spectralSupport Q
    R * W = P ∧ W * R = P ∧ P * W = W ∧ W * P = W := by
  classical
  dsimp only
  obtain ⟨hR, hW, hP, -, -, -, -, -⟩ := spectral_sqrt_normalization Q hQ
  have hsqrt : CFC.sqrt Q = cfc Real.sqrt Q := by
    rw [CFC.sqrt_eq_real_sqrt Q hQ.nonneg,
      cfcₙ_eq_cfc (f := Real.sqrt) (a := Q) (hf0 := by simp)]
  have hmul (f g : ℝ → ℝ) :
      cfc f Q * cfc g Q = cfc (fun x => f x * g x) Q :=
    (cfc_mul f g Q (Q.finite_real_spectrum.continuousOn f)
      (Q.finite_real_spectrum.continuousOn g)).symm
  have hRW : CFC.sqrt Q * spectralInverseSqrt Q = spectralSupport Q := by
    rw [hsqrt]
    change cfc Real.sqrt Q * cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q =
      cfc (fun x : ℝ => if x = 0 then 0 else 1) Q
    rw [hmul]
    apply cfc_congr
    intro x hx
    change Real.sqrt x * (Real.sqrt x)⁻¹ = if x = 0 then 0 else 1
    by_cases h : x = 0
    · simp [h]
    · have hx0 : 0 ≤ x := by
        rw [hQ.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        exact hQ.eigenvalues_nonneg i
      have hs : Real.sqrt x ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (lt_of_le_of_ne hx0 (Ne.symm h)))
      rw [if_neg h]
      exact mul_inv_cancel₀ hs
  have hWR : spectralInverseSqrt Q * CFC.sqrt Q = spectralSupport Q := by
    simpa only [Matrix.conjTranspose_mul, hR, hW, hP] using
      congrArg Matrix.conjTranspose hRW
  have hPW : spectralSupport Q * spectralInverseSqrt Q = spectralInverseSqrt Q := by
    change cfc (fun x : ℝ => if x = 0 then 0 else 1) Q *
        cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q =
      cfc (fun x : ℝ => (Real.sqrt x)⁻¹) Q
    rw [hmul]
    apply cfc_congr
    intro x hx
    by_cases h : x = 0 <;> simp [h]
  have hWP : spectralInverseSqrt Q * spectralSupport Q = spectralInverseSqrt Q := by
    simpa only [Matrix.conjTranspose_mul, hW, hP] using
      congrArg Matrix.conjTranspose hPW
  exact ⟨hRW, hWR, hPW, hWP⟩

/-- Exact kernel inclusion forces support. The complement of the spectral
support maps every vector into ker B, so the original hypothesis annihilates
A on that complement. No domination hypothesis replaces kernel inclusion. -/
private theorem support_of_kernel_inclusion (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hker : ∀ x : n → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0) :
    spectralSupport B * A = A ∧ A * spectralSupport B = A := by
  obtain ⟨-, -, hP, -, -, -, hPB, -⟩ := spectral_sqrt_normalization B hB
  have hBP : B * spectralSupport B = B := by
    simpa only [Matrix.conjTranspose_mul, hP, hB.isHermitian.eq] using
      congrArg Matrix.conjTranspose hPB
  have hBComplement : B * (1 - spectralSupport B) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hBP, sub_self]
  have hAComplement : A * (1 - spectralSupport B) = 0 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro x
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    apply hker
    rw [Matrix.mulVec_mulVec, hBComplement, Matrix.zero_mulVec]
  have hAP : A * spectralSupport B = A := by
    have hz : A - A * spectralSupport B = 0 := by
      simpa only [Matrix.mul_sub, Matrix.mul_one] using hAComplement
    exact (sub_eq_zero.mp hz).symm
  have hPA : spectralSupport B * A = A := by
    simpa only [Matrix.conjTranspose_mul, hP, hA.eq] using
      congrArg Matrix.conjTranspose hAP
  exact ⟨hPA, hAP⟩

/-- Reconstruct A from its inverse-root normalization using precisely
ker B ⊆ ker A. This is the input reconstruction consumed by the endpoint. -/
private theorem sqrt_inverse_reconstruction (A B : Matrix n n ℂ)
    (hA : A.IsHermitian) (hB : B.PosSemidef)
    (hker : ∀ x : n → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0) :
    CFC.sqrt B * (spectralInverseSqrt B * A * spectralInverseSqrt B) *
      CFC.sqrt B = A := by
  obtain ⟨hRW, hWR, -, -⟩ := spectral_sqrt_inverse_products B hB
  obtain ⟨hPA, hAP⟩ := support_of_kernel_inclusion A B hA hB hker
  calc
    _ = (CFC.sqrt B * spectralInverseSqrt B) * A *
        (spectralInverseSqrt B * CFC.sqrt B) := by
      simp only [Matrix.mul_assoc]
    _ = spectralSupport B * A * spectralSupport B := by rw [hRW, hWR]
    _ = A := by rw [hPA, hAP]

/-- Congruence of the actual ambient unitalization recovers every signed
Hermitian B-sandwich. The arbitrary complex coordinate compensation vanishes
under the outer square roots; its sign is never needed. -/
private theorem ambientUnitalization_sqrt_congruence
    (Φ : Matrix n n ℂ →ₚ[ℂ] Matrix m m ℂ)
    (B : Matrix n n ℂ) (hB : B.PosSemidef) (i : n)
    (Z : Matrix n n ℂ) (hZ : Z.IsHermitian) :
    CFC.sqrt (Φ B) * ambientUnitalization Φ B hB i Z * CFC.sqrt (Φ B) =
      Φ (CFC.sqrt B * Z * CFC.sqrt B) := by
  let C := Φ B
  let R := CFC.sqrt C
  let W := spectralInverseSqrt C
  let P := spectralSupport C
  let S := Φ (CFC.sqrt B * Z * CFC.sqrt B)
  have hC : C.PosSemidef := (map_nonneg Φ hB.nonneg).posSemidef
  obtain ⟨-, -, -, -, -, hRP, -, -⟩ := spectral_sqrt_normalization C hC
  change R * P = R at hRP
  obtain ⟨hRW, hWR, -, -⟩ := spectral_sqrt_inverse_products C hC
  change R * W = P at hRW
  change W * R = P at hWR
  obtain ⟨hPS, hSP⟩ := positive_map_sandwich_support Φ B hB Z hZ
  change P * S = S at hPS
  change S * P = S at hSP
  have hRComplement : R * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hRP, sub_self]
  change R * (W * S * W + Z i i • (1 - P)) * R = S
  calc
    _ = (R * W) * S * (W * R) + Z i i • (R * (1 - P) * R) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_assoc]
    _ = S := by
      rw [hRW, hWR, hPS, hSP, hRComplement, Matrix.zero_mul, smul_zero, add_zero]

section Uniform

variable {a b : Type u} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Supported perspective transformer for an arbitrary complex-linear positive
finite matrix map. The actual all-Hilbert operator-convex supplier and
continuity are explicit. No CP, unitality or trace preservation of Φ,
faithfulness, commutation, or restriction on f(0) is assumed. Empty carriers
and the zero output support are included. -/
theorem supportedPerspective_transformer {f : ℝ → ℝ}
    (hconv : LownerHeinzTheorem.OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f)
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ)))
    (Φ : Matrix a a ℂ →ₚ[ℂ] Matrix b b ℂ)
    (A B : Matrix a a ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hker : ∀ x : a → ℂ, B *ᵥ x = 0 → A *ᵥ x = 0) :
    supportedPerspective f (Φ A) (Φ B) ≤ Φ (supportedPerspective f A B) := by
  classical
  cases isEmpty_or_nonempty b with
  | inl hb =>
    letI := hb
    exact le_of_eq (Subsingleton.elim _ _)
  | inr hb =>
    letI := hb
    cases isEmpty_or_nonempty a with
    | inl ha =>
      letI := ha
      have hA0 : A = 0 := Subsingleton.elim _ _
      have hB0 : B = 0 := Subsingleton.elim _ _
      exact le_of_eq (by
        simp only [hA0, hB0, map_zero, supportedPerspective, CFC.sqrt_zero,
          Matrix.zero_mul, Matrix.mul_zero])
    | inr ha =>
      letI := ha
      let i : a := Classical.choice ha
      let X := spectralInverseSqrt B * A * spectralInverseSqrt B
      let R := CFC.sqrt (Φ B)
      let W := spectralInverseSqrt (Φ B)
      let q := spectralSupport (Φ B)
      let Y := W * Φ A * W
      obtain ⟨-, hWB, -, -, -, -, -, -⟩ := spectral_sqrt_normalization B hB
      have hX : X.PosSemidef := by
        simpa only [X, hWB] using
          hA.conjTranspose_mul_mul_same (spectralInverseSqrt B)
      have hrec : CFC.sqrt B * X * CFC.sqrt B = A :=
        sqrt_inverse_reconstruction A B hA.isHermitian hB hker
      have hNX : normalizedPositiveMap Φ B X = Y := by
        change W * Φ (CFC.sqrt B * X * CFC.sqrt B) * W = Y
        rw [hrec]
      have hY : Y.PosSemidef := by
        rw [← hNX]
        exact (map_nonneg (normalizedPositiveMap Φ B) hX.nonneg).posSemidef
      have hC : (Φ B).PosSemidef := (map_nonneg Φ hB.nonneg).posSemidef
      obtain ⟨hR, -, hq, hqq, hqR, hRq, -, -⟩ :=
        spectral_sqrt_normalization (Φ B) hC
      change Rᴴ = R at hR
      change qᴴ = q at hq
      change q * q = q at hqq
      change q * R = R at hqR
      change R * q = R at hRq
      obtain ⟨-, -, hqW, -⟩ := spectral_sqrt_inverse_products (Φ B) hC
      change q * W = W at hqW
      have hqY : q * Y = Y := by
        calc
          _ = (q * W) * Φ A * W := by simp only [Y, Matrix.mul_assoc]
          _ = Y := by simp only [hqW, Y]
      have hdiagReal : ((X i i).re : ℂ) = X i i := by
        apply Complex.ext
        · simp only [Complex.ofReal_re]
        · simpa only [Complex.ofReal_im] using
            (Complex.nonneg_iff.mp (hX.diag_nonneg (i := i))).2
      let t : ℝ := (X i i).re
      have hCompScalar : X i i • (1 - q) = t • (1 - q) := by
        calc
          _ = ((X i i).re : ℂ) • (1 - q) :=
            congrArg (fun c : ℂ => c • (1 - q)) hdiagReal.symm
          _ = t • (1 - q) := Complex.coe_smul _ _
      have hTheta : ambientUnitalization Φ B hB i X = Y + t • (1 - q) := by
        change normalizedPositiveMap Φ B X + X i i • (1 - q) = Y + t • (1 - q)
        rw [hNX, hCompScalar]
      have hLeft :
          R * cfc f (ambientUnitalization Φ B hB i X) * R =
            supportedPerspective f (Φ A) (Φ B) := by
        rw [hTheta]
        change R * cfc f (Y + t • (1 - q)) * R = R * cfc f Y * R
        exact cfc_supported_localization q Y R hq hqq hY.isHermitian hqY hqR hRq t f
      have hRight :
          R * ambientUnitalization Φ B hB i (cfc f X) * R =
            Φ (supportedPerspective f A B) := by
        change CFC.sqrt (Φ B) * ambientUnitalization Φ B hB i (cfc f X) *
          CFC.sqrt (Φ B) = Φ (CFC.sqrt B * cfc f X * CFC.sqrt B)
        exact ambientUnitalization_sqrt_congruence Φ B hB i (cfc f X)
          (cfc_predicate _ _)
      have hJ : cfc f (ambientUnitalization Φ B hB i X) ≤
          ambientUnitalization Φ B hB i (cfc f X) :=
        ambient_unitalized_jensen (@hconv) hcont Φ B hB i X hX
      have h := congruence_mono hJ R
      rw [hR, hLeft, hRight] at h
      exact h

end Uniform

end D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
