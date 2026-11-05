/- GID: D5/S3/Quantum/Reduction/SingularPositiveRefinement
   generality: I
   mirror-B: D5/B/S3/Quantum/Reduction/SingularPositiveRefinement
   mirror-E: none(waiver:finite-algebraic-proof)
   anchors: []
   utility: none
   digest: Positive domination by singular canonical filters reduces to their actual support corners. -/

import D5.S3.Quantum.Reduction.PositiveRefinementCorner
import D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
import Mathlib.Analysis.CStarAlgebra.Projection

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Reduction.PositiveRefinementRigidity
open D5.S3.Quantum.Lieb.PositiveMapJensen
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery
namespace D5.S3.Quantum.Reduction.SingularPositiveRefinement
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Domination by the actual square-root congruence removes input and output
kernel directions and gives an exact positive map on its supported corner. -/
theorem filter_support_reduction
    (E : Matrix n n ℂ) (hE : E.PosSemidef)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ CFC.sqrt E * X * CFC.sqrt E) :
    let R := CFC.sqrt E
    let W := spectralInverseSqrt E
    let P := spectralSupport E
    (∀ X, Φ (P * X * P) = Φ X) ∧
    (∀ X, P * Φ X = Φ X ∧ Φ X * P = Φ X) ∧
    (∀ X, X.PosSemidef → (W * Φ X * W).PosSemidef ∧ W * Φ X * W ≤ P * X * P) ∧
    (∀ X, R * (W * Φ X * W) * R = Φ X) := by
  dsimp only
  let R := CFC.sqrt E
  let W := spectralInverseSqrt E
  let P := spectralSupport E
  obtain ⟨hR, hW, hP, hPP, hPR, hRP, -, -⟩ := spectral_sqrt_normalization E hE
  obtain ⟨hRW, hWR, hPW, hWP⟩ := spectral_sqrt_inverse_products E hE
  change Rᴴ = R at hR
  change Wᴴ = W at hW
  change Pᴴ = P at hP
  change P * P = P at hPP
  change P * R = R at hPR
  change R * P = R at hRP
  change R * W = P at hRW
  change W * R = P at hWR
  have hin (X : Matrix n n ℂ) : Φ (P * X * P) = Φ X := by
    apply positive_map_projection_compression Φ hpos P hP hPP
    have hQ : (1 - P).PosSemidef :=
      (show IsStarProjection P from ⟨hPP, hP⟩).one_sub.nonneg.posSemidef
    have hRQ : R * (1 - P) = 0 := by rw [mul_sub, mul_one, hRP, sub_self]
    apply le_antisymm
    · simpa only [R, hRQ, zero_mul] using hdom (1 - P) hQ
    · exact (hpos _ hQ).nonneg
  let out : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := {
    toFun X := P * Φ X * P
    map_add' X Y := by simp [mul_add, add_mul]
    map_smul' c X := by simp [mul_smul_comm, smul_mul_assoc] }
  have houtEq : out = Φ := by
    apply eq_of_projection_eq
    intro Q hQ hQQ
    have hq : Q.PosSemidef := by
      simpa only [hQ, hQQ] using posSemidef_conjTranspose_mul_self Q
    have hPC : P * (R * Q * R) = R * Q * R := by
      rw [← mul_assoc, ← mul_assoc, hPR]
    have hs := support_of_nonneg_le_smul (R * Q * R) (Φ Q) P hP hPC
      (hpos Q hq) 1 (by simpa using hdom Q hq)
    exact (congrArg (fun M => M * P) hs.1).trans hs.2
  have hout (X : Matrix n n ℂ) : P * Φ X = Φ X ∧ Φ X * P = Φ X := by
    have hx : P * Φ X * P = Φ X := LinearMap.congr_fun houtEq X
    constructor
    · calc
        P * Φ X = P * (P * Φ X * P) := congrArg (fun M => P * M) hx.symm
        _ = P * Φ X * P := by simp only [← mul_assoc, hPP]
        _ = Φ X := hx
    · calc
        Φ X * P = (P * Φ X * P) * P := congrArg (fun M => M * P) hx.symm
        _ = P * Φ X * P := by rw [mul_assoc, hPP]
        _ = Φ X := hx
  refine ⟨hin, hout, ?_, ?_⟩
  · intro X hX
    constructor
    · simpa only [hW] using (hpos X hX).mul_mul_conjTranspose_same W
    · have h := congruence_mono (hdom X hX) W
      change Wᴴ * Φ X * W ≤ Wᴴ * (R * X * R) * W at h
      rw [hW] at h
      have he : W * (R * X * R) * W = P * X * P := by
        calc
          _ = (W * R) * X * (R * W) := by noncomm_ring
          _ = _ := by rw [hWR, hRW]
      rwa [he] at h
  · intro X
    calc
      R * (W * Φ X * W) * R = (R * W) * Φ X * (W * R) := by noncomm_ring
      _ = P * Φ X * P := by rw [hRW, hWR]
      _ = Φ X := by rw [(hout X).1, (hout X).2]


/-- A positive map dominated by one canonical filter is a nonnegative scalar
multiple of that filter, with singular and zero effects included. -/
theorem filter_dominated_scalar
    (E : Matrix n n ℂ) (hE : E.PosSemidef)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hpos : ∀ X, X.PosSemidef → (Φ X).PosSemidef)
    (hdom : ∀ X, X.PosSemidef → Φ X ≤ CFC.sqrt E * X * CFC.sqrt E) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      ∀ X, Φ X = (c : ℂ) • (CFC.sqrt E * X * CFC.sqrt E) := by
  classical
  let R := CFC.sqrt E
  let W := spectralInverseSqrt E
  let P := spectralSupport E
  obtain ⟨hR, hW, hP, hPP, hPR, hRP, -, -⟩ := spectral_sqrt_normalization E hE
  obtain ⟨hin, hout, hnorm, hrec⟩ := filter_support_reduction E hE Φ hpos hdom
  let T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ := {
    toFun X := W * Φ X * W
    map_add' X Y := by simp [mul_add, add_mul]
    map_smul' c X := by simp [mul_smul_comm, smul_mul_assoc] }
  obtain ⟨c, hc, hc', hT⟩ :=
    D5.S3.Quantum.Reduction.PositiveRefinementCorner.corner_dominated_scalar P hP hPP T
      (fun X hX => (hnorm X hX).1) (fun X hX => (hnorm X hX).2)
  refine ⟨c, hc, hc', ?_⟩
  intro X
  calc
    Φ X = R * T X * R := (hrec X).symm
    _ = R * ((c : ℂ) • (P * X * P)) * R := by rw [hT X]
    _ = (c : ℂ) • (R * X * R) := by
      simp only [mul_smul_comm, smul_mul_assoc]
      congr 1
      calc
        R * (P * X * P) * R = (R * P) * X * (P * R) := by noncomm_ring
        _ = R * X * R := by rw [hRP, hPR]

#print axioms filter_dominated_scalar

#print axioms filter_support_reduction
end D5.S3.Quantum.Reduction.SingularPositiveRefinement
