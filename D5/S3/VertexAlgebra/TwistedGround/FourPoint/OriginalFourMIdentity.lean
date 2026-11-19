/- GID: D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMIdentity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original rank-24 three-channel Jacobi identity. -/

import D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPolynomialClosure
import D5.S3.VertexAlgebra.TwistedGround.OriginalFourMReduction

/-! The real chart comparisons give Jacobi on the original twisted module.
The Laurent selectors determine the detector degree before linear extension. -/

set_option autoImplicit false
noncomputable section

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset

open Complex MvPolynomial LatticeGeneratingFieldLocality
open LatticeHalfFockChargedCoefficients (omega)
open LatticeTwistedGroundRealization.SignQuotient (ModTwoCharge)
open HalfFock.LatticeHalfFockParityField
open OriginalFourMActualChart (parameter)
open OriginalFourPointChartGluing (rA rB)
open OriginalFourMInputs (CompatiblePolynomial)
open OriginalFourMDLipMean (radial_nome_eq_chart radial_word_crossings
  radial_AD_crossing_of_words)
open OriginalFourMRadialChannels (radial_AB_crossing_on_overlap)
open D5.S3.Analytic.OriginalHalfBinomialDiskCorrection (disk)
open private FourForm slitAForm slitAForm_apply slitBForm slitBForm_apply
  radial_openings from D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMRadialChannels
open private dLipForm dLipForm_apply radial_channels_off_detector_degree from
  D5.S3.VertexAlgebra.TwistedGround.FourPoint.OriginalFourMPolynomialClosure

private theorem detector_basis_ext (D : LatticeData) (P Q R S : Oscillator D)
    (F G : FourForm D)
    (test : ∀ m : Index D →₀ ℕ, F ![P, Q, R, monomial m 1] = G ![P, Q, R, monomial m 1]) :
    F ![P, Q, R, S] = G ![P, Q, R, S] := by
  classical
  let v : Fin 4 → Oscillator D := ![P, Q, R, 0]
  have hupdate (W : Oscillator D) : Function.update v (3 : Fin 4) W = ![P, Q, R, W] := by
    funext i
    fin_cases i <;> simp [v, Function.update]
  have eq : F.toLinearMap v 3 = G.toLinearMap v 3 := by
    apply (basisMonomials (Index D) ℂ).ext
    intro m
    change F (Function.update v 3 (monomial m 1)) = G (Function.update v 3 (monomial m 1))
    rw [hupdate]
    exact test m
  have eqS := LinearMap.congr_fun eq S
  change F (Function.update v 3 S) = G (Function.update v 3 S) at eqS
  rwa [hupdate] at eqS

set_option maxHeartbeats 3000000 in
-- Elaborate both charge-sector comparisons after expanding the detector basis.
private theorem original_identityK_of_homogeneous_inputs (D : LatticeData)
    (hu : IsUnit D.G.det) (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))
    (h24 : D.rank = 24) (H K L : ℕ) (m n r : ℤ) (P Q R S : Oscillator D)
    (hP : P.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (H : ℤ) - 3))
    (hQ : Q.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (K : ℤ) - 3))
    (hR : R.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) (2 * (L : ℤ) - 3)) :
    identityK D hu H K L m n r P Q R S := by
  classical
  let degree : ℤ := 2 * ((H : ℤ) + K + L - (m + n + r) - 2) - 3
  apply identityK_of_real_interval_crossing D hu hD h24 H K L m n r P Q R S
  · intro a x hx hx₁
    let A := slitAForm D H K (m+n+r) a (rA (x : ℂ))
    let c := (2 : ℂ) ^ (12 : ℕ) * (x : ℂ) ^ (m+n+r+2)
    let B := c • slitBForm D H K L m n r a (rB (x : ℂ))
    have h := detector_basis_ext D P Q R S A B
    simp only [A, B, c, slitAForm_apply, slitBForm_apply, smul_apply,
      smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons] at h
    apply h
    intro e
    let U : Oscillator D := monomial e 1
    let d := Finsupp.weight (fun i => (omega D i : ℤ)) e
    have hu' : U.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases hd : d = degree
    · have hx₀ : 0 < x := by linarith
      obtain ⟨wA, wB, hwA, hwB, hsA, hsB⟩ := radial_openings hx hx₁
      have hda : parameter .A (x : ℂ) ∈ disk := by
        rw [← hsA]
        simpa only [disk, Metric.mem_ball, dist_zero_right, norm_pow] using
          (pow_lt_one₀ (norm_nonneg wA) hwA (by decide : (2 : ℕ) ≠ 0))
      have hdb : parameter .B (x : ℂ) ∈ disk := by
        rw [← hsB]
        simpa only [disk, Metric.mem_ball, dist_zero_right, norm_pow] using
          (pow_lt_one₀ (norm_nonneg wB) hwB (by decide : (2 : ℕ) ≠ 0))
      exact radial_AB_crossing_on_overlap D hu hD h24 a H K L m n r hx hx₁ true
        (radial_nome_eq_chart hx₀ hx₁ true .A (Or.inl rfl) hda)
        (radial_nome_eq_chart hx₀ hx₁ true .B (Or.inr rfl) hdb)
        P Q R U hP hQ hR (by rw [hd] at hu'; exact hu')
    · have zero := radial_channels_off_detector_degree D hu H K L m n r d P Q R U a
        (rA (x : ℂ)) (rB (x : ℂ)) (x : ℂ)⁻¹ hP hQ hR hu' hd
      rw [zero.1, zero.2.1, mul_zero]
  · intro a x hx hx₁
    let A := slitAForm D H K (m+n+r) a (rA (x : ℂ))
    let F := dLipForm D H K L m n r a (x : ℂ)⁻¹
    have h := detector_basis_ext D P Q R S A F
    simp only [A, F, slitAForm_apply, dLipForm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons] at h
    apply h
    intro e
    let U : Oscillator D := monomial e 1
    let d := Finsupp.weight (fun i => (omega D i : ℤ)) e
    have hu' : U.IsWeightedHomogeneous (fun i => (omega D i : ℤ)) d :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    by_cases hd : d = degree
    · exact radial_AD_crossing_of_words D H K L m n r a x
        (fun w hp hq hr hs =>
          (radial_word_crossings D hu hD h24 w H K L m n r hp hq hr hs a x hx hx₁).2)
        P Q R U hP hQ hR (by rw [hd] at hu'; exact hu')
    · have zero := radial_channels_off_detector_degree D hu H K L m n r d P Q R U a
        (rA (x : ℂ)) (rB (x : ℂ)) (x : ℂ)⁻¹ hP hQ hR hu' hd
      rw [zero.1, zero.2.2]

/-- The original all-state three-M Jacobi coefficient law, on the selected
rank-24 twisted lattice module and for every signed integer mode triple. -/
theorem original_fourM_jacobi (D : LatticeData) (hu : IsUnit D.G.det)
    (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ))) (h24 : D.rank = 24)
    (m n r : ℤ) (u v w : paritySpace D hu (-1)) :
    originalJacobi D hu hD m n r u v w := by
  apply (original_jacobi_iff_identityK D hu hD h24 m n r).mpr _ u v w
  intro H K L P Q R hP hQ hR S
  exact original_identityK_of_homogeneous_inputs D hu hD h24 H K L m n r P Q R S
    hP.2 hQ.2 hR.2

#print axioms original_fourM_jacobi

end D5.S3.VertexAlgebra.TwistedGround.OriginalFourMChargeCoset
