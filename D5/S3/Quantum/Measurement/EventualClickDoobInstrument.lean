/- GID: D5/S3/Quantum/Measurement/EventualClickDoobInstrument
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurement/EventualClickDoobInstrument
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A support Doob instrument represents conditioning on an eventual click. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
import D5.S3.Quantum.Recovery.SpectralTransposeRecovery

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.Measurement.EventualClickDoobInstrument

open Matrix Filter Topology
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Measurement.GeneralInstrumentDarkClosure
open D5.S3.Quantum.Measurement.GeneralInstrumentResidualTailContraction
open D5.S3.Quantum.Measurement.GeneralInstrumentSurvivalLimit
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery

/-- The square-root support transform gives a complete instrument whose finite click branches
are exactly the original branches conditioned on eventual detection. -/
theorem eventual_click_doob_instrument
    {d : ℕ} {α ξ β : Type}
    [Fintype α] [Fintype ξ] [Fintype β]
    (Q : α → Matrix (Fin d) (Fin d) ℂ)
    (L : ξ → β → Matrix (Fin d) (Fin d) ℂ)
    (hcomp : ∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b = 1)
    (F : Matrix (Fin d) (Fin d) ℂ)
    (hF : Tendsto (survival Q) atTop (𝓝 F)) :
    let N := PhyslibLeaf.MatrixMap.of_kraus Q Q
    let C := fun x => PhyslibLeaf.MatrixMap.of_kraus (L x) (L x)
    let R := 1 - F
    let P := spectralSupport R
    let G := cfc (fun t : ℝ => Real.sqrt t) R
    let Gplus := spectralInverseSqrt R
    let Ntilde := fun X => G * N (Gplus * X * Gplus) * G
    let Ctilde := fun x X => C x (Gplus * X * Gplus)
    R = noClickDual Q R + ∑ x, noClickDual (L x) 1 ∧
    (∀ a, P * Q a * (1 - P) = 0) ∧
    (∀ x b, L x b * (1 - P) = 0) ∧
    (∀ H, H = P * H * P → noClickDual Q H = P * noClickDual Q H * P) ∧
    (∀ x Z, noClickDual (L x) Z = P * noClickDual (L x) Z * P) ∧
    Gplus * G = P ∧ G * Gplus = P ∧ P * G = G ∧
    (∀ X, Ntilde X =
      ∑ a, (G * Q a * Gplus) * X * (G * Q a * Gplus)ᴴ) ∧
    (∀ x X, Ctilde x X =
      ∑ b, (L x b * Gplus) * X * (L x b * Gplus)ᴴ) ∧
    (∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) +
      ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) = P) ∧
    (∀ X, Ntilde (G * X * G) = G * N X * G) ∧
    (∀ x X, Ctilde x (G * X * G) = C x X) ∧
    ∀ (rho : DensityState (Fin d)) (n : ℕ), 1 ≤ n →
      let rhoMatrix : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm rho.1
      let r := (rhoMatrix * R).trace.re
      0 < r → ∀ x,
        let original := C x ((N^[n - 1]) rhoMatrix)
        let conditioned := Ctilde x ((Ntilde^[n - 1])
          (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))
        conditioned = ((r : ℂ)⁻¹) • original ∧
        conditioned.trace = original.trace / (r : ℂ) ∧
        (original.trace ≠ 0 → conditioned.trace ≠ 0 ∧
          (conditioned.trace)⁻¹ • conditioned = (original.trace)⁻¹ • original) := by
  classical
  let N := PhyslibLeaf.MatrixMap.of_kraus Q Q
  let C := fun x => PhyslibLeaf.MatrixMap.of_kraus (L x) (L x)
  let R : Matrix (Fin d) (Fin d) ℂ := 1 - F
  let P : Matrix (Fin d) (Fin d) ℂ := spectralSupport R
  let G : Matrix (Fin d) (Fin d) ℂ := cfc (fun t : ℝ => Real.sqrt t) R
  let Gplus : Matrix (Fin d) (Fin d) ℂ := spectralInverseSqrt R
  let Ntilde := fun X => G * N (Gplus * X * Gplus) * G
  let Ctilde := fun x X => C x (Gplus * X * Gplus)
  change
    R = noClickDual Q R + ∑ x, noClickDual (L x) 1 ∧
    (∀ a, P * Q a * (1 - P) = 0) ∧
    (∀ x b, L x b * (1 - P) = 0) ∧
    (∀ H, H = P * H * P → noClickDual Q H = P * noClickDual Q H * P) ∧
    (∀ x Z, noClickDual (L x) Z = P * noClickDual (L x) Z * P) ∧
    Gplus * G = P ∧ G * Gplus = P ∧ P * G = G ∧
    (∀ X, Ntilde X =
      ∑ a, (G * Q a * Gplus) * X * (G * Q a * Gplus)ᴴ) ∧
    (∀ x X, Ctilde x X =
      ∑ b, (L x b * Gplus) * X * (L x b * Gplus)ᴴ) ∧
    (∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) +
      ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) = P) ∧
    (∀ X, Ntilde (G * X * G) = G * N X * G) ∧
    (∀ x X, Ctilde x (G * X * G) = C x X) ∧
    ∀ (rho : DensityState (Fin d)) (n : ℕ), 1 ≤ n →
      let rhoMatrix : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm rho.1
      let r := (rhoMatrix * R).trace.re
      0 < r → ∀ x,
        let original := C x ((N^[n - 1]) rhoMatrix)
        let conditioned := Ctilde x ((Ntilde^[n - 1])
          (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))
        conditioned = ((r : ℂ)⁻¹) • original ∧
        conditioned.trace = original.trace / (r : ℂ) ∧
        (original.trace ≠ 0 → conditioned.trace ≠ 0 ∧
          (conditioned.trace)⁻¹ • conditioned = (original.trace)⁻¹ • original)
  let Lflat : ξ × β → Matrix (Fin d) (Fin d) ℂ := fun p => L p.1 p.2
  have hcompFlat :
      ∑ a, (Q a)ᴴ * Q a + ∑ p, (Lflat p)ᴴ * Lflat p = 1 := by
    simpa only [Lflat, Fintype.sum_prod_type] using hcomp
  obtain ⟨F', hF', hchain, hF'nonneg, hF'le, hF'fixed, -⟩ :=
    survival_tendsto_maximal_fixed_effect Q Lflat hcompFlat
  have hF'eq : F' = F := tendsto_nhds_unique hF' hF
  subst F'
  have hRnonneg : 0 ≤ R := by
    exact sub_nonneg.mpr hF'le
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hRnonneg
  have htail := residual_tail_contraction Q Lflat hcompFlat F hF
  have hAresidual : noClickDual Q R = ∑ a, (Q a)ᴴ * Q a - F := by
    have hone := (htail.1 1).1
    simpa only [R, survival, noClickDual, Function.iterate_one, Matrix.mul_one] using hone.symm
  have hbalance : R = noClickDual Q R + ∑ x, noClickDual (L x) 1 := by
    rw [hAresidual]
    simp only [noClickDual, Matrix.mul_one]
    dsimp only [R]
    calc
      1 - F = (∑ a, (Q a)ᴴ * Q a + ∑ x, ∑ b, (L x b)ᴴ * L x b) - F := by
        rw [hcomp]
      _ = ∑ a, (Q a)ᴴ * Q a - F + ∑ x, ∑ b, (L x b)ᴴ * L x b := by
        abel
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ R) :=
    R.finite_real_spectrum.continuousOn f
  have hspectrumNonneg : ∀ t ∈ spectrum ℝ R, 0 ≤ t :=
    fun t ht => spectrum_nonneg_of_nonneg hRnonneg ht
  have hGsq : G * G = R := by
    calc
      G * G = cfc (fun t : ℝ => Real.sqrt t * Real.sqrt t) R := by
        exact (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = cfc (fun t : ℝ => t) R := by
        apply cfc_congr
        intro t ht
        exact Real.mul_self_sqrt (hspectrumNonneg t ht)
      _ = R := cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint
  have hGstar : Gᴴ = G :=
    (cfc_predicate (fun t : ℝ => Real.sqrt t) R : IsSelfAdjoint G).star_eq
  have hGplusStar : Gplusᴴ = Gplus :=
    (cfc_predicate (fun t : ℝ => (Real.sqrt t)⁻¹) R :
        IsSelfAdjoint Gplus).star_eq
  have hPstar : Pᴴ = P :=
    (cfc_predicate (fun t : ℝ => if t = 0 then 0 else 1) R :
      IsSelfAdjoint P).star_eq
  have hGplusG : Gplus * G = P := by
    calc
      Gplus * G = cfc (fun t : ℝ =>
          (Real.sqrt t)⁻¹ * Real.sqrt t) R := by
        exact (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = P := by
        apply cfc_congr
        intro t ht
        have ht0 := hspectrumNonneg t ht
        by_cases htz : t = 0
        · simp [htz]
        · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
          simp [htz, Real.sqrt_ne_zero'.mpr htp]
  have hGGplus : G * Gplus = P := by
    calc
      G * Gplus = cfc (fun t : ℝ =>
          Real.sqrt t * (Real.sqrt t)⁻¹) R := by
        exact (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = P := by
        apply cfc_congr
        intro t ht
        have ht0 := hspectrumNonneg t ht
        by_cases htz : t = 0
        · simp [htz]
        · have htp : 0 < t := lt_of_le_of_ne ht0 (Ne.symm htz)
          simp [htz, Real.sqrt_ne_zero'.mpr htp]
  have hPG : P * G = G := by
    calc
      P * G = cfc (fun t : ℝ =>
          (if t = 0 then 0 else 1) * Real.sqrt t) R := by
        exact (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = G := by
        apply cfc_congr
        intro t _
        by_cases htz : t = 0 <;> simp [htz]
  have hGP : G * P = G := by
    have h := congrArg star hPG
    simpa only [star_eq_conjTranspose, Matrix.conjTranspose_mul,
      hGstar, hPstar] using h
  have hPP : P * P = P := by
    calc
      P * P = cfc (fun t : ℝ =>
          (if t = 0 then 0 else 1) * (if t = 0 then 0 else 1)) R := by
        exact (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = P := by
        apply cfc_congr
        intro t _
        by_cases htz : t = 0 <;> simp [htz]
  have hRP : R * P = R := by
    calc
      R * P = cfc (fun t : ℝ => t) R * P :=
        congrArg (fun X => X * P) (cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint).symm
      _ = cfc (fun t : ℝ => t) R *
          cfc (fun t : ℝ => if t = 0 then 0 else 1) R := rfl
      _ = cfc (fun t : ℝ => t * (if t = 0 then 0 else 1)) R :=
        (cfc_mul _ _ R (hcont _) (hcont _)).symm
      _ = cfc (fun t : ℝ => t) R := by
        apply cfc_congr
        intro t _
        by_cases htz : t = 0 <;> simp [htz]
      _ = R := cfc_id' ℝ R hRpsd.isHermitian.isSelfAdjoint
  have hRcomp : R * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hRP, sub_self]
  have hdark := darkLayer_closure Q Lflat hcompFlat
  have hkerToDark : ∀ v : Fin d → ℂ, R *ᵥ v = 0 → v ∈ darkLayer Q Lflat d := by
    intro v hRv
    rw [hdark.1 d, LinearMap.mem_ker, Matrix.mulVecLin_apply]
    have hdefectPsd : (1 - survival Q d).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hchain d).2.2.1)
    apply (hdefectPsd.dotProduct_mulVec_zero_iff v).mp
    have hresidualPsd : (survival Q d - F).PosSemidef := by
      exact Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr (hchain d).2.2.2)
    have hdefectQuad := hdefectPsd.dotProduct_mulVec_nonneg v
    have hresidualQuad := hresidualPsd.dotProduct_mulVec_nonneg v
    have hsum :
        star v ⬝ᵥ ((1 - survival Q d) *ᵥ v) +
          star v ⬝ᵥ ((survival Q d - F) *ᵥ v) = 0 := by
      rw [← dotProduct_add, ← Matrix.add_mulVec]
      have : (1 - survival Q d) + (survival Q d - F) = R := by
        dsimp only [R]
        abel
      rw [this, hRv, dotProduct_zero]
    exact (add_eq_zero_iff_of_nonneg hdefectQuad hresidualQuad).mp hsum |>.1
  have hdarkToKer : ∀ v : Fin d → ℂ, v ∈ darkLayer Q Lflat d → R *ᵥ v = 0 := by
    intro v hv
    have hvn : ∀ n, d ≤ n → survival Q n *ᵥ v = v := by
      intro n hn
      have hv' : v ∈ darkLayer Q Lflat n := by
        rw [hdark.2.1 n hn]
        exact hv
      rw [hdark.1 n, LinearMap.mem_ker, Matrix.mulVecLin_apply,
        Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv'
      exact hv'.symm
    have hmulLim : Tendsto (fun n => survival Q n *ᵥ v) atTop (𝓝 (F *ᵥ v)) := by
      exact (continuous_id.matrix_mulVec continuous_const).tendsto F |>.comp hF
    have hconstLim : Tendsto (fun _ : ℕ => v) atTop (𝓝 v) := tendsto_const_nhds
    have hevent : ∀ᶠ n in atTop, survival Q n *ᵥ v = v :=
      eventually_atTop.2 ⟨d, fun n hn => hvn n hn⟩
    have hFv : F *ᵥ v = v := tendsto_nhds_unique hmulLim
      (hconstLim.congr' (hevent.mono fun _ h => h.symm))
    dsimp only [R]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hFv, sub_self]
  have hPzeroOfRzero : ∀ v : Fin d → ℂ, R *ᵥ v = 0 → P *ᵥ v = 0 := by
    intro v hRv
    have hGv : G *ᵥ v = 0 := by
      apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero G v).mp
      rw [hGstar, hGsq]
      exact hRv
    rw [← hGplusG, ← Matrix.mulVec_mulVec, hGv, Matrix.mulVec_zero]
  have hQsupport : ∀ a, P * Q a * (1 - P) = 0 := by
    intro a
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    apply hPzeroOfRzero
    apply hdarkToKer
    exact hdark.2.2.2.1 a _ (hkerToDark _ (by
      rw [Matrix.mulVec_mulVec, hRcomp, Matrix.zero_mulVec]))
  have hLsupport : ∀ x b, L x b * (1 - P) = 0 := by
    intro x b
    rw [Matrix.ext_iff_mulVec]
    intro v
    rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
    exact hdark.2.2.1 (x, b) _ (hkerToDark _ (by
      rw [Matrix.mulVec_mulVec, hRcomp, Matrix.zero_mulVec]))
  have hPQ : ∀ a, P * Q a = P * Q a * P := by
    intro a
    apply sub_eq_zero.mp
    simpa only [Matrix.mul_sub, Matrix.mul_one] using hQsupport a
  have hLP : ∀ x b, L x b = L x b * P := by
    intro x b
    apply sub_eq_zero.mp
    simpa only [Matrix.mul_sub, Matrix.mul_one] using hLsupport x b
  have hQdualSupport : ∀ H, H = P * H * P →
      noClickDual Q H = P * noClickDual Q H * P := by
    intro H hH
    simp only [noClickDual, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    calc
      (Q a)ᴴ * H * Q a = (Q a)ᴴ * (P * H * P) * Q a :=
        congrArg (fun X => (Q a)ᴴ * X * Q a) hH
      _ = (P * Q a)ᴴ * H * (P * Q a) := by
        rw [Matrix.conjTranspose_mul, hPstar]
        simp only [Matrix.mul_assoc]
      _ = (P * Q a * P)ᴴ * H * (P * Q a * P) := by rw [← hPQ a]
      _ = P * ((Q a)ᴴ * (P * H * P) * Q a) * P := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPstar]
        simp only [Matrix.mul_assoc]
      _ = P * ((Q a)ᴴ * H * Q a) * P :=
        congrArg (fun X => P * ((Q a)ᴴ * X * Q a) * P) hH.symm
  have hLdualSupport : ∀ x Z,
      noClickDual (L x) Z = P * noClickDual (L x) Z * P := by
    intro x Z
    simp only [noClickDual, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    calc
      (L x b)ᴴ * Z * L x b = (L x b * P)ᴴ * Z * (L x b * P) := by
        rw [← hLP x b]
      _ = P * ((L x b)ᴴ * Z * L x b) * P := by
        rw [Matrix.conjTranspose_mul, hPstar]
        simp only [Matrix.mul_assoc]
  have hNtildeKraus : ∀ X, Ntilde X =
      ∑ a, (G * Q a * Gplus) * X * (G * Q a * Gplus)ᴴ := by
    intro X
    simp only [Ntilde, N, PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGstar, hGplusStar]
    simp only [Matrix.mul_assoc]
  have hCtildeKraus : ∀ x X, Ctilde x X =
      ∑ b, (L x b * Gplus) * X * (L x b * Gplus)ᴴ := by
    intro x X
    simp only [Ctilde, C, PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.conjTranspose_mul, hGplusStar]
    simp only [Matrix.mul_assoc]
  have hGPG : G * P * G = R := by rw [hGP, hGsq]
  have hNoClickComplete :
      ∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) =
        Gplus * noClickDual Q R * Gplus := by
    simp only [noClickDual, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGstar, hGplusStar]
    calc
      (Gplus * ((Q a)ᴴ * G)) * P * (G * Q a * Gplus) =
          Gplus * (Q a)ᴴ * (G * P * G) * Q a * Gplus := by
            simp only [Matrix.mul_assoc]
      _ = Gplus * ((Q a)ᴴ * R * Q a) * Gplus := by
        rw [hGPG]
        simp only [Matrix.mul_assoc]
  have hClickComplete :
      ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) =
        ∑ x, Gplus * noClickDual (L x) 1 * Gplus := by
    apply Finset.sum_congr rfl
    intro x _
    simp only [noClickDual, Matrix.mul_one, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.conjTranspose_mul, hGplusStar]
    simp only [Matrix.mul_assoc]
  have hComplete :
      ∑ a, (G * Q a * Gplus)ᴴ * P * (G * Q a * Gplus) +
        ∑ x, ∑ b, (L x b * Gplus)ᴴ * (L x b * Gplus) = P := by
    rw [hNoClickComplete, hClickComplete]
    calc
      Gplus * noClickDual Q R * Gplus +
          ∑ x, Gplus * noClickDual (L x) 1 * Gplus =
          Gplus * (noClickDual Q R + ∑ x, noClickDual (L x) 1) * Gplus := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul]
      _ = Gplus * R * Gplus := by rw [← hbalance]
      _ = Gplus * (G * G) * Gplus :=
        congrArg (fun X => Gplus * X * Gplus) hGsq.symm
      _ = (Gplus * G) * (G * Gplus) := by
        simp only [Matrix.mul_assoc]
      _ = P := by rw [hGplusG, hGGplus, hPP]
  have hGQP : ∀ a, G * Q a * P = G * Q a := by
    intro a
    calc
      G * Q a * P = (G * P) * Q a * P := by rw [hGP]
      _ = G * (P * Q a * P) := by simp only [Matrix.mul_assoc]
      _ = G * (P * Q a) := by rw [← hPQ a]
      _ = (G * P) * Q a := by rw [Matrix.mul_assoc]
      _ = G * Q a := by rw [hGP]
  have hPQstarG : ∀ a, P * ((Q a)ᴴ * G) = (Q a)ᴴ * G := by
    intro a
    have h := congrArg star (hGQP a)
    simpa only [star_eq_conjTranspose, Matrix.conjTranspose_mul, hPstar, hGstar,
      Matrix.mul_assoc] using h
  have hNintertwine : ∀ X, Ntilde (G * X * G) = G * N X * G := by
    intro X
    rw [hNtildeKraus]
    simp only [N, PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hGstar, hGplusStar]
    calc
      (G * Q a * Gplus) * (G * X * G) * (Gplus * ((Q a)ᴴ * G)) =
          (G * Q a * (Gplus * G)) * X * ((G * Gplus) * ((Q a)ᴴ * G)) := by
            simp only [Matrix.mul_assoc]
      _ = (G * Q a * P) * X * (P * ((Q a)ᴴ * G)) := by
        rw [hGplusG, hGGplus]
      _ = (G * Q a) * X * ((Q a)ᴴ * G) := by rw [hGQP, hPQstarG]
      _ = G * (Q a * X * (Q a)ᴴ) * G := by simp only [Matrix.mul_assoc]
  have hPLstar : ∀ x b, P * (L x b)ᴴ = (L x b)ᴴ := by
    intro x b
    have h := congrArg star (hLP x b)
    simpa only [star_eq_conjTranspose, Matrix.conjTranspose_mul, hPstar] using h.symm
  have hCintertwine : ∀ x X, Ctilde x (G * X * G) = C x X := by
    intro x X
    rw [hCtildeKraus]
    simp only [C, PhyslibLeaf.MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro b _
    rw [Matrix.conjTranspose_mul, hGplusStar]
    calc
      (L x b * Gplus) * (G * X * G) * (Gplus * (L x b)ᴴ) =
          (L x b * (Gplus * G)) * X * ((G * Gplus) * (L x b)ᴴ) := by
            simp only [Matrix.mul_assoc]
      _ = (L x b * P) * X * (P * (L x b)ᴴ) := by rw [hGplusG, hGGplus]
      _ = L x b * X * (L x b)ᴴ := by rw [← hLP, hPLstar]
  have hIterate : ∀ k X, (Ntilde^[k]) (G * X * G) = G * ((N^[k]) X) * G := by
    intro k X
    exact ((show Function.Semiconj (fun Y => G * Y * G) N Ntilde from
      fun Y => (hNintertwine Y).symm).iterate_right k X).symm
  have hNsmul : ∀ (c : ℂ) X, N (c • X) = c • N X := by
    intro c X
    exact N.map_smul c X
  have hNiterateSmul : ∀ k (c : ℂ) X, (N^[k]) (c • X) = c • (N^[k]) X := by
    intro k c X
    exact ((show Function.Semiconj (fun Y => c • Y) N N from
      fun Y => (hNsmul c Y).symm).iterate_right k X).symm
  refine ⟨hbalance, hQsupport, hLsupport, hQdualSupport, hLdualSupport,
    hGplusG, hGGplus, hPG, hNtildeKraus, hCtildeKraus, hComplete,
    hNintertwine, hCintertwine, ?_⟩
  intro rho n _hn
  dsimp only
  intro hr x
  let rhoMatrix : Matrix (Fin d) (Fin d) ℂ := CStarMatrix.ofMatrix.symm rho.1
  let r : ℝ := (rhoMatrix * R).trace.re
  change
    Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) • (G * rhoMatrix * G))) =
        ((r : ℂ)⁻¹) • C x ((N^[n - 1]) rhoMatrix) ∧
      (Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))).trace =
        (C x ((N^[n - 1]) rhoMatrix)).trace / (r : ℂ) ∧
      ((C x ((N^[n - 1]) rhoMatrix)).trace ≠ 0 →
        (Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) •
          (G * rhoMatrix * G)))).trace ≠ 0 ∧
        ((Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) •
          (G * rhoMatrix * G)))).trace)⁻¹ •
            Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) •
              (G * rhoMatrix * G))) =
          ((C x ((N^[n - 1]) rhoMatrix)).trace)⁻¹ •
            C x ((N^[n - 1]) rhoMatrix))
  have hscaled : ((r : ℂ)⁻¹) • (G * rhoMatrix * G) =
      G * (((r : ℂ)⁻¹) • rhoMatrix) * G := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hboxed :
      Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) • (G * rhoMatrix * G))) =
        ((r : ℂ)⁻¹) • C x ((N^[n - 1]) rhoMatrix) := by
    rw [hscaled, hIterate, hCintertwine, hNiterateSmul]
    exact (C x).map_smul ((r : ℂ)⁻¹) ((N^[n - 1]) rhoMatrix)
  have htrace :
      (Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) • (G * rhoMatrix * G)))).trace =
        (C x ((N^[n - 1]) rhoMatrix)).trace / (r : ℂ) := by
    rw [hboxed, Matrix.trace_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  refine ⟨hboxed, htrace, ?_⟩
  intro horiginal
  have hrComplex : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hconditioned :
      (Ctilde x ((Ntilde^[n - 1]) (((r : ℂ)⁻¹) •
        (G * rhoMatrix * G)))).trace ≠ 0 := by
    rw [htrace]
    exact div_ne_zero horiginal hrComplex
  refine ⟨hconditioned, ?_⟩
  rw [hboxed, Matrix.trace_smul, smul_smul]
  simp only [smul_eq_mul]
  congr 1
  field_simp [hrComplex, horiginal]

#print axioms eventual_click_doob_instrument

end D5.S3.Quantum.Measurement.EventualClickDoobInstrument
