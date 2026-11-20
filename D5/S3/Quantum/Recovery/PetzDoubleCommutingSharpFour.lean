import Batteries.Tactic.OpenPrivate
import D5.S3.DivergenceSupport.ZeroSupportDPI
import D5.S3.TotalVariation.Bhattacharyya
import D5.S3.Quantum.Information.StrongSubadditivity.Physlib.ForMathlib.Isometry
import D5.S3.Quantum.Recovery.PetzLikelihoodRectangularAmplitude
import D5.S3.Quantum.Recovery.PetzSingularInputLimit

/-!
# Ordinary Petz recovery with commuting input and output pairs

The trace dual pulls the common output eigenprojections back to effects on the input space.
A pair of horizontal amplitudes has left Grams equal to the input state and its ordinary
Petz recovery. Their real overlap is the average posterior Hellinger affinity for the
same stochastic kernel whose conditional relative entropy gives the Umegaki loss.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Divergence.ClassicalDPI (klDivergence channelOutput posterior)
open D5.S3.DivergenceSupport.ZeroSupportDPI
  (classical_dpi_identity_zero_support channel_output_absolute_continuity)
open D5.S3.TotalVariation.Bhattacharyya
  (bhattacharyya exp_neg_kl_divergence_le_bhattacharyya_sq)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt)
open PetzPositiveTraceFidelity (traceDual_unital)
open PetzPositiveTracePostselection (mapDensityState ordinaryPetz)
open PetzPostselectionSpectralJensen (stateMatrix)
open PetzLikelihoodRectangularAmplitude (horizontal)

open private horizontal_mul_adjoint horizontal_cross_trace frobenius_eq_one_of_gram_trace
  sqrt_adjoint sqrt_eq_real_cfc from D5.S3.Quantum.Recovery.PetzLikelihoodRectangularAmplitude

namespace PetzDoubleCommutingSharpFour

private theorem exp_neg_half_sq (d : ℝ) : Real.exp (-d / 2) ^ 2 = Real.exp (-d) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

section Classical

variable {a b : Type*} [Fintype a] [Fintype b]

omit [Fintype b] in
private theorem output_nonneg (r : a → ℝ) (W : a → b → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hW : ∀ i y, 0 ≤ W i y) (y : b) :
    0 ≤ channelOutput W r y :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hr i) (hW i y)

/-- Exponential Jensen averages the posterior Hellinger lower bounds with the first marginal. -/
private theorem average_posterior_affinity (r s : a → ℝ) (W : a → b → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hs : ∀ i, 0 ≤ s i)
    (hac : ∀ i, s i = 0 → r i = 0) (hW : ∀ i y, 0 ≤ W i y)
    (hP : ∑ y, channelOutput W r y = 1) :
    Real.exp (-(∑ y, channelOutput W r y *
        klDivergence (posterior W r y) (posterior W s y)) / 2) ≤
      ∑ y, channelOutput W r y * bhattacharyya (posterior W r y) (posterior W s y) := by
  let P := channelOutput W r
  let Q := channelOutput W s
  let d := fun y => klDivergence (posterior W r y) (posterior W s y)
  let A := fun y => bhattacharyya (posterior W r y) (posterior W s y)
  have hP0 := output_nonneg r W hr hW
  have hQ0 := output_nonneg s W hs hW
  have hmean : (∑ y, P y * (-d y / 2)) = -(∑ y, P y * d y) / 2 := by
    rw [← Finset.sum_neg_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  change Real.exp (-(∑ y, P y * d y) / 2) ≤ ∑ y, P y * A y
  rw [← hmean]
  calc
    _ ≤ ∑ y, P y * Real.exp (-d y / 2) := by
      simpa only [smul_eq_mul] using
        (convexOn_exp.map_sum_le (t := Finset.univ) (w := P) (p := fun y => -d y / 2)
          (fun y _ => hP0 y) hP (fun y _ => Set.mem_univ (-d y / 2)))
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : P y = 0
      · simp [hy]
      have hqy : Q y ≠ 0 :=
        fun h => hy (channel_output_absolute_continuity r s W hs hac hW y h)
      have hrpost : (∀ i, 0 ≤ posterior W r y i) ∧ ∑ i, posterior W r y i = 1 := by
        constructor
        · exact fun i => div_nonneg (mul_nonneg (hr i) (hW i y)) (hP0 y)
        · simp only [posterior, ← Finset.sum_div]
          exact div_self hy
      have hspost (i : a) : 0 ≤ posterior W s y i :=
        div_nonneg (mul_nonneg (hs i) (hW i y)) (hQ0 y)
      have hpostac (i : a) (hi : posterior W s y i = 0) : posterior W r y i = 0 := by
        have hnum : s i * W i y = 0 := by
          by_contra h
          exact (div_ne_zero h hqy) hi
        rcases mul_eq_zero.mp hnum with hsi | hWiy
        · simp [posterior, hac i hsi]
        · simp [posterior, hWiy]
      have hsq : Real.exp (-d y) ≤ A y ^ 2 :=
        exp_neg_kl_divergence_le_bhattacharyya_sq
          (posterior W r y) (posterior W s y) hrpost hspost hpostac
      have hA0 : 0 ≤ A y := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
      apply mul_le_mul_of_nonneg_left _ (hP0 y)
      exact (sq_le_sq₀ (Real.exp_pos _).le hA0).mp
        ((exp_neg_half_sq (d y)).le.trans hsq)

/-- Rescaling a posterior contribution gives its term in the unnormalized block overlap. -/
private theorem weighted_affinity_term (r s w P Q : ℝ)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hw : 0 ≤ w) (hP : 0 ≤ P) :
    P * Real.sqrt ((r * w / P) * (s * w / Q)) =
      Real.sqrt (P / Q) * (Real.sqrt r * Real.sqrt s * w) := by
  by_cases hPz : P = 0
  · simp [hPz]
  by_cases hQz : Q = 0
  · simp [hQz]
  have hroot : 0 < Real.sqrt P := Real.sqrt_pos.2 (lt_of_le_of_ne hP (Ne.symm hPz))
  have hcancel : P / Real.sqrt P = Real.sqrt P :=
    (div_eq_iff hroot.ne').2 (Real.mul_self_sqrt hP).symm
  rw [Real.sqrt_mul (div_nonneg (mul_nonneg hr hw) hP),
    Real.sqrt_div (mul_nonneg hr hw), Real.sqrt_div (mul_nonneg hs hw),
    Real.sqrt_mul hr, Real.sqrt_mul hs, Real.sqrt_div hP]
  calc
    _ = (P / Real.sqrt P) * (Real.sqrt r * Real.sqrt s * (Real.sqrt w * Real.sqrt w)) /
          Real.sqrt Q := by ring
    _ = _ := by rw [hcancel, Real.mul_self_sqrt hw]; ring

end Classical

section Coordinates

variable {n : Type*} [Fintype n] [DecidableEq n]

private abbrev fromBasis (U : Matrix.unitaryGroup n ℂ) :=
  Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U

private def realDiagonal (x : n → ℝ) : Matrix n n ℂ :=
  Matrix.diagonal fun i => (x i : ℂ)

private def mass (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) (i : n) : ℝ :=
  ((fromBasis U).symm X i i).re

private theorem trace_fromBasis (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    (fromBasis U X).trace = X.trace := by
  rw [fromBasis, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, Matrix.one_mul]

private theorem trace_toBasis (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    ((fromBasis U).symm X).trace = X.trace := by
  simpa only [StarAlgEquiv.apply_symm_apply] using
    (trace_fromBasis U ((fromBasis U).symm X)).symm

private theorem toBasis_pos (U : Matrix.unitaryGroup n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) : ((fromBasis U).symm X).PosSemidef :=
  hX.conjTranspose_mul_mul_same U.val

private theorem mass_nonneg (U : Matrix.unitaryGroup n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) (i : n) : 0 ≤ mass U X i :=
  (Complex.nonneg_iff.mp ((toBasis_pos U hX).diag_nonneg (i := i))).1

private theorem sum_mass (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) :
    ∑ i, mass U X i = X.trace.re := by
  rw [← trace_toBasis U X]
  simp only [mass, Matrix.trace, Matrix.diag_apply, Complex.re_sum]

private theorem fromBasis_diagonal (U : Matrix.unitaryGroup n ℂ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) (hdiag : ((fromBasis U).symm X).IsDiag) :
    X = fromBasis U (realDiagonal (mass U X)) := by
  have h : realDiagonal (mass U X) = (fromBasis U).symm X := by
    calc
      _ = Matrix.diagonal (Matrix.diag ((fromBasis U).symm X)) := by
        apply congrArg Matrix.diagonal
        funext i
        exact (toBasis_pos U hX).isHermitian.coe_re_apply_self i
      _ = _ := hdiag.diagonal_diag
  rw [h, StarAlgEquiv.apply_symm_apply]

private theorem shared_diagonal (X Y : Matrix n n ℂ)
    (hX : X.IsHermitian) (hY : Y.IsHermitian) (hXY : Commute X Y) :
    ∃ U : Matrix.unitaryGroup n ℂ,
      ((fromBasis U).symm X).IsDiag ∧ ((fromBasis U).symm Y).IsDiag := by
  refine ⟨Matrix.sharedEigenvectorUnitary hX hY hXY, ?_, ?_⟩
  · exact Matrix.SharedEigenbasis.star_shared_mul_A_mul_IsDiag hX hY hXY
  · exact Matrix.SharedEigenbasis.star_shared_mul_B_mul_IsDiag hX hY hXY

private theorem cfc_fromBasis (U : Matrix.unitaryGroup n ℂ) {X : Matrix n n ℂ}
    (hX : X.IsHermitian) {x : n → ℝ} (h : X = fromBasis U (realDiagonal x)) (f : ℝ → ℝ) :
    cfc f X = fromBasis U (realDiagonal fun i => f (x i)) := by
  rw [hX.cfc_eq f]
  have h' : X = U.val * Matrix.diagonal (RCLike.ofReal ∘ x) * star U.val := by
    simpa only [fromBasis, Unitary.conjStarAlgAut_apply, realDiagonal, Function.comp_def,
      RCLike.ofReal_eq_complex_ofReal] using h
  simpa only [fromBasis, Unitary.conjStarAlgAut_apply, realDiagonal, Function.comp_def,
    RCLike.ofReal_eq_complex_ofReal] using hX.cfc_eq_any_unitary h' f

private theorem realDiagonal_mul (x y : n → ℝ) :
    realDiagonal x * realDiagonal y = realDiagonal (fun i => x i * y i) := by
  simp only [realDiagonal, Matrix.diagonal_mul_diagonal, ← Complex.ofReal_mul]

omit [Fintype n] in
private theorem realDiagonal_sub (x y : n → ℝ) :
    realDiagonal x - realDiagonal y = realDiagonal (fun i => x i - y i) := by
  simp only [realDiagonal, Matrix.diagonal_sub, ← Complex.ofReal_sub]

private theorem toBasis_mulVec (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) (v : n → ℂ) :
    (fromBasis U).symm X *ᵥ ((star U : Matrix n n ℂ) *ᵥ v) =
      (star U : Matrix n n ℂ) *ᵥ (X *ᵥ v) := by
  simp only [fromBasis, Unitary.conjStarAlgAut_symm_apply, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [show U.val * star U.val = 1 from Unitary.coe_mul_star_self U, Matrix.mul_one]

private theorem fromBasis_mulVec (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) (v : n → ℂ) :
    fromBasis U X *ᵥ (U.val *ᵥ v) = U.val *ᵥ (X *ᵥ v) := by
  simp only [fromBasis, Unitary.conjStarAlgAut_apply, Matrix.mulVec_mulVec,
    Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.mul_one]

/-- In the common basis, support containment is absolute continuity of the two spectra. -/
private theorem support_iff (U : Matrix.unitaryGroup n ℂ) (ρ σ : DensityState n)
    (r s : n → ℝ) (hr : stateMatrix ρ = fromBasis U (realDiagonal r))
    (hs : stateMatrix σ = fromBasis U (realDiagonal s)) :
    SupportContained ρ σ ↔ ∀ i, s i = 0 → r i = 0 := by
  constructor
  · intro h i hi
    let e : n → ℂ := Pi.single i 1
    have hσe : realDiagonal s *ᵥ e = 0 := by
      funext j
      by_cases hj : j = i <;>
        simp [realDiagonal, Matrix.mulVec_diagonal, e, hj, hi]
    have hσ : stateMatrix σ *ᵥ (U.val *ᵥ e) = 0 := by
      rw [hs, fromBasis_mulVec, hσe, Matrix.mulVec_zero]
    have hρ : stateMatrix ρ *ᵥ (U.val *ᵥ e) = 0 := h hσ
    have hvec := toBasis_mulVec U (stateMatrix ρ) (U.val *ᵥ e)
    rw [hρ, Matrix.mulVec_zero, Matrix.mulVec_mulVec e, Unitary.coe_star_mul_self,
      Matrix.one_mulVec, hr, StarAlgEquiv.symm_apply_apply] at hvec
    have hi' := congrFun hvec i
    simpa [realDiagonal, Matrix.mulVec_diagonal, e] using hi'
  · intro h v hv
    change stateMatrix σ *ᵥ v = 0 at hv
    change stateMatrix ρ *ᵥ v = 0
    let z := (star U : Matrix n n ℂ) *ᵥ v
    have hσz : realDiagonal s *ᵥ z = 0 := by
      have hh := toBasis_mulVec U (stateMatrix σ) v
      rwa [hv, Matrix.mulVec_zero, hs, StarAlgEquiv.symm_apply_apply] at hh
    have hρz : realDiagonal r *ᵥ z = 0 := by
      funext i
      have hi := congrFun hσz i
      simp only [realDiagonal, Matrix.mulVec_diagonal, Pi.zero_apply] at hi ⊢
      rcases mul_eq_zero.mp hi with hsi | hzi
      · simp [h i (Complex.ofReal_eq_zero.mp hsi)]
      · simp [hzi]
    have hvz : U.val *ᵥ z = v := by
      dsimp only [z]
      rw [Matrix.mulVec_mulVec,
        show U.val * (star U : Matrix n n ℂ) = 1 from Unitary.coe_mul_star_self U,
        Matrix.one_mulVec]
    rw [← hvz, hr, fromBasis_mulVec, hρz, Matrix.mulVec_zero]

private theorem trace_diagonal_mul_re (U : Matrix.unitaryGroup n ℂ) (x : n → ℝ)
    (B : Matrix n n ℂ) :
    (fromBasis U (realDiagonal x) * B).trace.re = ∑ i, x i * mass U B i := by
  calc
    _ = (fromBasis U (realDiagonal x * (fromBasis U).symm B)).trace.re := by
      rw [map_mul, StarAlgEquiv.apply_symm_apply]
    _ = _ := by
      rw [trace_fromBasis]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul,
        realDiagonal, Complex.re_sum, Complex.re_ofReal_mul, mass]

private theorem finiteTraceLog_eq_kl (U : Matrix.unitaryGroup n ℂ) (ρ σ : DensityState n)
    (r s : n → ℝ) (hr : stateMatrix ρ = fromBasis U (realDiagonal r))
    (hs : stateMatrix σ = fromBasis U (realDiagonal s)) (hSupp : SupportContained ρ σ) :
    finiteTraceLogRelativeEntropy ρ σ = klDivergence r s := by
  have hac := (support_iff U ρ σ r s hr hs).mp hSupp
  rw [PetzSingularInputLimit.finiteTraceLog_eq_raw]
  change (stateMatrix ρ * (cfc Real.log (stateMatrix ρ) -
    cfc Real.log (stateMatrix σ))).trace.re = _
  rw [cfc_fromBasis U (density_posSemidef ρ).isHermitian hr,
    cfc_fromBasis U (density_posSemidef σ).isHermitian hs,
    hr, ← map_sub, ← map_mul, realDiagonal_sub, realDiagonal_mul, trace_fromBasis]
  simp only [realDiagonal, Matrix.trace_diagonal, Complex.re_sum, Complex.ofReal_re,
    klDivergence]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : r i = 0
  · simp [hi]
  · rw [Real.log_div hi (fun h => hi (hac i h))]

private def projector (U : Matrix.unitaryGroup n ℂ) (i : n) : Matrix n n ℂ :=
  fromBasis U (Matrix.single i i 1)

private theorem projector_pos (U : Matrix.unitaryGroup n ℂ) (i : n) :
    (projector U i).PosSemidef := by
  have hdiag : (Matrix.single i i (1 : ℂ)).PosSemidef := by
    rw [← Matrix.diagonal_single, Matrix.posSemidef_diagonal_iff]
    intro j
    by_cases hj : j = i <;> simp [hj]
  exact hdiag.mul_mul_conjTranspose_same U.val

private theorem sum_projector (U : Matrix.unitaryGroup n ℂ) :
    (∑ i, projector U i) = 1 := by
  simp only [projector, ← map_sum, Matrix.sum_single_one, map_one]

private theorem trace_mul_projector (U : Matrix.unitaryGroup n ℂ) (X : Matrix n n ℂ) (i : n) :
    (X * projector U i).trace = (fromBasis U).symm X i i := by
  calc
    _ = (fromBasis U ((fromBasis U).symm X * Matrix.single i i 1)).trace := by
      rw [map_mul, StarAlgEquiv.apply_symm_apply, projector]
    _ = _ := by rw [trace_fromBasis, Matrix.trace_mul_single, MulOpposite.op_one, one_smul]

private theorem diagonal_eq_sum_projector (U : Matrix.unitaryGroup n ℂ) (x : n → ℝ) :
    fromBasis U (realDiagonal x) = ∑ i, x i • projector U i := by
  rw [realDiagonal, ← Matrix.sum_single_eq_diagonal, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  change _ = (x i : ℂ) • fromBasis U (Matrix.single i i 1)
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

end Coordinates

section Recovery

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- For a positive trace-preserving map and supported density states commuting
both before and after the map, the squared full trace-norm error of the actual
ordinary Petz state is bounded by four times one minus the exponential of
negative finite Umegaki loss. -/
theorem traceNorm_sub_ordinaryPetz_sq_le_four_one_sub_exp_neg_umegakiLoss
    (ρ σ : DensityState a) (hSupp : SupportContained ρ σ)
    (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive) (hTP : Φ.IsTracePreserving)
    (hIn : Commute (stateMatrix ρ) (stateMatrix σ))
    (hOut : Commute (Φ (stateMatrix ρ)) (Φ (stateMatrix σ))) :
    let Δ := finiteTraceLogRelativeEntropy ρ σ -
      finiteTraceLogRelativeEntropy (mapDensityState Φ hΦ hTP ρ) (mapDensityState Φ hΦ hTP σ)
    traceNorm (stateMatrix ρ - ordinaryPetz Φ (stateMatrix σ) (Φ (stateMatrix ρ))) ^ 2 ≤
      4 * (1 - Real.exp (-Δ)) := by
  let R := stateMatrix ρ
  let S := stateMatrix σ
  let ρout := mapDensityState Φ hΦ hTP ρ
  let σout := mapDensityState Φ hΦ hTP σ
  let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy ρout σout
  change traceNorm (R - ordinaryPetz Φ S (Φ R)) ^ 2 ≤ 4 * (1 - Real.exp (-Δ))
  have hRpos : R.PosSemidef := density_posSemidef ρ
  have hSpos : S.PosSemidef := density_posSemidef σ
  obtain ⟨U, hRU, hSU⟩ := shared_diagonal R S hRpos.isHermitian hSpos.isHermitian hIn
  obtain ⟨V, hRV, hSV⟩ :=
    shared_diagonal (Φ R) (Φ S) (hΦ hRpos).isHermitian (hΦ hSpos).isHermitian hOut
  let r := mass U R
  let s := mass U S
  have hR : R = fromBasis U (realDiagonal r) := fromBasis_diagonal U hRpos hRU
  have hS : S = fromBasis U (realDiagonal s) := fromBasis_diagonal U hSpos hSU
  have hRtr : R.trace = 1 := ρ.2.2
  have hStr : S.trace = 1 := σ.2.2
  have hr : (∀ i, 0 ≤ r i) ∧ (∑ i, r i) = 1 :=
    ⟨mass_nonneg U hRpos, by rw [show (∑ i, r i) = R.trace.re from sum_mass U R, hRtr,
      Complex.one_re]⟩
  have hs : (∀ i, 0 ≤ s i) ∧ (∑ i, s i) = 1 :=
    ⟨mass_nonneg U hSpos, by rw [show (∑ i, s i) = S.trace.re from sum_mass U S, hStr,
      Complex.one_re]⟩
  have hac := (support_iff U ρ σ r s hR hS).mp hSupp
  -- Pull back the output projectors to obtain the stochastic kernel.
  let E := fun y : b => Φ.dual (projector V y)
  have hE (y : b) : (E y).PosSemidef := hΦ.dual (projector_pos V y)
  have hEsum : (∑ y, E y) = 1 := by
    change (∑ y, Φ.dual (projector V y)) = 1
    rw [← map_sum, sum_projector, traceDual_unital Φ hTP]
  let W := fun i y => mass U (E y) i
  have hW₀ (i : a) (y : b) : 0 ≤ W i y := mass_nonneg U (hE y) i
  have hW : (∀ i y, 0 ≤ W i y) ∧ ∀ i, ∑ y, W i y = 1 := by
    refine ⟨hW₀, fun i => ?_⟩
    have h := congrArg (fun B => mass U B i) hEsum
    simpa only [mass, map_sum, Matrix.sum_apply, Complex.re_sum, map_one, Matrix.one_apply_eq,
      Complex.one_re, W] using h
  have hMarginal (X : Matrix a a ℂ) (hX : X = fromBasis U (realDiagonal (mass U X))) :
      channelOutput W (mass U X) = mass V (Φ X) := by
    funext y
    calc
      channelOutput W (mass U X) y =
          (fromBasis U (realDiagonal (mass U X)) * E y).trace.re :=
        (trace_diagonal_mul_re U (mass U X) (E y)).symm
      _ = (X * E y).trace.re := congrArg (fun M => (M * E y).trace.re) hX.symm
      _ = ((Φ X) * projector V y).trace.re :=
        congrArg Complex.re (MatrixMap.Dual.trace_eq Φ X (projector V y)).symm
      _ = mass V (Φ X) y := congrArg Complex.re (trace_mul_projector V (Φ X) y)
  let P := channelOutput W r
  let Q := channelOutput W s
  have hPcoord : P = mass V (Φ R) := hMarginal R hR
  have hQcoord : Q = mass V (Φ S) := hMarginal S hS
  have hOutR : Φ R = fromBasis V (realDiagonal P) := by
    rw [hPcoord]
    exact fromBasis_diagonal V (hΦ hRpos) hRV
  have hOutS : Φ S = fromBasis V (realDiagonal Q) := by
    rw [hQcoord]
    exact fromBasis_diagonal V (hΦ hSpos) hSV
  have hPsum : (∑ y, P y) = 1 := by
    rw [hPcoord, sum_mass, hTP R, hRtr, Complex.one_re]
  have hP₀ := output_nonneg r W hr.1 hW₀
  have hQ₀ := output_nonneg s W hs.1 hW₀
  have hPQ (y : b) : Q y = 0 → P y = 0 :=
    channel_output_absolute_continuity r s W hs.1 hac hW₀ y
  have hOutSupp : SupportContained ρout σout :=
    (support_iff V ρout σout P Q hOutR hOutS).mpr hPQ
  have hLoss : Δ = ∑ y, P y * klDivergence (posterior W r y) (posterior W s y) := by
    change finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy ρout σout = _
    rw [finiteTraceLog_eq_kl U ρ σ r s hR hS hSupp,
      finiteTraceLog_eq_kl V ρout σout P Q hOutR hOutS hOutSupp]
    have h := classical_dpi_identity_zero_support r s W hr hs hac hW
    change klDivergence r s = klDivergence P Q +
      ∑ y, P y * klDivergence (posterior W r y) (posterior W s y) at h
    linarith only [h]
  -- The supported inverse square root gives the scalar output likelihood ratios.
  let T := CFC.sqrt R
  let B := CFC.sqrt S
  let H := spectralInverseSqrt (Φ S)
  let ratio := fun y => P y / Q y
  have hratio (y : b) : 0 ≤ ratio y := div_nonneg (hP₀ y) (hQ₀ y)
  have hH : H = fromBasis V (realDiagonal fun y => (Real.sqrt (Q y))⁻¹) :=
    cfc_fromBasis V (hΦ hSpos).isHermitian hOutS (fun x => (Real.sqrt x)⁻¹)
  have hSandwich : H * Φ R * H = ∑ y, ratio y • projector V y := by
    calc
      _ = fromBasis V (realDiagonal ratio) := by
        rw [hH, hOutR, ← map_mul, ← map_mul, realDiagonal_mul, realDiagonal_mul]
        apply congrArg (fun x : b → ℝ => fromBasis V (realDiagonal x))
        funext y
        change (Real.sqrt (Q y))⁻¹ * P y * (Real.sqrt (Q y))⁻¹ = P y / Q y
        calc
          _ = P y * (Real.sqrt (Q y) * Real.sqrt (Q y))⁻¹ := by
            rw [_root_.mul_inv_rev]
            ring
          _ = _ := by rw [Real.mul_self_sqrt (hQ₀ y), div_eq_mul_inv]
      _ = _ := diagonal_eq_sum_projector V ratio
  have hWeighted : (∑ y, ratio y • E y) = Φ.dual (H * Φ R * H) := by
    rw [hSandwich, map_sum]
    simp only [LinearMap.map_smul_of_tower, E]
  -- The two block matrices have the required states as their left Grams.
  let X := horizontal (fun y => T * CFC.sqrt (E y))
  let Y := horizontal (fun y => Real.sqrt (ratio y) • (B * CFC.sqrt (E y)))
  have hblock (A : Matrix a a ℂ) (y : b) :
      (A * CFC.sqrt (E y)) * (A * CFC.sqrt (E y))ᴴ = A * E y * Aᴴ := by
    rw [Matrix.conjTranspose_mul, sqrt_adjoint]
    calc
      _ = A * (CFC.sqrt (E y) * CFC.sqrt (E y)) * Aᴴ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self (E y) (hE y).nonneg]
  have hX : X * Xᴴ = R := by
    dsimp only [X]
    rw [horizontal_mul_adjoint]
    simp_rw [hblock]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hEsum, Matrix.mul_one,
      show Tᴴ = T from sqrt_adjoint R, CFC.sqrt_mul_sqrt_self R hRpos.nonneg]
  have hY : Y * Yᴴ = ordinaryPetz Φ S (Φ R) := by
    change Y * Yᴴ = B * Φ.dual (H * Φ R * H) * B
    dsimp only [Y]
    rw [horizontal_mul_adjoint]
    have hYblock (y : b) :
        (Real.sqrt (ratio y) • (B * CFC.sqrt (E y))) *
          (Real.sqrt (ratio y) • (B * CFC.sqrt (E y)))ᴴ = B * (ratio y • E y) * B := by
      simp only [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
        smul_smul, Real.mul_self_sqrt (hratio y), hblock, show Bᴴ = B from sqrt_adjoint S]
    simp_rw [hYblock]
    rw [← Matrix.sum_mul, ← Matrix.mul_sum, hWeighted]
  have hPetzSum : ordinaryPetz Φ S (Φ R) = ∑ y, ratio y • (B * E y * B) := by
    change B * Φ.dual (H * Φ R * H) * B = _
    rw [← hWeighted, Matrix.mul_sum, Matrix.sum_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hTraceEffect (y : b) : (B * E y * B).trace = (Q y : ℂ) := by
    change (CFC.sqrt S * Φ.dual (projector V y) * CFC.sqrt S).trace = _
    rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self S hSpos.nonneg,
      ← MatrixMap.Dual.trace_eq, trace_mul_projector, hOutS, StarAlgEquiv.symm_apply_apply]
    simp [realDiagonal]
  have hPetzTrace : (ordinaryPetz Φ S (Φ R)).trace = 1 := by
    rw [hPetzSum, Matrix.trace_sum]
    simp only [Matrix.trace_smul, Complex.real_smul, hTraceEffect, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum]
    have hcancel (y : b) : ratio y * Q y = P y := by
      dsimp only [ratio]
      by_cases hy : Q y = 0
      · simp [hy, hPQ y hy]
      · exact div_mul_cancel₀ _ hy
    rw [Finset.sum_congr rfl (fun y _ => hcancel y), hPsum, Complex.ofReal_one]
  -- The overlap is governed by the posteriors of the same stochastic kernel.
  have hCrossBlock (y : b) :
      ((T * CFC.sqrt (E y))ᴴ * (Real.sqrt (ratio y) • (B * CFC.sqrt (E y)))).trace =
        Real.sqrt (ratio y) • ((T * B) * E y).trace := by
    let D := CFC.sqrt (E y)
    change ((T * D)ᴴ * (Real.sqrt (ratio y) • (B * D))).trace = _
    simp only [Matrix.mul_smul, Matrix.conjTranspose_mul, Matrix.trace_smul,
      show Dᴴ = D from sqrt_adjoint (E y), show Tᴴ = T from sqrt_adjoint R]
    congr 1
    calc
      _ = (D * ((T * B) * D)).trace := by simp only [Matrix.mul_assoc]
      _ = (((T * B) * D) * D).trace := Matrix.trace_mul_comm _ _
      _ = _ := by rw [Matrix.mul_assoc, CFC.sqrt_mul_sqrt_self (E y) (hE y).nonneg]
  have hRoots : T * B = fromBasis U (realDiagonal fun i => Real.sqrt (r i) * Real.sqrt (s i)) := by
    change CFC.sqrt R * CFC.sqrt S = _
    rw [sqrt_eq_real_cfc hRpos, sqrt_eq_real_cfc hSpos,
      cfc_fromBasis U hRpos.isHermitian hR, cfc_fromBasis U hSpos.isHermitian hS,
      ← map_mul, realDiagonal_mul]
  have hCross : (Xᴴ * Y).trace.re =
      ∑ y, P y * bhattacharyya (posterior W r y) (posterior W s y) := by
    dsimp only [X, Y]
    rw [horizontal_cross_trace, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro y _
    rw [hCrossBlock, Complex.real_smul, Complex.re_ofReal_mul, hRoots, trace_diagonal_mul_re]
    rw [bhattacharyya, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact (weighted_affinity_term (r i) (s i) (W i y) (P y) (Q y)
      (hr.1 i) (hs.1 i) (hW₀ i y) (hP₀ y)).symm
  have hOverlap : Real.exp (-Δ / 2) ≤ (Xᴴ * Y).trace.re := by
    rw [hLoss, hCross]
    exact average_posterior_affinity r s W hr.1 hs.1 hac hW₀ hPsum
  have hNormX := frobenius_eq_one_of_gram_trace X (by rw [hX, hRtr])
  have hNormY := frobenius_eq_one_of_gram_trace Y (by rw [hY, hPetzTrace])
  have hGram := PetzPostselectedReference.traceNorm_gram_sub_sq_le X Y hNormX hNormY
  have hOverlapSq := pow_le_pow_left₀ (Real.exp_pos (-Δ / 2)).le hOverlap 2
  rw [exp_neg_half_sq Δ] at hOverlapSq
  calc
    _ ≤ 4 * (1 - (Xᴴ * Y).trace.re ^ 2) := by simpa only [hX, hY] using hGram
    _ ≤ _ := by linarith only [hOverlapSq]

end Recovery

end PetzDoubleCommutingSharpFour
