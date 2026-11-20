import D5.S3.Quantum.Recovery.PetzPositiveTraceFidelity
import D5.S3.Quantum.Recovery.PetzPostselectedPartialTrace

/-! Ordinary Petz recovery for finite positive trace-preserving maps after
a commuting spectral postselection. All support projections and inverse
roots are evaluated on the original finite matrix carriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Foundation.FiniteStateChannel (DensityState)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Foundation.FiniteTraceDistance
  (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open D5.S3.Quantum.CommutingMidpoint (rootFidelity)
open D5.S3.Quantum.Information.PartialTraceMutualInformation (density_posSemidef)
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy
  (SupportContained finiteTraceLogRelativeEntropy)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransport
  (positive_map_sandwich_support spectral_sqrt_normalization support_of_nonneg_le_smul)
open D5.S3.Quantum.Lieb.SupportPerspectiveTransformer (spectral_sqrt_inverse_products)
open D5.S3.Quantum.Recovery.SpectralTransposeRecovery (spectralInverseSqrt spectralSupport)
open PetzPositiveTraceFidelity (rootFidelity_mono_positive_tracePreserving traceDual_unital)
open PetzPostselectedReference
  (finiteTraceLogRelativeEntropy_of_postselection sqrt_mul_sqrt_of_postselection
    traceNorm_gram_sub_sq_le)
open PetzPostselectionSpectralJensen
  (stateMatrix exp_half_entropy_le_trace_threeHalves_inverseSqrt)

namespace PetzPositiveTracePostselection

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The density state given by the actual positive trace-preserving map. -/
def mapDensityState (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) (ρ : DensityState a) : DensityState b :=
  ⟨CStarMatrix.ofMatrix (Φ (stateMatrix ρ)),
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv (hΦ (density_posSemidef ρ)).nonneg,
    (hTP (stateMatrix ρ)).trans ρ.2.2⟩

/-- The ordinary Petz image, using the trace dual and the supported inverse
square root of the actual output reference. -/
def ordinaryPetz (Φ : MatrixMap a b ℂ) (σ : Matrix a a ℂ) (p : Matrix b b ℂ) :
    Matrix a a ℂ :=
  let H := spectralInverseSqrt (Φ σ)
  CFC.sqrt σ * Φ.dual (H * p * H) * CFC.sqrt σ

private theorem sqrt_eq_cfc_real {X : Matrix a a ℂ} (hX : X.PosSemidef) :
    CFC.sqrt X = cfc Real.sqrt X := by
  rw [CFC.sqrt_eq_real_sqrt X hX.nonneg,
    cfcₙ_eq_cfc (f := Real.sqrt) (a := X) (hf0 := by simp)]

private theorem postselection_le_inv_smul (ρ σ : DensityState a)
    {P : Matrix a a ℂ} {t : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    stateMatrix ρ ≤ t⁻¹ • stateMatrix σ := by
  let S := stateMatrix σ
  have hscaled : t • stateMatrix ρ = S * P := by
    rw [hρ, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hcomm : (1 - P) * S = S * (1 - P) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hSP.symm.eq]
  have hproj : (1 - P) * (1 - P) = 1 - P := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPP]
    abel
  have hcomp : (1 - P) * S * (1 - P)ᴴ = S - t • stateMatrix ρ := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP, hcomm, Matrix.mul_assoc,
      hproj, Matrix.mul_sub, Matrix.mul_one, hscaled]
  have hdiff : (S - t • stateMatrix ρ).PosSemidef := by
    rw [← hcomp]
    exact (density_posSemidef σ).mul_mul_conjTranspose_same (1 - P)
  apply Matrix.le_iff.mpr
  simpa only [S, smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using
    hdiff.smul (inv_nonneg.mpr ht.le)

private theorem map_le (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {X Y : Matrix a a ℂ} (hXY : X ≤ Y) : Φ X ≤ Φ Y := by
  apply Matrix.le_iff.mpr
  rw [← map_sub]
  exact hΦ (Matrix.le_iff.mp hXY)

private theorem supportContained_of_le_smul (p q : DensityState a) (r : ℝ)
    (hle : stateMatrix p ≤ r • stateMatrix q) : SupportContained p q := by
  intro v hv
  change stateMatrix q *ᵥ v = 0 at hv
  change stateMatrix p *ᵥ v = 0
  have hp := density_posSemidef p
  have hnonneg := hp.dotProduct_mulVec_nonneg v
  have hdiff := (Matrix.le_iff.mp hle).dotProduct_mulVec_nonneg v
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hv, smul_zero, dotProduct_sub,
    dotProduct_zero, zero_sub] at hdiff
  exact hp.dotProduct_mulVec_zero_iff.mp (le_antisymm (neg_nonneg.mp hdiff) hnonneg)

private theorem ordinaryPetz_state (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {σ : Matrix a a ℂ} (hσ : σ.PosSemidef) {p : Matrix b b ℂ}
    (hp : p.PosSemidef) (htr : p.trace = 1) (r : ℝ) (hle : p ≤ r • Φ σ) :
    (ordinaryPetz Φ σ p).PosSemidef ∧ (ordinaryPetz Φ σ p).trace = 1 := by
  let q := Φ σ
  let H := spectralInverseSqrt q
  let Q := spectralSupport q
  let S := CFC.sqrt σ
  obtain ⟨_, hH, hQ, _, _, _, hQq, hHqH⟩ := spectral_sqrt_normalization q (hΦ hσ)
  change Hᴴ = H at hH
  change Qᴴ = Q at hQ
  change Q * q = q at hQq
  change H * q * H = Q at hHqH
  obtain ⟨hQp, _⟩ := support_of_nonneg_le_smul q p Q hQ hQq hp r hle
  have hS : Sᴴ = S := (CFC.sqrt_nonneg σ).posSemidef.isHermitian.eq
  have hM : (H * p * H).PosSemidef := by
    simpa only [hH] using hp.mul_mul_conjTranspose_same H
  change (S * Φ.dual (H * p * H) * S).PosSemidef ∧
    (S * Φ.dual (H * p * H) * S).trace = 1
  refine ⟨?_, ?_⟩
  · simpa only [hS] using (hΦ.dual hM).mul_mul_conjTranspose_same S
  · calc
      _ = (σ * Φ.dual (H * p * H)).trace := by
        rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self σ hσ.nonneg]
      _ = (q * (H * p * H)).trace := (MatrixMap.Dual.trace_eq Φ σ (H * p * H)).symm
      _ = ((H * q * H) * p).trace := by
        rw [← Matrix.mul_assoc q (H * p) H, Matrix.trace_mul_cycle q (H * p) H]
        simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hHqH, hQp, htr]

/-- Completion of the supported fidelity transport by preparation of the
input state with the trace mass on the complementary output subspace. -/
def fidelityTransport (Φ : MatrixMap a b ℂ) (B : Matrix a a ℂ) : MatrixMap b a ℂ where
  toFun X :=
    let S := CFC.sqrt B
    let D := spectralInverseSqrt (Φ B)
    let E := spectralSupport (Φ B)
    S * Φ.dual (D * X * D) * S + ((1 - E) * X).trace • B
  map_add' X Y := by
    dsimp only
    simp only [Matrix.mul_add, Matrix.add_mul, map_add, Matrix.trace_add, add_smul]
    abel
  map_smul' c X := by
    dsimp only [RingHom.id_apply]
    simp only [Matrix.mul_smul, Matrix.smul_mul, map_smul, Matrix.trace_smul, smul_eq_mul,
      smul_add, smul_smul]

private theorem fidelityTransport_positive (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {B : Matrix a a ℂ} (hB : B.PosSemidef) : (fidelityTransport Φ B).IsPositive := by
  let S := CFC.sqrt B
  let D := spectralInverseSqrt (Φ B)
  let E := spectralSupport (Φ B)
  obtain ⟨_, hD, hE, hEE, _, _, _, _⟩ := spectral_sqrt_normalization (Φ B) (hΦ hB)
  change Dᴴ = D at hD
  change Eᴴ = E at hE
  change E * E = E at hEE
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hcomp : (1 - E : Matrix b b ℂ).PosSemidef := by
    have hgram : (1 - E)ᴴ * (1 - E) = 1 - E := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hE,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hEE]
      abel
    rw [← hgram]
    exact Matrix.posSemidef_conjTranspose_mul_self (1 - E)
  intro X hX
  have hDXD : (D * X * D).PosSemidef := by
    simpa only [hD] using hX.mul_mul_conjTranspose_same D
  have hcore : (S * Φ.dual (D * X * D) * S).PosSemidef := by
    simpa only [hS] using (hΦ.dual hDXD).mul_mul_conjTranspose_same S
  exact hcore.add (hB.smul (hcomp.trace_mul_nonneg hX))

private theorem fidelityTransport_tracePreserving (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {B : Matrix a a ℂ} (hB : B.PosSemidef) (htr : B.trace = 1) :
    (fidelityTransport Φ B).IsTracePreserving := by
  let S := CFC.sqrt B
  let D := spectralInverseSqrt (Φ B)
  let E := spectralSupport (Φ B)
  obtain ⟨_, _, _, _, _, _, _, hDpD⟩ := spectral_sqrt_normalization (Φ B) (hΦ hB)
  change D * Φ B * D = E at hDpD
  intro X
  have hcore : (S * Φ.dual (D * X * D) * S).trace = (E * X).trace := by
    calc
      _ = (B * Φ.dual (D * X * D)).trace := by
        rw [Matrix.trace_mul_cycle, CFC.sqrt_mul_sqrt_self B hB.nonneg]
      _ = (Φ B * (D * X * D)).trace := (MatrixMap.Dual.trace_eq Φ B (D * X * D)).symm
      _ = ((D * Φ B * D) * X).trace := by
        rw [← Matrix.mul_assoc (Φ B) (D * X) D, Matrix.trace_mul_cycle (Φ B) (D * X) D]
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDpD]
  change (S * Φ.dual (D * X * D) * S + ((1 - E) * X).trace • B).trace = X.trace
  rw [Matrix.trace_add, hcore, Matrix.trace_smul, htr, smul_eq_mul, mul_one,
    Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub]
  abel

/-- Forward sandwiches by the input square root lie on the output support.
Trace duality gives the corresponding compression of the pulled-back effect. -/
private theorem dual_sandwich_supported (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {B : Matrix a a ℂ} (hB : B.PosSemidef) (Y : Matrix b b ℂ) :
    let S := CFC.sqrt B
    let E := spectralSupport (Φ B)
    S * Φ.dual (E * Y * E) * S = S * Φ.dual Y * S := by
  let S := CFC.sqrt B
  let E := spectralSupport (Φ B)
  let Ψ : Matrix a a ℂ →ₚ[ℂ] Matrix b b ℂ :=
    PositiveLinearMap.mk₀ Φ (fun _ hX => (hΦ hX.posSemidef).nonneg)
  have hHerm (Z : Matrix a a ℂ) (hZ : Z.IsHermitian) :
      E * Φ (S * Z * S) * E = Φ (S * Z * S) := by
    obtain ⟨hleft, hright⟩ := positive_map_sandwich_support Ψ B hB Z hZ
    change E * Φ (S * Z * S) = Φ (S * Z * S) at hleft
    change Φ (S * Z * S) * E = Φ (S * Z * S) at hright
    rw [hleft, hright]
  have hsupp (Z : Matrix a a ℂ) : E * Φ (S * Z * S) * E = Φ (S * Z * S) := by
    rw [← realPart_add_I_smul_imaginaryPart Z]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, map_add, map_smul]
    rw [hHerm _ (realPart Z).property, hHerm _ (imaginaryPart Z).property]
  have hpair (Z : Matrix a a ℂ) (K : Matrix b b ℂ) :
      (Z * (S * Φ.dual K * S)).trace = (Φ (S * Z * S) * K).trace := by
    rw [← Matrix.mul_assoc Z (S * Φ.dual K) S,
      Matrix.trace_mul_cycle Z (S * Φ.dual K) S,
      ← Matrix.mul_assoc (S * Z) S (Φ.dual K), ← MatrixMap.Dual.trace_eq]
  change S * Φ.dual (E * Y * E) * S = S * Φ.dual Y * S
  apply Matrix.ext_iff_trace_mul_left.mpr
  intro Z
  calc
    _ = (Φ (S * Z * S) * (E * Y * E)).trace := hpair Z _
    _ = ((E * Φ (S * Z * S) * E) * Y).trace := by
      rw [← Matrix.mul_assoc (Φ (S * Z * S)) (E * Y) E,
        Matrix.trace_mul_cycle (Φ (S * Z * S)) (E * Y) E]
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hsupp]; exact (hpair Z Y).symm

private theorem fidelityTransport_output (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) {B : Matrix a a ℂ} (hB : B.PosSemidef) :
    fidelityTransport Φ B (Φ B) = B := by
  let p := Φ B
  let S := CFC.sqrt B
  let D := spectralInverseSqrt p
  let E := spectralSupport p
  obtain ⟨_, _, _, hEE, _, _, hEp, hDpD⟩ := spectral_sqrt_normalization p (hΦ hB)
  change E * E = E at hEE
  change E * p = p at hEp
  change D * p * D = E at hDpD
  have hcomp : (1 - E) * p = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hEp, sub_self]
  have hcorner := dual_sandwich_supported Φ hΦ hB (1 : Matrix b b ℂ)
  change S * Φ.dual (E * 1 * E) * S = S * Φ.dual 1 * S at hcorner
  rw [Matrix.mul_one, hEE, traceDual_unital Φ hTP, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self B hB.nonneg] at hcorner
  change S * Φ.dual (D * p * D) * S + ((1 - E) * p).trace • B = B
  simpa only [hDpD, hcomp, Matrix.trace_zero, zero_smul, add_zero] using hcorner

/-- The retained positive test for the fidelity argument. -/
private def retainedTest (p M : Matrix b b ℂ) (t : ℝ) : Matrix b b ℂ :=
  t • (CFC.sqrt p * M * CFC.sqrt p)

private theorem fidelityTransport_retainedTest (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    {B : Matrix a a ℂ} (hB : B.PosSemidef) (M : Matrix b b ℂ) (t : ℝ) :
    fidelityTransport Φ B (retainedTest (Φ B) M t) =
      t • (CFC.sqrt B * Φ.dual M * CFC.sqrt B) := by
  let p := Φ B
  let V := CFC.sqrt p
  let D := spectralInverseSqrt p
  let E := spectralSupport p
  let S := CFC.sqrt B
  let W := retainedTest p M t
  obtain ⟨_, _, _, _, hEV, _, _, _⟩ := spectral_sqrt_normalization p (hΦ hB)
  obtain ⟨hVD, hDV, _, _⟩ := spectral_sqrt_inverse_products p (hΦ hB)
  change E * V = V at hEV
  change V * D = E at hVD
  change D * V = E at hDV
  have hEW : E * W = W := by
    change E * (t • (V * M * V)) = t • (V * M * V)
    simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hEV]
  have hcomp : (1 - E) * W = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, hEW, sub_self]
  have hDWD : D * W * D = t • (E * M * E) := by
    calc
      _ = t • ((D * V) * M * (V * D)) := by
        change D * (t • (V * M * V)) * D = _
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [hDV, hVD]
  change S * Φ.dual (D * W * D) * S + ((1 - E) * W).trace • B =
    t • (S * Φ.dual M * S)
  rw [hcomp, Matrix.trace_zero, zero_smul, add_zero, hDWD, Φ.dual.map_smul_of_tower,
    Matrix.mul_smul, Matrix.smul_mul, dual_sandwich_supported Φ hΦ hB M]

private theorem support_mul_sqrt_reference (ρ σ : DensityState a)
    {P : Matrix a a ℂ} {t : ℝ}
    (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let C := spectralSupport (stateMatrix ρ)
    let S := CFC.sqrt (stateMatrix ρ)
    let T := CFC.sqrt (stateMatrix σ)
    C * T = Real.sqrt t • S ∧ T * C = Real.sqrt t • S := by
  let B := stateMatrix ρ
  let C := spectralSupport B
  let D := spectralInverseSqrt B
  let S := CFC.sqrt B
  let T := CFC.sqrt (stateMatrix σ)
  have hB := density_posSemidef ρ
  obtain ⟨hS, _, hC, _, hCS, _, _, _⟩ := spectral_sqrt_normalization B hB
  obtain ⟨_, hDS, _, _⟩ := spectral_sqrt_inverse_products B hB
  change Sᴴ = S at hS
  change Cᴴ = C at hC
  change C * S = S at hCS
  change D * S = C at hDS
  have hT : Tᴴ = T := (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
  have hST : S * T = Real.sqrt t • B := by
    change CFC.sqrt (stateMatrix ρ) * CFC.sqrt (stateMatrix σ) = _
    rw [sqrt_eq_cfc_real hB, sqrt_eq_cfc_real (density_posSemidef σ)]
    exact sqrt_mul_sqrt_of_postselection hB (density_posSemidef σ) hSP hPP ht hρ
  have hDB : D * B = S := by
    calc
      D * B = D * (S * S) := by rw [CFC.sqrt_mul_sqrt_self B hB.nonneg]
      _ = S := by rw [← Matrix.mul_assoc, hDS, hCS]
  have hleft : C * T = Real.sqrt t • S := by
    rw [← hDS, Matrix.mul_assoc, hST, Matrix.mul_smul, hDB]
  change C * T = Real.sqrt t • S ∧ T * C = Real.sqrt t • S
  refine ⟨hleft, ?_⟩
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul, star_trivial, hS, hC, hT]
    using congrArg Matrix.conjTranspose hleft

private theorem fidelityTransport_petz_compression (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (ρ σ : DensityState a) {P : Matrix a a ℂ} {t : ℝ}
    (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let B := stateMatrix ρ
    let p := Φ B
    let H := spectralInverseSqrt (Φ (stateMatrix σ))
    let C := spectralSupport B
    fidelityTransport Φ B (retainedTest p (H * p * H) t) =
      C * ordinaryPetz Φ (stateMatrix σ) p * C := by
  let B := stateMatrix ρ
  let p := Φ B
  let H := spectralInverseSqrt (Φ (stateMatrix σ))
  let C := spectralSupport B
  let S := CFC.sqrt B
  let T := CFC.sqrt (stateMatrix σ)
  let M := H * p * H
  obtain ⟨hCT, hTC⟩ := support_mul_sqrt_reference ρ σ hPP hSP ht hρ
  change C * T = Real.sqrt t • S at hCT
  change T * C = Real.sqrt t • S at hTC
  change fidelityTransport Φ B (retainedTest p M t) = C * (T * Φ.dual M * T) * C
  calc
    _ = t • (S * Φ.dual M * S) :=
      fidelityTransport_retainedTest Φ hΦ (density_posSemidef ρ) M t
    _ = (C * T) * Φ.dual M * (T * C) := by
      rw [hCT, hTC]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt ht.le]
    _ = _ := by simp only [Matrix.mul_assoc]

private theorem rootFidelity_compress (B R : Matrix a a ℂ) (hB : B.PosSemidef) :
    rootFidelity B (spectralSupport B * R * spectralSupport B) = rootFidelity B R := by
  let C := spectralSupport B
  let S := CFC.sqrt B
  obtain ⟨_, _, _, _, hCS, hSC, _, _⟩ := spectral_sqrt_normalization B hB
  change C * S = S at hCS
  change S * C = S at hSC
  have h : S * (C * R * C) * S = S * R * S := by
    calc
      _ = (S * C) * R * (C * S) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSC, hCS]
  change (CFC.sqrt (S * (C * R * C) * S)).trace.re = (CFC.sqrt (S * R * S)).trace.re
  rw [h]

private theorem threeHalves_eq_mul_sqrt {p : Matrix b b ℂ} (hp : p.PosSemidef) :
    cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p = p * CFC.sqrt p := by
  rw [sqrt_eq_cfc_real hp]
  calc
    _ = cfc (fun x : ℝ => x * Real.sqrt x) p := by
      apply cfc_congr
      intro x hx
      change x ^ (3 / 2 : ℝ) = x * Real.sqrt x
      have hx₀ := spectrum_nonneg_of_nonneg hp.nonneg hx
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add_of_nonneg hx₀ zero_le_one (by norm_num), Real.rpow_one]
    _ = cfc (fun x : ℝ => x) p * cfc Real.sqrt p :=
      cfc_mul (fun x : ℝ => x) Real.sqrt p continuous_id.continuousOn
        Real.continuous_sqrt.continuousOn
    _ = _ := by rw [cfc_id' ℝ p hp.isHermitian.isSelfAdjoint]

private theorem retainedTest_fidelity_lower {p H : Matrix b b ℂ}
    (hp : p.PosSemidef) (hH : Hᴴ = H) {t : ℝ} (ht : 0 ≤ t) :
    Real.sqrt t * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p * H).trace.re ≤
      rootFidelity p (retainedTest p (H * p * H) t) := by
  let V := CFC.sqrt p
  let G : Matrix b b ℂ := Real.sqrt t • (V * H * p)
  have hV : Vᴴ = V := (CFC.sqrt_nonneg p).posSemidef.isHermitian.eq
  have hVV : V * V = p := CFC.sqrt_mul_sqrt_self p hp.nonneg
  have hGram : V * retainedTest p (H * p * H) t * V = Gᴴ * G := by
    calc
      _ = t • (p * (H * p * H) * p) := by
        change V * (t • (V * (H * p * H) * V)) * V = _
        rw [Matrix.mul_smul, Matrix.smul_mul]
        congr 1
        calc
          _ = (V * V) * (H * p * H) * (V * V) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hVV]
      _ = _ := by
        change _ = (Real.sqrt t • (V * H * p))ᴴ * (Real.sqrt t • (V * H * p))
        rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul,
          smul_smul, Real.mul_self_sqrt ht]
        congr 1
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hp.isHermitian.eq, hH, hV]
        symm
        calc
          _ = p * H * (V * V) * H * p := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hVV]; simp only [Matrix.mul_assoc]
  have htrace : G.trace.re =
      Real.sqrt t * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) p * H).trace.re := by
    change ((Real.sqrt t • (V * H * p)).trace).re = _
    rw [Matrix.trace_smul, Complex.real_smul, Complex.re_ofReal_mul,
      Matrix.trace_mul_cycle V H p, threeHalves_eq_mul_sqrt hp]
  have hmax : G.trace.re ≤ traceNorm G :=
    (traceNorm_eq_max_re_tr_U G).2 ⟨1, by simp⟩
  rw [← htrace]
  change G.trace.re ≤ (CFC.sqrt (V * retainedTest p (H * p * H) t * V)).trace.re
  rw [hGram]
  exact hmax

/-- A unitary attaining the trace-norm maximum supplies the second unit
amplitude for the symmetric Schatten estimate. -/
private theorem traceNorm_sub_sq_le_four_one_sub_fidelity_sq {B R : Matrix a a ℂ}
    (hB : B.PosSemidef) (hR : R.PosSemidef) (hBtr : B.trace = 1) (hRtr : R.trace = 1) :
    traceNorm (B - R) ^ 2 ≤ 4 * (1 - rootFidelity B R ^ 2) := by
  let S := CFC.sqrt B
  let T := CFC.sqrt R
  have hS : Sᴴ = S := (CFC.sqrt_nonneg B).posSemidef.isHermitian.eq
  have hT : Tᴴ = T := (CFC.sqrt_nonneg R).posSemidef.isHermitian.eq
  have hSS : S * S = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hTT : T * T = R := CFC.sqrt_mul_sqrt_self R hR.nonneg
  have hfid : traceNorm (T * S) = rootFidelity B R := by
    have hGram : (T * S)ᴴ * (T * S) = S * R * S := by
      rw [Matrix.conjTranspose_mul, hS, hT]
      calc
        _ = S * (T * T) * S := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hTT]
    change (CFC.sqrt ((T * S)ᴴ * (T * S))).trace.re = (CFC.sqrt (S * R * S)).trace.re
    rw [hGram]
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U (T * S)).1
  let V := T * U.valᴴ
  have hunit : U.valᴴ * U.val = 1 := Matrix.mem_unitaryGroup_iff'.mp U.prop
  have hSgram : S * Sᴴ = B := by rw [hS, hSS]
  have hVgram : V * Vᴴ = R := by
    change (T * U.valᴴ) * (T * U.valᴴ)ᴴ = R
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hT]
    calc
      _ = T * (U.valᴴ * U.val) * T := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hunit, Matrix.mul_one, hTT]
  have hnorm (X Y : Matrix a a ℂ) (hXY : X * Xᴴ = Y) (hY : Y.trace = 1) : ‖X‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg X) zero_le_one).mp
    have h := congrArg Complex.re (frobenius_norm_sq_eq_trace X)
    simpa only [Complex.ofReal_re, Matrix.trace_mul_comm Xᴴ X, hXY, hY,
      Complex.one_re, one_pow] using h
  have hcross : (Sᴴ * V).trace.re = rootFidelity B R := by
    have hadj : (Sᴴ * V)ᴴ = U.val * (T * S) := by
      change (Sᴴ * (T * U.valᴴ))ᴴ = _
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hT,
        Matrix.mul_assoc]
    have hre : (Sᴴ * V).trace.re = ((Sᴴ * V)ᴴ).trace.re := by
      rw [Matrix.trace_conjTranspose] <;> rfl
    rw [hre, hadj, hU, hfid]
  simpa only [hcross, hSgram, hVgram] using
    traceNorm_gram_sub_sq_le S V (hnorm S B hSgram hBtr) (hnorm V R hVgram hRtr)

/-- For a spectral postselection and an actual positive trace-preserving map,
the squared full trace-norm error of ordinary Petz recovery is bounded by
both the nonlinear and linear expressions in the finite Umegaki loss. -/
theorem traceNorm_sub_ordinaryPetz_sq_le (Φ : MatrixMap a b ℂ) (hΦ : Φ.IsPositive)
    (hTP : Φ.IsTracePreserving) (ρ σ : DensityState a)
    {P : Matrix a a ℂ} {t : ℝ}
    (hP : Pᴴ = P) (hPP : P * P = P) (hSP : Commute (stateMatrix σ) P)
    (ht : 0 < t) (hρ : stateMatrix ρ = t⁻¹ • (stateMatrix σ * P)) :
    let p := mapDensityState Φ hΦ hTP ρ
    let q := mapDensityState Φ hΦ hTP σ
    let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
    let R := ordinaryPetz Φ (stateMatrix σ) (stateMatrix p)
    traceNorm (stateMatrix ρ - R) ^ 2 ≤ 4 * (1 - Real.exp (-Δ)) ∧
      4 * (1 - Real.exp (-Δ)) ≤ 4 * Δ := by
  let B := stateMatrix ρ
  let p := mapDensityState Φ hΦ hTP ρ
  let q := mapDensityState Φ hΦ hTP σ
  let Δ := finiteTraceLogRelativeEntropy ρ σ - finiteTraceLogRelativeEntropy p q
  let R := ordinaryPetz Φ (stateMatrix σ) (stateMatrix p)
  let H := spectralInverseSqrt (stateMatrix q)
  let M := H * stateMatrix p * H
  let W := retainedTest (stateMatrix p) M t
  let A := fidelityTransport Φ B
  have hB := density_posSemidef ρ
  have hp := density_posSemidef p
  have hq := density_posSemidef q
  have hle : stateMatrix p ≤ t⁻¹ • stateMatrix q := by
    change Φ (stateMatrix ρ) ≤ t⁻¹ • Φ (stateMatrix σ)
    simpa only [Φ.map_smul_of_tower] using
      map_le Φ hΦ (postselection_le_inv_smul ρ σ hP hPP hSP ht hρ)
  have hsupport : SupportContained p q := supportContained_of_le_smul p q t⁻¹ hle
  obtain ⟨hR, hRtr⟩ := ordinaryPetz_state Φ hΦ (density_posSemidef σ) hp p.2.2 t⁻¹ hle
  change R.PosSemidef at hR
  change R.trace = 1 at hRtr
  obtain ⟨_, hH, _, _, _, _, _, _⟩ := spectral_sqrt_normalization (stateMatrix q) hq
  change Hᴴ = H at hH
  have hM : M.PosSemidef := by
    simpa only [M, hH] using hp.mul_mul_conjTranspose_same H
  have hW : W.PosSemidef := by
    have hV : (CFC.sqrt (stateMatrix p))ᴴ = CFC.sqrt (stateMatrix p) :=
      (CFC.sqrt_nonneg _).posSemidef.isHermitian.eq
    change (t • (CFC.sqrt (stateMatrix p) * M * CFC.sqrt (stateMatrix p))).PosSemidef
    simpa only [hV] using (hM.mul_mul_conjTranspose_same (CFC.sqrt (stateMatrix p))).smul ht.le
  have hAp : A (stateMatrix p) = B := fidelityTransport_output Φ hΦ hTP hB
  have hAW : A W = spectralSupport B * R * spectralSupport B :=
    fidelityTransport_petz_compression Φ hΦ ρ σ hPP hSP ht hρ
  have hmono : rootFidelity (stateMatrix p) W ≤ rootFidelity B R := by
    have h := rootFidelity_mono_positive_tracePreserving A
      (fidelityTransport_positive Φ hΦ hB)
      (fidelityTransport_tracePreserving Φ hΦ hB ρ.2.2) (stateMatrix p) W hp hW
    rwa [hAp, hAW, rootFidelity_compress B R hB] at h
  have hlog : -Δ / 2 = Real.log t / 2 + finiteTraceLogRelativeEntropy p q / 2 := by
    dsimp only [Δ]
    rw [finiteTraceLogRelativeEntropy_of_postselection ρ σ hSP hPP ht hρ]
    ring
  have hmoment :
      Real.exp (-Δ / 2) ≤
        Real.sqrt t * (cfc (fun x : ℝ => x ^ (3 / 2 : ℝ)) (stateMatrix p) * H).trace.re := by
    rw [hlog, Real.exp_add, Real.exp_half (Real.log t), Real.exp_log ht]
    exact mul_le_mul_of_nonneg_left
      (exp_half_entropy_le_trace_threeHalves_inverseSqrt p q hsupport) (Real.sqrt_nonneg t)
  have hfid : Real.exp (-Δ / 2) ≤ rootFidelity B R :=
    hmoment.trans ((retainedTest_fidelity_lower hp hH ht.le).trans hmono)
  have hexp_sq : Real.exp (-Δ / 2) ^ 2 = Real.exp (-Δ) := by
    rw [pow_two, ← Real.exp_add, add_halves]
  have hsq : Real.exp (-Δ) ≤ rootFidelity B R ^ 2 := by
    rw [← hexp_sq]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hfid 2
  change traceNorm (B - R) ^ 2 ≤ 4 * (1 - Real.exp (-Δ)) ∧
    4 * (1 - Real.exp (-Δ)) ≤ 4 * Δ
  refine ⟨?_, by linarith only [Real.add_one_le_exp (-Δ)]⟩
  exact (traceNorm_sub_sq_le_four_one_sub_fidelity_sq hB hR ρ.2.2 hRtr).trans
    (by linarith only [hsq])

end PetzPositiveTracePostselection
