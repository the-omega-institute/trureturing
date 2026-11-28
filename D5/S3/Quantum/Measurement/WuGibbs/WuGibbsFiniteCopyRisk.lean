/- GID: D5/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk
   generality: I
   mirror-B: D5/B/S3/Quantum/Measurement/WuGibbs/WuGibbsFiniteCopyRisk
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The physical one-mode Wu deficit bounds the probability gap of every collective binary effect at every finite copy count. -/

import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability
import D5.S3.Quantum.Measurement.Auric.DiamondBounds
import D5.S3.Quantum.Semigroups.WuQubitSharpTwoPhysical

/-!
# Finite-copy testing against Wu's Gibbs state

Symmetrizing the difference of the squares of the two positive roots gives
the affinity bound in trace distance via the Hilbert–Schmidt product inequality.
The affinity of the actual tensor powers is the power of the one-copy affinity.
-/

noncomputable section

open _root_.Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Measurement.WuGibbsFiniteCopyRisk

set_option autoImplicit false

open D5.S3.Quantum.Entanglement.PrecessionSpinOneSeparableBound (entryNormSq)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_mul_le_hsSq)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_eq_max_re_tr_U)
open D5.S3.Quantum.Measurement.AdvantageQuantumNonSimulability (copyState)
open D5.S3.Quantum.Measurement.Auric.DiamondBounds (twice_effect_trace_le_traceNorm)
open D5.S3.Quantum.Matrix.SpectralPower (mpow)
open D5.S3.Quantum.Semigroups.WuQubitSharpTwoPhysical
  (Qubit gibbs ratePlus rateMinus energy entropy exact_affinity_stability)
open D5.S3.Quantum.Semigroups.WuQubitSharpTwoRigidity
  (exactAffinityCoefficient exactAffinityCoefficient_pos sharpCoefficient)

open scoped Matrix.Norms.Frobenius in
private theorem entryNormSq_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ) : entryNormSq M = (Mᴴ * M).trace.re := by
  rw [D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability.entryNormSq_eq_hs_sq]
  simpa only [Complex.ofReal_re] using
    congrArg Complex.re (D5.S3.Quantum.GNSMatrix.frobenius_norm_sq_eq_trace M)

/-- The ordinary affinity of two positive roots controls the full half trace
distance of finite-dimensional density matrices, including singular states. -/
theorem traceNorm_sub_half_le_sqrt_one_sub_affinity_sq
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hρtr : ρ.trace = 1) (hσtr : σ.trace = 1) :
    traceNorm (ρ - σ) / 2 ≤ Real.sqrt (1 - (CFC.sqrt ρ * CFC.sqrt σ).trace.re ^ 2) := by
  let P := CFC.sqrt ρ
  let Q := CFC.sqrt σ
  let a := (P * Q).trace.re
  let X := P - Q
  let Y := P + Q
  have hPstar : Pᴴ = P := (CFC.sqrt_nonneg ρ).posSemidef.isHermitian.eq
  have hQstar : Qᴴ = Q := (CFC.sqrt_nonneg σ).posSemidef.isHermitian.eq
  have hP2 : P * P = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hQ2 : Q * Q = σ := CFC.sqrt_mul_sqrt_self σ hσ.nonneg
  have hXX : Xᴴ * X = ρ + σ - (P * Q + Q * P) := by
    rw [show Xᴴ = X by simp only [X, Matrix.conjTranspose_sub, hPstar, hQstar]]
    calc
      X * X = P * P + Q * Q - (P * Q + Q * P) := by
        dsimp only [X]
        noncomm_ring
      _ = _ := by rw [hP2, hQ2]
  have hYY : Yᴴ * Y = ρ + σ + (P * Q + Q * P) := by
    rw [show Yᴴ = Y by simp only [Y, Matrix.conjTranspose_add, hPstar, hQstar]]
    calc
      Y * Y = P * P + Q * Q + (P * Q + Q * P) := by
        dsimp only [Y]
        noncomm_ring
      _ = _ := by rw [hP2, hQ2]
  have hXnorm : entryNormSq X = 2 - 2 * a := by
    rw [entryNormSq_eq_trace, hXX]
    simp only [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re,
      hρtr, hσtr, Complex.one_re, Matrix.trace_mul_comm Q P]
    change 1 + 1 - (a + a) = 2 - 2 * a
    ring
  have hYnorm : entryNormSq Y = 2 + 2 * a := by
    rw [entryNormSq_eq_trace, hYY]
    simp only [Matrix.trace_add, Complex.add_re, hρtr, hσtr, Complex.one_re,
      Matrix.trace_mul_comm Q P]
    change 1 + 1 + (a + a) = 2 + 2 * a
    ring
  have hXnonneg : 0 ≤ 2 - 2 * a := by
    rw [← hXnorm]
    unfold entryNormSq
    positivity
  have hdouble : (ρ - σ) + (ρ - σ) = X * Y + Y * X := by
    calc
      _ = (P * P - Q * Q) + (P * P - Q * Q) := by rw [hP2, hQ2]
      _ = _ := by
        dsimp only [X, Y]
        noncomm_ring
  obtain ⟨U, hU⟩ := (traceNorm_eq_max_re_tr_U (ρ - σ)).1
  change (U.val * (ρ - σ)).trace.re = traceNorm (ρ - σ) at hU
  have hdual (M : Matrix ι ι ℂ) : (U.val * M).trace.re ≤ traceNorm M :=
    (traceNorm_eq_max_re_tr_U M).2 ⟨U, rfl⟩
  have hsum := congrArg (fun M : Matrix ι ι ℂ => (U.val * M).trace.re) hdouble
  change (U.val * ((ρ - σ) + (ρ - σ))).trace.re =
    (U.val * (X * Y + Y * X)).trace.re at hsum
  simp only [Matrix.mul_add, Matrix.trace_add, Complex.add_re, hU] at hsum
  have hXY := traceNorm_mul_le_hsSq X Y
  have hYX := traceNorm_mul_le_hsSq Y X
  rw [hXnorm, hYnorm] at hXY hYX
  rw [mul_comm (Real.sqrt (2 + 2 * a)) (Real.sqrt (2 - 2 * a))] at hYX
  change traceNorm (ρ - σ) / 2 ≤ Real.sqrt (1 - a ^ 2)
  calc
    _ ≤ Real.sqrt (2 - 2 * a) * Real.sqrt (2 + 2 * a) / 2 := by
      linarith only [hsum, hdual (X * Y), hdual (Y * X), hXY, hYX]
    _ = _ := by
      have hfactor : (2 - 2 * a) * (2 + 2 * a) = 4 * (1 - a ^ 2) := by ring
      have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      rw [← Real.sqrt_mul hXnonneg, hfactor, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
        hsqrt4]
      ring

private theorem copyState_mul {ι : Type*} [Fintype ι]
    (n : ℕ) (A B : Matrix ι ι ℂ) :
    copyState n A * copyState n B = copyState n (A * B) := by
  ext x y
  simp only [Matrix.mul_apply, copyState, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (k : Fin n) (j : ι) => A (x k) j * B j (y k))).symm

private theorem copyState_conjTranspose {ι : Type*} (n : ℕ) (A : Matrix ι ι ℂ) :
    (copyState n A)ᴴ = copyState n Aᴴ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, copyState, star_prod]

private theorem copyState_posSemidef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    (copyState n A).PosSemidef := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  change A = Bᴴ * B at hB
  rw [hB, ← copyState_mul, ← copyState_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

private theorem trace_copyState {ι : Type*} [Fintype ι]
    (n : ℕ) (A : Matrix ι ι ℂ) : (copyState n A).trace = A.trace ^ n := by
  exact (Fintype.sum_pow (fun i => A i i) n).symm

private theorem sqrt_copyState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) {A : Matrix ι ι ℂ} (hA : A.PosSemidef) :
    CFC.sqrt (copyState n A) = copyState n (CFC.sqrt A) := by
  apply CFC.sqrt_unique
  · rw [copyState_mul, CFC.sqrt_mul_sqrt_self A hA.nonneg]
  · exact (copyState_posSemidef n (CFC.sqrt_nonneg A).posSemidef).nonneg

private theorem affinity_trace_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) : 0 ≤ (CFC.sqrt A * CFC.sqrt B).trace :=
  (CFC.sqrt_nonneg A).posSemidef.trace_mul_nonneg (CFC.sqrt_nonneg B).posSemidef

private theorem affinity_copyState {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : ℕ) {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (CFC.sqrt (copyState n A) * CFC.sqrt (copyState n B)).trace.re =
      (CFC.sqrt A * CFC.sqrt B).trace.re ^ n := by
  rw [sqrt_copyState n hA, sqrt_copyState n hB, copyState_mul, trace_copyState]
  let z := (CFC.sqrt A * CFC.sqrt B).trace
  have hz : (z.re : ℂ) = z := Complex.ext rfl
    (by simpa only [Complex.ofReal_im] using (Complex.nonneg_iff.mp
      (affinity_trace_nonneg A B)).2)
  change (z ^ n).re = z.re ^ n
  calc
    (z ^ n).re = ((z.re : ℂ) ^ n).re :=
      congrArg (fun w : ℂ => (w ^ n).re) hz.symm
    _ = _ := by rw [← Complex.ofReal_pow, Complex.ofReal_re]

private theorem gibbs_density (h : ℝ) : (gibbs h).PosSemidef ∧ (gibbs h).trace = 1 := by
  have hd : 0 < 2 * Real.cosh h := mul_pos (by norm_num) (Real.cosh_pos h)
  have hp : 0 ≤ ratePlus h := div_nonneg (Real.exp_pos h).le hd.le
  have hm : 0 ≤ rateMinus h := div_nonneg (Real.exp_pos (-h)).le hd.le
  have hsum : ratePlus h + rateMinus h = 1 := by
    unfold ratePlus rateMinus
    rw [← add_div, Real.cosh_eq]
    have he : 0 < Real.exp h + Real.exp (-h) := add_pos (Real.exp_pos _) (Real.exp_pos _)
    rw [show 2 * ((Real.exp h + Real.exp (-h)) / 2) =
      Real.exp h + Real.exp (-h) by ring, div_self he.ne']
  constructor
  · unfold gibbs
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr hp
    · exact Complex.zero_le_real.mpr hm
  · rw [gibbs, Matrix.trace_diagonal, Fin.sum_univ_two]
    change (ratePlus h : ℂ) + (rateMinus h : ℂ) = 1
    rw [← Complex.ofReal_add, hsum, Complex.ofReal_one]

private theorem mpow_half_eq_sqrt {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.PosSemidef) : mpow A (1 / 2) = CFC.sqrt A := by
  rw [mpow, ← CFC.rpow_eq_cfc_real hA.nonneg, ← CFC.sqrt_eq_rpow]

/-- Every collective binary effect has absolute probability gap bounded by the
half trace distance, the tensorized affinity envelope, and its deficit-only
envelope. For equal priors, half the probability gap bounds the success
advantage over random guessing. -/
theorem collective_effect_gap_le {h : ℝ} (hh : 0 ≤ h) {ρ : Qubit}
    (hρ : ρ.PosSemidef) (hρtr : ρ.trace = 1) (n : ℕ)
    (E : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ)
    (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef) :
    let A := (CFC.sqrt ρ * CFC.sqrt (gibbs h)).trace.re
    let δ := energy h ρ - sharpCoefficient h * entropy h ρ
    let L := max 0 (1 - Real.sqrt (δ / exactAffinityCoefficient h))
    let D := copyState n ρ - copyState n (gibbs h)
    |(E * D).trace.re| ≤ traceNorm D / 2 ∧
      traceNorm D / 2 ≤ Real.sqrt (1 - (A ^ n) ^ 2) ∧
      Real.sqrt (1 - (A ^ n) ^ 2) ≤ Real.sqrt (1 - (L ^ n) ^ 2) := by
  let A := (CFC.sqrt ρ * CFC.sqrt (gibbs h)).trace.re
  let δ := energy h ρ - sharpCoefficient h * entropy h ρ
  let L := max 0 (1 - Real.sqrt (δ / exactAffinityCoefficient h))
  let D := copyState n ρ - copyState n (gibbs h)
  change |(E * D).trace.re| ≤ traceNorm D / 2 ∧
    traceNorm D / 2 ≤ Real.sqrt (1 - (A ^ n) ^ 2) ∧
    Real.sqrt (1 - (A ^ n) ^ 2) ≤ Real.sqrt (1 - (L ^ n) ^ 2)
  obtain ⟨hG, hGtr⟩ := gibbs_density h
  have hρn := copyState_posSemidef n hρ
  have hGn := copyState_posSemidef n hG
  have hρntr : (copyState n ρ).trace = 1 := by rw [trace_copyState, hρtr, one_pow]
  have hGntr : (copyState n (gibbs h)).trace = 1 := by rw [trace_copyState, hGtr, one_pow]
  have hD : D.IsHermitian := hρn.isHermitian.sub hGn.isHermitian
  have hDtr : D.trace = 0 := by simp only [D, Matrix.trace_sub, hρntr, hGntr, sub_self]
  have hupper := twice_effect_trace_le_traceNorm D E hD hDtr hE hEc
  have hlower := twice_effect_trace_le_traceNorm D (1 - E) hD hDtr hEc
    (by simpa only [sub_sub_cancel] using hE)
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.trace_sub, Complex.sub_re,
    hDtr, Complex.zero_re, zero_sub] at hlower
  refine ⟨abs_le.mpr ⟨by linarith only [hlower], by linarith only [hupper]⟩, ?_, ?_⟩
  · have hbound :=
      traceNorm_sub_half_le_sqrt_one_sub_affinity_sq hρn hGn hρntr hGntr
    rw [affinity_copyState n hρ hG] at hbound
    exact hbound
  · have hstab : exactAffinityCoefficient h * (1 - A) ^ 2 ≤ δ := by
      simpa only [A, δ, mpow_half_eq_sqrt hρ, mpow_half_eq_sqrt hG] using
        exact_affinity_stability hh hρ hρtr
    have hsquare : (1 - A) ^ 2 ≤ δ / exactAffinityCoefficient h := by
      apply (le_div_iff₀ (exactAffinityCoefficient_pos hh)).mpr
      simpa only [mul_comm] using hstab
    have hroot : 1 - A ≤ Real.sqrt (δ / exactAffinityCoefficient h) :=
      Real.le_sqrt_of_sq_le hsquare
    have hA : 0 ≤ A := (Complex.nonneg_iff.mp (affinity_trace_nonneg ρ (gibbs h))).1
    have hL : 0 ≤ L := le_max_left _ _
    have hLA : L ≤ A := max_le hA (by linarith only [hroot])
    have hpow : L ^ n ≤ A ^ n := pow_le_pow_left₀ hL hLA n
    exact Real.sqrt_le_sqrt
      (sub_le_sub_left (pow_le_pow_left₀ (pow_nonneg hL n) hpow 2) 1)

end D5.S3.Quantum.Measurement.WuGibbsFiniteCopyRisk
