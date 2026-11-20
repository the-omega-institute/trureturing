import D5.S3.Analytic.PetzStripFiniteSeries
import D5.S3.Quantum.Recovery.PetzPhysicalCoordinates
import D5.S3.Quantum.Recovery.PetzOverlapEntropyDerivative
import D5.S3.Quantum.Recovery.PetzBoundaryTraceConsumer

/-!
# Faithful partial-trace Petz recovery

The physical overlap gives the entropy loss as the sum of the two weighted
boundary errors. The retained-dimension estimate controls the amplitude at
zero rotation, where its Gram matrix is the ordinary Petz output.
-/

set_option autoImplicit false

noncomputable section

open Matrix MeasureTheory
open scoped BigOperators ComplexOrder Kronecker MatrixOrder Matrix.Norms.Frobenius
open D5.S3.Quantum.Information.PartialTraceMutualInformation (partialTraceRight)
open D5.S3.Quantum.Divergence.UmegakiReferenceTransport (partialTraceRight_posDef)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm traceNorm_nonneg)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)
open PetzPhysicalAmplitude PetzPhysicalCoordinates PetzOverlapEntropyDerivative
open PetzExponentialBoundaryEvaluation (petzWeight)
open PetzCothStripMode (lowerWeight)
open PetzStripFiniteSeries
open PetzBoundaryTraceConsumer (traceNorm_gram_sub_le_two)

namespace PetzFaithfulDimensionRecovery

universe u

variable {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
variable {ρ σ : Matrix (A × B) (A × B) ℂ}

private theorem sqrt_conjTranspose (hρ : ρ.PosDef) :
    (cfc Real.sqrt ρ)ᴴ = cfc Real.sqrt ρ := by
  have hreal : star (((1 / 2 : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [← spectralCPow_half hρ, spectralCPow_conjTranspose, hreal]

section Strip

variable [Nonempty B]

theorem gamma_zero (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    gamma hρ hσ 0 = cfc Real.sqrt ρ := by
  simp only [gamma, neg_zero, spectralCPow_zero, Matrix.one_mul, lift,
    Matrix.one_kronecker_one, sub_zero, spectralCPow_half]

/-- On the lower boundary all factors around the input square root are unitary. -/
theorem gamma_lower_frobenius_eq_one (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1) (s : ℝ) :
    ‖gamma hρ hσ ((s : ℂ) * Complex.I)‖ = 1 := by
  let hp := partialTraceRight_posDef (R := A) (a := B) ρ hρ
  let hq := partialTraceRight_posDef (R := A) (a := B) σ hσ
  let z := (s : ℂ) * Complex.I
  let U := spectralCPow hσ z
  let Q := spectralCPow hq (-z)
  let P := spectralCPow hp z
  let V := spectralCPow hρ (-z)
  let L := U * lift (B := B) (Q * P)
  let S := cfc Real.sqrt ρ
  have hneg : -z = ((-s : ℝ) : ℂ) * Complex.I := by
    dsimp only [z]
    rw [Complex.ofReal_neg, neg_mul]
  have hU : Uᴴ * U = 1 := (spectralCPow_imaginary_unitary hσ s).2
  have hQ : Qᴴ * Q = 1 := by
    dsimp only [Q]
    rw [hneg]
    exact (spectralCPow_imaginary_unitary hq (-s)).2
  have hP : Pᴴ * P = 1 := (spectralCPow_imaginary_unitary hp s).2
  have hV : V * Vᴴ = 1 := by
    dsimp only [V]
    rw [hneg]
    exact (spectralCPow_imaginary_unitary hρ (-s)).1
  have hRetained : (Q * P)ᴴ * (Q * P) = 1 := by
    calc
      _ = Pᴴ * (Qᴴ * Q) * P := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hQ, Matrix.mul_one, hP]
  have hL : Lᴴ * L = 1 := by
    calc
      _ = (lift (B := B) (Q * P))ᴴ * (Uᴴ * U) * lift (Q * P) := by
        simp only [L, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by
        rw [hU, Matrix.mul_one, lift_conjTranspose, ← lift_mul, hRetained,
          lift, Matrix.one_kronecker_one]
  have hGamma : gamma hρ hσ z = L * S * V := by
    unfold gamma
    rw [sub_eq_add_neg, ← spectralCPow_mul, spectralCPow_half]
    simp only [L, U, P, Q, V, S, hp, hq, Matrix.mul_assoc]
  have hTrace : ((L * S * V)ᴴ * (L * S * V)).trace = (Sᴴ * S).trace := by
    calc
      _ = (Vᴴ * (Sᴴ * (Lᴴ * L) * S) * V).trace := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (Vᴴ * (Sᴴ * S) * V).trace := by rw [hL, Matrix.mul_one]
      _ = (V * Vᴴ * (Sᴴ * S)).trace := Matrix.trace_mul_cycle _ _ _
      _ = _ := by rw [hV, Matrix.one_mul]
  change ‖gamma hρ hσ z‖ = 1
  have hSq : ((‖gamma hρ hσ z‖ ^ 2 : ℝ) : ℂ) = ((‖S‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [hGamma, frobenius_norm_sq_eq_trace] using hTrace
  have hNorm : ‖gamma hρ hσ z‖ = ‖S‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by
      simpa only [Complex.ofReal_re] using congrArg Complex.re hSq)
  exact hNorm.trans (sqrt_frobenius_eq_one hρ htrace)

/-- One frequency for each pair of full eigenvector indices and retained projectors. -/
abbrev OverlapIndex (A B : Type u) := ((A × B) × (A × B)) × (A × A)

/-- The actual trace overlap is a finite exponential series on the entire complex plane. -/
theorem overlap_eq_finiteOverlap (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ∃ (ω : OverlapIndex A B → ℝ) (c : OverlapIndex A B → ℂ),
      overlap hρ hσ = finiteOverlap ω c := by
  let ratio (i j : A × B) (k : A × A) : ℝ :=
    outerSpectrum hρ hσ (i, j) / (retainedSpectrum hσ k.1 / retainedSpectrum hρ k.2)
  let ω (m : OverlapIndex A B) : ℝ := Real.log (ratio m.1.1 m.1.2 m.2)
  let entry (m : OverlapIndex A B) : Matrix (A × B) (A × B) ℂ :=
    Matrix.single m.1.1 m.1.2 (retainedCoordinates hρ hσ m.2 m.1.1 m.1.2)
  let U : Matrix (A × B) (A × B) ℂ := hσ.isHermitian.eigenvectorUnitary
  let V : Matrix (A × B) (A × B) ℂ := hρ.isHermitian.eigenvectorUnitary
  let component (m : OverlapIndex A B) : Matrix (A × B) (A × B) ℂ :=
    U * entry m * star V
  have hExp (i j : A × B) (k : A × A) (z : ℂ) :
      (ratio i j k : ℂ) ^ z = Complex.exp ((ω ((i, j), k) : ℂ) * z) := by
    have hpos : 0 < ratio i j k :=
      div_pos (outerSpectrum_pos hρ hσ (i, j))
        (div_pos (retainedSpectrum_pos hσ k.1) (retainedSpectrum_pos hρ k.2))
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),
      ← Complex.ofReal_log hpos.le]
  have hCoordinates (z : ℂ) :
      mixedCoordinates hρ hσ (gamma hρ hσ z) =
        ∑ m : OverlapIndex A B, Complex.exp ((ω m : ℂ) * z) • entry m := by
    calc
      _ = ∑ i : A × B, ∑ j : A × B,
          Matrix.single i j (mixedCoordinates hρ hσ (gamma hρ hσ z) i j) :=
        Matrix.matrix_eq_sum_single _
      _ = _ := by
        rw [Fintype.sum_prod_type (α₁ := (A × B) × (A × B)) (α₂ := A × A)]
        rw [Fintype.sum_prod_type (α₁ := A × B) (α₂ := A × B)]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        calc
          _ = ∑ k : A × A, Matrix.single i j
                ((ratio i j k : ℂ) ^ z * retainedCoordinates hρ hσ k i j) := by
              rw [gamma_coordinate]
              exact map_sum (Matrix.singleAddMonoidHom i j) _ Finset.univ
          _ = _ := by
              refine Finset.sum_congr rfl fun k _ => ?_
              simp only [entry, Matrix.smul_single, smul_eq_mul, hExp]
  have hAmplitude (z : ℂ) :
      gamma hρ hσ z =
        ∑ m : OverlapIndex A B, Complex.exp ((ω m : ℂ) * z) • component m := by
    have hU : U * star U = 1 := Unitary.coe_mul_star_self hσ.isHermitian.eigenvectorUnitary
    have hV : V * star V = 1 := Unitary.coe_mul_star_self hρ.isHermitian.eigenvectorUnitary
    calc
      _ = (U * star U) * gamma hρ hσ z * (V * star V) := by
        rw [hU, hV, Matrix.one_mul, Matrix.mul_one]
      _ = U * mixedCoordinates hρ hσ (gamma hρ hσ z) * star V := by
        simp only [mixedCoordinates, U, V, Matrix.mul_assoc]
      _ = _ := by
        rw [hCoordinates]
        simp only [component, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨ω, fun m => (cfc Real.sqrt ρ * component m).trace, ?_⟩
  funext z
  unfold overlap
  rw [finiteOverlap_eq_trace, ← hAmplitude z]

private theorem overlap_deficit_eq_frobenius_sq (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1) (z : ℂ) (hGamma : ‖gamma hρ hσ z‖ = 1) :
    2 * (1 - (overlap hρ hσ z).re) = ‖cfc Real.sqrt ρ - gamma hρ hσ z‖ ^ 2 := by
  let S := cfc Real.sqrt ρ
  let G := gamma hρ hσ z
  have hS : Sᴴ = S := sqrt_conjTranspose hρ
  have hSNorm : ‖S‖ = 1 := sqrt_frobenius_eq_one hρ htrace
  have hGNorm : ‖G‖ = 1 := hGamma
  have hCross : (Gᴴ * S).trace = star ((S * G).trace) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hS]
  have hSq (M : Matrix (A × B) (A × B) ℂ) : ‖M‖ ^ 2 = (Mᴴ * M).trace.re := by
    simpa only [Complex.ofReal_re] using congrArg Complex.re (frobenius_norm_sq_eq_trace M)
  change 2 * (1 - (S * G).trace.re) = ‖S - G‖ ^ 2
  symm
  calc
    _ = ((Sᴴ * S).trace.re - (Sᴴ * G).trace.re) -
        ((Gᴴ * S).trace.re - (Gᴴ * G).trace.re) := by
      rw [hSq (S - G)]
      simp only [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
        Complex.sub_re]
      ring
    _ = _ := by
      rw [← hSq S, ← hSq G, hS, hCross, Complex.star_def, Complex.conj_re, hSNorm, hGNorm]
      ring

/-- The nonnegative lower-boundary integral can be dropped from the entropy identity. -/
theorem upper_boundary_integral_le_entropyLoss (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1) :
    (∫ s : ℝ, petzWeight s * ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent s)‖ ^ 2) ≤
      entropyLoss ρ σ := by
  obtain ⟨ω, c, hSeries⟩ := overlap_eq_finiteOverlap hρ hσ
  have hZero : overlap hρ hσ 0 = 1 := by
    unfold overlap
    rw [gamma_zero]
    calc
      _ = (cfc Real.sqrt ρ * (cfc Real.sqrt ρ)ᴴ).trace := by rw [sqrt_conjTranspose hρ]
      _ = 1 := by rw [sqrt_gram hρ, htrace]
  have hNormalized : (finiteOverlap ω c 0).re = 1 := by
    rw [← hSeries, hZero, Complex.one_re]
  have hLower (s : ℝ) : overlapDeficit ω c 0 s =
      ‖cfc Real.sqrt ρ - gamma hρ hσ ((s : ℂ) * Complex.I)‖ ^ 2 := by
    change 2 * (1 - (finiteOverlap ω c (((0 : ℝ) : ℂ) + (s : ℂ) * Complex.I)).re) = _
    rw [Complex.ofReal_zero, zero_add, ← hSeries]
    exact overlap_deficit_eq_frobenius_sq hρ hσ htrace _
      (gamma_lower_frobenius_eq_one hρ hσ htrace s)
  have hUpper (s : ℝ) : overlapDeficit ω c (1 / 2) s =
      ‖cfc Real.sqrt ρ - gamma hρ hσ (upperExponent s)‖ ^ 2 := by
    change 2 * (1 - (finiteOverlap ω c (upperExponent s)).re) = _
    rw [← hSeries]
    exact overlap_deficit_eq_frobenius_sq hρ hσ htrace _
      (gamma_upper_frobenius_eq_one hρ hσ htrace s)
  have hLowerNonneg (s : ℝ) : 0 ≤ overlapDeficit ω c 0 s := by
    rw [hLower]
    exact sq_nonneg _
  have hUpperNonneg (s : ℝ) : 0 ≤ overlapDeficit ω c (1 / 2) s := by
    rw [hUpper]
    exact sq_nonneg _
  have hLoss := (integral_finiteOverlap_strip ω c hNormalized hLowerNonneg hUpperNonneg).2.2
  rw [← hSeries, overlap_deriv_zero_re hρ hσ, neg_neg] at hLoss
  have hNonneg : 0 ≤ ∫ s : ℝ, lowerWeight s * overlapDeficit ω c 0 s :=
    integral_nonneg fun s => mul_nonneg
      (div_nonneg Real.pi_pos.le (sub_nonneg.mpr (Real.one_le_cosh _))) (hLowerNonneg s)
  calc
    _ = ∫ s : ℝ, petzWeight s * overlapDeficit ω c (1 / 2) s := by simp only [hUpper]
    _ ≤ _ := by
      rw [← hLoss]
      exact le_add_of_nonneg_left hNonneg

end Strip

/-- The squared trace norm of the ordinary partial-trace Petz error is at most
`8 * (1 + (card A)^2)` times the actual Umegaki entropy loss. -/
theorem traceNorm_sub_ordinaryPetz_sq_le (hρ : ρ.PosDef) (hσ : σ.PosDef)
    (htrace : ρ.trace = 1) :
    traceNorm (ρ - ordinaryPetz σ (partialTraceRight ρ)) ^ 2 ≤
      (8 * (1 + (Fintype.card A : ℝ) ^ 2)) * entropyLoss ρ σ := by
  letI : Nonempty B := Classical.byContradiction fun h => by
    have hzero : ρ.trace = 0 := by
      unfold Matrix.trace
      exact Finset.sum_eq_zero (fun i _ => (h ⟨i.2⟩).elim)
    exact one_ne_zero (htrace.symm.trans hzero)
  let S := cfc Real.sqrt ρ
  let G := gamma hρ hσ (upperExponent 0)
  have hHalf : upperExponent 0 = ((1 / 2 : ℝ) : ℂ) := by
    simp only [upperExponent, Complex.ofReal_zero, zero_mul, add_zero]
  have hG : G * Gᴴ = ordinaryPetz σ (partialTraceRight ρ) := by
    simpa only [G, hHalf] using gamma_half_gram hρ hσ
  have hS : S * Sᴴ = ρ := sqrt_gram hρ
  have hTrace : traceNorm (ρ - ordinaryPetz σ (partialTraceRight ρ)) ≤ 2 * ‖S - G‖ := by
    simpa only [hS, hG] using traceNorm_gram_sub_le_two G S
      (gamma_upper_frobenius_eq_one hρ hσ htrace 0) (sqrt_frobenius_eq_one hρ htrace)
  calc
    _ ≤ (2 * ‖S - G‖) ^ 2 := pow_le_pow_left₀ (traceNorm_nonneg _) hTrace 2
    _ = 4 * ‖S - G‖ ^ 2 := by ring
    _ ≤ 4 * ((2 * ((1 + Fintype.card A ^ 2 : ℕ) : ℝ)) *
          (∫ s : ℝ, petzWeight s * ‖S - gamma hρ hσ (upperExponent s)‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (weighted_evaluation_physical_boundary hρ hσ).2 (by norm_num)
    _ ≤ 4 * ((2 * ((1 + Fintype.card A ^ 2 : ℕ) : ℝ)) * entropyLoss ρ σ) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (upper_boundary_integral_le_entropyLoss hρ hσ htrace)
          (by positivity)) (by norm_num)
    _ = _ := by
      simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_one]
      ring

end PetzFaithfulDimensionRecovery
