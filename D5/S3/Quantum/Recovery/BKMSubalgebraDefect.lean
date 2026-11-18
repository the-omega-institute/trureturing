/- GID: D5/S3/Quantum/Recovery/BKMSubalgebraDefect
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/BKMSubalgebraDefect
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive BKM transposes force commutation with reduced-state projections. -/

import D5.S3.Quantum.Matrix.BKMProjectionRigidity
import D5.S3.Quantum.Algebra.OrderedGNSProjection
import D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Isometric

/-! # Faithful finite matrix subalgebras and the actual BKM transpose -/

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra

namespace D5.S3.Quantum.Recovery.BKMSubalgebraDefect

open D5.S3.Quantum.Algebra.OrderedGNSProjection
open D5.S3.Quantum.Matrix.BKMLogarithmicMeanInverse
open D5.S3.Quantum.Matrix.BKMProjectionRigidity
open D5.S3.Quantum.Recovery.BKMMetricAdjointOrderObstruction (omega)
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM (traceNorm_mul_le_hsSq)
open D5.S3.Quantum.Foundation.HilbertSchmidtTraceStability (entryNormSq_eq_hs_sq)
open D5.S3.Quantum.GNSMatrix (frobenius_norm_sq_eq_trace)

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

private abbrev Mat (n : Type*) := Matrix n n ℂ

private def tracialDensity (n : Type*) [Fintype n] [DecidableEq n] : Mat n :=
  (1 / (Fintype.card n : ℝ)) • 1

private theorem tracialDensity_posDef : (tracialDensity n).PosDef :=
  Matrix.PosDef.one.smul (one_div_pos.mpr (by exact_mod_cast Fintype.card_pos))

private theorem tracialDensity_trace : (tracialDensity n).trace = 1 := by
  have hd : (Fintype.card n : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [tracialDensity, Matrix.trace_smul, Complex.real_smul, hd]

/-- The actual trace-orthogonal projection, with its codomain restricted to B. -/
def traceExpectation (B : StarSubalgebra ℂ (Mat n)) : Mat n →ₗ[ℂ] B :=
  LinearMap.codRestrict B.toSubmodule
    (projection (tracialDensity n) tracialDensity_posDef B)
    (ordered_gns_characterization _ tracialDensity_posDef tracialDensity_trace B).2.1

private theorem traceExpectation_contract (B : StarSubalgebra ℂ (Mat n)) :
    Expectation (tracialDensity n) B (projection (tracialDensity n) tracialDensity_posDef B) := by
  let ρ := tracialDensity n
  let hρ : ρ.PosDef := tracialDensity_posDef
  have ht (X : Mat n) : state ρ X = (1 / (Fintype.card n : ℝ)) • X.trace := by
    simp [ρ, tracialDensity, state, Matrix.trace_smul]
  have hGNS := ordered_gns_characterization ρ hρ tracialDensity_trace B
  apply hGNS.2.2.2.2.2.mp
  intro X b hb
  have h := hGNS.2.2.1 X (star b) (B.star_mem' hb)
  simpa only [star_star, ht, Matrix.trace_mul_comm b] using h

private theorem traceExpectation_mono (B : StarSubalgebra ℂ (Mat n)) :
    Monotone (fun X => (traceExpectation B X : Mat n)) := by
  intro X Y h
  change projection _ _ B X ≤ projection _ _ B Y
  rw [← sub_nonneg, ← map_sub, Matrix.nonneg_iff_posSemidef]
  exact (traceExpectation_contract B).2.2.1.1 (Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h))

private theorem traceExpectation_smul_one (B : StarSubalgebra ℂ (Mat n)) (r : ℝ) :
    (traceExpectation B (r • (1 : Mat n)) : Mat n) = r • 1 := by
  change ((projection _ _ B).restrictScalars ℝ) (r • (1 : Mat n)) = _
  rw [map_smul]
  exact congrArg (r • ·) (traceExpectation_contract B).1

private theorem reduced_posDef (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    (traceExpectation B a : Mat n).PosDef := by
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ ha.isHermitian.eigenvalues
    Finset.univ_nonempty
  let l := ha.isHermitian.eigenvalues i
  have hl : l • (1 : Mat n) ≤ a :=
    (Matrix.PosSemidef.smul_one_le_of_eigenvalues_iff ha.isHermitian l).mp
      (fun j => hi j (Finset.mem_univ j))
  have h := traceExpectation_mono B hl
  change (traceExpectation B (l • (1 : Mat n)) : Mat n) ≤ (traceExpectation B a : Mat n) at h
  rw [traceExpectation_smul_one] at h
  exact (Matrix.PosDef.one.smul (ha.eigenvalues_pos i)).isStrictlyPositive.of_le h |>.posDef

/-- The actual BKM transpose from B into the ambient complex matrix algebra. -/
def bkmTranspose (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    B →ₗ[ℂ] Mat n :=
  (omegaEquiv a ha).toLinearMap.comp
    (B.toSubmodule.subtype.comp
      (omegaRestrict B (traceExpectation B a) (reduced_posDef B a ha)).symm.toLinearMap)

/-- Positivity of the actual transpose forces every projection in B that
commutes with the reduced state to commute with the faithful ambient state. -/
theorem bkmTranspose_positive_commute (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef)
    (hpos : ∀ Y : B, (Y : Mat n).PosSemidef → (bkmTranspose B a ha Y).PosSemidef)
    (P : B) (hp : (P : Mat n).IsHermitian) (hp2 : (P : Mat n) * (P : Mat n) = P)
    (hc : Commute (traceExpectation B a : Mat n) (P : Mat n)) : Commute a (P : Mat n) := by
  let τ := traceExpectation B a
  let hτ := reduced_posDef B a ha
  let Y := omegaRestrict B τ hτ P
  have hY : (Y : Mat n).PosSemidef := by
    change (omegaRestrict B τ hτ P : Mat n).PosSemidef
    rw [omegaRestrict_apply, omega_of_commute _ _ hτ hc]
    have hcorner : (τ : Mat n) * (P : Mat n) = (P : Mat n) * (τ : Mat n) * (P : Mat n) := by
      calc
        (τ : Mat n) * (P : Mat n) = (τ : Mat n) * ((P : Mat n) * (P : Mat n)) := by rw [hp2]
        _ = _ := by rw [← mul_assoc, hc.eq]
    rw [hcorner]
    simpa only [hp.eq] using hτ.posSemidef.mul_mul_conjTranspose_same (P : Mat n)
  have h := hpos Y hY
  change (omegaEquiv a ha
    (((omegaRestrict B τ hτ).symm (omegaRestrict B τ hτ P) : B) : Mat n)).PosSemidef at h
  rw [LinearEquiv.symm_apply_apply, omegaEquiv_apply] at h
  exact (omega_projection_posSemidef_iff a P ha hp hp2).mp h

private def normalizedTests (B : StarSubalgebra ℂ (Mat n)) : Set B :=
  {Y | (Y : Mat n).PosSemidef ∧ (Y : Mat n).trace = 1}

/-- The supremum of negative spectral mass on the actual trace-one positive tests. -/
def positivityDefect (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) : ℝ :=
  sSup ((fun Y : B => negTrace (bkmTranspose B a ha Y)) '' normalizedTests B)

omit [Nonempty n] in
private theorem negTrace_nonneg (H : Mat n) : 0 ≤ negTrace H := by
  exact (Complex.nonneg_iff.mp
    (Matrix.nonneg_iff_posSemidef.mp (CFC.negPart_nonneg H)).trace_nonneg).1

private theorem defect_bddAbove (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    BddAbove ((fun Y : B => negTrace (bkmTranspose B a ha Y)) '' normalizedTests B) := by
  let : FiniteDimensional ℂ B := (inferInstance : FiniteDimensional ℂ B.toSubmodule)
  let R := (bkmTranspose B a ha).toContinuousLinearMap
  let L := (Matrix.traceLinearMap n ℂ ℂ).toContinuousLinearMap
  refine ⟨‖L‖ * ‖R‖, ?_⟩
  rintro _ ⟨Y, ⟨hY, htr⟩, rfl⟩
  have hnorm : ‖Y‖ ≤ 1 := by
    change ‖(Y : Mat n)‖ ≤ 1
    apply (CStarAlgebra.norm_le_one_iff_of_nonneg (Y : Mat n) hY.nonneg).mpr
    rw [← one_smul ℝ (1 : Mat n)]
    apply (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff hY.isHermitian 1).mp
    intro i
    have hs : (∑ j, hY.isHermitian.eigenvalues j) = 1 := by
      simpa [htr, Complex.re_sum] using
        (congrArg Complex.re hY.isHermitian.trace_eq_sum_eigenvalues).symm
    rw [← hs]
    exact Finset.single_le_sum (fun j _ => hY.eigenvalues_nonneg j) (Finset.mem_univ i)
  calc
    negTrace (bkmTranspose B a ha Y) ≤ ‖L ((R Y)⁻)‖ :=
      Complex.re_le_norm (L ((R Y)⁻))
    _ ≤ ‖L‖ * ‖(R Y)⁻‖ := L.le_opNorm _
    _ ≤ ‖L‖ * ‖R‖ := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (CStarAlgebra.norm_negPart_le _).trans
        ((R.le_opNorm Y).trans (by simpa using mul_le_mul_of_nonneg_left hnorm (norm_nonneg R)))

private theorem defect_nonneg (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) :
    0 ≤ positivityDefect B a ha := by
  let Y : B := ⟨tracialDensity n, by
    unfold tracialDensity
    change (((↑(1 / (Fintype.card n : ℝ)) : ℂ) • (1 : Mat n)) ∈ B)
    exact B.smul_mem B.one_mem _⟩
  have hm : Y ∈ normalizedTests B := ⟨tracialDensity_posDef.posSemidef, tracialDensity_trace⟩
  exact (negTrace_nonneg _).trans (le_csSup (defect_bddAbove B a ha) ⟨Y, hm, rfl⟩)

private theorem defect_bound (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef)
    (Y : B) (hY : (Y : Mat n).PosSemidef) :
    negTrace (bkmTranspose B a ha Y) ≤ positivityDefect B a ha * (Y : Mat n).trace.re := by
  let t := (Y : Mat n).trace.re
  have ht0 : 0 ≤ t := (Complex.nonneg_iff.mp hY.trace_nonneg).1
  have htr : (Y : Mat n).trace = (t : ℂ) := by
    exact Complex.ext rfl (by simpa using (Complex.nonneg_iff.mp hY.trace_nonneg).2.symm)
  by_cases hz : t = 0
  · have hzero : Y = 0 := Subtype.ext (hY.trace_eq_zero_iff.mp (by simp [htr, hz]))
    simp [hzero, negTrace]
  have ht : 0 < t := lt_of_le_of_ne ht0 (Ne.symm hz)
  let Z : B := t⁻¹ • Y
  have hZ : Z ∈ normalizedTests B := by
    change (t⁻¹ • (Y : Mat n)).PosSemidef ∧ (t⁻¹ • (Y : Mat n)).trace = 1
    refine ⟨hY.smul (inv_nonneg.mpr ht0), ?_⟩
    rw [Matrix.trace_smul, htr, Complex.real_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hz,
      Complex.ofReal_one]
  have hs : negTrace (bkmTranspose B a ha Z) ≤ positivityDefect B a ha :=
    le_csSup (defect_bddAbove B a ha) ⟨Z, hZ, rfl⟩
  have hy : Y = t • Z := by
    dsimp [Z]
    rw [smul_smul, mul_inv_cancel₀ hz, one_smul]
  calc
    negTrace (bkmTranspose B a ha Y) = t * negTrace (bkmTranspose B a ha Z) := by
      rw [hy]
      change negTrace (((bkmTranspose B a ha).restrictScalars ℝ) (t • Z)) = _
      rw [map_smul, negTrace, CFC.negPart_smul_of_nonneg ht0, Matrix.trace_smul,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    _ ≤ _ := by simpa [mul_comm, t] using mul_le_mul_of_nonneg_left hs ht0

omit [Nonempty n] [DecidableEq n] in
private theorem traceNorm_frobSq (X : Mat n) :
    traceNorm X ≤ Real.sqrt (Fintype.card n : ℝ) * Real.sqrt (RHLinalg.frobSq X) := by
  classical
  have h := traceNorm_mul_le_hsSq (1 : Mat n) X
  rw [one_mul, entryNormSq_eq_hs_sq, entryNormSq_eq_hs_sq] at h
  rw [← Complex.ofReal_re (_ ^ 2), frobenius_norm_sq_eq_trace,
    ← Complex.ofReal_re (_ ^ 2), frobenius_norm_sq_eq_trace] at h
  simpa [RHLinalg.frobSq] using h

omit [Nonempty n] [DecidableEq n] in
private theorem frobSq_sum_rows {s : Type*} [Fintype s] (E : s → Mat n)
    (hE : ∀ i j, i ≠ j → (E i)ᴴ * E j = 0) :
    RHLinalg.frobSq (∑ j, E j) = ∑ j, RHLinalg.frobSq (E j) := by
  have h (i : s) : (E i)ᴴ * (∑ j, E j) = (E i)ᴴ * E i := by
    classical
    rw [Finset.mul_sum, Finset.sum_eq_single i]
    · intro j _ hij
      exact hE i j hij.symm
    · simp
  change (((∑ j, E j)ᴴ) * (∑ j, E j)).trace.re = ∑ j, ((E j)ᴴ * E j).trace.re
  simp only [Matrix.conjTranspose_sum, Finset.sum_mul, h, Matrix.trace_sum, Complex.re_sum]

/-- The defect of the actual BKM transpose controls the trace-norm pinching error. -/
theorem bkm_pinching_traceNorm_le
    (B : StarSubalgebra ℂ (Mat n)) (a : Mat n) (ha : a.PosDef) (_htr : a.trace = 1)
    (κ : ℝ) (hκ : 0 < κ) (_hκ1 : κ ≤ 1)
    (hlo : (κ / Fintype.card n) • (1 : Mat n) ≤ a)
    (hhi : a ≤ (1 / (κ * Fintype.card n)) • (1 : Mat n))
    {s : Type*} [Fintype s] (P : s → B)
    (hP : ∀ j, (P j : Mat n).IsHermitian ∧ (P j : Mat n) * (P j : Mat n) = (P j : Mat n))
    (horth : ∀ j k, j ≠ k → (P j : Mat n) * (P k : Mat n) = 0)
    (hsum : (∑ j, (P j : Mat n)) = 1)
    (hcomm : ∀ j, Commute (traceExpectation B a : Mat n) (P j : Mat n)) :
    traceNorm (a - ∑ j, (P j : Mat n) * a * (P j : Mat n)) ≤
      Real.sqrt 12 * κ ^ (-(2 : ℤ)) * Real.sqrt (positivityDefect B a ha) := by
  let d : ℝ := Fintype.card n
  let l := κ / d
  let u := 1 / (κ * d)
  let ε := positivityDefect B a ha
  let τ := traceExpectation B a
  let hτ := reduced_posDef B a ha
  let E := fun j => (P j : Mat n) * a * (1 - (P j : Mat n))
  have hd : 0 < d := by
    change (0 : ℝ) < (Fintype.card n : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card n)
  have hl : 0 < l := div_pos hκ hd
  have hu : 0 < u := one_div_pos.mpr (mul_pos hκ hd)
  have hε : 0 ≤ ε := defect_nonneg B a ha
  have huτ : (τ : Mat n) ≤ u • 1 := by
    have hh := traceExpectation_mono B hhi
    change (τ : Mat n) ≤ (traceExpectation B (u • (1 : Mat n)) : Mat n) at hh
    rwa [traceExpectation_smul_one] at hh
  have hrow (j : s) : RHLinalg.frobSq (E j) ≤
      (12 * u ^ 2 / l) * (ε * (u * (P j : Mat n).trace.re)) := by
    let p : Mat n := P j
    let Y := omegaRestrict B τ hτ (P j)
    have hYeq : (Y : Mat n) = (τ : Mat n) * p := by
      exact (omegaRestrict_apply B τ hτ (P j)).trans (omega_of_commute _ _ hτ (hcomm j))
    have hph : pᴴ = p := (hP j).1.eq
    have hpp : p * p = p := (hP j).2
    have hp : p.PosSemidef := by
      simpa only [hph, hpp] using Matrix.posSemidef_conjTranspose_mul_self p
    have hY : (Y : Mat n).PosSemidef := by
      have hc : (τ : Mat n) * p = p * (τ : Mat n) * p := by
        rw [← (hcomm j).eq, mul_assoc, (hP j).2]
      rw [hYeq, hc]
      simpa only [hph] using hτ.posSemidef.mul_mul_conjTranspose_same p
    have htrace : 0 ≤ (((u • (1 : Mat n) - (τ : Mat n)) * p)).trace.re :=
      RHLinalg.trace_mul_nonneg_of_posSemidef (Matrix.le_iff.mp huτ) hp
    simp only [sub_mul, Matrix.smul_mul, one_mul, Matrix.trace_sub, Complex.sub_re,
      Matrix.trace_smul, Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at htrace
    have htest := defect_bound B a ha Y hY
    have hRY : bkmTranspose B a ha Y = omega a p := by
      change omegaEquiv a ha
        (((omegaRestrict B τ hτ).symm (omegaRestrict B τ hτ (P j)) : B) : Mat n) = _
      rw [LinearEquiv.symm_apply_apply, omegaEquiv_apply]
    rw [hRY, hYeq] at htest
    exact (omega_projection_leakage a p ha (hP j).1 (hP j).2 l u hl hu hlo hhi).trans
      (mul_le_mul_of_nonneg_left (htest.trans (mul_le_mul_of_nonneg_left
        (sub_nonneg.mp htrace) hε)) (by positivity))
  have hErr : a - ∑ j, (P j : Mat n) * a * (P j : Mat n) = ∑ j, E j := by
    simp only [E, mul_sub, mul_one, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have hOrth (i j : s) (hij : i ≠ j) : (E i)ᴴ * E j = 0 := by
    simp only [E, Matrix.conjTranspose_mul, (hP i).1.eq, ha.isHermitian.eq]
    calc
      _ = (1 - (P i : Mat n))ᴴ * a * ((P i : Mat n) * (P j : Mat n)) * a *
          (1 - (P j : Mat n)) := by noncomm_ring
      _ = 0 := by simp [horth i j hij]
  have hmass : (∑ j, (P j : Mat n).trace.re) = d := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, hsum]
    simp [d]
  have htSq : RHLinalg.frobSq (a - ∑ j, (P j : Mat n) * a * (P j : Mat n)) ≤
      12 * ε / (κ ^ 4 * d) := by
    rw [hErr, frobSq_sum_rows E hOrth]
    calc
      _ ≤ ∑ j, (12 * u ^ 2 / l) * (ε * (u * (P j : Mat n).trace.re)) :=
        Finset.sum_le_sum fun j _ => hrow j
      _ = (12 * u ^ 2 / l) * (ε * (u * d)) := by rw [← hmass]; simp [Finset.mul_sum]
      _ = _ := by dsimp [u, l]; field_simp [hκ.ne', hd.ne']
  calc
    _ ≤ Real.sqrt d * Real.sqrt (RHLinalg.frobSq
          (a - ∑ j, (P j : Mat n) * a * (P j : Mat n))) := traceNorm_frobSq _
    _ ≤ Real.sqrt d * Real.sqrt (12 * ε / (κ ^ 4 * d)) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt htSq) (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Real.sqrt_div (by positivity), Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12),
        Real.sqrt_mul (by positivity : 0 ≤ κ ^ 4), show κ ^ 4 = (κ ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity), _root_.zpow_neg]
      field_simp [hκ.ne', (Real.sqrt_pos.2 hd).ne']
      <;> ring

#print axioms bkm_pinching_traceNorm_le

#print axioms bkmTranspose_positive_commute

end D5.S3.Quantum.Recovery.BKMSubalgebraDefect
