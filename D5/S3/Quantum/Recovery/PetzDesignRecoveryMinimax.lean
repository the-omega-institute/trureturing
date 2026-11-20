import D5.S3.Quantum.Recovery.PetzDesignRecovery
import D5.S3.Quantum.Recovery.PetzSingerDesignMoment
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
The common CPTP optimum for the transpose experiment in Section 3 of
toric-design-transpose-recovery.txt, with the explicit Singer probes.
-/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Quantum.Recovery.PetzDesignRecoveryMinimax

open Matrix PetzDesignRecovery
open scoped BigOperators ComplexOrder Kronecker Matrix MatrixOrder
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Foundation.FiniteTraceDistance (traceNorm)
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
open PetzToricDesignMoment (PairMatrix swapMatrix haarMoment)

variable {d : ℕ}

private theorem trace_one_fin (d : ℕ) : (1 : Mat d).trace = (d : ℂ) := by
  simp [Matrix.trace_one]

private theorem succ_cast_ne_zero (d : ℕ) : (d : ℂ) + 1 ≠ 0 := by
  exact_mod_cast (Nat.succ_ne_zero d)

/-- The common recovery channel for the transpose experiment. -/
def rstar (d : ℕ) : MatrixMap (Fin d) (Fin d) ℂ :=
  ((d : ℂ) + 1)⁻¹ •
    ((Matrix.transposeLinearEquiv (Fin d) (Fin d) ℂ ℂ).toLinearMap +
      (Matrix.traceLinearMap (Fin d) ℂ ℂ).smulRight (1 : Mat d))

theorem rstar_apply (X : Mat d) :
    rstar d X = ((d : ℂ) + 1)⁻¹ • (Xᵀ + X.trace • (1 : Mat d)) :=
  rfl

/-- The unnormalized Choi matrix in the output-first convention. -/
theorem rstar_choi (d : ℕ) :
    (rstar d).choi_matrix = ((d : ℂ) + 1)⁻¹ • ((1 : PairMatrix d) + swapMatrix d) := by
  apply Matrix.ext
  rintro ⟨b, i⟩ ⟨c, j⟩
  change rstar d (Matrix.single i j 1) b c =
    (((d : ℂ) + 1)⁻¹ • ((1 : PairMatrix d) + swapMatrix d)) (b, i) (c, j)
  have hswap : (Matrix.single i j (1 : ℂ))ᵀ b c = swapMatrix d (b, i) (c, j) := by
    have h : (i = c ∧ j = b) ↔ (b = j ∧ i = c) :=
      ⟨fun h => ⟨h.2.symm, h.1⟩, fun h => ⟨h.2, h.1.symm⟩⟩
    simp only [Matrix.transpose_apply, Matrix.single_apply, swapMatrix, Matrix.of_apply,
      Prod.swap, Prod.mk.injEq, h]
  have hid : ((Matrix.single i j (1 : ℂ)).trace • (1 : Mat d)) b c =
      (1 : PairMatrix d) (b, i) (c, j) := by
    by_cases hij : i = j
    · subst j
      simp [Matrix.trace_single_eq_same, Matrix.one_apply, Prod.mk.injEq]
    · simp [Matrix.one_apply, Prod.mk.injEq, hij]
  calc
    _ = ((d : ℂ) + 1)⁻¹ • (swapMatrix d (b, i) (c, j) + (1 : PairMatrix d) (b, i) (c, j)) := by
      rw [rstar_apply, Matrix.smul_apply, Matrix.add_apply, hswap, hid]
    _ = _ := by simp only [Matrix.smul_apply, Matrix.add_apply, add_comm]

theorem rstar_completelyPositive (d : ℕ) : (rstar d).IsCompletelyPositive := by
  apply (MatrixMap.choi_PSD_iff_CP_map (rstar d)).mpr
  rw [rstar_choi]
  have hc : 0 ≤ ((d : ℂ) + 1)⁻¹ := by
    simpa only [Complex.ofReal_inv, Complex.ofReal_add, Complex.ofReal_natCast,
      Complex.ofReal_one] using
      (Complex.zero_le_real.mpr (show 0 ≤ ((d : ℝ) + 1)⁻¹ by positivity))
  exact (one_add_swap_psd d).smul hc

theorem rstar_tracePreserving (d : ℕ) : (rstar d).IsTracePreserving := by
  intro X
  rw [rstar_apply, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_transpose,
    Matrix.trace_smul, trace_one_fin]
  simp only [smul_eq_mul]
  calc
    _ = ((d : ℂ) + 1)⁻¹ * (((d : ℂ) + 1) * X.trace) := by ring
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ (succ_cast_ne_zero d), one_mul]

theorem rstar_cptp (d : ℕ) : IsCPTP (rstar d) :=
  ⟨rstar_completelyPositive d, rstar_tracePreserving d⟩

/-- The residual on a trace-one projection probe after the actual transpose. -/
theorem rstar_residual (hd : 0 < d) (ε : ℝ) {P : Mat d} (hP : IsRankOneProjection P) :
    residual (rstar d) ε P = ((ε : ℂ) / ((d : ℂ) + 1)) • ((d : ℂ) • P - 1) := by
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  rw [PetzDesignRecovery.residual, rstar_apply, Matrix.transpose_transpose, Matrix.trace_transpose,
    probe_trace hd ε hP]
  simp only [one_smul]
  apply Matrix.ext
  intro i j
  simp only [probe, reference, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_sub, Complex.ofReal_one]
  field_simp [hdC, succ_cast_ne_zero d] <;> ring

/-- The full trace norm of each rank-one projection probe's residual. -/
theorem rstar_residual_traceNorm (hd : 0 < d) {ε : ℝ} (hε : 0 ≤ ε)
    {P : Mat d} (hP : IsRankOneProjection P) :
    traceNorm (residual (rstar d) ε P) = 2 * ε * ((d : ℝ) - 1) / ((d : ℝ) + 1) := by
  let Q : Mat d := 1 - P
  have hQ : Qᴴ = Q := by
    simp only [Q, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1.eq]
  have hPQ : P * Q = 0 := by
    simp only [Q, mul_sub, mul_one, hP.2.1, sub_self]
  have hQP : Q * P = 0 := by
    simp only [Q, sub_mul, one_mul, hP.2.1, sub_self]
  have hQQ : Q * Q = Q := by
    change (1 - P) * Q = Q
    rw [sub_mul, one_mul, hPQ, sub_zero]
  have hPpos : P.PosSemidef := by
    simpa only [hP.1.eq, hP.2.1] using Matrix.posSemidef_conjTranspose_mul_self P
  have hQpos : Q.PosSemidef := by
    simpa only [hQ, hQQ] using Matrix.posSemidef_conjTranspose_mul_self Q
  let b : ℝ := ε / ((d : ℝ) + 1)
  let a : ℝ := b * ((d : ℝ) - 1)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (Nat.succ_le_of_lt hd)
  have hb : 0 ≤ b := div_nonneg hε (by positivity)
  have ha : 0 ≤ a := mul_nonneg hb (sub_nonneg.mpr hdR)
  let A : Mat d := (a : ℂ) • P
  let B : Mat d := (b : ℂ) • Q
  have hA : A.PosSemidef := hPpos.smul (Complex.zero_le_real.mpr ha)
  have hB : B.PosSemidef := hQpos.smul (Complex.zero_le_real.mpr hb)
  have hAB : A * B = 0 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hPQ, smul_zero]
  have hBA : B * A = 0 := by
    simp only [A, B, Matrix.smul_mul, Matrix.mul_smul, hQP, smul_zero]
  have hres : residual (rstar d) ε P = A - B := by
    have hbC : (b : ℂ) = (ε : ℂ) / ((d : ℂ) + 1) := by
      simp only [b, Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_natCast,
        Complex.ofReal_one]
    have haC : (a : ℂ) = (b : ℂ) * ((d : ℂ) - 1) := by
      simp only [a, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_natCast,
        Complex.ofReal_one]
    rw [rstar_residual hd ε hP, ← hbC]
    simp only [A, B, Q, haC, smul_sub, smul_smul, mul_sub, mul_one, sub_smul]
    abel
  have hsquare : (A + B) * (A + B) = (A - B)ᴴ * (A - B) := by
    rw [Matrix.conjTranspose_sub, hA.1.eq, hB.1.eq]
    noncomm_ring [hAB, hBA]
  have hsqrt := CFC.sqrt_unique hsquare (hA.add hB).nonneg
  rw [hres]
  change (CFC.sqrt ((A - B)ᴴ * (A - B))).trace.re = _
  rw [hsqrt]
  simp only [A, B, Q, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sub, trace_one_fin,
    hP.2.2, smul_eq_mul, mul_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re, Complex.natCast_re, Complex.one_re]
  dsimp only [a, b]
  ring

variable {ι : Type*}

/-- The largest full trace error over the probes when the finite label type is nonempty. -/
def worstCaseError (R : MatrixMap (Fin d) (Fin d) ℂ) (ε : ℝ) (P : ι → Mat d) : ℝ :=
  sSup (Set.range fun i => traceNorm (residual R ε (P i)))

theorem worstCaseError_isGreatest [Finite ι] [Nonempty ι]
    (R : MatrixMap (Fin d) (Fin d) ℂ) (ε : ℝ) (P : ι → Mat d) :
    IsGreatest (Set.range fun i => traceNorm (residual R ε (P i))) (worstCaseError R ε P) :=
  (Set.range_nonempty _).isGreatest_csSup (Set.finite_range _)

def minimaxValue (d : ℕ) (ε : ℝ) : ℝ :=
  2 * ε * ((d : ℝ) - 1) / ((d : ℝ) + 1)

/-- A weighted Haar design attains the least worst-case error over all common CPTP maps. -/
theorem design_minimax [Fintype ι] (hd : 2 ≤ d) {ε : ℝ} (hε : 0 < ε)
    (P : ι → Mat d) (w : ι → ℝ)
    (hP : ∀ i, IsRankOneProjection (P i)) (hw₀ : ∀ i, 0 ≤ w i) (hw : ∑ i, w i = 1)
    (hm : (∑ i, (w i : ℂ) • (P i ⊗ₖ P i)) = haarMoment d) :
    IsCPTP (rstar d) ∧ worstCaseError (rstar d) ε P = minimaxValue d ε ∧
      IsLeast {v : ℝ | ∃ R : MatrixMap (Fin d) (Fin d) ℂ, IsCPTP R ∧
        worstCaseError R ε P = v} (minimaxValue d ε) := by
  have hd₀ : 0 < d := by omega
  have hstar := rstar_cptp d
  obtain ⟨i, _⟩ := exists_large_residual hd hε P w hP hw₀ hw hm (rstar d) hstar
  let _ : Nonempty ι := ⟨i⟩
  have hvalue : worstCaseError (rstar d) ε P = minimaxValue d ε := by
    obtain ⟨j, hj⟩ := (worstCaseError_isGreatest (rstar d) ε P).1
    exact hj.symm.trans (rstar_residual_traceNorm hd₀ hε.le (hP j))
  refine ⟨hstar, hvalue, ⟨⟨rstar d, hstar, hvalue⟩, ?_⟩⟩
  rintro v ⟨R, hR, rfl⟩
  obtain ⟨j, hj⟩ := exists_large_residual hd hε P w hP hw₀ hw hm R hR
  exact hj.trans ((worstCaseError_isGreatest R ε P).2 ⟨j, rfl⟩)

private theorem rankOneProjection_vecMulVec (v : Fin d → ℂ)
    (hv : (∑ i, v i * star (v i)) = 1) :
    IsRankOneProjection (Matrix.vecMulVec v (fun i => star (v i))) := by
  change IsRankOneProjection (Matrix.vecMulVec v (star v))
  have ht : (Matrix.vecMulVec v (star v)).trace = 1 := by
    rw [Matrix.trace_vecMulVec]
    exact hv
  have hdot : star v ⬝ᵥ v = 1 := by
    rw [dotProduct_comm, ← Matrix.trace_vecMulVec]
    exact ht
  refine ⟨(Matrix.posSemidef_vecMulVec_self_star v).1, ?_, ht⟩
  rw [Matrix.vecMulVec_mul_vecMulVec, hdot, one_smul]

private theorem probe_injective {ε : ℝ} (hε : ε ≠ 0) :
    Function.Injective (probe (d := d) ε) := by
  intro P Q h
  unfold probe at h
  exact smul_right_injective (Mat d) (Complex.ofReal_ne_zero.mpr hε) (add_left_cancel h)

open PetzSingerDesignMoment (Label projector weight)

/-- For each prime, the actual Singer projectors yield exactly `(p + 1)^2 + 1`
distinct faithful probes at every mixing parameter strictly between zero and one. -/
theorem singer_minimax (p : ℕ) [Fact p.Prime] :
    ∃ (α : GaloisField p 3) (hα : orderOf α = p ^ 3 - 1),
      Fintype.card (Label p) = (p + 1) ^ 2 + 1 ∧
      (∀ a : Label p, IsRankOneProjection (projector α hα a)) ∧
      (∀ a : Label p, 0 < weight a) ∧ (∑ a : Label p, weight a) = 1 ∧
      (∑ a : Label p, (weight a : ℂ) • (projector α hα a ⊗ₖ projector α hα a)) =
        haarMoment (p + 1) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        Function.Injective (fun a : Label p => probe ε (projector α hα a)) ∧
        (∀ a : Label p, (probe ε (projector α hα a)).PosDef ∧
          (probe ε (projector α hα a)).trace = 1) ∧
        IsCPTP (rstar (p + 1)) ∧
        worstCaseError (rstar (p + 1)) ε (projector α hα) = minimaxValue (p + 1) ε ∧
        IsLeast {v : ℝ | ∃ R : MatrixMap (Fin (p + 1)) (Fin (p + 1)) ℂ, IsCPTP R ∧
          worstCaseError R ε (projector α hα) = v} (minimaxValue (p + 1) ε) := by
  obtain ⟨α, hα, _, hcard, hinj, houter, hw₀, hw, hm⟩ :=
    PetzSingerDesignMoment.result (p := p)
  have hP (a : Label p) : IsRankOneProjection (projector α hα a) := by
    obtain ⟨v, hv, heq⟩ := houter a
    rw [heq]
    exact rankOneProjection_vecMulVec v hv
  have hd : 2 ≤ p + 1 := by
    have hp := (Fact.out : p.Prime).two_le
    omega
  refine ⟨α, hα, hcard, hP, hw₀, hw, hm, ?_⟩
  intro ε hε hε₁
  refine ⟨(probe_injective hε.ne').comp hinj, ?_, ?_⟩
  · intro a
    exact ⟨probe_posDef (Nat.succ_pos p) hε.le hε₁ (hP a),
      probe_trace (Nat.succ_pos p) ε (hP a)⟩
  · exact design_minimax hd hε (projector α hα) weight hP (fun a => (hw₀ a).le) hw hm

end D5.S3.Quantum.Recovery.PetzDesignRecoveryMinimax
