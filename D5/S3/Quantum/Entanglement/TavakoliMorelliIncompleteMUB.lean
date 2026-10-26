/- GID: D5/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/TavakoliMorelliIncompleteMUB
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Incomplete mutually unbiased bases and Schmidt-number correlation bounds. -/

import D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
import D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB

open D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteEAM
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Tomography.RankOneContextCommutator
open D5.S3.Quantum.Tomography.PurityPythagorasDecomposition
open D5.S3.Quantum.Measurement.BasisMeasurementProjection
open D5.S3.Observer.Conditioning

attribute [local instance]
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixNormedAddCommGroup
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixComplexInnerProductSpace
  D5.S3.Quantum.Measurement.BasisMeasurementProjection.matrixRealInnerProductSpace

/-- Arbitrary unitary bases with the prescribed overlaps between distinct bases. -/
abbrev MUBFamily (d m : ℕ) :=
  {U : Fin m → Matrix.unitaryGroup (Fin d) ℂ //
    ∀ l k, l ≠ k → ∀ a b,
      ‖((U l).valᴴ * (U k).val) a b‖ ^ 2 = 1 / (d : ℝ)}

def MUBFamily.ket {d m : ℕ} (A : MUBFamily d m) (l : Fin m) (a : Fin d) :
    Ket (Fin d) :=
  ⟨fun i => (A.val l).val i a, Matrix.unitaryGroup_row_norm (A.val l) a⟩

def MUBFamily.effect {d m : ℕ} (A : MUBFamily d m) (p : Fin m × Fin d) : Op d :=
  proj (A.ket p.1 p.2)

def Qm {d m : ℕ} (ρ : BipartiteOp d) (A B : MUBFamily d m) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ :=
  correlation ρ A.effect B.effect

private theorem mub_effect_scaledPure {d m : ℕ} (A : MUBFamily d m) (p : Fin m × Fin d) :
    ScaledPure (A.effect p) :=
  ⟨1, A.ket p.1 p.2, zero_le_one, (one_smul ℂ _).symm⟩

private theorem mub_effect_sum {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    ∑ a, A.effect (l, a) = 1 := by
  ext i j
  change (∑ a, proj (A.ket l a)) i j = _
  simp (congrConsts := false) only [Matrix.sum_apply, MState.pure_apply]
  change ∑ a, (A.val l).val i a * star ((A.val l).val j a) = _
  exact congrArg (fun M : Op d => M i j) (Unitary.mul_star_self_of_mem (A.val l).prop)

/-- The complete rank-one context determined by a basis of the family. -/
def MUBFamily.context {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    RankOneContext d where
  projector a := A.effect (l, a)
  rankOne a := by
    refine ⟨(scaledPure_hermitian (mub_effect_scaledPure A (l, a))).eq, ?_, ?_, ?_⟩
    · rw [show A.effect (l, a) = proj (A.ket l a) by rfl, proj_eq_outer]
      exact (D5.S3.Quantum.PureState.PureStateHandshake.pure_state_handshake
        (A.ket l a).vec (ket_dot_self _) 1).1
    · exact MState.tr' (MState.pure (A.ket l a))
    · intro X
      rw [scaledPure_sandwich (mub_effect_scaledPure A (l, a)), Matrix.trace_mul_comm]
  resolvesIdentity := mub_effect_sum A l

private theorem mub_column_inner {d m : ℕ} (A : MUBFamily d m) (l k : Fin m) (a b : Fin d) :
    star (A.ket l a).vec ⬝ᵥ (A.ket k b).vec =
      ((A.val l).valᴴ * (A.val k).val) a b := by
  rfl

private theorem mub_context_record {d m : ℕ} (A : MUBFamily d m) (l : Fin m) :
    IsRecordMeasurement (A.context l).projector := by
  refine ⟨?_, fun a => ((A.context l).rankOne a).2.1, ?_, (A.context l).resolvesIdentity⟩
  · intro a
    exact ((A.context l).rankOne a).1
  · intro a b hab
    change proj (A.ket l a) * proj (A.ket l b) = 0
    rw [proj_eq_outer, proj_eq_outer, vecMulVec_mul_vecMulVec, mub_column_inner]
    have hUnitary : ((A.val l).valᴴ * (A.val l).val) a b = 0 := by
      simpa only [Matrix.star_eq_conjTranspose, Matrix.one_apply_ne hab] using
        congrArg (fun M : Op d => M a b) (Unitary.star_mul_self_of_mem (A.val l).prop)
    rw [hUnitary, zero_smul, vecMulVec_zero]

private theorem mub_context_overlap {d m : ℕ} (A : MUBFamily d m) (l k : Fin m)
    (hlk : l ≠ k) (a b : Fin d) :
    overlap (A.context l) (A.context k) a b = (d : ℝ)⁻¹ := by
  change (proj (A.ket l a) * proj (A.ket k b)).trace.re = _
  rw [proj_overlap, Complex.ofReal_re, mub_column_inner, A.property l k hlk]
  exact one_div _

private theorem mub_measurements_orthogonal {d m : ℕ} (hd : 1 ≤ d)
    (A : MUBFamily d m) [NeZero d] :
    PairwiseOrthogonalMeasurements A.context (mub_context_record A) := by
  intro l k hlk x y
  let P := fun l => traceZeroBasisMeasurement (A.context l) (mub_context_record A l)
  change inner ℝ (P l x) (P k y) = 0
  by_cases hd2 : 2 ≤ d
  · have hPlanes :=
      D5.S3.Quantum.Tomography.MutuallyUnbiasedDiagonalPlanes.mutually_unbiased_diagonal_planes
        hd2 (A.context l) (A.context k) (mub_context_record A l) (mub_context_record A k)
    have hZero := hPlanes.2.1.mp (hPlanes.1.mp (mub_context_overlap A l k hlk))
    let Y : D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.HermitianTraceZero
        (d := Fin d) := ⟨y.1.1, y.1.2, y.2⟩
    have hComposition : P l (P k y) = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      exact (hZero Y).1
    rw [(trace_zero_basis_measurement_is_orthogonal_projection
      (A.context l) (mub_context_record A l)).1.isSymmetric x (P k y), hComposition]
    exact inner_zero_right (𝕜 := ℝ) x
  · have hd1 : d = 1 := by omega
    subst d
    have hy : y = 0 := by
      apply Subtype.ext
      apply Subtype.ext
      have htrace : Matrix.trace y.1.1 = 0 := y.2
      ext i j
      fin_cases i
      fin_cases j
      change y.1.1 0 0 = 0
      simpa only [Matrix.trace_fin_one] using htrace
    rw [hy, map_zero]
    exact inner_zero_right (𝕜 := ℝ) (P l x)

/-- Squared probabilities of arbitrary Hermitian inputs obey the incomplete-MUB moment bound. -/
private theorem mub_second_moment {d m : ℕ} (hd : 1 ≤ d)
    (A : MUBFamily d m) (H : Op d) (hH : H.IsHermitian) :
    moment A.effect H ≤ (H * H).trace.re +
      (((m : ℝ) - 1) / (d : ℝ)) * (H.trace.re) ^ 2 := by
  have : NeZero d := ⟨by omega⟩
  let X : traceZeroHermitian d :=
    ⟨⟨D5.S3.Quantum.Fibers.ReadoutOrthogonalEquivalence.centeredEffect H,
        (D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem H hH).1⟩,
      (D5.S3.Quantum.Fibers.TraceZeroReadoutOrthogonalEquivalence.centered_effect_mem H hH).2⟩
  have hX : X.1.1 = H - (H.trace / (d : ℂ)) • 1 := by
    change H - (H.trace / (Fintype.card (Fin d) : ℂ)) • 1 = _
    rw [Fintype.card_fin]
  let q := H.trace.re
  let p := fun l a => (H * A.effect (l, a)).trace.re
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hreal : H.trace = (H.trace.re : ℂ) := by
    simpa only [Matrix.mul_one] using trace_mul_real_of_hermitian H 1 hH isHermitian_one
  have hshift (l : Fin m) (a : Fin d) :
      (X.1.1 * A.effect (l, a)).trace.re = p l a - q / (d : ℝ) := by
    rw [hX]
    rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_sub, Matrix.trace_smul]
    change ((H * A.effect (l, a)).trace - (H.trace / (d : ℂ)) *
      (proj (A.ket l a)).trace).re = _
    rw [MState.tr' (MState.pure (A.ket l a)), mul_one, hreal]
    rw [← Complex.ofReal_natCast d]
    simp only [← Complex.ofReal_div, Complex.sub_re,
      Complex.ofReal_re]
    rfl
  have hsum (l : Fin m) : ∑ a, p l a = q := by
    simpa only [p, q, MUBFamily.context.eq_1, recordWeight,
      D5.S3.Quantum.FiniteDimensional.bornProbability, Complex.re_sum] using
      congrArg Complex.re (recordWeight_sum (mub_context_record A l) H)
  have hBasis (l : Fin m) :
      ∑ a, ((X.1.1 * A.effect (l, a)).trace.re) ^ 2 =
        (∑ a, (p l a) ^ 2) - q ^ 2 / (d : ℝ) := by
    simp_rw (congrConsts := false) [hshift, sub_sq]
    simp (congrConsts := false) only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum,
      hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [hd0]
    ring
  have hNorm : ‖X.1.1‖ ^ 2 = (H * H).trace.re - q ^ 2 / (d : ℝ) := by
    rw [hX]
    exact centered_hermitian_norm_sq H hH
  have hEnergy := traceZero_context_pythagoras A.context (mub_context_record A)
    (mub_measurements_orthogonal hd A) X
  simp_rw (congrConsts := false) [traceZero_measurement_norm_sq] at hEnergy
  change ‖X.1.1‖ ^ 2 =
    (∑ l, ∑ a, ((X.1.1 * A.effect (l, a)).trace.re) ^ 2) +
      ‖residualVector A.context (mub_context_record A) X‖ ^ 2 at hEnergy
  simp_rw (congrConsts := false) [hBasis] at hEnergy
  rw [hNorm] at hEnergy
  simp (congrConsts := false) only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hEnergy
  have hMoment : moment A.effect H = ∑ l, ∑ a, (p l a) ^ 2 := by
    rw [moment.eq_1, Fintype.sum_prod_type]
  rw [hMoment]
  dsimp only [q] at hEnergy ⊢
  have hCoeff : (((m : ℝ) - 1) / (d : ℝ)) * H.trace.re ^ 2 =
      (m : ℝ) * (H.trace.re ^ 2 / (d : ℝ)) - H.trace.re ^ 2 / (d : ℝ) := by ring
  rw [hCoeff]
  calc
    (∑ l, ∑ a, (p l a) ^ 2) ≤
        ((H * H).trace.re - H.trace.re ^ 2 / (d : ℝ)) +
          (m : ℝ) * (H.trace.re ^ 2 / (d : ℝ)) := by
      apply sub_le_iff_le_add.mp
      exact (le_add_of_nonneg_right
        (sq_nonneg ‖residualVector A.context (mub_context_record A) X‖)).trans hEnergy.symm.le
    _ = _ := by ring

def claim : Prop :=
  ∀ (d m r : ℕ), 1 ≤ d → 1 ≤ m → m ≤ d → 1 ≤ r → r ≤ d →
    ∀ (A B : MUBFamily d m) (ρ : BipartiteOp d), SchmidtNumberLE ρ r →
      traceNorm (Qm ρ A B) ≤ 1 + ((m : ℝ) - 1) * (r : ℝ) / (d : ℝ)

theorem result : claim := by
  intro d m r hd hm _hmd _hr _hrd A B ρ hρ
  have hmreal : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hβ : 0 ≤ ((m : ℝ) - 1) / (d : ℝ) :=
    div_nonneg (sub_nonneg.mpr hmreal) (Nat.cast_nonneg _)
  have hBound := schmidt_traceNorm_le_of_moment ρ A.effect B.effect
    1 (((m : ℝ) - 1) / (d : ℝ)) (mub_effect_scaledPure A) (mub_effect_scaledPure B)
    zero_le_one hβ (fun H hH => by simpa only [one_mul] using mub_second_moment hd A H hH)
    (fun H hH => by simpa only [one_mul] using mub_second_moment hd B H hH) hρ
  change traceNorm (correlation ρ A.effect B.effect) ≤ _
  convert hBound using 1
  ring

end D5.S3.Quantum.Entanglement.TavakoliMorelliIncompleteMUB
