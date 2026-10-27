/- GID: D5/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful
   generality: G
   mirror-B: D5/B/S3/Quantum/QuantumChannels/PostprocessedImprovementUnfaithful
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Biased post-processed interferometric improvements fail faithfulness. -/

import D5.S3.Quantum.Foundation.FiniteTraceDistance
import D5.S3.Quantum.QuantumChannels.IptPptSquaredEquivalence
import D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open D5.S3.Quantum.Foundation.FiniteTraceDistance
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.Decoherence.ProjectedUnistochasticDynamics (projectiveReadout)

namespace D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful

/-- Full dephasing in the coordinate basis, as a complex linear map. -/
def dephase {n : ℕ} : MatrixMap (Fin n) (Fin n) ℂ where
  toFun := projectiveReadout
  map_add' a b := by
    change diagonal (diag (a + b)) = diagonal (diag a) + diagonal (diag b)
    exact (Matrix.diagonalAddMonoidHom (Fin n) ℂ).map_add _ _
  map_smul' c a := by
    change diagonal (fun i => c * a i i) = c • diagonal (diag a)
    exact Matrix.diagonal_smul c (diag a)

/-- A finite-dimensional quantum channel is completely positive and trace preserving. -/
def IsChannel {a b : ℕ} (θ : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  θ.IsCompletelyPositive ∧ ∀ x, (θ x).trace = x.trace

/-- Maximally incoherent operations preserve the diagonal matrices. -/
def IsMIO {a b : ℕ} (ψ : MatrixMap (Fin a) (Fin b) ℂ) : Prop :=
  IsChannel ψ ∧ ∀ x, ψ (dephase x) = dephase (ψ (dephase x))

private def phaseUnitary {m : ℕ} (φ : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℂ :=
  diagonal (fun i => Complex.exp ((φ i : ℂ) * Complex.I))

/-- The interferometer's fixed diagonal unitary conjugation. -/
def phaseChannel {m : ℕ} (φ : Fin m → ℝ) : MatrixMap (Fin m) (Fin m) ℂ where
  toFun a := phaseUnitary φ * a * (phaseUnitary φ)ᴴ
  map_add' a b := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c a := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- The induced trace norm uses the full complex matrix unit ball. -/
def inducedTraceNorm {a b : ℕ} (Φ : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ x, traceNorm x ≤ 1 ∧ traceNorm (Φ x) = r}

/-- The optimized post-processed improvement with prior `λ` and phases `φ`. -/
def postImprovement {a b m : ℕ} (λ : ℝ) (φ : Fin m → ℝ)
    (θ : MatrixMap (Fin a) (Fin b) ℂ) : ℝ :=
  sSup {r : ℝ | ∃ ψ : MatrixMap (Fin b) (Fin m) ℂ, IsMIO ψ ∧
    inducedTraceNorm ((((λ : ℂ) • LinearMap.id -
      ((1 - λ : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp (θ.comp dephase)) = r} -
    |λ - (1 - λ)|

private def prepare {a b : ℕ} (ρ : Matrix (Fin b) (Fin b) ℂ) :
    MatrixMap (Fin a) (Fin b) ℂ :=
  (Matrix.traceLinearMap (Fin a) ℂ ℂ).smulRight ρ

private def rho (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, (t : ℂ) / 2; (t : ℂ) / 2, 1 / 2]

private def halfIdentity : Matrix (Fin 2) (Fin 2) ℂ := (1 / 2 : ℝ) • 1

private def halfPauli : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1 / 2; 1 / 2, 0]

private theorem phase_properties {m : ℕ} (φ : Fin m → ℝ) :
    (∀ a, (phaseChannel φ a).trace = a.trace) ∧
    (∀ a, a.PosSemidef → (phaseChannel φ a).PosSemidef) ∧
    (∀ a, dephase a = a → phaseChannel φ a = a) := by
  sorry

private theorem sandwich {m : ℕ} (λ : ℝ) (hλ : 0 ≤ λ) (hλ1 : λ ≤ 1)
    (φ : Fin m → ℝ) (d e : Matrix (Fin m) (Fin m) ℂ)
    (hd : dephase d = d) (hp : (d + e).PosSemidef) (hn : (d - e).PosSemidef) :
    (d + (λ • e - (1 - λ) • phaseChannel φ e)).PosSemidef ∧
    (d - (λ • e - (1 - λ) • phaseChannel φ e)).PosSemidef := by
  have hphase := phase_properties φ
  sorry

private theorem biased_norm {m : ℕ} (λ t : ℝ) (φ : Fin m → ℝ)
    (d e : Matrix (Fin m) (Fin m) ℂ) (hd : d.PosSemidef) (htrd : d.trace = 1)
    (htre : e.trace = 0) (ht : 0 ≤ t) (htδ : t ≤ |2 * λ - 1|)
    (hs : (d + (λ • e - (1 - λ) • phaseChannel φ e)).PosSemidef ∧
      (d - (λ • e - (1 - λ) • phaseChannel φ e)).PosSemidef) :
    traceNorm ((2 * λ - 1) • d + t • (λ • e - (1 - λ) • phaseChannel φ e)) =
      |2 * λ - 1| := by
  have hphase := (phase_properties φ).1 e
  sorry

private theorem postprocessing_data {m : ℕ} (ψ : MatrixMap (Fin 2) (Fin m) ℂ)
    (hψ : IsMIO ψ) :
    dephase (ψ halfIdentity) = ψ halfIdentity ∧ (ψ halfIdentity).PosSemidef ∧
      (ψ halfIdentity).trace = 1 ∧ (ψ halfPauli).trace = 0 ∧
      (ψ halfIdentity + ψ halfPauli).PosSemidef ∧
      (ψ halfIdentity - ψ halfPauli).PosSemidef := by
  sorry

private theorem prepared_channel (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IsChannel (prepare (a := 2) (rho t)) := by
  sorry

private theorem prepared_not_mio (t : ℝ) (ht : t ≠ 0) :
    ¬ IsMIO (prepare (a := 2) (rho t)) := by
  sorry

private theorem trace_bound {a : ℕ} (x : Matrix (Fin a) (Fin a) ℂ) :
    ‖x.trace‖ ≤ traceNorm x := by
  sorry

private theorem norm_prepare {a b : ℕ} (ha : 1 ≤ a)
    (h : Matrix (Fin b) (Fin b) ℂ) :
    inducedTraceNorm (prepare (a := a) h) = traceNorm h := by
  have hb := trace_bound (Matrix.single (⟨0, ha⟩ : Fin a) ⟨0, ha⟩ (1 : ℂ))
  sorry

private theorem postprocessed_norm {m : ℕ} (λ : ℝ) (hλ : 0 ≤ λ) (hλ1 : λ ≤ 1)
    (φ : Fin m → ℝ) (ψ : MatrixMap (Fin 2) (Fin m) ℂ) (hψ : IsMIO ψ) :
    inducedTraceNorm ((((λ : ℂ) • LinearMap.id -
      ((1 - λ : ℝ) : ℂ) • phaseChannel φ).comp ψ).comp
        ((prepare (a := 2) (rho (|2 * λ - 1| / 2))).comp dephase)) =
      |2 * λ - 1| := by
  obtain ⟨hdiag, hd, htrd, htre, hp, hn⟩ := postprocessing_data ψ hψ
  have hs := sandwich λ hλ hλ1 φ (ψ halfIdentity) (ψ halfPauli) hdiag hp hn
  have hv := biased_norm λ (|2 * λ - 1| / 2) φ (ψ halfIdentity) (ψ halfPauli)
    hd htrd htre (by positivity) (by linarith [abs_nonneg (2 * λ - 1)]) hs
  have hr := norm_prepare (a := 2) (by omega)
    ((2 * λ - 1) • ψ halfIdentity +
      (|2 * λ - 1| / 2) • (λ • ψ halfPauli - (1 - λ) • phaseChannel φ (ψ halfPauli)))
  sorry

private theorem mio_nonempty (m : ℕ) (hm : 1 ≤ m) :
    ∃ ψ : MatrixMap (Fin 2) (Fin m) ℂ, IsMIO ψ := by
  sorry

private theorem improvement_zero {m : ℕ} (hm : 1 ≤ m) (λ : ℝ)
    (hλ : 0 ≤ λ) (hλ1 : λ ≤ 1) (φ : Fin m → ℝ) :
    postImprovement λ φ (prepare (a := 2) (rho (|2 * λ - 1| / 2))) = 0 := by
  obtain ⟨ψ, hψ⟩ := mio_nonempty m hm
  have hvalue := postprocessed_norm λ hλ hλ1 φ ψ hψ
  sorry

/-- Every biased prior admits a coherent qubit channel with zero optimized improvement. -/
theorem result (λ : ℝ) (hλ : 0 ≤ λ) (hλ1 : λ ≤ 1) (hbiased : λ ≠ 1 / 2)
    (m : ℕ) (hm : 1 ≤ m) (φ : Fin m → ℝ) :
    ∃ θ : MatrixMap (Fin 2) (Fin 2) ℂ,
      IsChannel θ ∧ ¬ IsMIO θ ∧ postImprovement λ φ θ = 0 := by
  have hδ : |2 * λ - 1| ≠ 0 := by
    intro h
    have := abs_eq_zero.mp h
    apply hbiased
    linarith
  refine ⟨prepare (rho (|2 * λ - 1| / 2)),
    prepared_channel _ (by positivity) ?_, prepared_not_mio _ ?_,
    improvement_zero hm λ hλ hλ1 φ⟩
  · have hbound : |2 * λ - 1| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · exact div_ne_zero hδ (by norm_num)

end D5.S3.Quantum.QuantumChannels.PostprocessedImprovementUnfaithful
