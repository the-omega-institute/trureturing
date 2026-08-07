/- GID: D5/S3/Quantum/ChannelFixedState
   generality: G
   mirror-B: D5/B/S3/Quantum/ChannelFixedState
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Positive trace-preserving finite-dimensional matrix maps admit an invariant state. -/

/- Library-search audit trail (2026-08-07):
   * LeanSearch query: "A positive trace-preserving linear map on finite-dimensional complex
     matrices has a positive trace-one fixed point." The pinned LeanSearch client was present, but
     the remote query timed out after 30 seconds in the network-restricted worktree (exit 142).
   * Loogle query: `Matrix.PosSemidef, Matrix.trace, _ = _`. The pinned client was present, but the
     same restricted-network invocation timed out before returning results (exit 142).
   * Local mathlib grep terms: `fixed point`, `invariant state`, `stationary state`, `quantum
     channel`, `CPTP`, `trace-preserving`, `Cesaro`, `mean ergodic`, `PosSemidef trace norm`, and
     `IsCompact tendsto_subseq`. No channel fixed-state theorem was found. Reusable primitives were
     found in `Dynamics.BirkhoffSum`, finite-dimensional compactness, and matrix positivity. The
     mean ergodic theorem was not directly applicable because it assumes contraction in a Hilbert
     norm, which does not follow here from positivity and trace preservation alone.
   * Third-party dependency search terms: `Timeroot`, `QuantumInfo`, `CPTP`, and `quantum channel`.
     Neither Timeroot nor QuantumInfo occurs in the pinned `lake-manifest.json` or local packages;
     therefore no third-party theorem is importable in this toolchain.
   * Literature-search conclusion: Watrous, The Theory of Quantum Information (Cambridge University
     Press, 2018), Section 4.4, attests the finite-dimensional channel fixed-point setting (DOI
     10.1017/9781316848142). No specific theorem number was verified or attributed.
-/

import Mathlib

namespace D5.S3.Quantum.ChannelFixedState

open Filter Function Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator Topology

/-- Every positive trace-preserving linear map on a nonempty finite-dimensional complex matrix
algebra has a positive semidefinite trace-one fixed point. -/
theorem channel_fixed_state_exists {n : Type*} [Fintype n] [Nonempty n]
    (Phi : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hPos : ∀ rho : Matrix n n ℂ, rho.PosSemidef → (Phi rho).PosSemidef)
    (hTrace : ∀ rho : Matrix n n ℂ, Matrix.trace (Phi rho) = Matrix.trace rho) :
    ∃ rho : Matrix n n ℂ,
      rho.PosSemidef ∧ Matrix.trace rho = 1 ∧ Phi rho = rho := by
  classical
  letI : CStarAlgebra (Matrix n n ℂ) := { }
  let sigma : Matrix n n ℂ :=
    ((Fintype.card n : ℝ)⁻¹ : ℂ) • (1 : Matrix n n ℂ)
  let average : ℕ → Matrix n n ℂ := fun N =>
    birkhoffAverage ℂ (Phi : Matrix n n ℂ → Matrix n n ℂ) id (N + 1) sigma
  have hCardPos : 0 < (Fintype.card n : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hSigmaPos : sigma.PosSemidef := by
    exact Matrix.PosSemidef.one.smul (by positivity)
  have hSigmaTrace : Matrix.trace sigma = 1 := by
    simp [sigma, Matrix.trace]
  have hIterPos (k : ℕ) :
      ((Phi : Matrix n n ℂ → Matrix n n ℂ)^[k] sigma).PosSemidef := by
    induction k with
    | zero => simpa using hSigmaPos
    | succ k ih =>
        rw [iterate_succ_apply']
        exact hPos _ ih
  have hIterTrace (k : ℕ) (rho : Matrix n n ℂ) :
      Matrix.trace ((Phi : Matrix n n ℂ → Matrix n n ℂ)^[k] rho) =
        Matrix.trace rho := by
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [iterate_succ_apply', hTrace, ih]
  have hAveragePos (N : ℕ) : (average N).PosSemidef := by
    dsimp [average, birkhoffAverage, birkhoffSum]
    apply (Matrix.posSemidef_sum (Finset.range (N + 1)) ?_).smul
    · positivity
    · intro k _
      simpa using hIterPos k
  have hAverageTrace (N : ℕ) : Matrix.trace (average N) = 1 := by
    have hN : ((N + 1 : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero N
    have hN' : (N : ℂ) + 1 ≠ 0 := by
      simpa [Nat.cast_add, Nat.cast_one] using hN
    simp [average, birkhoffAverage, birkhoffSum, hIterTrace, hSigmaTrace, hN']
  have state_norm_le_one {rho : Matrix n n ℂ} (hrhoPos : rho.PosSemidef)
      (hrhoTrace : Matrix.trace rho = 1) : ‖rho‖ ≤ 1 := by
    have hEigenvalueSum : ∑ j, hrhoPos.isHermitian.eigenvalues j = 1 := by
      have hComplexSum := hrhoPos.isHermitian.trace_eq_sum_eigenvalues
      rw [hrhoTrace] at hComplexSum
      simpa using congrArg Complex.re hComplexSum.symm
    have hNormSpectrum :=
      CStarAlgebra.norm_or_neg_norm_mem_spectrum (a := rho)
        (ha := hrhoPos.isHermitian.isSelfAdjoint)
    rw [hrhoPos.isHermitian.spectrum_real_eq_range_eigenvalues] at hNormSpectrum
    rcases hNormSpectrum with ⟨i, hi⟩ | ⟨i, hi⟩
    · rw [← hi, ← hEigenvalueSum]
      exact Finset.single_le_sum
        (fun j _ => hrhoPos.eigenvalues_nonneg j) (Finset.mem_univ i)
    · have hEigenvalueNonneg := hrhoPos.eigenvalues_nonneg i
      rw [hi] at hEigenvalueNonneg
      linarith [norm_nonneg rho]
  have hAverageBall (N : ℕ) :
      average N ∈ Metric.closedBall (0 : Matrix n n ℂ) 1 := by
    simpa [Metric.mem_closedBall, dist_zero_right] using
      state_norm_le_one (hAveragePos N) (hAverageTrace N)
  obtain ⟨rho, _, subsequence, hSubsequenceMono, hSubsequenceLimit⟩ :=
    (isCompact_closedBall (0 : Matrix n n ℂ) 1).tendsto_subseq hAverageBall
  have hRhoPos : rho.PosSemidef := by
    rw [← Matrix.nonneg_iff_posSemidef]
    exact ge_of_tendsto hSubsequenceLimit <|
      Eventually.of_forall fun k => (hAveragePos (subsequence k)).nonneg
  have hTraceContinuous : Continuous (Matrix.traceLinearMap n ℂ ℂ) :=
    LinearMap.continuous_of_finiteDimensional _
  have hRhoTrace : Matrix.trace rho = 1 := by
    have hTraceLimit :
        Tendsto (fun k => Matrix.trace (average (subsequence k))) atTop
          (nhds (Matrix.trace rho)) := by
      simpa [Function.comp_def] using
        (hTraceContinuous.tendsto rho).comp hSubsequenceLimit
    apply tendsto_nhds_unique hTraceLimit
    simp [hAverageTrace]
  have hOrbitBounded :
      Bornology.IsBounded
        (range fun k => (Phi : Matrix n n ℂ → Matrix n n ℂ)^[k] sigma) := by
    refine isBounded_iff_forall_norm_le.2 ⟨1, Set.forall_mem_range.2 fun k => ?_⟩
    exact state_norm_le_one (hIterPos k) ((hIterTrace k sigma).trans hSigmaTrace)
  have hMapAverage (N : ℕ) :
      Phi (average N) =
        birkhoffAverage ℂ (Phi : Matrix n n ℂ → Matrix n n ℂ) id (N + 1) (Phi sigma) := by
    simp only [average, birkhoffAverage, birkhoffSum, LinearMap.map_smul, map_sum, id_eq]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [← iterate_succ_apply' (Phi : Matrix n n ℂ → Matrix n n ℂ) k sigma,
      iterate_succ_apply (Phi : Matrix n n ℂ → Matrix n n ℂ) k sigma]
  have hAverageDifference :
      Tendsto (fun N => Phi (average N) - average N) atTop (nhds 0) := by
    have hTelescoping :=
      (tendsto_birkhoffAverage_apply_sub_birkhoffAverage
        (𝕜 := ℂ) (f := (Phi : Matrix n n ℂ → Matrix n n ℂ)) (g := id) (x := sigma)
        hOrbitBounded).comp
        (tendsto_add_atTop_nat 1)
    simpa [average, hMapAverage, Function.comp_def] using hTelescoping
  have hPhiContinuous : Continuous Phi := Phi.continuous_of_finiteDimensional
  have hLimitDifference :
      Tendsto (fun k => Phi (average (subsequence k)) - average (subsequence k)) atTop
        (nhds (Phi rho - rho)) :=
    (by
      simpa [Function.comp_def] using
        ((hPhiContinuous.tendsto rho).comp hSubsequenceLimit).sub hSubsequenceLimit)
  have hLimitDifferenceZero :
      Tendsto (fun k => Phi (average (subsequence k)) - average (subsequence k)) atTop
        (nhds 0) :=
    hAverageDifference.comp hSubsequenceMono.tendsto_atTop
  have hFixed : Phi rho = rho := by
    exact sub_eq_zero.mp (tendsto_nhds_unique hLimitDifference hLimitDifferenceZero)
  exact ⟨rho, hRhoPos, hRhoTrace, hFixed⟩

end D5.S3.Quantum.ChannelFixedState
