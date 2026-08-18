/- GID: D5/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExactSpan
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ReferenceFrame/ComplexReferenceFrameTaxExactSpan
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Identify the exact complex reference-frame tax and its paired sine-mode span. -/

import D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExact

/- Library-search audit trail (2026-08-18):
   * The frozen complex exact-tax theorem directly supplies the unitary, conservation,
     fidelity, optimum, sine-tax, flat-tax, and dimension clauses.
   * The frozen complexification module contains the required span equality only as a
     private helper, so its construction from path averaging and the two sine modes is
     repeated here without changing that module.
   * Pinned Mathlib supplies `linearIndependent_algebraMap_comp_iff`,
     `linearIndependent_iff_card_eq_finrank_span`, `finrank_span_eq_card`,
     `Module.End.mem_eigenspace_iff`, and `Submodule.eq_of_le_of_finrank_le`.
   * Repository and pinned-Mathlib searches found no public theorem packaging all clauses. -/

namespace D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExactSpan

open scoped BigOperators
open scoped Matrix
open D5.S3.QuantumBounds.ReferenceFrameTax
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
open D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace
open D5.S3.QuantumBounds.ReferenceFrame.Complexification
open D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExact

/-- Zero-boundary nearest-neighbor averaging on complex reference amplitudes. -/
noncomputable def complexPathAverage (N : ℕ) :
    Module.End ℂ (Fin N → ℂ) where
  toFun := fun c m ↦
    ((if _h : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2
  map_add' := by
    intro c d
    funext m
    by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
      simp [hl, hr] <;> ring
  map_smul' := by
    intro a c
    funext m
    by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
      simp [hl, hr, Pi.smul_apply, smul_eq_mul] <;> ring

/-- The low-edge sine mode and its sign-alternating high-edge partner over complex scalars. -/
noncomputable def complexPairedSineModes (N : ℕ) :
    Fin 2 → (Fin N → ℂ) :=
  fun k ↦ (algebraMap ℝ ℂ) ∘ topModeFamily N k

private theorem complex_edge_average_of_real {N : ℕ} (c : Fin N → ℝ) :
    complexPathAverage N (fun i ↦ (c i : ℂ)) =
      fun m ↦ (nearestNeighborAverage c m : ℂ) := by
  funext m
  unfold complexPathAverage nearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr]

private theorem complex_edge_squared_average_of_real {N : ℕ} (c : Fin N → ℝ)
    (hc : nearestNeighborAverage (nearestNeighborAverage c) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • c) :
    complexPathAverage N (complexPathAverage N (fun i ↦ (c i : ℂ))) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) •
        (fun i ↦ (c i : ℂ)) := by
  rw [complex_edge_average_of_real c]
  rw [complex_edge_average_of_real (nearestNeighborAverage c)]
  rw [hc]
  ext i
  simp [Pi.smul_apply, smul_eq_mul]

private theorem complex_edge_mode_mem_top_eigenspace (N : ℕ) (k : Fin 2) :
    complexPairedSineModes N k ∈
      Module.End.eigenspace
        ((complexPathAverage N).comp (complexPathAverage N))
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) := by
  rw [Module.End.mem_eigenspace_iff]
  change complexPathAverage N
      (complexPathAverage N (fun i ↦ (topModeFamily N k i : ℂ))) =
    (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) •
      (fun i ↦ (topModeFamily N k i : ℂ))
  apply complex_edge_squared_average_of_real
  apply top_mode_space_squared_eigenvector
  exact Submodule.subset_span (Set.mem_range_self k)

private theorem complex_edge_average_re {N : ℕ} (c : Fin N → ℂ) (m : Fin N) :
    (complexPathAverage N c m).re =
      nearestNeighborAverage (fun i ↦ (c i).re) m := by
  unfold complexPathAverage nearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr]

private theorem complex_edge_average_im {N : ℕ} (c : Fin N → ℂ) (m : Fin N) :
    (complexPathAverage N c m).im =
      nearestNeighborAverage (fun i ↦ (c i).im) m := by
  unfold complexPathAverage nearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr]

private theorem real_part_edge_squared_eigenvector {N : ℕ} (c : Fin N → ℂ)
    (hc : complexPathAverage N (complexPathAverage N c) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) • c) :
    nearestNeighborAverage (nearestNeighborAverage (fun i ↦ (c i).re)) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • (fun i ↦ (c i).re) := by
  funext m
  have hm := congrArg Complex.re (congrFun hc m)
  rw [← Complex.ofReal_pow] at hm
  simpa only [complex_edge_average_re, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hm

private theorem imaginary_part_edge_squared_eigenvector {N : ℕ} (c : Fin N → ℂ)
    (hc : complexPathAverage N (complexPathAverage N c) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) • c) :
    nearestNeighborAverage (nearestNeighborAverage (fun i ↦ (c i).im)) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • (fun i ↦ (c i).im) := by
  funext m
  have hm := congrArg Complex.im (congrFun hc m)
  rw [← Complex.ofReal_pow] at hm
  simpa only [complex_edge_average_im, Pi.smul_apply, smul_eq_mul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hm

private theorem mem_complex_edge_mode_span_iff (N : ℕ) (c : Fin N → ℂ) :
    c ∈ Submodule.span ℂ (Set.range (complexPairedSineModes N)) ↔
      ∃ a b : ℂ,
        a • complexPairedSineModes N 0 + b • complexPairedSineModes N 1 = c := by
  have hrange : Set.range (complexPairedSineModes N) =
      {complexPairedSineModes N 0, complexPairedSineModes N 1} := by
    ext x
    simp [eq_comm]
  rw [hrange, Submodule.mem_span_pair]

private theorem complex_edge_modes_linear_independent (N : ℕ) (hN : 2 ≤ N) :
    LinearIndependent ℂ (complexPairedSineModes N) := by
  unfold complexPairedSineModes
  apply linearIndependent_algebraMap_comp_iff.mpr
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change 2 = Module.finrank ℝ (topModeSpace N)
  exact (top_mode_space_finrank N hN).symm

private theorem complex_top_eigenspace_eq_edge_mode_span (N : ℕ) (hN : 2 ≤ N) :
    Module.End.eigenspace
        ((complexPathAverage N).comp (complexPathAverage N))
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) =
      Submodule.span ℂ (Set.range (complexPairedSineModes N)) := by
  apply le_antisymm
  · intro c hc
    have hcLaw := Module.End.mem_eigenspace_iff.mp hc
    have hre : (fun i ↦ (c i).re) ∈ squaredTopEigenspace N :=
      (mem_squared_top_eigenspace_iff N _).mpr
        (real_part_edge_squared_eigenvector c hcLaw)
    have him : (fun i ↦ (c i).im) ∈ squaredTopEigenspace N :=
      (mem_squared_top_eigenspace_iff N _).mpr
        (imaginary_part_edge_squared_eigenvector c hcLaw)
    rw [squared_top_eigenspace_eq_top_mode_space N hN, mem_top_mode_space_iff] at hre him
    rcases hre with ⟨ar, br, hre⟩
    rcases him with ⟨ai, bi, him⟩
    apply (mem_complex_edge_mode_span_iff N c).mpr
    refine ⟨(ar : ℂ) + Complex.I * (ai : ℂ),
      (br : ℂ) + Complex.I * (bi : ℂ), ?_⟩
    funext i
    apply Complex.ext
    · simpa [complexPairedSineModes, topModeFamily, Pi.smul_apply, smul_eq_mul]
        using congrFun hre i
    · simpa [complexPairedSineModes, topModeFamily, Pi.smul_apply, smul_eq_mul]
        using congrFun him i
  · apply Submodule.span_le.mpr
    intro c hc
    rcases hc with ⟨k, rfl⟩
    exact complex_edge_mode_mem_top_eigenspace N k

/-- The finite exchange model has the exact complex-amplitude reference-frame tax, and its
optimal squared eigenspace is precisely the complex span of the low and high edge sine modes. -/
theorem complex_reference_frame_tax_exact_span (N : ℕ) (hN : 2 ≤ N) :
    (exchangeUnitary N)ᴴ * exchangeUnitary N = 1 ∧
    (∀ x : JointBasis N, totalExcitation (exchangeBasis x) = totalExcitation x) ∧
    (∀ c : Fin N → ℂ,
      (1 / 4 : ℝ) * (∑ r : Fin N,
          (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
              exchangeUnitary N (sOut, r) (sIn, m) * c m);
            Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
        ∑ m : Fin N,
          Complex.normSq
            (((if _h : 0 < m.val then
                c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
              (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2)) ∧
    IsGreatest
      {q : ℝ | ∃ c : Fin N → ℂ,
        (∑ i : Fin N, Complex.normSq (c i)) = 1 ∧
        (1 / 4 : ℝ) * (∑ r : Fin N,
            (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
                exchangeUnitary N (sOut, r) (sIn, m) * c m);
              Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) = q}
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) ∧
    1 - Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 =
      Real.sin (Real.pi / (N + 1 : ℝ)) ^ 2 ∧
    1 - (1 / 4 : ℝ) * (∑ r : Fin N,
        (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
            exchangeUnitary N (sOut, r) (sIn, m) *
              ((1 / Real.sqrt (N : ℝ) : ℝ) : ℂ));
          Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
      3 / (2 * (N : ℝ)) ∧
    Module.End.eigenspace
        ((complexPathAverage N).comp (complexPathAverage N))
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) =
      Submodule.span ℂ (Set.range (complexPairedSineModes N)) ∧
    Module.finrank ℂ
      (Module.End.eigenspace
        ((complexPathAverage N).comp (complexPathAverage N))
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ)) = 2 := by
  rcases complex_reference_frame_tax_exact N hN with
    ⟨hunitary, hconservation, hfidelity, hoptimum, htax, hflat, _hdim⟩
  have hspan := complex_top_eigenspace_eq_edge_mode_span N hN
  have hdim :
      Module.finrank ℂ
        (Module.End.eigenspace
          ((complexPathAverage N).comp (complexPathAverage N))
          (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ)) = 2 := by
    rw [hspan]
    rw [finrank_span_eq_card (complex_edge_modes_linear_independent N hN)]
    norm_num
  exact ⟨hunitary, hconservation, hfidelity, hoptimum, htax, hflat, hspan, hdim⟩

/-- The ladder-length hypothesis has a concrete witness. -/
example : ∃ N : ℕ, 2 ≤ N := ⟨2, by norm_num⟩

/-- The complex reference-vector domain is inhabited. -/
example : Nonempty (Fin 2 → ℂ) := ⟨fun _ ↦ 0⟩

#print axioms complex_reference_frame_tax_exact_span

end D5.S3.QuantumBounds.ReferenceFrame.ComplexReferenceFrameTaxExactSpan
