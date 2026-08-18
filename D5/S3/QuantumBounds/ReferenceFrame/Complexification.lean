/- GID: D5/S3/QuantumBounds/ReferenceFrame/Complexification
   generality: G
   mirror-B: D5/B/S3/QuantumBounds/ReferenceFrame/Complexification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Complexify the channel-fidelity quadratic, its optimum, and its paired top eigenspace. -/

/-
Library-search audit trail (mathlib v4.31.0, offline, 2026-08-18):

* `Complex.normSq_apply`, `Complex.normSq_div`, and `Complex.normSq_ofReal` provide the
  real-imaginary norm decomposition and scaling identities.
* `linearIndependent_algebraMap_comp_iff` transports the frozen real two-mode independence to
  complex scalars; no packaged complexification theorem for this path eigenspace was found.

Repository search audit trail (working tree, 2026-08-18):

* The physical trace reduction reuses `ChannelFidelityBridge`; optimality and the full squared
  eigenspace reuse `ReferenceFrameTaxOptimal` and `TopEigenspace` rather than re-proving them.
-/

import D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
import D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace

namespace D5.S3.QuantumBounds.ReferenceFrame.Complexification

open scoped BigOperators
open scoped Matrix
open D5.S3.QuantumBounds.ReferenceFrameTax
open D5.S3.QuantumBounds.ReferenceFrame.ChannelFidelityBridge
open D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace
private noncomputable def complexNearestNeighborAverage {N : ℕ}
    (c : Fin N → ℂ) (m : Fin N) : ℂ :=
  ((if _h : 0 < m.val then
      c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
    (if _h : m.val + 1 < N then
      c ⟨m.val + 1, _h⟩ else 0)) / 2
private noncomputable def complexNearestNeighborQuadratic {N : ℕ}
    (c : Fin N → ℂ) : ℝ :=
  ∑ m : Fin N, Complex.normSq (complexNearestNeighborAverage c m)
private noncomputable def complexExchangeKraus {N : ℕ} (c : Fin N → ℂ) (r : Fin N) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  fun sOut sIn ↦ ∑ m : Fin N,
    exchangeUnitary N (sOut, r) (sIn, m) * c m
private noncomputable def complexEntanglementFidelity {N : ℕ} (c : Fin N → ℂ) : ℝ :=
  (1 / 4 : ℝ) * ∑ r : Fin N,
    Complex.normSq (Matrix.trace (bitFlipᴴ * complexExchangeKraus c r))
private theorem complex_exchange_kraus_one_zero {N : ℕ} (c : Fin N → ℂ) (r : Fin N) :
    complexExchangeKraus c r 1 0 =
      (if _h : r.val + 1 < N then c ⟨r.val + 1, _h⟩ else 0) := by
  classical
  by_cases hr : r.val + 1 < N
  · simp only [hr, ↓reduceDIte, complexExchangeKraus]
    rw [Finset.sum_eq_single ⟨r.val + 1, hr⟩]
    · simp [exchangeUnitary, exchangeBasis, hr]
    · intro b _ hb
      apply mul_eq_zero.mpr
      left
      unfold exchangeUnitary
      rw [if_neg]
      intro h
      apply hb
      have hval := congrArg (fun x => x.2.val) h
      apply Fin.ext
      simpa [exchangeBasis, hr] using hval
    · simp
  · simp only [hr, ↓reduceDIte, complexExchangeKraus]
    apply Finset.sum_eq_zero
    intro b _hb
    simp [exchangeUnitary, exchangeBasis, hr]
private theorem complex_exchange_kraus_zero_one {N : ℕ} (c : Fin N → ℂ) (r : Fin N) :
    complexExchangeKraus c r 0 1 =
      (if _h : 0 < r.val then
        c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ else 0) := by
  classical
  by_cases hl : 0 < r.val
  · simp only [hl, ↓reduceDIte, complexExchangeKraus]
    rw [Finset.sum_eq_single
      ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩]
    · simp [exchangeUnitary, exchangeBasis, hl]
    · intro b _ hb
      apply mul_eq_zero.mpr
      left
      unfold exchangeUnitary
      rw [if_neg]
      intro h
      apply hb
      have hval := congrArg (fun x => x.2.val) h
      apply Fin.ext
      simpa [exchangeBasis, hl] using hval
    · simp
  · simp only [hl, ↓reduceDIte, complexExchangeKraus]
    apply Finset.sum_eq_zero
    intro b _hb
    simp [exchangeUnitary, exchangeBasis, hl]
private theorem complex_exchange_kraus_trace {N : ℕ} (c : Fin N → ℂ) (r : Fin N) :
    Matrix.trace (bitFlipᴴ * complexExchangeKraus c r) =
      (if _h : 0 < r.val then
          c ⟨r.val - 1, lt_of_le_of_lt (Nat.sub_le ..) r.isLt⟩ else 0) +
        (if _h : r.val + 1 < N then c ⟨r.val + 1, _h⟩ else 0) := by
  simp only [bitFlip, Matrix.conjTranspose_apply, Matrix.of_apply, Matrix.trace,
    Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]
  rw [complex_exchange_kraus_one_zero, complex_exchange_kraus_zero_one]
  by_cases hl : 0 < r.val <;> by_cases hr : r.val + 1 < N <;>
    simp [hl, hr, add_comm]
private theorem complex_average_eq_real_parts {N : ℕ} (c : Fin N → ℂ) (m : Fin N) :
    complexNearestNeighborAverage c m =
      (nearestNeighborAverage (fun i => (c i).re) m : ℂ) +
        Complex.I * nearestNeighborAverage (fun i => (c i).im) m := by
  unfold complexNearestNeighborAverage nearestNeighborAverage
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im, one_mul, zero_mul]
  · by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;> simp [hl, hr] <;> ring
  · by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;> simp [hl, hr] <;> ring
private theorem complex_nearest_neighbor_quadratic_eq_real_parts {N : ℕ} (c : Fin N → ℂ) :
    complexNearestNeighborQuadratic c =
      nearestNeighborQuadratic (fun m => (c m).re) +
        nearestNeighborQuadratic (fun m => (c m).im) := by
  unfold complexNearestNeighborQuadratic
  rw [show (∑ m : Fin N, Complex.normSq (complexNearestNeighborAverage c m)) =
      ∑ m : Fin N, (nearestNeighborAverage (fun i => (c i).re) m) ^ 2 +
        ∑ m : Fin N, (nearestNeighborAverage (fun i => (c i).im) m) ^ 2 by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [complex_average_eq_real_parts]
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      one_mul, zero_mul, sub_zero, add_zero]
    ring]
  rfl
private theorem complex_entanglement_fidelity_eq_real_parts {N : ℕ} (c : Fin N → ℂ) :
    complexEntanglementFidelity c =
      entanglementFidelity (fun i => (c i).re) +
        entanglementFidelity (fun i => (c i).im) := by
  unfold complexEntanglementFidelity entanglementFidelity
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  rw [complex_exchange_kraus_trace]
  have hre := complex_exchange_kraus_trace (fun i => ((c i).re : ℂ)) r
  have him := complex_exchange_kraus_trace (fun i => ((c i).im : ℂ)) r
  change Matrix.trace (bitFlipᴴ * exchangeKraus (fun i => (c i).re) r) = _ at hre
  change Matrix.trace (bitFlipᴴ * exchangeKraus (fun i => (c i).im) r) = _ at him
  rw [hre, him]
  by_cases hl : 0 < r.val <;> by_cases hr : r.val + 1 < N <;>
    simp [hl, hr, Complex.normSq_apply] <;> ring
/-- Complex-amplitude channel fidelity is the squared norm of zero-boundary path averaging. -/
theorem complex_entanglement_fidelity_eq_nearest_neighbor_quadratic {N : ℕ} (c : Fin N → ℂ) :
    (1 / 4 : ℝ) * (∑ r : Fin N,
        (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
            exchangeUnitary N (sOut, r) (sIn, m) * c m);
          Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
      ∑ m : Fin N,
        Complex.normSq
          (((if _h : 0 < m.val then
              c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
            (if _h : m.val + 1 < N then c ⟨m.val + 1, _h⟩ else 0)) / 2) := by
  change complexEntanglementFidelity c = complexNearestNeighborQuadratic c
  calc
    complexEntanglementFidelity c =
        entanglementFidelity (fun i => (c i).re) +
          entanglementFidelity (fun i => (c i).im) :=
      complex_entanglement_fidelity_eq_real_parts c
    _ = nearestNeighborQuadratic (fun i => (c i).re) +
          nearestNeighborQuadratic (fun i => (c i).im) := by
      rw [entanglement_fidelity_eq_nearest_neighbor_quadratic,
        entanglement_fidelity_eq_nearest_neighbor_quadratic]
    _ = complexNearestNeighborQuadratic c :=
      (complex_nearest_neighbor_quadratic_eq_real_parts c).symm
private theorem complex_fidelity_eq_quadratic {N : ℕ} (c : Fin N → ℂ) :
    complexEntanglementFidelity c = complexNearestNeighborQuadratic c := by
  have h := complex_entanglement_fidelity_eq_nearest_neighbor_quadratic c
  change complexEntanglementFidelity c = complexNearestNeighborQuadratic c at h
  exact h
private theorem complex_norm_sum_eq_real_parts {N : ℕ} (c : Fin N → ℂ) :
    (∑ i : Fin N, Complex.normSq (c i)) =
      (∑ i : Fin N, (c i).re ^ 2) + ∑ i : Fin N, (c i).im ^ 2 := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  ring
/-- Complex unit vectors have the same sharp fidelity optimum as real unit vectors. -/
theorem complex_tax_optimum_eq_real_optimum (N : ℕ) (hN : 1 ≤ N) :
    IsGreatest
      {q : ℝ | ∃ c : Fin N → ℂ,
        (∑ i : Fin N, Complex.normSq (c i)) = 1 ∧
        (1 / 4 : ℝ) * (∑ r : Fin N,
            (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
                exchangeUnitary N (sOut, r) (sIn, m) * c m);
              Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) = q}
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2) := by
  change IsGreatest
    {q : ℝ | ∃ c : Fin N → ℂ,
      (∑ i : Fin N, Complex.normSq (c i)) = 1 ∧
      complexEntanglementFidelity c = q}
    (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2)
  let lambdaSq := Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2
  have hreal := reference_frame_tax_isGreatest N hN
  constructor
  · rcases hreal.1 with ⟨a, ha, hq⟩
    refine ⟨fun i => (a i : ℂ), ?_, ?_⟩
    · calc
        (∑ i : Fin N, Complex.normSq (a i : ℂ)) = ∑ i : Fin N, a i ^ 2 := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Complex.normSq_ofReal]
          ring
        _ = 1 := ha
    · rw [complex_fidelity_eq_quadratic,
        complex_nearest_neighbor_quadratic_eq_real_parts]
      simpa [nearestNeighborQuadratic] using hq
  · intro q hq
    rcases hq with ⟨c, hc, hq⟩
    have hparts :
        (∑ i : Fin N, (c i).re ^ 2) + ∑ i : Fin N, (c i).im ^ 2 = 1 := by
      rw [← complex_norm_sum_eq_real_parts]
      exact hc
    have hre := nearestNeighborQuadratic_le_cos_sq N (fun i => (c i).re)
    have him := nearestNeighborQuadratic_le_cos_sq N (fun i => (c i).im)
    calc
      q = complexEntanglementFidelity c := hq.symm
      _ = complexNearestNeighborQuadratic c :=
        complex_fidelity_eq_quadratic c
      _ = nearestNeighborQuadratic (fun i => (c i).re) +
          nearestNeighborQuadratic (fun i => (c i).im) :=
        complex_nearest_neighbor_quadratic_eq_real_parts c
      _ ≤ lambdaSq * (∑ i : Fin N, (c i).re ^ 2) +
          lambdaSq * (∑ i : Fin N, (c i).im ^ 2) := add_le_add hre him
      _ = lambdaSq *
          ((∑ i : Fin N, (c i).re ^ 2) + ∑ i : Fin N, (c i).im ^ 2) := by ring
      _ = lambdaSq := by rw [hparts, mul_one]
private theorem complex_nearest_neighbor_average_add {N : ℕ} (c d : Fin N → ℂ) :
    complexNearestNeighborAverage (c + d) =
      complexNearestNeighborAverage c + complexNearestNeighborAverage d := by
  funext m
  unfold complexNearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr] <;> ring
private theorem complex_nearest_neighbor_average_smul {N : ℕ} (a : ℂ) (c : Fin N → ℂ) :
    complexNearestNeighborAverage (a • c) = a • complexNearestNeighborAverage c := by
  funext m
  unfold complexNearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr, Pi.smul_apply, smul_eq_mul] <;> ring
private noncomputable def complexNearestNeighborMap (N : ℕ) :
    Module.End ℂ (Fin N → ℂ) where
  toFun := complexNearestNeighborAverage
  map_add' := complex_nearest_neighbor_average_add
  map_smul' := complex_nearest_neighbor_average_smul
private noncomputable def complexSquaredTopEigenspace (N : ℕ) :
    Submodule ℂ (Fin N → ℂ) :=
  Module.End.eigenspace
    ((complexNearestNeighborMap N).comp (complexNearestNeighborMap N))
    (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ)
private noncomputable def complexTopModeFamily (N : ℕ) : Fin 2 → (Fin N → ℂ) :=
  fun k ↦ (algebraMap ℝ ℂ) ∘ topModeFamily N k
private noncomputable def complexTopModeSpace (N : ℕ) : Submodule ℂ (Fin N → ℂ) :=
  Submodule.span ℂ (Set.range (complexTopModeFamily N))
private theorem complex_average_of_real {N : ℕ} (c : Fin N → ℝ) :
    complexNearestNeighborAverage (fun i => (c i : ℂ)) =
      fun m => (nearestNeighborAverage c m : ℂ) := by
  funext m
  unfold complexNearestNeighborAverage nearestNeighborAverage
  by_cases hl : 0 < m.val <;> by_cases hr : m.val + 1 < N <;>
    simp [hl, hr]
private theorem complex_average_re {N : ℕ} (c : Fin N → ℂ) (m : Fin N) :
    (complexNearestNeighborAverage c m).re =
      nearestNeighborAverage (fun i => (c i).re) m := by
  rw [complex_average_eq_real_parts]
  simp
private theorem complex_average_im {N : ℕ} (c : Fin N → ℂ) (m : Fin N) :
    (complexNearestNeighborAverage c m).im =
      nearestNeighborAverage (fun i => (c i).im) m := by
  rw [complex_average_eq_real_parts]
  simp
private theorem complex_squared_average_of_real {N : ℕ} (c : Fin N → ℝ)
    (hc : nearestNeighborAverage (nearestNeighborAverage c) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • c) :
    complexNearestNeighborAverage
        (complexNearestNeighborAverage (fun i => (c i : ℂ))) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) •
        (fun i => (c i : ℂ)) := by
  rw [complex_average_of_real c]
  rw [complex_average_of_real (nearestNeighborAverage c)]
  rw [hc]
  ext i
  simp [Pi.smul_apply, smul_eq_mul]
private theorem complex_top_mode_family_mem_eigenspace (N : ℕ) (k : Fin 2) :
    complexTopModeFamily N k ∈ complexSquaredTopEigenspace N := by
  rw [complexSquaredTopEigenspace, Module.End.mem_eigenspace_iff]
  apply complex_squared_average_of_real
  apply top_mode_space_squared_eigenvector
  exact Submodule.subset_span (Set.mem_range_self k)
private theorem real_part_squared_eigenvector {N : ℕ} (c : Fin N → ℂ)
    (hc : complexNearestNeighborAverage (complexNearestNeighborAverage c) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) • c) :
    nearestNeighborAverage (nearestNeighborAverage (fun i => (c i).re)) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • (fun i => (c i).re) := by
  funext m
  have hm := congrArg Complex.re (congrFun hc m)
  rw [← Complex.ofReal_pow] at hm
  simpa only [complex_average_re, Pi.smul_apply, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using hm
private theorem imaginary_part_squared_eigenvector {N : ℕ} (c : Fin N → ℂ)
    (hc : complexNearestNeighborAverage (complexNearestNeighborAverage c) =
      (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ) • c) :
    nearestNeighborAverage (nearestNeighborAverage (fun i => (c i).im)) =
      Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 • (fun i => (c i).im) := by
  funext m
  have hm := congrArg Complex.im (congrFun hc m)
  rw [← Complex.ofReal_pow] at hm
  simpa only [complex_average_im, Pi.smul_apply, smul_eq_mul, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using hm
private theorem mem_complex_top_mode_space_iff (N : ℕ) (c : Fin N → ℂ) :
    c ∈ complexTopModeSpace N ↔
      ∃ a b : ℂ,
        a • complexTopModeFamily N 0 + b • complexTopModeFamily N 1 = c := by
  have hrange : Set.range (complexTopModeFamily N) =
      {complexTopModeFamily N 0, complexTopModeFamily N 1} := by
    ext x
    simp [eq_comm]
  rw [complexTopModeSpace, hrange, Submodule.mem_span_pair]
private theorem complex_squared_top_eigenspace_eq_top_mode_space (N : ℕ) (hN : 2 ≤ N) :
    complexSquaredTopEigenspace N = complexTopModeSpace N := by
  apply le_antisymm
  · intro c hc
    have hcLaw := (Module.End.mem_eigenspace_iff.mp hc)
    have hre : (fun i => (c i).re) ∈ squaredTopEigenspace N :=
      (mem_squared_top_eigenspace_iff N _).mpr (real_part_squared_eigenvector c hcLaw)
    have him : (fun i => (c i).im) ∈ squaredTopEigenspace N :=
      (mem_squared_top_eigenspace_iff N _).mpr (imaginary_part_squared_eigenvector c hcLaw)
    rw [squared_top_eigenspace_eq_top_mode_space N hN, mem_top_mode_space_iff] at hre him
    rcases hre with ⟨ar, br, hre⟩
    rcases him with ⟨ai, bi, him⟩
    apply (mem_complex_top_mode_space_iff N c).mpr
    refine ⟨(ar : ℂ) + Complex.I * (ai : ℂ),
      (br : ℂ) + Complex.I * (bi : ℂ), ?_⟩
    funext i
    apply Complex.ext
    · simpa [complexTopModeFamily, topModeFamily, Pi.smul_apply, smul_eq_mul]
        using congrFun hre i
    · simpa [complexTopModeFamily, topModeFamily, Pi.smul_apply, smul_eq_mul]
        using congrFun him i
  · apply Submodule.span_le.mpr
    intro c hc
    rcases hc with ⟨k, rfl⟩
    exact complex_top_mode_family_mem_eigenspace N k
private theorem complex_top_mode_family_linear_independent (N : ℕ) (hN : 2 ≤ N) :
    LinearIndependent ℂ (complexTopModeFamily N) := by
  unfold complexTopModeFamily
  apply linearIndependent_algebraMap_comp_iff.mpr
  apply linearIndependent_iff_card_eq_finrank_span.mpr
  change 2 = Module.finrank ℝ (topModeSpace N)
  exact (top_mode_space_finrank N hN).symm
/-- The squared complex path-averaging top eigenspace has complex dimension two. -/
theorem complex_top_eigenspace_finrank (N : ℕ) (hN : 2 ≤ N) :
    let average : Module.End ℂ (Fin N → ℂ) :=
      { toFun := fun c m ↦
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
            simp [hl, hr, Pi.smul_apply, smul_eq_mul] <;> ring }
    Module.finrank ℂ
      (Module.End.eigenspace (average.comp average)
        (Real.cos (Real.pi / (N + 1 : ℝ)) ^ 2 : ℂ)) = 2 := by
  dsimp only
  change Module.finrank ℂ (complexSquaredTopEigenspace N) = 2
  rw [complex_squared_top_eigenspace_eq_top_mode_space N hN]
  unfold complexTopModeSpace
  rw [finrank_span_eq_card (complex_top_mode_family_linear_independent N hN)]
  norm_num
/-- The complex flat vector has tax `3/(2N)` for `N >= 2`; the frozen `N = 1` value is `1`. -/
theorem flat_tax_complex (N : ℕ) (hN : 2 ≤ N) :
    1 - (1 / 4 : ℝ) * (∑ r : Fin N,
        (let K : Matrix (Fin 2) (Fin 2) ℂ := (fun sOut sIn ↦ ∑ m : Fin N,
            exchangeUnitary N (sOut, r) (sIn, m) *
              ((1 / Real.sqrt (N : ℝ) : ℝ) : ℂ));
          Complex.normSq (Matrix.trace (bitFlipᴴ * K)))) =
      3 / (2 * (N : ℝ)) := by
  change 1 - complexEntanglementFidelity
    (fun _ : Fin N => ((1 / Real.sqrt (N : ℝ) : ℝ) : ℂ)) = 3 / (2 * (N : ℝ))
  rw [complex_fidelity_eq_quadratic,
    complex_nearest_neighbor_quadratic_eq_real_parts]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  rw [show nearestNeighborQuadratic (N := N) (fun _ => 0) = 0 by
    simp [nearestNeighborQuadratic], add_zero]
  exact flat_reference_frame_tax N hN
#print axioms complex_entanglement_fidelity_eq_nearest_neighbor_quadratic
#print axioms complex_tax_optimum_eq_real_optimum
#print axioms complex_top_eigenspace_finrank
#print axioms flat_tax_complex

end D5.S3.QuantumBounds.ReferenceFrame.Complexification
