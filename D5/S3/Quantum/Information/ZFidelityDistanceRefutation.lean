/- GID: D5/S3/Quantum/Information/ZFidelityDistanceRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ZFidelityDistanceRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Information/ZFidelityDistanceRefutation.claim; result=D5/S3/Quantum/Information/ZFidelityDistanceRefutation.result; claim=D5/S3/Quantum/Information/ZFidelityDistanceRefutation.claim
   digest: The z-fidelity distance at z = 2 violates the triangle inequality on qubits. -/

/-
proof_shape: zFidelity, zDistance: definition (Eq. (eq:z-fid-def) of arXiv:2404.16101 and the
  distance of its Open Question 3)
proof_shape: claim: definition (published question, read as the triangle inequality for every
  z in (1/2, 1) ∪ (1, ∞), every dimension and all density matrices)
proof_shape: stateP, stateQ, stateT: definition (the counterexample states)
proof_shape: result: bind-only (as local steps: real powers of positive idempotents through the
  continuous functional calculus, square roots of positive diagonal matrices by uniqueness, and
  evaluation of the three traces)
escape_witness: none (the settlement of the external named question is the new content)
admission_basis: open-problem-resolution (issue #12705; Refuted)
Direct frozen dependencies (GID, statement_id): none
-/

import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Information.ZFidelityDistanceRefutation

/-!
T. Nuradha, H. K. Mishra, F. Leditzky and M. M. Wilde, *Multivariate Fidelities*,
arXiv:2404.16101 (J. Phys. A 58 (2025) 165304), define the `z`-fidelity
`F_z(ρ, σ) = Tr[(σ^{1/(4z)} ρ^{1/(2z)} σ^{1/(4z)})^z]` and ask, in Open Question 3, whether
`√(2(1 - F_z(ρ, σ)))` is a distance measure for `z ∈ (1/2, 1) ∪ (1, ∞)`. At `z = 2` it is not:
for the rank-one projections `P = (9, 3; 3, 1)/10`, `T = (9, -3; -3, 1)/10` and
`Q = diag(16, 1)/17`, one has `F_2(P, T) = 256/625` and `F_2(P, Q) = F_2(Q, T) = 361/(100√17)`,
so `d(P, T) > d(P, Q) + d(Q, T)` because `9025² - 17 · 2131² = 4250888 > 0`.
-/

open scoped MatrixOrder ComplexOrder
open Matrix

/-- The `z`-fidelity `Tr[(σ^{1/(4z)} ρ^{1/(2z)} σ^{1/(4z)})^z]`, real part of the trace. -/
noncomputable def zFidelity {n : ℕ} (z : ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ((σ ^ (1 / (4 * z)) * ρ ^ (1 / (2 * z)) * σ ^ (1 / (4 * z))) ^ z).trace.re

/-- The distance `√(2(1 - F_z(ρ, σ)))` of Open Question 3. -/
noncomputable def zDistance {n : ℕ} (z : ℝ) (ρ σ : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  Real.sqrt (2 * (1 - zFidelity z ρ σ))

/-- Open Question 3, affirmative reading: for every `z ∈ (1/2, 1) ∪ (1, ∞)` the distance satisfies
the triangle inequality on the density matrices of every dimension. -/
def claim : Prop :=
  ∀ z : ℝ, (1 / 2 < z ∧ z < 1) ∨ 1 < z → ∀ (n : ℕ) (ρ σ τ : Matrix (Fin n) (Fin n) ℂ),
    ρ.PosSemidef → ρ.trace = 1 → σ.PosSemidef → σ.trace = 1 → τ.PosSemidef → τ.trace = 1 →
      zDistance z ρ τ ≤ zDistance z ρ σ + zDistance z σ τ

/-- The projection onto `(3, 1)/√10`. -/
noncomputable def stateP : Matrix (Fin 2) (Fin 2) ℂ := !![9 / 10, 3 / 10; 3 / 10, 1 / 10]
/-- The diagonal state `diag(16, 1)/17`. -/
noncomputable def stateQ : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun i => (((![16 / 17, 1 / 17] : Fin 2 → ℝ) i : ℝ) : ℂ)
/-- The projection onto `(3, -1)/√10`. -/
noncomputable def stateT : Matrix (Fin 2) (Fin 2) ℂ := !![9 / 10, -3 / 10; -3 / 10, 1 / 10]

set_option maxHeartbeats 4000000 in -- the explicit trace evaluations share this declaration
/-- The triangle inequality fails at `z = 2` for `stateP`, `stateQ`, `stateT`. -/
theorem result : ¬ claim := by
  intro h
  -- generic facts
  have hdiag_nonneg : ∀ v : Fin 2 → ℝ, (∀ i, 0 ≤ v i) →
      (0 : Matrix (Fin 2) (Fin 2) ℂ) ≤ diagonal fun i => ((v i : ℝ) : ℂ) := by
    intro v hv
    rw [Matrix.nonneg_iff_posSemidef]
    exact Matrix.PosSemidef.diagonal (fun i => Complex.zero_le_real.mpr (hv i))
  have hproj_pow : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, 0 ≤ M → M * M = M → ∀ r : ℝ, 0 < r →
      M ^ r = M := by
    intro M hM hidem r hr
    rw [CFC.rpow_eq_cfc_real hM]
    have hsa : IsSelfAdjoint M := hM.isSelfAdjoint
    conv_rhs => rw [← cfc_id' ℝ M]
    refine cfc_congr fun x hx => ?_
    rcases IsIdempotentElem.spectrum_subset ℝ (p := M) hidem hx with h | h
    · simp [h, Real.zero_rpow hr.ne']
    · simp [Set.mem_singleton_iff.mp h]
  have hproj_nonneg : ∀ M : Matrix (Fin 2) (Fin 2) ℂ, Mᴴ = M → M * M = M → 0 ≤ M := by
    intro M hH hidem
    rw [Matrix.nonneg_iff_posSemidef]
    have : M = Mᴴ * M := by rw [hH, hidem]
    rw [this]
    exact Matrix.posSemidef_conjTranspose_mul_self M
  -- the projections
  have hPH : statePᴴ = stateP := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [stateP, conjTranspose_apply] <;> norm_num
  have hTH : stateTᴴ = stateT := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [stateT, conjTranspose_apply] <;> norm_num
  have hPP : stateP * stateP = stateP := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [stateP, mul_apply, Fin.sum_univ_two] <;> norm_num
  have hTT : stateT * stateT = stateT := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [stateT, mul_apply, Fin.sum_univ_two] <;> norm_num
  have hP0 : 0 ≤ stateP := hproj_nonneg _ hPH hPP
  have hT0 : 0 ≤ stateT := hproj_nonneg _ hTH hTT
  set s : ℝ := Real.sqrt (Real.sqrt 17) with hs
  have hs0 : 0 < s := by positivity
  have hs2 : s ^ 2 = Real.sqrt 17 := Real.sq_sqrt (Real.sqrt_nonneg _)
  have h17 : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have h17C : ((Real.sqrt 17 : ℝ) : ℂ) ^ 2 = 17 := by exact_mod_cast h17
  set qv : Fin 2 → ℝ := ![16 / 17, 1 / 17] with hqv
  set rv : Fin 2 → ℝ := ![4 / Real.sqrt 17, 1 / Real.sqrt 17] with hrv
  have hQ : stateQ = diagonal fun i => ((qv i : ℝ) : ℂ) := rfl
  set R : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => ((rv i : ℝ) : ℂ) with hR
  have hQ0 : 0 ≤ stateQ := hdiag_nonneg qv (fun i => by fin_cases i <;> simp [hqv] <;> norm_num)
  have hR0 : 0 ≤ R := hdiag_nonneg rv (fun i => by fin_cases i <;> simp [hrv] <;> positivity)
  have hQR : CFC.sqrt stateQ = R := by
    rw [CFC.sqrt_eq_iff stateQ R hQ0 hR0, hR, hQ, diagonal_mul_diagonal]
    congr 1
    ext i
    have h17' : (Real.sqrt 17 : ℝ) ≠ 0 := by positivity
    fin_cases i <;> simp [hrv, hqv] <;> push_cast <;> field_simp <;> rw [h17C] <;> norm_num
  set sv : Fin 2 → ℝ := ![2 / s, 1 / s] with hsv
  set S : Matrix (Fin 2) (Fin 2) ℂ := diagonal fun i => ((sv i : ℝ) : ℂ) with hS
  have hS0 : 0 ≤ S := hdiag_nonneg sv (fun i => by fin_cases i <;> simp [hsv] <;> positivity)
  have hsC : ((s : ℝ) : ℂ) ^ 2 = ((Real.sqrt 17 : ℝ) : ℂ) := by exact_mod_cast hs2
  have hSmat : S = !![((2 / s : ℝ) : ℂ), 0; 0, ((1 / s : ℝ) : ℂ)] := by
    rw [hS]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hsv]
  have hRS : CFC.sqrt R = S := by
    rw [CFC.sqrt_eq_iff R S hR0 hS0, hS, hR, diagonal_mul_diagonal]
    congr 1
    ext i
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    fin_cases i <;> simp [hrv, hsv] <;> field_simp <;> rw [hsC] <;> ring
  have hQunit : IsUnit stateQ := by
    rw [hQ, Matrix.isUnit_diagonal]
    refine Pi.isUnit_iff.mpr fun i => ?_
    fin_cases i <;> simp [hqv]
  have hQpos : IsStrictlyPositive stateQ := hQunit.isStrictlyPositive hQ0
  have hQ4 : stateQ ^ (1 / 4 : ℝ) = S := by
    rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num,
      ← CFC.rpow_rpow stateQ _ _ (by norm_num) hQpos,
      ← CFC.sqrt_eq_rpow, ← CFC.sqrt_eq_rpow, hQR, hRS]
  have hQ8 : stateQ ^ (1 / 8 : ℝ) * stateQ ^ (1 / 8 : ℝ) = stateQ ^ (1 / 4 : ℝ) := by
    rw [← CFC.rpow_add hQunit]; norm_num
  have h2a : (1 / (4 * (2 : ℝ))) = 1 / 8 := by norm_num
  have h2b : (1 / (2 * (2 : ℝ))) = 1 / 4 := by norm_num
  have h2n : (2 : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
  have hPq : stateP ^ (1 / 4 : ℝ) = stateP := hproj_pow _ hP0 hPP _ (by norm_num)
  have hTe : stateT ^ (1 / 8 : ℝ) = stateT := hproj_pow _ hT0 hTT _ (by norm_num)
  have hQ8n : 0 ≤ stateQ ^ (1 / 8 : ℝ) := CFC.rpow_nonneg
  have hFPT : zFidelity 2 stateP stateT = 256 / 625 := by
    unfold zFidelity
    rw [h2a, h2b, hTe, hPq, h2n, CFC.rpow_natCast _ _ (conjugate_nonneg_of_nonneg hP0 hT0)]
    simp [stateP, stateT, sq, trace_fin_two, mul_apply, Fin.sum_univ_two]
    norm_num
  have hFPQ : zFidelity 2 stateP stateQ = 361 / (100 * Real.sqrt 17) := by
    unfold zFidelity
    rw [h2a, h2b, hPq, h2n, CFC.rpow_natCast _ _ (conjugate_nonneg_of_nonneg hP0 hQ8n), sq]
    have : stateQ ^ (1 / 8 : ℝ) * stateP * stateQ ^ (1 / 8 : ℝ) *
        (stateQ ^ (1 / 8 : ℝ) * stateP * stateQ ^ (1 / 8 : ℝ)) =
        stateQ ^ (1 / 8 : ℝ) * (stateP * (stateQ ^ (1 / 8 : ℝ) * stateQ ^ (1 / 8 : ℝ)) * stateP *
          stateQ ^ (1 / 8 : ℝ)) := by simp only [Matrix.mul_assoc]
    rw [this, trace_mul_comm, hQ8, hQ4, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      hQ8, hQ4, hSmat]
    have key : (stateP * (!![((2 / s : ℝ) : ℂ), 0; 0, ((1 / s : ℝ) : ℂ)] * (stateP *
        !![((2 / s : ℝ) : ℂ), 0; 0, ((1 / s : ℝ) : ℂ)]))).trace =
        ((361 / (100 * Real.sqrt 17) : ℝ) : ℂ) := by
      unfold stateP
      simp only [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const]
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      have h17' : ((Real.sqrt 17 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : Real.sqrt 17 ≠ 0)
      push_cast
      rw [← hsC]
      field_simp
      ring
    rw [key, Complex.ofReal_re]
  have hFQT : zFidelity 2 stateQ stateT = 361 / (100 * Real.sqrt 17) := by
    unfold zFidelity
    rw [h2a, h2b, hTe, hQ4, h2n, CFC.rpow_natCast _ _ (conjugate_nonneg_of_nonneg hS0 hT0), sq,
      hSmat]
    have key : (stateT * !![((2 / s : ℝ) : ℂ), 0; 0, ((1 / s : ℝ) : ℂ)] * stateT *
        (stateT * !![((2 / s : ℝ) : ℂ), 0; 0, ((1 / s : ℝ) : ℂ)] * stateT)).trace =
        ((361 / (100 * Real.sqrt 17) : ℝ) : ℂ) := by
      unfold stateT
      simp only [Matrix.mul_fin_two, Matrix.trace_fin_two, Matrix.of_apply, Matrix.cons_val',
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
        Matrix.cons_val_fin_one, Matrix.head_fin_const]
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      have h17' : ((Real.sqrt 17 : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : Real.sqrt 17 ≠ 0)
      push_cast
      rw [← hsC]
      field_simp
      ring
    rw [key, Complex.ofReal_re]
  have hstates : ∀ M ∈ [stateP, stateQ, stateT], M.PosSemidef ∧ M.trace = 1 := by
    intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl | rfl
    · exact ⟨Matrix.nonneg_iff_posSemidef.mp hP0, by simp [stateP, trace_fin_two]; norm_num⟩
    · refine ⟨Matrix.nonneg_iff_posSemidef.mp hQ0, ?_⟩
      rw [hQ]; simp [hqv, trace_fin_two]; norm_num
    · exact ⟨Matrix.nonneg_iff_posSemidef.mp hT0, by simp [stateT, trace_fin_two]; norm_num⟩
  have hPs := hstates stateP (by simp)
  have hQs := hstates stateQ (by simp)
  have hTs := hstates stateT (by simp)
  have htri := h 2 (Or.inr (by norm_num)) 2 stateP stateQ stateT hPs.1 hPs.2 hQs.1 hQs.2 hTs.1 hTs.2
  unfold zDistance at htri
  rw [hFPT, hFPQ, hFQT] at htri
  have h17 : Real.sqrt 17 < 9025 / 2131 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have h17pos : 0 < Real.sqrt 17 := by positivity
  set a : ℝ := 361 / (100 * Real.sqrt 17) with ha
  have ha1 : 2131 / 2500 < a := by
    rw [ha, lt_div_iff₀ (by positivity)]; nlinarith
  have ha2 : a < 1 := by
    rw [ha, div_lt_one (by positivity)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 17 by norm_num), Real.sqrt_nonneg 17]
  have hsum : Real.sqrt (2 * (1 - a)) + Real.sqrt (2 * (1 - a)) = Real.sqrt (8 * (1 - a)) := by
    rw [← two_mul, show (8 : ℝ) * (1 - a) = 2 ^ 2 * (2 * (1 - a)) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [hsum] at htri
  have hlt : Real.sqrt (8 * (1 - a)) < Real.sqrt (2 * (1 - 256 / 625)) :=
    Real.sqrt_lt_sqrt (by linarith) (by linarith)
  linarith

end D5.S3.Quantum.Information.ZFidelityDistanceRefutation
