/- GID: D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.claim; result=D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.result; claim=D5/S3/Quantum/Dynamics/PathDoubleBlowUpPGSTRefutation.claim
   digest: Vertex-four twins in the double blow-up of P_11 admit PGST. -/

/-
proof_shape: result: content
escape_witness: BiquadraticKroneckerTimes.biquadratic_independent lies on the live derivation
  of pgst_twins_vertex_four and hence of result.
admission_basis: open-problem-resolution (#14649; Refuted)
Direct frozen dependencies:
  D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity.exp_mulVec_of_eigenvector:
    declaration statement_id: sha256:4c9f2eff40b9ab9a5dd6bf3511ef67bd738e5144793aa9213135c3c33bf35942
  D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.sine_mode_eigenvector:
    declaration statement_id: sha256:2dc6b6016d0cbb1925b155d51e020cccd688c5c7e8be78c3221e4bac99132224
  D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.sineMode:
    declaration statement_id: sha256:a8129b01c1e40c391cc750c34027fd0d7e3ff5363d6e55a2e29663428a3f112d
  D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle:
    declaration statement_id: sha256:48c85a071c8f0fa940574f0087ed604ef3891ce2c887f707f2a53c1e03f367b8
  D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow.hamiltonianPropagator:
    declaration statement_id: sha256:cda9b54324a60c3d19d82ae43fd312bec7fd42bc7d2748ad663e34115d863ceb
Same-delivery dependencies: BiquadraticKroneckerTimes.biquadratic_independent,
  dense_circle_sequence.
Utility: the P_11, vertex-4 spectral certificate refutes claim through result.
Information-escape registration is paused under CLAUDE.md section 3.9.
proof_shape: blow_pow_succ: bind-only; consumer: exp_blow_entry.
proof_shape: exp_blow_entry: bind-only; consumer: twin_amplitude.
proof_shape: twin_amplitude: bind-only; consumer: pgst_twins_vertex_four.
proof_shape: path11_row: bind-only; consumers: path11_sine_eigenvector.
proof_shape: path11_sine_eigenvector: bind-only; consumers: path11_sine_evolution.
proof_shape: cosine_sum: bind-only; consumers: cosine_sum_value.
proof_shape: cosine_sum_value: bind-only; consumers: sine_resolution_at_four.
proof_shape: sine_product_sum: bind-only; consumers: sine_resolution_at_four.
proof_shape: sine_resolution_at_four: bind-only; consumers: sine_decomposition.
proof_shape: sine_decomposition: bind-only; consumers: sine_diagonal_expansion.
proof_shape: path11_sine_evolution: bind-only; consumers: sine_diagonal_expansion.
proof_shape: sine_diagonal_expansion: bind-only; consumers: spectral_weights.
proof_shape: sine_weights: bind-only; consumers: spectral_weights.
proof_shape: path11_cosine_pairs: bind-only; consumers: spectral_weights.
proof_shape: path11_positive_eigenvalues: bind-only; consumers: spectral_weights.
proof_shape: paired_exponentials: bind-only; consumers: spectral_weights.
proof_shape: spectral_weights: bind-only; consumers: pgst_twins_vertex_four.
proof_shape: sqrt_two_three_six_independent: content; consumers: frequency_character_independent.
proof_shape: frequency_character_independent: content; consumers: approximation_times.
proof_shape: approximation_times: content; consumers: pgst_twins_vertex_four.
proof_shape: pgst_twins_vertex_four: content; consumers: result.
-/

import D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
import Mathlib.Algebra.Group.Idempotent
import D5.S3.Fourier.BiquadraticKroneckerTimes
import D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
import D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace

set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Quantum.Dynamics.PathDoubleBlowUpPGSTRefutation
open Matrix Filter Real Complex
open scoped Topology BigOperators Matrix.Norms.L2Operator
open D5.S3.Quantum.Dynamics.ProjectionProbabilityFlow
open D5.S3.Quantum.Dynamics.EnergyEigenstateStationarity
open D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace
open D5.S3.Fourier.BiquadraticKroneckerTimes

section TwinAmplitude
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem blow_pow_succ (A : Matrix ι ι ℂ) (k : ℕ) :
    (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A) ^ (k + 1) = (2 : ℂ)^k • (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) (A^(k+1))) := by
  let J : Matrix (Fin 2) (Fin 2) ℂ := Matrix.of (fun _ _ => 1)
  let E : Matrix (Fin 2) (Fin 2) ℂ := (1/2 : ℂ) • J
  have hE : IsIdempotentElem E := by
    unfold IsIdempotentElem
    ext i j
    norm_num [E, J, Matrix.mul_apply, Fin.sum_univ_succ]
  have hJE : J = (2 : ℂ) • E := by
    dsimp [E]
    norm_num [smul_smul]
  have hJ : J^(k+1) = (2 : ℂ)^k • J := calc
    J^(k+1) = ((2 : ℂ) • E)^(k+1) := congrArg (fun M => M^(k+1)) hJE
    _ = (2 : ℂ)^(k+1) • E := by rw [smul_pow, hE.pow_succ_eq]
    _ = (2 : ℂ)^k • J := by
      dsimp [E]
      rw [smul_smul, pow_succ]
      congr 1
      ring
  let f : (Matrix (Fin 2) (Fin 2) ℂ × Matrix ι ι ℂ) →*
      Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ :=
    { toFun := fun X => Matrix.kronecker X.1 X.2
      map_one' := Matrix.one_kronecker_one
      map_mul' := fun X Y => Matrix.mul_kronecker_mul X.1 Y.1 X.2 Y.2 }
  have hp := map_pow f (J,A) (k+1)
  change Matrix.kronecker (J^(k+1)) (A^(k+1)) = (Matrix.kronecker J A)^(k+1) at hp
  change (Matrix.kronecker J A)^(k+1) = (2 : ℂ)^k • Matrix.kronecker J (A^(k+1))
  rw [← hp, hJ]
  exact Matrix.smul_kronecker _ _ _

private theorem exp_blow_entry (A : Matrix ι ι ℂ) (u : ι) :
    NormedSpace.exp ((Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)) (0,u) (1,u) =
      (NormedSpace.exp ((2 : ℂ) • A) u u - 1) / 2 := by
  let L : Matrix (Fin 2 × ι) (Fin 2 × ι) ℂ →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun M => M (0,u) (1,u)
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply (1,u)).comp (continuous_apply (0,u)) }
  let K : Matrix ι ι ℂ →L[ℂ] ℂ :=
    { toLinearMap :=
        { toFun := fun M => M u u
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      cont := (continuous_apply u).comp (continuous_apply u) }
  have hsB := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)))
  have hsA := K.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) ((2 : ℂ) • A))
  have hp (k : ℕ) :
      (((k.factorial : ℂ)⁻¹ • (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A) ^ k) (0,u) (1,u)) =
        (1 / 2 : ℂ) * (((k.factorial : ℂ)⁻¹ • ((2 : ℂ) • A)^k) u u) -
          (if k = 0 then (1 / 2 : ℂ) else 0) := by
    cases k with
    | zero => simp
    | succ k =>
      rw [blow_pow_succ, smul_pow]
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.kroneckerMap_apply, Matrix.of_apply, one_mul, Nat.succ_ne_zero,
        if_false, sub_zero, pow_succ]
      ring
  have hsum := (hsA.mul_left (1 / 2 : ℂ)).sub (hasSum_ite_eq 0 (1 / 2 : ℂ))
  change HasSum (fun k : ℕ => (((k.factorial : ℂ)⁻¹ • (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A) ^ k) (0,u) (1,u)))
    (NormedSpace.exp ((Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)) (0,u) (1,u)) at hsB
  simp_rw [hp] at hsB
  have he := hsB.unique hsum
  change NormedSpace.exp ((Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)) (0,u) (1,u) =
    (1 / 2 : ℂ) * NormedSpace.exp ((2 : ℂ) • A) u u - 1 / 2 at he
  linear_combination he

private theorem twin_amplitude (A : Matrix ι ι ℂ) (u : ι) (t : ℝ) :
    hamiltonianPropagator ((Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)) (-t) (0,u) (1,u) =
      (hamiltonianPropagator A (-(2*t)) u u - 1) / 2 := by
  unfold hamiltonianPropagator hamiltonianGenerator
  have h1 : (-t) • (-Complex.I • (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) A)) =
      (Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ))) ((Complex.I * (t : ℂ)) • A)) := by
    ext p q
    simp [Matrix.kroneckerMap_apply, Matrix.of_apply, Complex.real_smul]
    ring
  have h2 : (2 : ℂ) • ((Complex.I * (t : ℂ)) • A) =
      (-(2*t)) • (-Complex.I • A) := by
    ext p q
    simp [Complex.real_smul]
    ring
  rw [h1, exp_blow_entry, h2]

end TwinAmplitude

def pathAdj (n : ℕ) : Matrix (Fin n) (Fin n) ℂ := fun i j =>
  if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else 0

def doubleBlowUp (n : ℕ) : Matrix (Fin 2 × Fin n) (Fin 2 × Fin n) ℂ :=
  fun p q => pathAdj n p.2 q.2

def PGST {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (a b : ι) : Prop :=
  ∃ τ : ℕ → ℝ, Tendsto (fun k => ‖hamiltonianPropagator A (-(τ k)) a b‖)
    atTop (𝓝 1)

def claim : Prop := ∀ t r : ℕ, 2 ≤ t → r.Prime → Odd r →
  ∀ u : Fin (2^t*r - 1), 2^(t-1) ∣ u.val + 1 →
    ¬ PGST (doubleBlowUp (2^t*r - 1)) (0, u) (1, u)

private theorem path11_row (v : Fin 11 → ℂ) : pathAdj 11 *ᵥ v =
    ![v 1, v 0+v 2, v 1+v 3, v 2+v 4, v 3+v 5, v 4+v 6,
      v 5+v 7, v 6+v 8, v 7+v 9, v 8+v 10, v 9] := by
  ext i
  fin_cases i <;> simp [pathAdj, mulVec, dotProduct, Fin.sum_univ_succ]

private theorem path11_sine_eigenvector (k : ℕ) :
    pathAdj 11 *ᵥ (fun j : Fin 11 => (sineMode 11 k j : ℂ)) = (2 * (Real.cos (modeAngle 11 k) : ℂ)) • (fun j : Fin 11 => (sineMode 11 k j : ℂ)) := by
  rw [path11_row]
  ext i
  have h := D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.sine_mode_eigenvector 11 k i
  unfold D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.nearestNeighborAverage
    D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.sineMode
    D5.S3.QuantumBounds.ReferenceFrame.TopEigenspace.modeAngle at h
  fin_cases i <;> norm_num [sineMode, modeAngle] at h ⊢
  all_goals
    have hc := congrArg (fun x : ℝ => (x : ℂ)) h
    push_cast at hc
    linear_combination 2*hc

private theorem cosine_sum (m : ℕ) (hpos : 0 < m) (hmax : m < 24) :
    (∑ k ∈ Finset.range 11, Real.cos (m * modeAngle 11 (k+1))) =
      -Real.cos (m * Real.pi / 2)^2 := by
  have hsin : Real.sin (m * Real.pi / 24) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by
      have hm : (m : ℝ) < 24 := by exact_mod_cast hmax
      nlinarith [Real.pi_pos])).ne'
  have hs := Real.sin_mul_sum_cos 11 (m * Real.pi / 12) (m * Real.pi / 12)
  have harg : ∀ k : ℕ, m * modeAngle 11 (k+1) = m * Real.pi / 12 * k + m * Real.pi / 12 := by
    intro k; unfold modeAngle; push_cast; ring
  simp_rw [harg]
  have hmul : Real.sin (m * Real.pi / 2) * Real.cos (m * Real.pi / 2) = 0 := by
    have ht := Real.sin_two_mul (m * Real.pi / 2)
    rw [show 2*(m*Real.pi/2) = (m : ℝ)*Real.pi by ring, Real.sin_nat_mul_pi] at ht
    linarith
  have hright : Real.sin (11*(m*Real.pi/12)/2) *
      Real.cos (10*(m*Real.pi/12)/2+m*Real.pi/12) =
        -Real.sin (m*Real.pi/24)*Real.cos (m*Real.pi/2)^2 := by
    rw [show 10*(m*Real.pi/12)/2+m*Real.pi/12 = m*Real.pi/2 by ring,
      show 11*(m*Real.pi/12)/2 = m*Real.pi/2-m*Real.pi/24 by ring,
      Real.sin_sub]
    linear_combination Real.cos (m*Real.pi/24)*hmul
  norm_num only [Nat.cast_ofNat] at hs
  rw [show m*Real.pi/12/2 = m*Real.pi/24 by ring, hright] at hs
  exact (mul_left_cancel₀ hsin (by linear_combination hs))

private theorem cosine_sum_value (m : ℕ) (hpos : 0 < m) (hmax : m < 24) :
    (∑ k ∈ Finset.range 11, Real.cos (m * modeAngle 11 (k+1))) =
      -(1+(-1 : ℝ)^m)/2 := by
  rw [cosine_sum m hpos hmax]
  have ht := Real.cos_two_mul (m*Real.pi/2)
  rw [show 2*(m*Real.pi/2) = (m : ℝ)*Real.pi by ring, Real.cos_nat_mul_pi] at ht
  linarith

private theorem sine_product_sum (j : Fin 11) :
    (∑ k ∈ Finset.range 11, Real.sin (4*modeAngle 11 (k+1))*Real.sin ((j.val+1)*modeAngle 11 (k+1))) =
      ((∑ k ∈ Finset.range 11, Real.cos ((4-(j.val+1))*modeAngle 11 (k+1))) -
        (∑ k ∈ Finset.range 11, Real.cos ((4+(j.val+1))*modeAngle 11 (k+1)))) / 2 := by
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (4-((j.val : ℝ)+1))*modeAngle 11 (k+1) =
      4*modeAngle 11 (k+1)-((j.val : ℝ)+1)*modeAngle 11 (k+1) by ring,
    show (4+((j.val : ℝ)+1))*modeAngle 11 (k+1) =
      4*modeAngle 11 (k+1)+((j.val : ℝ)+1)*modeAngle 11 (k+1) by ring,
    Real.cos_sub, Real.cos_add]
  ring

private theorem sine_resolution_at_four (j : Fin 11) :
    (∑ k ∈ Finset.range 11, Real.sin (4*modeAngle 11 (k+1))*Real.sin ((j.val+1)*modeAngle 11 (k+1))) =
      if j = 3 then 6 else 0 := by
  have h := sine_product_sum j
  have hc (m : ℕ) (h1 : 0 < m) (h2 : m < 24) := cosine_sum_value m h1 h2
  have hz : (∑ k ∈ Finset.range 11, Real.cos (0*modeAngle 11 (k+1))) = 11 := by simp
  fin_cases j
  · norm_num at h ⊢
    have h1 := hc 3 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 5 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 6 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 1 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 7 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h2 := hc 8 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 1 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 9 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 2 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 10 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 3 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 11 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 4 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 12 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 5 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 13 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 6 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 14 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h
  · norm_num at h ⊢
    have h1 := hc 7 (by norm_num) (by norm_num)
    norm_num at h1
    rw [h1] at h
    have h2 := hc 15 (by norm_num) (by norm_num)
    norm_num at h2
    rw [h2] at h
    norm_num at h
    exact h

private theorem sine_decomposition : (Pi.single 3 1 : Fin 11 → ℂ) =
    (1/6 : ℂ) • ∑ k ∈ Finset.range 11,
      (Real.sin (4*modeAngle 11 (k+1)) : ℂ) • (fun j : Fin 11 => (sineMode 11 (k+1) j : ℂ)) := by
  ext j
  simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, sineMode]
  have h := sine_resolution_at_four j
  have hc := congrArg (fun x : ℝ => (x : ℂ)) h
  push_cast at hc
  by_cases hj : j = 3
  · simp [hj, Pi.single_apply] at hc ⊢
    linear_combination -(1/6 : ℂ)*hc
  · simp [hj, Ne.symm hj, Pi.single_apply] at hc ⊢
    try rw [hc] <;> ring

private theorem path11_sine_evolution (k : ℕ) (s : ℝ) :
    hamiltonianPropagator (pathAdj 11) (-s) *ᵥ (fun j : Fin 11 => (sineMode 11 k j : ℂ)) =
      Complex.exp (Complex.I * (s : ℂ) * (2*(Real.cos (modeAngle 11 k) : ℂ))) • (fun j : Fin 11 => (sineMode 11 k j : ℂ)) := by
  unfold hamiltonianPropagator hamiltonianGenerator
  apply exp_mulVec_of_eigenvector
  rw [smul_mulVec, smul_mulVec, path11_sine_eigenvector, ← Complex.coe_smul,
    smul_smul, smul_smul]
  congr 1
  push_cast
  ring

private theorem sine_diagonal_expansion (s : ℝ) :
    hamiltonianPropagator (pathAdj 11) (-s) 3 3 =
      (1/6 : ℂ) * ∑ k ∈ Finset.range 11,
        Complex.exp (Complex.I * (s : ℂ) * (2*(Real.cos (modeAngle 11 (k+1)) : ℂ))) *
          (Real.sin (4*modeAngle 11 (k+1)) : ℂ)^2 := by
  have h0 : hamiltonianPropagator (pathAdj 11) (-s) 3 3 =
      (hamiltonianPropagator (pathAdj 11) (-s) *ᵥ Pi.single 3 1) 3 := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [h0, sine_decomposition, mulVec_smul, Matrix.mulVec_sum]
  simp_rw [mulVec_smul, path11_sine_evolution]
  simp only [Pi.smul_apply, Finset.sum_apply, sineMode, Fin.val_ofNat, Nat.cast_ofNat]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  norm_num [smul_eq_mul]
  ring

private def pathWeights : Fin 11 → ℝ := ![3/4,3/4,0,3/4,3/4,0,3/4,3/4,0,3/4,3/4]
private theorem sine_weights (k : Fin 11) : Real.sin (4*modeAngle 11 (k.val+1))^2 = pathWeights k := by
  fin_cases k
  · have ha : 4*modeAngle 11 (1) = Real.pi/3+(0 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (2) = -Real.pi/3+(1 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (3) = 0+(1 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (4) = Real.pi/3+(1 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (5) = -Real.pi/3+(2 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (6) = 0+(2 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (7) = Real.pi/3+(2 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (8) = -Real.pi/3+(3 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (9) = 0+(3 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (10) = Real.pi/3+(3 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]
  · have ha : 4*modeAngle 11 (11) = -Real.pi/3+(4 : ℕ)*Real.pi := by unfold modeAngle; push_cast; ring
    norm_num only [Fin.val_mk] at ⊢
    rw [ha, Real.sin_add_nat_mul_pi]
    norm_num [pathWeights, neg_div, Real.sin_neg, Real.sq_sin_pi_div_three, Real.sq_sqrt, div_pow]

private theorem path11_cosine_pairs (k : ℕ) (hk : k ≤ 12) :
    Real.cos (modeAngle 11 (12-k)) = -Real.cos (modeAngle 11 k) := by
  rw [show modeAngle 11 (12-k) = Real.pi-modeAngle 11 k by unfold modeAngle; rw [Nat.cast_sub hk]; push_cast; ring,
      Real.cos_pi_sub]

private theorem path11_positive_eigenvalues :
    2*Real.cos (modeAngle 11 1) = (Real.sqrt 6+Real.sqrt 2)/2 ∧
    2*Real.cos (modeAngle 11 2) = Real.sqrt 3 ∧
    2*Real.cos (modeAngle 11 4) = 1 ∧
    2*Real.cos (modeAngle 11 5) = (Real.sqrt 6-Real.sqrt 2)/2 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2*Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  have h1 : modeAngle 11 1 = Real.pi/4-Real.pi/6 := by unfold modeAngle; push_cast; ring
  have h2 : modeAngle 11 2 = Real.pi/6 := by unfold modeAngle; push_cast; ring
  have h4 : modeAngle 11 4 = Real.pi/3 := by unfold modeAngle; push_cast; ring
  have h5 : modeAngle 11 5 = Real.pi/4+Real.pi/6 := by unfold modeAngle; push_cast; ring
  rw [h1,h2,h4,h5,Real.cos_sub,Real.cos_add,Real.cos_pi_div_four,
    Real.sin_pi_div_four,Real.cos_pi_div_six,Real.sin_pi_div_six,Real.cos_pi_div_three,h6]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

private theorem paired_exponentials (s x : ℝ) :
    Complex.exp (Complex.I*(s : ℂ)*(x : ℂ)) +
      Complex.exp (Complex.I*(s : ℂ)*((-x : ℝ) : ℂ)) =
        2*(Real.cos (s*x) : ℂ) := by
  rw [show Complex.I*(s : ℂ)*(x : ℂ) = ((s*x : ℝ) : ℂ)*Complex.I by push_cast; ring,
    show Complex.I*(s : ℂ)*((-x : ℝ) : ℂ) = ((-(s*x) : ℝ) : ℂ)*Complex.I by push_cast; ring,
    Complex.exp_ofReal_mul_I,Complex.exp_ofReal_mul_I,Real.cos_neg,Real.sin_neg]
  push_cast
  ring

private theorem spectral_weights (s : ℝ) :
    hamiltonianPropagator (pathAdj 11) (-s) 3 3 =
      ((1/4 : ℝ)*(Real.cos (s*((Real.sqrt 6+Real.sqrt 2)/2)) +
        Real.cos (s*Real.sqrt 3) + Real.cos s +
        Real.cos (s*((Real.sqrt 6-Real.sqrt 2)/2))) : ℂ) := by
  have h := sine_diagonal_expansion s
  have hw0 : (Real.sin (4*modeAngle 11 1) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (0 : Fin 11)
    change Real.sin (4*modeAngle 11 1)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw1 : (Real.sin (4*modeAngle 11 2) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (1 : Fin 11)
    change Real.sin (4*modeAngle 11 2)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw2 : (Real.sin (4*modeAngle 11 3) : ℂ)^2 = (0 : ℂ) := by
    have ht := sine_weights (2 : Fin 11)
    change Real.sin (4*modeAngle 11 3)^2 = (0 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw3 : (Real.sin (4*modeAngle 11 4) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (3 : Fin 11)
    change Real.sin (4*modeAngle 11 4)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw4 : (Real.sin (4*modeAngle 11 5) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (4 : Fin 11)
    change Real.sin (4*modeAngle 11 5)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw5 : (Real.sin (4*modeAngle 11 6) : ℂ)^2 = (0 : ℂ) := by
    have ht := sine_weights (5 : Fin 11)
    change Real.sin (4*modeAngle 11 6)^2 = (0 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw6 : (Real.sin (4*modeAngle 11 7) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (6 : Fin 11)
    change Real.sin (4*modeAngle 11 7)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw7 : (Real.sin (4*modeAngle 11 8) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (7 : Fin 11)
    change Real.sin (4*modeAngle 11 8)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw8 : (Real.sin (4*modeAngle 11 9) : ℂ)^2 = (0 : ℂ) := by
    have ht := sine_weights (8 : Fin 11)
    change Real.sin (4*modeAngle 11 9)^2 = (0 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw9 : (Real.sin (4*modeAngle 11 10) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (9 : Fin 11)
    change Real.sin (4*modeAngle 11 10)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  have hw10 : (Real.sin (4*modeAngle 11 11) : ℂ)^2 = (3/4 : ℂ) := by
    have ht := sine_weights (10 : Fin 11)
    change Real.sin (4*modeAngle 11 11)^2 = (3/4 : ℝ) at ht
    simpa only [Complex.ofReal_pow,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_zero]
      using congrArg (fun x : ℝ => (x : ℂ)) ht
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.reduceAdd] at h
  rw [hw0,hw1,hw2,hw3,hw4,hw5,hw6,hw7,hw8,hw9,hw10] at h
  obtain ⟨e1,e2,e4,e5⟩ := path11_positive_eigenvalues
  have c1 : 2*(Real.cos (modeAngle 11 1) : ℂ) = (((Real.sqrt 6+Real.sqrt 2)/2 : ℝ) : ℂ) := by exact_mod_cast e1
  have c2 : 2*(Real.cos (modeAngle 11 2) : ℂ) = (Real.sqrt 3 : ℂ) := by exact_mod_cast e2
  have c4 : 2*(Real.cos (modeAngle 11 4) : ℂ) = 1 := by exact_mod_cast e4
  have c5 : 2*(Real.cos (modeAngle 11 5) : ℂ) = (((Real.sqrt 6-Real.sqrt 2)/2 : ℝ) : ℂ) := by exact_mod_cast e5
  have c7 : 2*(Real.cos (modeAngle 11 7) : ℂ) = -(((Real.sqrt 6-Real.sqrt 2)/2 : ℝ) : ℂ) := by
    have hp := path11_cosine_pairs 5 (by norm_num)
    norm_num at hp
    rw [hp,Complex.ofReal_neg,mul_neg,c5]
  have c8 : 2*(Real.cos (modeAngle 11 8) : ℂ) = -1 := by
    have hp := path11_cosine_pairs 4 (by norm_num)
    norm_num at hp
    rw [hp,Complex.ofReal_neg,mul_neg,c4]
  have c10 : 2*(Real.cos (modeAngle 11 10) : ℂ) = -(Real.sqrt 3 : ℂ) := by
    have hp := path11_cosine_pairs 2 (by norm_num)
    norm_num at hp
    rw [hp,Complex.ofReal_neg,mul_neg,c2]
  have c11 : 2*(Real.cos (modeAngle 11 11) : ℂ) = -(((Real.sqrt 6+Real.sqrt 2)/2 : ℝ) : ℂ) := by
    have hp := path11_cosine_pairs 1 (by norm_num)
    norm_num at hp
    rw [hp,Complex.ofReal_neg,mul_neg,c1]
  rw [c1,c2,c4,c5,c7,c8,c10,c11] at h
  have p1 := paired_exponentials s ((Real.sqrt 6+Real.sqrt 2)/2)
  have p2 := paired_exponentials s (Real.sqrt 3)
  have p4 := paired_exponentials s 1
  have p5 := paired_exponentials s ((Real.sqrt 6-Real.sqrt 2)/2)
  push_cast at h p1 p2 p4 p5 ⊢
  simp only [mul_one] at h p4 ⊢
  linear_combination h + (1/8 : ℂ)*(p1+p2+p4+p5)

private theorem sqrt_two_three_six_independent (a b c d : ℚ)
    (h : (a : ℝ) + b*Real.sqrt 2 + c*Real.sqrt 3 + d*Real.sqrt 6 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h6 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [h6] at h
  apply biquadratic_independent 2 3 (Real.sqrt 2) (Real.sqrt 3)
    (by norm_num [Real.sq_sqrt]) (by norm_num [Real.sq_sqrt])
    irrational_sqrt_two (by norm_num [Rat.isSquare_ofNat_iff])
    (by norm_num [Rat.isSquare_ofNat_iff]) a b c d h

private def frequency : Fin 3 → ℝ :=
  ![(Real.sqrt 6+Real.sqrt 2)/2, Real.sqrt 3, (Real.sqrt 6-Real.sqrt 2)/2]

private theorem frequency_character_independent (k : Fin 3 → ℤ) (m : ℤ)
    (h : (∑ i, (k i : ℝ)*frequency i) = m) : ∀ i, k i = 0 := by
  let a : ℚ := -(m : ℚ)
  let b : ℚ := ((k 0-k 2 : ℤ) : ℚ)/2
  let c : ℚ := k 1
  let d : ℚ := ((k 0+k 2 : ℤ) : ℚ)/2
  have hlin : (a : ℝ) + (b : ℝ)*Real.sqrt 2 +
      (c : ℝ)*Real.sqrt 3 + (d : ℝ)*Real.sqrt 6 = 0 := by
    simp [Fin.sum_univ_succ, frequency] at h
    dsimp [a,b,c,d]
    push_cast
    linear_combination h
  obtain ⟨hm,h2,h3,h6⟩ := sqrt_two_three_six_independent a b c d hlin
  dsimp [b,c,d] at h2 h3 h6
  have hsum : k 0+k 2 = 0 := by exact_mod_cast (div_eq_zero_iff.mp h6).resolve_right (by norm_num)
  have hdiff : k 0-k 2 = 0 := by exact_mod_cast (div_eq_zero_iff.mp h2).resolve_right (by norm_num)
  have hmiddle : k 1 = 0 := by exact_mod_cast h3
  intro i
  fin_cases i
  · change k 0 = 0; omega
  · change k 1 = 0; exact hmiddle
  · change k 2 = 0; omega

private theorem approximation_times : ∃ m : ℕ → ℕ, ∀ i : Fin 3,
    Tendsto (fun k => Real.cos (2*(Real.pi/2+Real.pi*(m k))*frequency i)) atTop (𝓝 (-1)) := by
  let z : Fin 3 → Circle := fun i => Circle.exp (Real.pi*(1-frequency i))
  obtain ⟨m,hm⟩ := dense_circle_sequence frequency frequency_character_independent z
  refine ⟨m, ?_⟩
  intro i
  have hi := (continuous_apply i).tendsto z |>.comp hm
  have hexp : Tendsto (fun k => Circle.exp (2*(Real.pi/2+Real.pi*(m k))*frequency i))
      atTop (𝓝 (Circle.exp Real.pi)) := by
    have ht := (tendsto_const_nhds (x := Circle.exp (Real.pi*frequency i)) (f := atTop)).mul hi
    have heq : ∀ k : ℕ, Circle.exp (2*(Real.pi/2+Real.pi*(m k))*frequency i) =
        Circle.exp (Real.pi*frequency i)*Circle.exp (2*Real.pi*frequency i)^(m k) := by
      intro k
      rw [← Circle.exp_natCast_mul, ← Circle.exp_add]
      congr 1; ring
    have hz : Circle.exp (Real.pi*frequency i)*z i = Circle.exp Real.pi := by
      dsimp only [z]
      rw [← Circle.exp_add]
      congr 1; ring
    rw [hz] at ht
    simp_rw [heq]
    exact ht
  have ht := (Complex.continuous_re.comp continuous_subtype_val).tendsto _ |>.comp hexp
  have hre (t : ℝ) : (Circle.exp t : ℂ).re = Real.cos t := by
    rw [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  change Tendsto (fun k => (Circle.exp (2*(Real.pi/2+Real.pi*(m k))*frequency i) : ℂ).re)
    atTop (𝓝 ((Circle.exp Real.pi : ℂ).re)) at ht
  simpa only [hre, Real.cos_pi] using ht

private theorem pgst_twins_vertex_four : PGST (doubleBlowUp 11) (0,3) (1,3) := by
  obtain ⟨m,hm⟩ := approximation_times
  let τ : ℕ → ℝ := fun k => Real.pi/2+Real.pi*(m k)
  have h0 : Tendsto (fun k => Real.cos (2*τ k*((Real.sqrt 6+Real.sqrt 2)/2))) atTop (𝓝 (-1)) := by
    simpa [τ,frequency] using hm 0
  have h1 : Tendsto (fun k => Real.cos (2*τ k*Real.sqrt 3)) atTop (𝓝 (-1)) := by
    simpa [τ,frequency] using hm 1
  have h2 : Tendsto (fun k => Real.cos (2*τ k*((Real.sqrt 6-Real.sqrt 2)/2))) atTop (𝓝 (-1)) := by
    simpa [τ,frequency] using hm 2
  have hfixed : Tendsto (fun k => Real.cos (2*τ k)) atTop (𝓝 (-1)) := by
    have he : (fun k => Real.cos (2*τ k)) = (fun _ : ℕ => (-1 : ℝ)) := by
      funext k
      rw [show 2*τ k = (m k : ℝ)*(2*Real.pi)+Real.pi by dsimp [τ]; ring,
        Real.cos_nat_mul_two_pi_add_pi]
    rw [he]
    exact tendsto_const_nhds
  have hr : Tendsto (fun k => (1/4 : ℝ)*
      (Real.cos (2*τ k*((Real.sqrt 6+Real.sqrt 2)/2)) +
        Real.cos (2*τ k*Real.sqrt 3) + Real.cos (2*τ k) +
        Real.cos (2*τ k*((Real.sqrt 6-Real.sqrt 2)/2)))) atTop (𝓝 (-1)) := by
    convert (tendsto_const_nhds (x := (1/4 : ℝ))).mul (((h0.add h1).add hfixed).add h2) using 1 <;> norm_num
  have hc := Complex.continuous_ofReal.tendsto (-1) |>.comp hr
  have hdiag : Tendsto (fun k => hamiltonianPropagator (pathAdj 11) (-(2*τ k)) 3 3)
      atTop (𝓝 (-1 : ℂ)) := by
    simpa only [Function.comp_def, spectral_weights, Complex.ofReal_neg, Complex.ofReal_one,
      Complex.ofReal_mul, Complex.ofReal_add] using hc
  have hamp : Tendsto (fun k => hamiltonianPropagator (doubleBlowUp 11) (-τ k) (0,3) (1,3))
      atTop (𝓝 (-1 : ℂ)) := by
    have ht := (hdiag.sub (tendsto_const_nhds (x := (1 : ℂ)))).div_const (2 : ℂ)
    have he : ∀ k, hamiltonianPropagator (doubleBlowUp 11) (-τ k) (0,3) (1,3) =
        (hamiltonianPropagator (pathAdj 11) (-(2*τ k)) 3 3 - 1)/2 := by
      intro k
      have hB : doubleBlowUp 11 =
          Matrix.kroneckerMap (· * ·) (Matrix.of (fun _ _ : Fin 2 => (1 : ℂ)))
            (pathAdj 11) := by
        ext p q
        simp [doubleBlowUp, Matrix.kroneckerMap_apply]
      rw [hB]
      exact twin_amplitude (pathAdj 11) 3 (τ k)
    simp_rw [he]
    convert ht using 1 <;> norm_num
  exact ⟨τ, by simpa using hamp.norm⟩

/-- Conjecture 1 of Bhattacharjya–Monterde–Pal is refuted by t=2, r=3, vertex 4. -/
theorem result : ¬ claim := by
  intro h
  have hh := h 2 3 (by norm_num) (by norm_num) (by decide)
    (show Fin (2^2*3-1) from (3 : Fin 11)) (by norm_num)
  exact hh pgst_twins_vertex_four

end D5.S3.Quantum.Dynamics.PathDoubleBlowUpPGSTRefutation
