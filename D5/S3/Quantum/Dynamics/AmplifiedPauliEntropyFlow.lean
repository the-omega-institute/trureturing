/- GID: D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Pauli pinching flow and finite-memory entropy dissipation. -/

import D5.S3.Quantum.Divergence.TraceEntropyCalculus
import D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-! proof_shape: content; admission_basis: escape-witness.
The actual amplified pinchings compose to the partial-trace equilibrium map.
The raw all-real curve has derivative minus its actual generator. Positivity
at positive times and the trace-entropy chain rule yield entropy dissipation
for arbitrary joint states whose actual memory marginal is faithful.
These are general analytic and matrix identities, not bounded certificates.
The all-state two-axis inequality and singular-memory limit remain separate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix Filter
open scoped BigOperators Topology Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open D5.S3.Quantum.Foundation.FiniteStateChannel
open D5.S3.Quantum.Foundation.FiniteKrausChannel
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (spin)
open D5.S3.Quantum.Information.TraceNormDiscordMutualCorrelationBound
  (spin_hermitian spin_square)
open D5.S3.Quantum.Information.MixedUnitaryPinchingCommutation (spin_triple)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidCHSH (vlen_sq sigma_succ)
open D5.S3.Quantum.Entanglement.SteeringEllipsoidFullyEntangledFraction (pauli)
open D5.S3.QuantumChannels.ChannelTimeReversalNoGo.Qubit (pauli_expansion)
open D5.S3.Quantum.Divergence.TraceEntropyCalculus
open D5.S3.Quantum.Divergence.SupportAwareRelativeEntropy

namespace D5.S3.Quantum.Dynamics.AmplifiedPauliEntropyFlow

variable {R : Type*} [Fintype R] [DecidableEq R]

/-- The actual spin unitary acting on the qubit and trivially on the memory. -/
def spinLift (v : Fin 3 → ℝ) : Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
  spin v ⊗ₖ (1 : Matrix R R ℂ)

/-- The Kraus pinching `(id + Ad(spin(v) tensor I))/2`, on all matrices. -/
def pinching (v : Fin 3 → ℝ) :
    Matrix (Fin 2 × R) (Fin 2 × R) ℂ →ₗ[ℝ] Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
  (1 / 2 : ℝ) • (LinearMap.id +
    (LinearMap.mulLeftRight ℂ (spinLift v, (spinLift v)ᴴ)).restrictScalars ℝ)

/-- The fixed-point expectation formed from the actual memory partial trace. -/
def equilibrium :
    Matrix (Fin 2 × R) (Fin 2 × R) ℂ →ₗ[ℝ] Matrix (Fin 2 × R) (Fin 2 × R) ℂ where
  toFun X := (1 / 2 : ℂ) • ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ partialTraceLeft X)
  map_add' X Y := by
    simp [partialTraceLeft_add, Matrix.kronecker_add, smul_add]
  map_smul' c X := by
    ext p q
    simp [partialTraceLeft, Finset.mul_sum, Complex.real_smul, Matrix.kronecker_apply,
      mul_left_comm, mul_assoc, mul_comm]

private lemma lift_hermitian (v : Fin 3 → ℝ) :
    (spinLift (R := R) v)ᴴ = spinLift v := by
  simp [spinLift, Matrix.conjTranspose_kronecker, (spin_hermitian v).eq]

private lemma lift_square (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) :
    spinLift (R := R) v * spinLift v = 1 := by
  have h := spin_square v
  rw [vlen_sq, hv, one_smul] at h
  simp only [spinLift, ← Matrix.mul_kronecker_mul, h, Matrix.one_mul,
    Matrix.one_kronecker_one]

private def qubitPinching (v : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ →ₗ[ℂ] Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (LinearMap.id + LinearMap.mulLeftRight ℂ (spin v, spin v))

private lemma qubitPinching_one (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) :
    qubitPinching v 1 = 1 := by
  have h := spin_square v
  rw [vlen_sq, hv, one_smul] at h
  simp [qubitPinching, h, ← add_smul]

private lemma qubitPinching_spin (v w : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) :
    qubitPinching v (spin w) = ((v ⬝ᵥ w : ℝ) : ℂ) • spin v := by
  simp only [qubitPinching, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.mulLeftRight_apply, spin_triple, hv,
    Complex.ofReal_one, one_smul]
  module

private lemma qubitPinching_comp (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    qubitPinching a (qubitPinching b X) = (X.trace / 2) • 1 := by
  let f := (qubitPinching a).comp (qubitPinching b)
  have h1 : f 1 = 1 := by
    simp only [f, LinearMap.comp_apply, qubitPinching_one a ha, qubitPinching_one b hb]
  have hs (v : Fin 3 → ℝ) : f (spin v) = 0 := by
    simp [f, LinearMap.comp_apply, qubitPinching_spin b v hb, map_smul,
      qubitPinching_spin a b ha, hab]
  have hp (j : Fin 3) : f (pauli j) = 0 := by
    simpa [spin, sigma_succ] using hs (Pi.single j 1)
  change f X = _
  conv_lhs => rw [pauli_expansion X]
  simp only [map_add, map_smul, map_sum, h1, hp, smul_zero, Finset.sum_const_zero, add_zero]

private lemma pinching_block (v : Fin 3 → ℝ)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (r s : R) (p q : Fin 2) :
    pinching v X (p, r) (q, s) =
      qubitPinching v (fun j k => X (j, r) (k, s)) p q := by
  simp [pinching, qubitPinching, spinLift, lift_hermitian, (spin_hermitian v).eq,
    Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Matrix.kronecker_apply, Complex.real_smul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]

/-- Orthogonal Pauli pinchings erase exactly the qubit, for every matrix and memory. -/
theorem pinching_comp_eq_equilibrium (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    pinching a (pinching b X) = equilibrium X ∧
      pinching b (pinching a X) = equilibrium X := by
  have hcomp (u v : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1)
      (huv : u ⬝ᵥ v = 0) : pinching u (pinching v X) = equilibrium X := by
    ext ⟨p, r⟩ ⟨q, s⟩
    rw [pinching_block]
    have hh : (fun j k => pinching v X (j, r) (k, s)) =
        qubitPinching v (fun j k => X (j, r) (k, s)) := by
      ext j k
      exact pinching_block v X r s j k
    rw [hh, qubitPinching_comp u v hu hv huv]
    simp only [equilibrium, LinearMap.coe_mk, AddHom.coe_mk, Matrix.smul_apply,
      Matrix.kronecker_apply, partialTraceLeft, Matrix.trace, Matrix.diag_apply,
      smul_eq_mul]
    ring
  exact ⟨hcomp a b ha hb hab, hcomp b a hb ha (by rwa [dotProduct_comm])⟩

private lemma pinching_idempotent (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    pinching v (pinching v X) = pinching v X := by
  have hU := lift_square (R := R) v hv
  simp only [pinching, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearMap.mulLeftRight_apply, lift_hermitian,
    smul_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hUX : spinLift v * (spinLift v * X * spinLift v) * spinLift v = X := by
    calc
      _ = (spinLift v * spinLift v) * X * (spinLift v * spinLift v) := by noncomm_ring
      _ = X := by rw [hU, one_mul, mul_one]
  rw [hUX]
  module

private lemma pinching_equilibrium (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    pinching v (equilibrium X) = equilibrium X := by
  have h := spin_square v
  rw [vlen_sq, hv, one_smul] at h
  simp only [pinching, equilibrium, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.restrictScalars_apply, LinearMap.mulLeftRight_apply, lift_hermitian,
    spinLift, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
    one_mul, mul_one, h]
  simp only [← add_smul, smul_smul]
  norm_num

private lemma qubitPinching_trace (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : (qubitPinching v X).trace = X.trace := by
  have h := spin_square v
  rw [vlen_sq, hv, one_smul] at h
  simp only [qubitPinching, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.id_apply, LinearMap.mulLeftRight_apply, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_mul_cycle, h, Matrix.one_mul, smul_eq_mul]
  ring

/-- Pinching preserves the actual memory marginal, on every complex matrix. -/
theorem partialTraceLeft_pinching (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    partialTraceLeft (pinching v X) = partialTraceLeft X := by
  ext r s
  change (∑ p : Fin 2, pinching v X (p, r) (p, s)) = _
  simp_rw [pinching_block]
  exact qubitPinching_trace v hv (fun p q => X (p, r) (q, s))

private lemma equilibrium_marginal (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    partialTraceLeft (equilibrium X) = partialTraceLeft X := by
  ext r s
  simp [equilibrium, partialTraceLeft, Fin.sum_univ_two]
  ring

private lemma pinching_trace (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) : (pinching v X).trace = X.trace := by
  rw [← trace_partialTraceLeft, partialTraceLeft_pinching v hv, trace_partialTraceLeft]

private lemma equilibrium_trace (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    (equilibrium X).trace = X.trace := by
  rw [← trace_partialTraceLeft, equilibrium_marginal, trace_partialTraceLeft]

private lemma pinching_posSemidef (v : Fin 3 → ℝ)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef) :
    (pinching v X).PosSemidef := by
  exact (hX.add (hX.mul_mul_conjTranspose_same (spinLift v))).smul (by norm_num :
    (0 : ℝ) ≤ 1 / 2)

private lemma equilibrium_posSemidef {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ}
    (hX : X.PosSemidef) : (equilibrium X).PosSemidef :=
  (Matrix.PosSemidef.one.kronecker (partialTraceLeft_posSemidef hX)).smul
    (by norm_num : (0 : ℂ) ≤ 1 / 2)

/-- The reference is faithful when the actual memory marginal is faithful. -/
theorem equilibrium_posDef (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ)
    (hR : (partialTraceLeft X).PosDef) : (equilibrium X).PosDef :=
  (Matrix.PosDef.one.kronecker hR).smul (by norm_num : (0 : ℂ) < 1 / 2)

/-- The raw matrix curve is defined for every real time. Only nonnegative times
are certified as channels or states. -/
def flow (a b : Fin 3 → ℝ) (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (t : ℝ) :
    Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
  Real.exp (-t) ^ 2 • X +
    (Real.exp (-t) * (1 - Real.exp (-t))) • (pinching a X + pinching b X) +
    (1 - Real.exp (-t)) ^ 2 • equilibrium X

/-- The positive generator convention: the evolution equation is `X' = -L(X)`. -/
def generator (a b : Fin 3 → ℝ) (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
  (2 : ℝ) • X - pinching a X - pinching b X

/-- The actual flow preserves the input memory marginal at every real time. -/
theorem partialTraceLeft_flow (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (t : ℝ) :
    partialTraceLeft (flow a b X t) = partialTraceLeft X := by
  have hs (c : ℝ) (Y : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
      partialTraceLeft (c • Y) = c • partialTraceLeft Y := by
    ext r s
    simp [partialTraceLeft, Finset.smul_sum]
  simp only [flow, partialTraceLeft_add, hs, partialTraceLeft_pinching a ha,
    partialTraceLeft_pinching b hb, equilibrium_marginal]
  module

private lemma flow_trace (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (t : ℝ) :
    (flow a b X t).trace = X.trace := by
  rw [← trace_partialTraceLeft, partialTraceLeft_flow a b ha hb, trace_partialTraceLeft]

/-- A positive-time lower bound by the actual fixed memory reference. -/
theorem flow_lower_bound (a b : Fin 3 → ℝ)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) :
    (1 - Real.exp (-t)) ^ 2 • equilibrium X ≤ flow a b X t := by
  have hs : 0 ≤ 1 - Real.exp (-t) := sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))
  have hp := ((pinching_posSemidef a hX).add (pinching_posSemidef b hX)).smul
    (mul_nonneg (Real.exp_pos _).le hs)
  have hq := hX.smul (sq_nonneg (Real.exp (-t)))
  rw [Matrix.le_iff]
  simpa only [flow, add_sub_cancel_right] using hq.add hp

private lemma flow_posSemidef (a b : Fin 3 → ℝ)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef)
    (t : ℝ) (ht : 0 ≤ t) : (flow a b X t).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp
    (((equilibrium_posSemidef hX).smul (sq_nonneg (1 - Real.exp (-t)))).nonneg.trans
      (flow_lower_bound a b hX t ht))

/-- A singular joint state becomes faithful at positive times if its memory is faithful. -/
theorem flow_posDef (a b : Fin 3 → ℝ)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef)
    (hR : (partialTraceLeft X).PosDef) (t : ℝ) (ht : 0 < t) :
    (flow a b X t).PosDef := by
  have hs : 0 < 1 - Real.exp (-t) := sub_pos.mpr
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht))
  exact ((equilibrium_posDef X hR).isStrictlyPositive.smul (sq_pos_of_pos hs) |>.of_le
    (flow_lower_bound a b hX t ht.le)).posDef

/-- The derivative of the all-real matrix curve is minus the actual generator. -/
theorem hasDerivAt_flow (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (t : ℝ) :
    HasDerivAt (flow a b X) (-generator a b (flow a b X t)) t := by
  have hs : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t := by
    simpa using (hasDerivAt_id t).neg.exp
  have hd := (((hs.pow 2).smul_const X).add
    ((hs.mul (hs.const_sub 1)).smul_const (pinching a X + pinching b X))).add
      (((hs.const_sub 1).pow 2).smul_const (equilibrium X))
  convert hd using 1
  simp only [generator, flow, map_add, map_smul, pinching_idempotent a ha,
    pinching_idempotent b hb, (pinching_comp_eq_equilibrium a b ha hb hab X).1,
    (pinching_comp_eq_equilibrium a b ha hb hab X).2, pinching_equilibrium a ha,
    pinching_equilibrium b hb]
  module

end D5.S3.Quantum.Dynamics.AmplifiedPauliEntropyFlow
