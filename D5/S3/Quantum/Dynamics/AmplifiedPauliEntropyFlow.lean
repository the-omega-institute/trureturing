/- GID: D5/S3/Quantum/Dynamics/AmplifiedPauliEntropyFlow
   generality: I
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
I-bearing scope warning: the qubit factor and its Pauli spin matrices are fixed.
The finite quantum memory and real unit axes are arbitrary within this model;
the results do not cover arbitrary algebras or conditional expectations.
These are analytic and matrix identities, not bounded certificates.
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
    ring

lemma lift_hermitian (v : Fin 3 → ℝ) :
    (spinLift (R := R) v)ᴴ = spinLift v := by
  simp [spinLift, Matrix.conjTranspose_kronecker, (spin_hermitian v).eq]

lemma lift_square (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1) :
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
  norm_num

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
  let Z : Matrix (Fin 2) (Fin 2) ℂ := fun j k => X (j, r) (k, s)
  change ((1 / 2 : ℝ) • (X + spinLift v * X * (spinLift v)ᴴ) :
    Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (p, r) (q, s) =
    ((1 / 2 : ℂ) • (Z + spin v * Z * spin v) : Matrix (Fin 2) (Fin 2) ℂ) p q
  rw [lift_hermitian]
  change (1 / 2 : ℝ) • (X (p, r) (q, s) +
    (spinLift v * X * spinLift v : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (p, r) (q, s)) =
    (1 / 2 : ℂ) * (X (p, r) (q, s) +
      ∑ k : Fin 2, (∑ j : Fin 2, spin v p j * X (j, r) (k, s)) * spin v k q)
  simp [spinLift, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply,
    Complex.real_smul] <;> ring

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
    rw [hh]
    have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M p q)
      (qubitPinching_comp u v hu hv huv (fun j k => X (j, r) (k, s)))
    trans (((Matrix.trace (fun j k => X (j, r) (k, s)) / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℂ)) p q)
    · exact hc
    change (Matrix.trace (fun j k => X (j, r) (k, s)) / 2) * (1 : Matrix (Fin 2) (Fin 2) ℂ) p q =
      (1 / 2 : ℂ) * ((1 : Matrix (Fin 2) (Fin 2) ℂ) p q * partialTraceLeft X r s)
    have htrace : Matrix.trace (fun j k => X (j, r) (k, s)) = partialTraceLeft X r s := rfl
    rw [htrace]
    generalize partialTraceLeft X r s = z
    ring
  exact ⟨hcomp a b ha hb hab, hcomp b a hb ha (by rwa [dotProduct_comm])⟩

lemma pinching_idempotent (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
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

lemma pinching_equilibrium (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    pinching v (equilibrium X) = equilibrium X := by
  have h := spin_square v
  rw [vlen_sq, hv, one_smul] at h
  change (1 / 2 : ℝ) • (equilibrium X +
    spinLift v * equilibrium X * (spinLift v)ᴴ) = equilibrium X
  rw [lift_hermitian]
  have he : spinLift v * equilibrium X * spinLift v = equilibrium X := by
    simp only [equilibrium, LinearMap.coe_mk, AddHom.coe_mk, spinLift,
      Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_kronecker_mul,
      one_mul, mul_one, h]
  rw [he]
  module

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

lemma pinching_trace (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) : (pinching v X).trace = X.trace := by
  rw [← trace_partialTraceLeft, partialTraceLeft_pinching v hv, trace_partialTraceLeft]

private lemma equilibrium_trace (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    (equilibrium X).trace = X.trace := by
  rw [← trace_partialTraceLeft, equilibrium_marginal, trace_partialTraceLeft]

lemma pinching_posSemidef (v : Fin 3 → ℝ)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef) :
    (pinching v X).PosSemidef := by
  exact (hX.add (hX.mul_mul_conjTranspose_same (spinLift v))).smul (by norm_num :
    (0 : ℝ) ≤ 1 / 2)

lemma equilibrium_posSemidef {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ}
    (hX : X.PosSemidef) : (equilibrium X).PosSemidef :=
  (Matrix.PosSemidef.one.kronecker (partialTraceLeft_posSemidef hX)).smul
    (Complex.nonneg_iff.mpr ⟨by norm_num, by norm_num⟩ : (0 : ℂ) ≤ 1 / 2)

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
    (mul_nonneg (Real.exp_pos (-t)).le hs)
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
  apply hd.congr_deriv
  simp only [generator, flow, map_add, map_smul, pinching_idempotent a ha,
    pinching_idempotent b hb, (pinching_comp_eq_equilibrium a b ha hb hab X).1,
    (pinching_comp_eq_equilibrium a b ha hb hab X).2, pinching_equilibrium a ha,
    pinching_equilibrium b hb]
  module

private lemma generator_trace (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    (generator a b X).trace = 0 := by
  simp only [generator, Matrix.trace_sub, Matrix.trace_smul,
    pinching_trace a ha, pinching_trace b hb]
  module

lemma pinching_log_pairing (v : Fin 3 → ℝ) (hv : v ⬝ᵥ v = 1)
    (X Y : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    (pinching v Y * cfc Real.log (equilibrium X)).trace =
      (Y * cfc Real.log (equilibrium X)).trace := by
  have hc : Commute (equilibrium X) (spinLift v) := by
    change equilibrium X * spinLift v = spinLift v * equilibrium X
    simp [equilibrium, spinLift, Matrix.smul_mul, Matrix.mul_smul,
      ← Matrix.mul_kronecker_mul]
  have hlog := (hc.cfc_real Real.log).eq
  have hU := lift_square (R := R) v hv
  let U : Matrix (Fin 2 × R) (Fin 2 × R) ℂ := spinLift v
  let H : Matrix (Fin 2 × R) (Fin 2 × R) ℂ := cfc Real.log (equilibrium X)
  have hconj : (spinLift v * Y * spinLift v * cfc Real.log (equilibrium X)).trace =
      (Y * cfc Real.log (equilibrium X)).trace := by
    change (U * Y * U * H).trace = (Y * H).trace
    have hh : H * U = U * H := hlog
    have hu : U * U = 1 := hU
    calc
      (U * Y * U * H).trace = (Y * U * H * U).trace := by
        simpa only [Matrix.mul_assoc] using (Matrix.trace_mul_comm U (Y * U * H))
      _ = (Y * (U * U) * H).trace := by
        rw [Matrix.mul_assoc (Y * U) H U, hh]
        congr 1
        noncomm_ring
      _ = _ := by rw [hu, mul_one]
  simp only [pinching, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    LinearMap.restrictScalars_apply, LinearMap.mulLeftRight_apply, lift_hermitian,
    smul_mul_assoc, Matrix.add_mul, Matrix.trace_smul, Matrix.trace_add, hconj]
  module

/-- The fixed memory reference has zero pairing with the actual generator. -/
theorem generator_log_equilibrium_pairing (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1)
    (X Y : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
    (generator a b Y * cfc Real.log (equilibrium X)).trace = 0 := by
  simp only [generator, Matrix.sub_mul, smul_mul_assoc, Matrix.trace_sub,
    Matrix.trace_smul, pinching_log_pairing a ha, pinching_log_pairing b hb]
  module

/-- The raw relative entropy observable against the actual input memory reference. -/
def relativeEntropyCurve (a b : Fin 3 → ℝ)
    (X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) (t : ℝ) : ℝ :=
  (flow a b X t * (cfc Real.log (flow a b X t) - cfc Real.log (equilibrium X))).trace.re

private lemma relativeEntropyCurve_derivative (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    {X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ} (hX : X.PosSemidef)
    (hR : (partialTraceLeft X).PosDef) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (relativeEntropyCurve a b X)
      (-(generator a b (flow a b X t) *
        (cfc Real.log (flow a b X t) - cfc Real.log (equilibrium X))).trace.re) t ∧
    HasDerivAt (relativeEntropyCurve a b X)
      (-(generator a b (flow a b X t) * cfc Real.log (flow a b X t)).trace.re) t := by
  have hflow := hasDerivAt_flow a b ha hb hab X t
  have hherm : ∀ᶠ u in 𝓝 t, (flow a b X u).IsHermitian := by
    filter_upwards [eventually_ge_nhds ht] with u hu
    exact (flow_posSemidef a b hX u hu).isHermitian
  have hent := hasDerivAt_trace_mul_log (flow a b X)
    (-generator a b (flow a b X t)) t hflow hherm (flow_posDef a b hX hR t ht)
  let T : Matrix (Fin 2 × R) (Fin 2 × R) ℂ →L[ℝ] ℝ :=
    Complex.reCLM.comp (Matrix.traceLinearMap (Fin 2 × R) ℝ ℂ).toContinuousLinearMap
  have hfixed := T.hasFDerivAt.comp_hasDerivAt t
    (hflow.mul_const (cfc Real.log (equilibrium X)))
  have hraw := hent.sub hfixed
  change HasDerivAt (fun u => (flow a b X u * cfc Real.log (flow a b X u)).trace.re -
    T (flow a b X u * cfc Real.log (equilibrium X))) _ t at hraw
  have hfunc : (fun u => (flow a b X u * cfc Real.log (flow a b X u)).trace.re -
      T (flow a b X u * cfc Real.log (equilibrium X))) = relativeEntropyCurve a b X := by
    funext u
    simp only [relativeEntropyCurve, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]
    rfl
  rw [hfunc] at hraw
  have htr := congrArg Complex.re (generator_trace a b ha hb (flow a b X t))
  have hpair := congrArg Complex.re
    (generator_log_equilibrium_pairing a b ha hb X (flow a b X t))
  simp only [Complex.zero_re] at htr hpair
  have hfirst : HasDerivAt (relativeEntropyCurve a b X)
      (-(generator a b (flow a b X t) *
        (cfc Real.log (flow a b X t) - cfc Real.log (equilibrium X))).trace.re) t := by
    apply hraw.congr_deriv
    change (-generator a b (flow a b X t) * (cfc Real.log (flow a b X t) + 1)).trace.re -
      (-generator a b (flow a b X t) * cfc Real.log (equilibrium X)).trace.re = _
    simp only [Matrix.neg_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one,
      Matrix.trace_neg, Matrix.trace_add, Matrix.trace_sub,
      Complex.neg_re, Complex.add_re, Complex.sub_re] at htr ⊢
    linarith
  refine ⟨hfirst, hfirst.congr_deriv ?_⟩
  simp only [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, hpair, Complex.zero_re,
    sub_zero]

/-- At nonnegative times the actual matrix action is a canonical CPTP channel.
The four Kraus operators are weighted `I`, `Ua`, `Ub`, and `Ua Ub`. -/
theorem flow_quantumChannel (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ channel : QuantumChannel (Fin 2 × R) (Fin 2 × R),
      ∀ X : Matrix (Fin 2 × R) (Fin 2 × R) ℂ,
        CStarMatrix.ofMatrix.symm
          (channel.toCompletelyPositiveMap (CStarMatrix.ofMatrix X)) = flow a b X t := by
  let p := (1 + Real.exp (-t)) / 2
  let q := (1 - Real.exp (-t)) / 2
  let w : Fin 4 → ℝ := ![p ^ 2, p * q, p * q, q ^ 2]
  let U : Fin 4 → Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
    ![1, spinLift a, spinLift b, spinLift a * spinLift b]
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hq : 0 ≤ q := div_nonneg (sub_nonneg.mpr
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht))) (by norm_num)
  have hw0 (j : Fin 4) : 0 ≤ w j := by
    fin_cases j <;> simp [w, sq_nonneg, mul_nonneg hp hq]
  have hw : ∑ j, w j = 1 := by
    simp [w, Fin.sum_univ_four]
    dsimp [p, q]
    ring
  have hu (j : Fin 4) : (U j)ᴴ * U j = 1 := by
    fin_cases j
    · simp [U]
    · simpa [U, lift_hermitian] using lift_square (R := R) a ha
    · simpa [U, lift_hermitian] using lift_square (R := R) b hb
    · change (spinLift (R := R) a * spinLift b)ᴴ * (spinLift a * spinLift b) = 1
      rw [Matrix.conjTranspose_mul, lift_hermitian, lift_hermitian]
      calc
        (spinLift (R := R) b * spinLift a) * (spinLift a * spinLift b) =
            spinLift b * (spinLift a * spinLift a) * spinLift b := by noncomm_ring
        _ = 1 := by rw [lift_square a ha, mul_one, lift_square b hb]
  let K : Fin 4 → Matrix (Fin 2 × R) (Fin 2 × R) ℂ :=
    fun j => (Real.sqrt (w j) : ℂ) • U j
  have hsqrt (j : Fin 4) :
      (Real.sqrt (w j) : ℂ) * (Real.sqrt (w j) : ℂ) = (w j : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hw0 j)]
  have hnorm (j : Fin 4) : (K j)ᴴ * K j = (w j : ℂ) • 1 := by
    simp only [K, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqrt, hu]
  have hK : ∑ j, (K j)ᴴ * K j = 1 := by
    simp only [hnorm, ← Finset.sum_smul, ← Complex.ofReal_sum, hw,
      Complex.ofReal_one, one_smul]
  obtain ⟨channel, hc⟩ := finite_kraus_quantum_channel K hK
  refine ⟨channel, fun X => (hc X).trans ?_⟩
  have hact (j : Fin 4) : K j * X * (K j)ᴴ = (w j : ℂ) • (U j * X * (U j)ᴴ) := by
    simp only [K, Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsqrt]
  simp only [hact]
  have hcast (r : ℝ) (Y : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) :
      (r : ℂ) • Y = r • Y := by
    ext j k
    simp [Complex.real_smul]
  simp only [Fin.sum_univ_four]
  change ((p ^ 2 : ℝ) : ℂ) • ((1 : Matrix (Fin 2 × R) (Fin 2 × R) ℂ) * X * 1ᴴ) +
    ((p * q : ℝ) : ℂ) • (spinLift a * X * (spinLift a)ᴴ) +
    ((p * q : ℝ) : ℂ) • (spinLift b * X * (spinLift b)ᴴ) +
    ((q ^ 2 : ℝ) : ℂ) • ((spinLift a * spinLift b) * X * (spinLift a * spinLift b)ᴴ) = _
  rw [flow, ← (pinching_comp_eq_equilibrium a b ha hb hab X).1]
  simp only [hcast, Matrix.conjTranspose_one, one_mul, mul_one,
    Matrix.conjTranspose_mul, lift_hermitian, pinching, LinearMap.smul_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearMap.restrictScalars_apply,
    LinearMap.mulLeftRight_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc]
  dsimp only [p, q]
  module

/-- The canonical state obtained from the actual nonnegative-time channel. -/
def flowState (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (rho : DensityState (Fin 2 × R)) (t : ℝ) (ht : 0 ≤ t) : DensityState (Fin 2 × R) :=
  (Classical.choose (flow_quantumChannel a b ha hb hab t ht)).mapState rho

private lemma flowState_matrix (a b : Fin 3 → ℝ)
    (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (rho : DensityState (Fin 2 × R)) (t : ℝ) (ht : 0 ≤ t) :
    (flowState a b ha hb hab rho t ht).1 =
      CStarMatrix.ofMatrix (flow a b (CStarMatrix.ofMatrix.symm rho.1) t) := by
  exact congrArg CStarMatrix.ofMatrix
    (Classical.choose_spec (flow_quantumChannel a b ha hb hab t ht)
      (CStarMatrix.ofMatrix.symm rho.1))

/-- The canonical reference state, formed using the input's own memory marginal. -/
def equilibriumState (rho : DensityState (Fin 2 × R)) : DensityState (Fin 2 × R) := by
  refine ⟨CStarMatrix.ofMatrix (equilibrium (CStarMatrix.ofMatrix.symm rho.1)), ?_, ?_⟩
  · exact map_nonneg CStarMatrix.ofMatrixStarAlgEquiv
      (equilibrium_posSemidef (density_posSemidef rho)).nonneg
  · exact (equilibrium_trace (CStarMatrix.ofMatrix.symm rho.1)).trans rho.2.2

/-- Entropy dissipation for the actual amplified channel and its supported
canonical relative entropy, allowing the input joint state to be singular. -/
theorem supported_relativeEntropy_flow_derivative [Nonempty R]
    (a b : Fin 3 → ℝ) (ha : a ⬝ᵥ a = 1) (hb : b ⬝ᵥ b = 1) (hab : a ⬝ᵥ b = 0)
    (rho : DensityState (Fin 2 × R))
    (hR : (partialTraceLeft (CStarMatrix.ofMatrix.symm rho.1)).PosDef)
    (t : ℝ) (ht : 0 < t) :
    let X := CStarMatrix.ofMatrix.symm rho.1
    HasDerivAt (relativeEntropyCurve a b X)
      (-(generator a b (flow a b X t) *
        (cfc Real.log (flow a b X t) - cfc Real.log (equilibrium X))).trace.re) t ∧
    HasDerivAt (relativeEntropyCurve a b X)
      (-(generator a b (flow a b X t) * cfc Real.log (flow a b X t)).trace.re) t ∧
    partialTraceLeft (flow a b X t) = partialTraceLeft X ∧
    (flow a b X t).trace = 1 ∧
    SupportContained (flowState a b ha hb hab rho t ht.le) (equilibriumState rho) ∧
    finiteTraceLogRelativeEntropy (flowState a b ha hb hab rho t ht.le)
      (equilibriumState rho) = relativeEntropyCurve a b X t ∧
    extendedQuantumRelativeEntropy (flowState a b ha hb hab rho t ht.le)
      (equilibriumState rho) = (relativeEntropyCurve a b X t : WithTop ℝ) := by
  dsimp only
  obtain ⟨hder, hsimpl⟩ := relativeEntropyCurve_derivative a b ha hb hab
    (density_posSemidef rho) hR t ht
  have hsupport : SupportContained (flowState a b ha hb hab rho t ht.le)
      (equilibriumState rho) := by
    intro v hv
    change equilibrium (CStarMatrix.ofMatrix.symm rho.1) *ᵥ v = 0 at hv
    have hz : v = 0 := (equilibrium_posDef (CStarMatrix.ofMatrix.symm rho.1) hR).mulVec_injective
      (hv.trans (Matrix.mulVec_zero _).symm)
    change (CStarMatrix.ofMatrix.symm (flowState a b ha hb hab rho t ht.le).1) *ᵥ v = 0
    rw [hz, Matrix.mulVec_zero]
  have hfinite : finiteTraceLogRelativeEntropy (flowState a b ha hb hab rho t ht.le)
      (equilibriumState rho) = relativeEntropyCurve a b (CStarMatrix.ofMatrix.symm rho.1) t := by
    unfold finiteTraceLogRelativeEntropy
    rw [flowState_matrix]
    rfl
  exact ⟨hder, hsimpl, partialTraceLeft_flow a b ha hb _ t,
    (flow_trace a b ha hb _ t).trans rho.2.2, hsupport, hfinite,
    (extendedQuantumRelativeEntropy_eq_coe_of_support hsupport).trans
      (congrArg (fun r : ℝ => (r : WithTop ℝ)) hfinite)⟩

example : ∃ a b : Fin 3 → ℝ, a ⬝ᵥ a = 1 ∧ b ⬝ᵥ b = 1 ∧ a ⬝ᵥ b = 0 := by
  exact ⟨![1, 0, 0], ![0, 1, 0], by norm_num [dotProduct, Fin.sum_univ_three]⟩

-- Faithful memory does not force the input joint state to be faithful.
example : ∃ rho : DensityState (Fin 2 × Unit),
    (partialTraceLeft (CStarMatrix.ofMatrix.symm rho.1)).PosDef ∧
      ¬ (CStarMatrix.ofMatrix.symm rho.1).PosDef := by
  let X : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℂ :=
    Matrix.diagonal fun p => if p.1 = 0 then 1 else 0
  have hX : X.PosSemidef := Matrix.posSemidef_diagonal_iff.mpr (by
    intro p
    split_ifs <;> norm_num)
  have htr : X.trace = 1 := by
    change (Matrix.diagonal (fun p : Fin 2 × Unit =>
      if p.1 = 0 then (1 : ℂ) else 0)).trace = 1
    rw [Matrix.trace_diagonal, Fintype.sum_prod_type]
    norm_num [Fin.sum_univ_two]
  let rho : DensityState (Fin 2 × Unit) := ⟨CStarMatrix.ofMatrix X,
    map_nonneg CStarMatrix.ofMatrixStarAlgEquiv hX.nonneg, htr⟩
  refine ⟨rho, ?_, ?_⟩
  · change (partialTraceLeft X).PosDef
    have hm : partialTraceLeft X = 1 := by
      ext r s
      cases r
      cases s
      simp [X, partialTraceLeft, Fin.sum_univ_two]
    rw [hm]
    exact Matrix.PosDef.one
  · change ¬ X.PosDef
    intro hp
    have hz := Matrix.posDef_diagonal_iff.mp hp (1, ())
    norm_num at hz

end D5.S3.Quantum.Dynamics.AmplifiedPauliEntropyFlow
