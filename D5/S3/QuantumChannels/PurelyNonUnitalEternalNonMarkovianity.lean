/- GID: D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity
   generality: I
   mirror-B: D5/B/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.claim; result=D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.result; claim=D5/S3/QuantumChannels/PurelyNonUnitalEternalNonMarkovianity.claim
   digest: Rotating replacement states refute purely non-unital eternal non-Markovianity. -/

/-
admission_basis: open-problem-resolution (#16599; Refuted)
escape_witness: none
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
All theorem proofs are bind-only: frozen Kraus positivity, pinned derivative rules,
logical assembly, and exact scalar/matrix normalization suffice.
FiniteKrausRepresentation is Closed but unfrozen; only its required Choi definition is used.
Complete positivity uses frozen FiniteKrausChannel; calculus uses pinned Mathlib.
The intermediate map is depolarized; its CPTP property uses the frozen channel_cptp owner.
The channel_cptp owner audit is unfinished: https://github.com/the-omega-institute/trureturing/issues/16744.
Direct frozen dependencies:
  F1: D5/S3/Quantum/FiniteDimensional.QubitMatrix
    statement_id: sha256:e376bbe008ddbbc49fcf9763247304ed70ec54ac5cf49af3c6f7fb58fa626f30
  F2: D5/S3/Quantum/FiniteDimensional.qubitX
    statement_id: sha256:cfaddf4a17693b52013e93be8cd6559e7021ed57ca0305492712468b57f882f7
  F3: D5/S3/Quantum/FiniteDimensional.qubitZ
    statement_id: sha256:381a2bec567456715f58fe6c0c413d59d37882b8499fc81a486c49e7c081d78c
  F4: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap
    statement_id: sha256:df01dcc9d6d91985f3214eaee7e1c5eacebab3335dff64bb7b620043c650cad7
  F5: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.IsCompletelyPositive
    statement_id: sha256:39e2682fd93035c705a08181bb7fdfb77067eba43afcc98c200c30543b913ed4
  F6: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus
    statement_id: sha256:024ca3125b8f182e070b880d7c41840a31fa9cb0aaa89e5d81dbe4ebb3c5f287
  F7: D5/S3/Quantum/Foundation/FiniteKrausChannel.PhyslibLeaf.MatrixMap.of_kraus_isCompletelyPositive
    statement_id: sha256:522daaecff9970808def6ecdd938d4b89107d2820c79bafbf378ab083767f57f
  F8: D5/S3/Quantum/Information/StabilizerPairLocalUnitaryInequivalence.pauliMatrix
    statement_id: sha256:7f853eaeda888a9eccbab5fe25474fc62b519a3229013530986887de25cb28d7
  F9: D5/S3/Quantum/QuantumChannels/TracePreservingEigenvalueBound.depolarized
    statement_id: sha256:24b644702cdd55fca7f15864e69044d03389fbf696780b679efb0e0478b51b69
  F10: D5/S3/QuantumChannels/CoPRelativeQuantumnessRefutation.IsCPTP
    statement_id: sha256:1440f7e681ed2017e7c90aedfe54aa0ad218d57311655f9d554863853dd8f53c
  F11: D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.channel_cptp
    statement_id: sha256:12d1096835e803a33aaada5cb586f2c51f81dc4c2fe95a86cc39cb93d815a686
  F12: D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.pauliChannel
    statement_id: sha256:9cfa737a89862177f5d79fc573c20d89f1d36c060c850c5782748e1dac6132cb
  F13: D5/S3/QuantumChannels/PauliThreeWeightBayesianInverseUniqueness.sigma
    statement_id: sha256:8d32b4e3e5803524e6569b40c43fffbb84b46699655ec967674ed337624d369d
Declaration classifications (F-labels above supply declaration identities):
  unitalPart: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: PurelyNonUnital,unital_formula,dep_intermediate,phi_purely
  PurelyNonUnital: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4,F10; consumers: claim,phi_purely
  IsGeneratorAt: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: EternallyNonMarkovian,phi_generator,phi_eternal
  CondCP: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: EternallyNonMarkovian,l_not_condcp,phi_eternal
  EternallyNonMarkovian: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: claim,phi_eternal
  claim: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4,F10; consumers: result
  D: proof_shape: not-applicable; escape_witness: none;
    dependencies: none; consumers: D_ne,Phi,K,kraus_action,phi_trace,phi_zero,phi_nonunital,unital_formula,dep_intermediate,L,PhiInv,inverse_pair,dotPhi,generator_composition,rational_deriv,phi_generator,v_form
  D_ne: proof_shape: bind-only; escape_witness: none;
    dependencies: none; consumers: kraus_action,phi_trace,phi_nonunital,unital_formula,dep_intermediate,inverse_pair,generator_composition,rational_deriv,phi_generator,v_form
  affine: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: Phi,unital_formula,dep_intermediate,L,PhiInv,dotPhi
  Phi: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: kraus_action,phi_trace,phi_cptp,phi_zero,phi_nonunital,unital_formula,dep_intermediate,phi_purely,inverse_pair,phi_generator,phi_eternal,result
  K: proof_shape: not-applicable; escape_witness: none;
    dependencies: none; consumers: kraus_action,phi_cptp
  kraus_action: proof_shape: bind-only; escape_witness: none;
    dependencies: F4,F6; consumers: phi_cptp
  phi_trace: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_cptp
  phi_cptp: proof_shape: bind-only; escape_witness: none;
    dependencies: F4,F6,F7,F5,F10; consumers: result
  phi_zero: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: result
  phi_nonunital: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_purely
  dep_cptp: proof_shape: bind-only; escape_witness: none;
    dependencies: F3,F2,F1,F8,F13,F9,F4,F11,F12,F10; consumers: phi_purely
  unital_formula: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: dep_intermediate
  dep_intermediate: proof_shape: bind-only; escape_witness: none;
    dependencies: F4,F9; consumers: phi_purely
  phi_purely: proof_shape: bind-only; escape_witness: none;
    dependencies: F4,F9,F3,F2,F1,F8,F13,F11,F12,F10; consumers: result
  L: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: generator_composition,phi_generator,v_form,l_not_condcp,phi_eternal
  PhiInv: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: inverse_pair,generator_composition,phi_generator
  inverse_pair: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_generator
  dotPhi: proof_shape: not-applicable; escape_witness: none;
    dependencies: F4; consumers: generator_composition,phi_generator
  generator_composition: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_generator
  rational_deriv: proof_shape: bind-only; escape_witness: none;
    dependencies: none; consumers: phi_generator
  phi_generator: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_eternal
  v: proof_shape: not-applicable; escape_witness: none;
    dependencies: none; consumers: v_trace,v_form,l_not_condcp
  v_trace: proof_shape: bind-only; escape_witness: none;
    dependencies: none; consumers: l_not_condcp
  v_form: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: l_not_condcp
  l_not_condcp: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: phi_eternal
  phi_eternal: proof_shape: bind-only; escape_witness: none;
    dependencies: F4; consumers: result
  result: proof_shape: bind-only; escape_witness: none;
    dependencies: F4,F9,F3,F2,F1,F8,F13,F11,F12,F10,F6,F7,F5; consumers: none
-/

import D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound
import D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators
open Matrix
open D5.S3.QuantumChannels.PauliThreeWeightBayesianInverseUniqueness (sigma pauliChannel channel_cptp)
open D5.S3.Quantum.QuantumChannels.TracePreservingEigenvalueBound (depolarized)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.QuantumChannels.CoPRelativeQuantumnessRefutation (IsCPTP)
noncomputable section
namespace D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity

def unitalPart (Phi : ℝ → MatrixMap (Fin 2) (Fin 2) ℂ) (t : ℝ)
    (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Phi t X - (X.trace / 2) • (Phi t 1 - 1)

def PurelyNonUnital (Phi : ℝ → MatrixMap (Fin 2) (Fin 2) ℂ) : Prop :=
  (∀ t, 0 < t → Phi t 1 ≠ 1) ∧ ∀ s t, 0 ≤ s → s ≤ t →
    ∃ V : MatrixMap (Fin 2) (Fin 2) ℂ, IsCPTP V ∧
      ∀ X, V (unitalPart Phi s X) = unitalPart Phi t X

def IsGeneratorAt (Phi : ℝ → MatrixMap (Fin 2) (Fin 2) ℂ) (t : ℝ)
    (L : MatrixMap (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ X i j, HasDerivAt (fun u : ℝ => Phi u X i j) (L (Phi t X) i j) t

def CondCP (L : MatrixMap (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ v : Fin 2 × Fin 2 → ℂ, (∑ i, v (i,i)) = 0 →
    0 ≤ (star v ⬝ᵥ (MatrixMap.choi_matrix L *ᵥ v)).re

def EternallyNonMarkovian (Phi : ℝ → MatrixMap (Fin 2) (Fin 2) ℂ) : Prop :=
  ∀ t, 0 < t → ∃ L, IsGeneratorAt Phi t L ∧ ¬ CondCP L

def claim : Prop := ∀ Phi : ℝ → MatrixMap (Fin 2) (Fin 2) ℂ,
  (∀ t, 0 ≤ t → IsCPTP (Phi t)) → (∀ X, Phi 0 X = X) →
    PurelyNonUnital Phi → ¬ EternallyNonMarkovian Phi

private def D (t : ℝ) : ℂ := 1 + (t : ℂ)^2
private theorem D_ne (t : ℝ) : D t ≠ 0 := by
  have h : (1 + t^2 : ℝ) ≠ 0 := ne_of_gt (by positivity)
  change 1 + (t : ℂ)^2 ≠ 0
  exact_mod_cast h

private def affine (a : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) : MatrixMap (Fin 2) (Fin 2) ℂ :=
  a • LinearMap.id + (Matrix.traceLinearMap (Fin 2) ℂ ℂ).smulRight B

private def Phi (t : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ := affine (1 / D t) (((t : ℂ)^2 / D t^2) •
    (Matrix.vecMulVec ![1, (t : ℂ)] (star ![1, (t : ℂ)])))

private def K (t : ℝ) : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![(1 / D t) • 1, ((t : ℂ) / D t) • 1,
    ((t : ℂ) / D t) • Matrix.vecMulVec ![1, (t : ℂ)] ![1, 0],
    ((t : ℂ) / D t) • Matrix.vecMulVec ![1, (t : ℂ)] ![0, 1]]

private theorem kraus_action (t : ℝ) : MatrixMap.of_kraus (K t) (K t) = Phi t := by
  ext X i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.of_kraus, K, Phi, affine, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, D,
          Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul,
      map_add, map_pow, map_div₀] <;>
    field_simp [show 1 + (t : ℂ)^2 ≠ 0 from D_ne t] <;> ring

private theorem phi_trace (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : (Phi t X).trace = X.trace := by
  simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, D, Matrix.trace,
          Fin.sum_univ_succ, smul_eq_mul]
  field_simp [show 1 + (t : ℂ)^2 ≠ 0 from D_ne t]
  ring

private theorem phi_cptp (t : ℝ) : IsCPTP (Phi t) :=
  ⟨kraus_action t ▸ MatrixMap.of_kraus_isCompletelyPositive (K t), phi_trace t⟩

private theorem phi_zero (X : Matrix (Fin 2) (Fin 2) ℂ) : Phi 0 X = X := by
  simp [Phi, affine, LinearMap.id_apply,
      Matrix.vecMulVec, D]

private theorem phi_nonunital (t : ℝ) (ht : 0 < t) : Phi t 1 ≠ 1 := by
  intro h
  have e := congrFun (congrFun h 0) 1
  simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, Matrix.trace,
          smul_eq_mul,
    ne_of_gt ht, D_ne t] at e
private theorem dep_cptp (eta : ℝ) (h0 : 0 ≤ eta) (h1 : eta ≤ 1) :
    IsCPTP (depolarized (d := 2) LinearMap.id (1 - eta)) := by
  let p : Fin 4 → ℝ := ![eta+(1-eta)/4, (1-eta)/4, (1-eta)/4, (1-eta)/4]
  have hp : ∀ μ, 0 ≤ p μ := by
    intro μ
    fin_cases μ <;> simp [p] <;> linarith
  have hs : ∑ μ, p μ = 1 := by
    simp [p, Fin.sum_univ_succ]
    ring
  have hc := channel_cptp p hp hs
  have heq : pauliChannel p = depolarized (d := 2) LinearMap.id (1-eta) := by
    ext X i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliChannel, p, sigma,
        D5.S3.Quantum.Information.StabilizerPairLocalUnitaryInequivalence.pauliMatrix,
        D5.S3.Quantum.FiniteDimensional.qubitX, D5.S3.Quantum.FiniteDimensional.qubitZ,
        depolarized, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.mul_apply,
        Matrix.trace, Matrix.vecMul, dotProduct, Fin.sum_univ_succ, smul_eq_mul] <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  exact heq ▸ hc

private theorem unital_formula (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    unitalPart Phi t X = affine (1 / D t) (((t : ℂ)^2 / (2*D t)) • 1) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unitalPart, Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, D, Matrix.trace,
          Fin.sum_univ_succ,
      smul_eq_mul] <;>
    field_simp [show 1 + (t : ℂ)^2 ≠ 0 from D_ne t] <;> ring

private theorem dep_intermediate (s t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    depolarized (d := 2) LinearMap.id (1 - (1+s^2)/(1+t^2)) (unitalPart Phi s X) = unitalPart Phi
        t X := by
  rw [unital_formula, unital_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [depolarized, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul] <;>
    field_simp [show 1 + (s : ℂ)^2 ≠ 0 from D_ne s,
      show 1 + (t : ℂ)^2 ≠ 0 from D_ne t] <;> ring

private theorem phi_purely : PurelyNonUnital Phi := by
  refine ⟨phi_nonunital, ?_⟩
  intro s t hs hst
  have he0 : 0 ≤ ((1+s^2)/(1+t^2)) := by positivity
  have he1 : ((1+s^2)/(1+t^2)) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 1+t^2)).mpr
    nlinarith
  exact ⟨depolarized (d := 2) LinearMap.id (1 - (1+s^2)/(1+t^2)), dep_cptp _ he0 he1,
      dep_intermediate s t⟩
private def L (t : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ := affine (-2*(t : ℂ)/D t) ((1 / D t^3) •
  !![2*(t : ℂ), (t : ℂ)^2*((t : ℂ)^2+3);
    (t : ℂ)^2*((t : ℂ)^2+3), 2*(t : ℂ)^3*((t : ℂ)^2+2)])

private def PhiInv (t : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ := affine (D t) (-(t : ℂ)^2 • ((1 / D t)
    • (Matrix.vecMulVec ![1, (t : ℂ)] (star ![1, (t : ℂ)]))))

private theorem inverse_pair (t : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    PhiInv t (Phi t X) = X ∧ Phi t (PhiInv t X) = X := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [PhiInv, Phi, Matrix.vecMulVec, affine, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, D, Matrix.trace,
          Fin.sum_univ_succ,
      smul_eq_mul] <;>
    field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t] <;> ring

private def dotPhi (t : ℝ) : MatrixMap (Fin 2) (Fin 2) ℂ := affine (-2*(t : ℂ)/D t^2)
  ((1 / D t^3) •
    !![2*(t : ℂ)*(1-(t : ℂ)^2), (t : ℂ)^2*(3-(t : ℂ)^2);
      (t : ℂ)^2*(3-(t : ℂ)^2), 4*(t : ℂ)^3])

private theorem generator_composition (t : ℝ) (Y : Matrix (Fin 2) (Fin 2) ℂ) :
    L t Y = dotPhi t (PhiInv t Y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [L, dotPhi, PhiInv, Matrix.vecMulVec, affine, LinearMap.add_apply, LinearMap.smul_apply,
        LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, D, Matrix.trace,
          Fin.sum_univ_succ,
      smul_eq_mul] <;>
    field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t] <;> ring

private theorem rational_deriv (t : ℝ) (n : ℕ) (A C : ℂ) :
    HasDerivAt (fun u : ℝ => A / D u + C * (u : ℂ)^n / D u^2)
      ((0 * D t - A*(2*(t : ℂ))) / D t^2 +
        ((C * (n * (t : ℂ)^(n-1) * 1)) * D t^2 -
          (C * (t : ℂ)^n) * (2*D t*(2*(t : ℂ)))) / (D t^2)^2) t := by
  have hx : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 t :=
    Complex.ofRealCLM.hasDerivAt
  have hd : HasDerivAt D (2*(t : ℂ)) t := by
    change HasDerivAt (fun u : ℝ => 1+(u : ℂ)^2) (2*(t : ℂ)) t
    simpa only [show (2 : ℕ)-1=1 from rfl, pow_one, mul_one, Nat.cast_ofNat, zero_add] using
      (hasDerivAt_const t (1 : ℂ)).fun_add (hx.fun_pow 2)
  have hd2 : HasDerivAt (fun u => D u^2) (2*D t*(2*(t : ℂ))) t := by
    simpa using hd.fun_pow 2
  exact ((hasDerivAt_const t A).fun_div hd (D_ne t)).fun_add
    (((hx.fun_pow n).const_mul C).fun_div hd2 (pow_ne_zero _ (D_ne t)))

private theorem phi_generator (t : ℝ) : IsGeneratorAt Phi t (L t) := by
  intro X i j
  rw [generator_composition, (inverse_pair t X).1]
  fin_cases i <;> fin_cases j
  · convert rational_deriv t 2 (X 0 0) (X.trace) using 1
    · funext u
      simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, Matrix.trace,
          Fin.sum_univ_succ, smul_eq_mul]
      ring
    · simp [dotPhi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul]
      field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t]
      ring
  · convert rational_deriv t 3 (X 0 1) (X.trace) using 1
    · funext u
      simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, Matrix.trace,
          Fin.sum_univ_succ, smul_eq_mul]
      ring
    · simp [dotPhi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul]
      field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t]
      ring
  · convert rational_deriv t 3 (X 1 0) (X.trace) using 1
    · funext u
      simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, Matrix.trace,
          Fin.sum_univ_succ, smul_eq_mul]
      ring
    · simp [dotPhi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul]
      field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t]
      ring
  · convert rational_deriv t 4 (X 1 1) (X.trace) using 1
    · funext u
      simp [Phi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, Matrix.vecMulVec, Matrix.trace,
          Fin.sum_univ_succ, smul_eq_mul]
      ring
    · simp [dotPhi, affine, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, D, Matrix.trace, Fin.sum_univ_succ,
          smul_eq_mul]
      field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t]
      ring

private def v (t : ℝ) (p : Fin 2 × Fin 2) : ℂ :=
  !![-2*(t : ℂ)*((t : ℂ)^2+3), -(t : ℂ)^2*((t : ℂ)^2+3)^2;
    4, 2*(t : ℂ)*((t : ℂ)^2+3)] p.1 p.2

private theorem v_trace (t : ℝ) : (∑ i, v t (i,i)) = 0 := by
  simp [v, Fin.sum_univ_succ]

private theorem v_form (t : ℝ) :
    star (v t) ⬝ᵥ (MatrixMap.choi_matrix (L t) *ᵥ v t) =
      ((-2*t^3*(1+t^2)*(t^2+4) : ℝ) : ℂ) := by
  simp [dotProduct, Matrix.mulVec, MatrixMap.choi_matrix, L, affine, LinearMap.add_apply,
      LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.smulRight_apply, Matrix.traceLinearMap_apply, v, D,
    Matrix.single, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_succ,
    smul_eq_mul, map_add, map_pow, map_mul]
  norm_num [starRingEnd_apply, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton]
  field_simp [show 1+(t : ℂ)^2 ≠ 0 from D_ne t]
  ring

private theorem l_not_condcp (t : ℝ) (ht : 0 < t) : ¬ CondCP (L t) := by
  intro h
  have hh := h (v t) (v_trace t)
  rw [v_form] at hh
  simp only [Complex.ofReal_re] at hh
  have hp : 0 < 2*t^3*(1+t^2)*(t^2+4) := by positivity
  nlinarith

private theorem phi_eternal : EternallyNonMarkovian Phi := by
  intro t ht
  exact ⟨L t, phi_generator t, l_not_condcp t ht⟩

theorem result : ¬ claim := by
  intro h
  exact h Phi (fun t _ => phi_cptp t) phi_zero phi_purely phi_eternal

end D5.S3.QuantumChannels.PurelyNonUnitalEternalNonMarkovianity
