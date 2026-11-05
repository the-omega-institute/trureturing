/- GID: D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim; result=D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result; claim=D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim
   digest: Tracing the control makes the assemblages free and refutes their angle ordering. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.QuantumBounds.CHSHWitness
import D5.S3.QuantumBounds.StatisticalStrengthMagicSquare
import D5.S3.Quantum.Dynamics.PositivePauliClockOrder
import D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction

/-! The literal controlled-rotation family admits a conversion against its angle ordering. -/

set_option linter.style.longLine false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096

noncomputable section

open scoped BigOperators Kronecker Matrix

namespace D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.Divergence.ConditionalHockeyStickOrthogonalReduction
  (partialTraceRight_smul)
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.CHSHWitness (bellDensity)
open D5.S3.QuantumBounds.StatisticalStrengthMagicSquare (chshAlice)
open D5.S3.Quantum.Dynamics.PositivePauliClockOrder (controlled)

/-- Complete positivity at all finite amplifications, and trace preservation on all matrices. -/
def IsCPTP {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (φ : MatrixMap A B ℂ) : Prop :=
  φ.IsCompletelyPositive ∧ ∀ X, (φ X).trace = X.trace

abbrev Assemblage := Fin 2 → Fin 2 → MatrixMap (Fin 2) (Fin 2) ℂ

/-- Rotation around the y axis, with the source's half-angle convention. -/
def rotationY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (Matrix.planeConformalMatrix (Real.cos (θ / 2) : ℂ) (Real.sin (θ / 2) : ℂ)
    (by exact_mod_cast (Real.cos_sq_add_sin_sq (θ / 2)).trans_ne one_ne_zero)).val

/-- Equation CRfam: Bell input, controlled rotation, trace B, then measurement and trace A. -/
def assemblage (θ : ℝ) : Assemblage := fun a x =>
  { toFun := fun ρ =>
      let gate := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ controlled 1 (rotationY θ)
      let joint := Matrix.reindex (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2))
        (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)) (bellDensity ⊗ₖ ρ)
      let evolved := gate * joint * gate.conjTranspose
      let reduced := partialTraceRight (evolved.submatrix
        (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1, (p.2, p.1.2)))
        (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1, (p.2, p.1.2))))
      partialTraceLeft ((chshAlice x a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * reduced)
    map_add' := by
      intro ρ σ
      dsimp only
      simp only [Matrix.kronecker_add, Matrix.reindex_apply, Matrix.submatrix_add,
        Pi.add_apply, Matrix.mul_add, Matrix.add_mul, partialTraceRight_add,
        partialTraceLeft_add]
    map_smul' := by
      intro z ρ
      dsimp only
      simp only [RingHom.id_apply, Matrix.kronecker_smul, Matrix.reindex_apply,
        Matrix.submatrix_smul, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul,
        partialTraceRight_smul]
      ext i j
      unfold partialTraceLeft
      exact (Finset.mul_sum _ _ _).symm }

/-- Equation LOSRtrans-channel, including shared randomness, no retrocausation and memory. -/
def LOSRConvertible (I I' : Assemblage) : Prop :=
  ∃ (Λ S : Type) (fΛ : Fintype Λ) (fS : Fintype S) (dS : DecidableEq S),
    letI := fΛ
    letI := fS
    letI := dS
    ∃ (p : Λ → ℝ) (q : Λ → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
      (pre : Λ → MatrixMap (Fin 2) (Fin 2 × S) ℂ)
      (post : Λ → MatrixMap (Fin 2 × S) (Fin 2) ℂ),
      (∀ l, 0 ≤ p l) ∧ (∑ l, p l) = 1 ∧
      (∀ l a' x a x', 0 ≤ q l a' x a x') ∧
      (∀ l a x', ∑ a', ∑ x, q l a' x a x' = 1) ∧
      (∀ l x x' a₁ a₂, ∑ a', q l a' x a₁ x' = ∑ a', q l a' x a₂ x') ∧
      (∀ l, IsCPTP (pre l)) ∧ (∀ l, IsCPTP (post l)) ∧
      ∀ a' x' ρ, I' a' x' ρ = ∑ l, ∑ a, ∑ x,
        (p l * q l a' x a x') •
          post l (MatrixMap.kron (I a x) (LinearMap.id : MatrixMap S S ℂ) (pre l ρ))

/-- Zjawin–Schmid–Hoban–Sainz Conjecture 3, for the literal family and LOSR formula. -/
def claim : Prop :=
  ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Ioc 0 (Real.pi / 2) → θ₂ ∈ Set.Ioc 0 (Real.pi / 2) →
    (LOSRConvertible (assemblage θ₁) (assemblage θ₂) ↔ θ₁ ≥ θ₂)

set_option maxHeartbeats 4000000 in
-- Expand the three-qubit construction on its finite computational basis.
private lemma free_form (θ : ℝ) (a x : Fin 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    assemblage θ a x ρ = if x = 0 then
      (if a = 0 then (1 / 2 : ℂ) • ρ
        else (1 / 2 : ℂ) • (rotationY θ * ρ * (rotationY θ).conjTranspose))
      else (1 / 4 : ℂ) • (ρ + rotationY θ * ρ * (rotationY θ).conjTranspose) := by
  ext i j
  unfold assemblage
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.reindex_apply]
  unfold partialTraceLeft
  simp only [Matrix.mul_apply, Matrix.kroneckerMap_apply]
  unfold partialTraceRight
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  fin_cases a <;> fin_cases x <;> fin_cases i <;> fin_cases j <;>
    with_unfolding_all simp [D5.S3.QuantumBounds.StatisticalStrengthMagicSquare.chshAlice,
      D5.S3.Quantum.Dynamics.PositivePauliClockOrder.controlled,
      Matrix.blockDiagonal_apply, rotationY.eq_1, Matrix.mul_apply, Matrix.one_apply,
      Matrix.reindex_apply, Matrix.submatrix_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
      D5.S3.QuantumBounds.CHSHWitness.bellDensity,
      D5.S3.QuantumBounds.CHSHWitness.bellVector,
      D5.S3.Quantum.QubitWitnesses.bellCoefficients, qubitX, qubitZ,
      Matrix.vecMulVec_apply, -Matrix.cons_mul, Matrix.conjTranspose_apply,
      Complex.conj_ofReal,
      D5.S3.QuantumBounds.CHSHWitness.complex_sqrt_two_inv_mul_self,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring

private def preKraus : Unit → Matrix (Fin 2 × Fin 2) (Fin 2) ℂ :=
  fun _ i j => if i.1 = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j else 0

private def preMap : MatrixMap (Fin 2) (Fin 2 × Fin 2) ℂ :=
  MatrixMap.of_kraus preKraus preKraus

private def targetUnitary (b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  if b = 0 then 1 else rotationY (Real.pi / 2)

private def postKraus (b : Fin 2) : Fin 2 → Matrix (Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun k i j => if j.1 = k then targetUnitary b i j.2 else 0

private def postMap (b : Fin 2) : MatrixMap (Fin 2 × Fin 2) (Fin 2) ℂ :=
  MatrixMap.of_kraus (postKraus b) (postKraus b)

private def alice (l : Fin 2 × Fin 2) (a' x _a x' : Fin 2) : ℝ :=
  if x = 0 ∧ a' = (if x' = 0 then l.1 else l.2) then 1 else 0

private lemma pre_cptp : IsCPTP preMap := by
  have hK : (∑ k : Unit, (preKraus k).conjTranspose * preKraus k) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [preKraus.eq_1, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.one_apply]
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive preKraus, ?_⟩
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel preKraus hK
  intro ρ
  change (MatrixMap.of_kraus preKraus preKraus ρ).trace = ρ.trace
  unfold MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hchannel ρ]
  exact channel.trace_preserving (CStarMatrix.ofMatrix ρ)

private lemma post_cptp (b : Fin 2) : IsCPTP (postMap b) := by
  have hcircle : (Real.cos (Real.pi * (1 / 4)) : ℂ) ^ 2 +
      (Real.sin (Real.pi * (1 / 4)) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (Real.pi * (1 / 4))
  have hU : (targetUnitary b).conjTranspose * targetUnitary b = 1 := by
    fin_cases b
    · simp [targetUnitary.eq_1]
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [targetUnitary.eq_1, rotationY.eq_1, Matrix.mul_apply, Fin.sum_univ_two,
          Matrix.conjTranspose_apply, Complex.conj_ofReal,
          -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
        (try ring) <;> linear_combination hcircle
  have hK : (∑ k : Fin 2, (postKraus b k).conjTranspose * postKraus b k) = 1 := by
    ext i j
    rcases i with ⟨i, r⟩
    rcases j with ⟨j, s⟩
    have h := congrFun (congrFun hU r) s
    fin_cases i <;> fin_cases j <;>
      simpa [postKraus.eq_1, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
        Matrix.one_apply] using h
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (postKraus b), ?_⟩
  obtain ⟨channel, hchannel⟩ := finite_kraus_quantum_channel (postKraus b) hK
  intro ρ
  change (MatrixMap.of_kraus (postKraus b) (postKraus b) ρ).trace = ρ.trace
  unfold MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← hchannel ρ]
  exact channel.trace_preserving (CStarMatrix.ofMatrix ρ)

private lemma memory_action (Φ : MatrixMap (Fin 2) (Fin 2) ℂ) (b : Fin 2)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    postMap b (MatrixMap.kron Φ (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ)
      (preMap ρ)) = (Φ (Matrix.single 0 0 1)).trace •
        (targetUnitary b * ρ * (targetUnitary b).conjTranspose) := by
  unfold preMap postMap MatrixMap.of_kraus
  simp only [LinearMap.sum_apply, LinearMap.coe_mk, AddHom.coe_mk]
  ext i j
  simp only [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  simp_rw [MatrixMap.kron_def]
  unfold Matrix.single Matrix.trace
  simp [preKraus.eq_1, postKraus.eq_1, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

private lemma source_branch_trace (θ : ℝ) (a : Fin 2) :
    (assemblage θ a 0 (Matrix.single 0 0 1)).trace = (1 / 2 : ℂ) := by
  have hcircle : (Real.cos (θ * (1 / 2)) : ℂ) ^ 2 +
      (Real.sin (θ * (1 / 2)) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.cos_sq_add_sin_sq (θ * (1 / 2))
  rw [free_form]
  unfold Matrix.trace Matrix.single
  fin_cases a <;>
    simp [rotationY.eq_1, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      -Matrix.cons_mul, Matrix.vecHead, Matrix.vecTail, div_eq_mul_inv,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    simp only [one_div] at hcircle <;>
    linear_combination (1 / 2 : ℂ) * hcircle

private lemma conversion_identity (a' x' : Fin 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    assemblage (Real.pi / 2) a' x' ρ =
      ∑ l : Fin 2 × Fin 2, ∑ a : Fin 2, ∑ x : Fin 2,
        ((1 / 4 : ℝ) * alice l a' x a x') • postMap l.1
          (MatrixMap.kron (assemblage (Real.pi / 3) a x)
            (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) (preMap ρ)) := by
  rw [free_form]
  fin_cases a' <;> fin_cases x'
  all_goals norm_num only [Fintype.sum_prod_type, Fin.sum_univ_two, alice.eq_1]
  all_goals simp only [memory_action, source_branch_trace]
  all_goals
    ext i j
    simp [targetUnitary.eq_1, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply]
    ring

private lemma conversion :
    LOSRConvertible (assemblage (Real.pi / 3)) (assemblage (Real.pi / 2)) := by
  refine ⟨Fin 2 × Fin 2, Fin 2, inferInstance, inferInstance, inferInstance,
    fun _ => 1 / 4, alice, fun _ => preMap, fun l => postMap l.1, ?_⟩
  refine ⟨by intro l; norm_num, by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two],
    ?_, ?_, ?_, fun _ => pre_cptp, fun l => post_cptp l.1, conversion_identity⟩
  · intro l a' x a x'
    rw [alice.eq_1]
    split_ifs <;> norm_num
  · intro l a x'
    rcases l with ⟨b, r⟩
    fin_cases b <;> fin_cases r <;> fin_cases x' <;>
      simp only [alice.eq_1, Fin.sum_univ_two, Fin.isValue, ↓reduceIte, and_true, and_false,
        zero_add, add_zero]
      <;> norm_num
  · intro l x x' a₁ a₂
    rfl

private lemma witness_angles :
    Real.pi / 3 ∈ Set.Ioc 0 (Real.pi / 2) ∧
      Real.pi / 2 ∈ Set.Ioc 0 (Real.pi / 2) ∧ Real.pi / 3 < Real.pi / 2 := by
  have hp := Real.pi_pos
  constructor
  · constructor <;> linarith
  constructor
  · exact ⟨Real.pi_div_two_pos, le_rfl⟩
  · linarith

theorem result : ¬ claim := by
  intro h
  have hw := witness_angles
  have horder := (h _ _ hw.1 hw.2.1).mp conversion
  exact (not_le_of_gt hw.2.2) horder

end D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
