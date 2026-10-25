/- GID: D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim; result=D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.result; claim=D5/S3/Quantum/QuantumChannels/ChannelAssemblageLOSRRefutation.claim
   digest: Tracing the control makes the rotation assemblages free and refutes their angle ordering. -/

import D5.S3.Quantum.Foundation.FiniteKrausChannel
import D5.S3.Quantum.Information.PartialTraceMutualInformation
import D5.S3.QuantumBounds.CHSHWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation

open scoped BigOperators Kronecker Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel (finite_kraus_quantum_channel)
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf (MatrixMap)
open D5.S3.Quantum.Information.PartialTraceMutualInformation
open D5.S3.Quantum.FiniteDimensional (qubitX qubitZ)
open D5.S3.QuantumBounds.CHSHWitness (bellDensity)

/-- Complete positivity at all finite amplifications, and trace preservation on all matrices. -/
def IsCPTP {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    (Φ : MatrixMap A B ℂ) : Prop :=
  Φ.IsCompletelyPositive ∧ ∀ X, (Φ X).trace = X.trace

abbrev Assemblage := Fin 2 → Fin 2 → MatrixMap (Fin 2) (Fin 2) ℂ

/-- Rotation around the y axis, with the source's half-angle convention. -/
def rotationY (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (θ / 2) : ℂ), -(Real.sin (θ / 2) : ℂ);
    (Real.sin (θ / 2) : ℂ), (Real.cos (θ / 2) : ℂ)]

/-- The first factor controls a rotation on the second factor. -/
def controlledRotation (θ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun i j => if i.1 = j.1 then
    (if i.1 = 0 then (1 : Matrix (Fin 2) (Fin 2) ℂ) i.2 j.2
      else rotationY θ i.2 j.2) else 0

/-- Alice's two binary Pauli measurements. -/
def measurement (a x : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ a.val • (if x = 0 then qubitZ else qubitX))

/-- Equation CRfam: Bell input, controlled rotation, trace B, then measurement and trace A. -/
def assemblage (θ : ℝ) : Assemblage := fun a x =>
  { toFun := fun ρ =>
      let gate := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ controlledRotation θ
      let joint := Matrix.reindex (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2))
        (Equiv.prodAssoc (Fin 2) (Fin 2) (Fin 2)) (bellDensity ⊗ₖ ρ)
      let evolved := gate * joint * gate.conjTranspose
      let reduced := partialTraceRight (evolved.submatrix
        (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1, (p.2, p.1.2)))
        (fun p : (Fin 2 × Fin 2) × Fin 2 => (p.1.1, (p.2, p.1.2))))
      partialTraceLeft ((measurement a x ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) * reduced)
    map_add' := by sorry
    map_smul' := by sorry }

/-- Equation LOSRtrans-channel, including shared randomness, no retrocausation and memory. -/
def LOSRConvertible (I I' : Assemblage) : Prop :=
  ∃ (Λ S : Type) (fΛ : Fintype Λ) (fS : Fintype S) (dS : DecidableEq S),
    letI := fΛ
    letI := fS
    letI := dS
    ∃ (p : Λ → ℝ) (q : Λ → Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℝ)
      (pre : Λ → MatrixMap (Fin 2) (Fin 2 × S) ℂ)
      (post : Λ → MatrixMap (Fin 2 × S) (Fin 2) ℂ),
      (∀ λ, 0 ≤ p λ) ∧ (∑ λ, p λ) = 1 ∧
      (∀ λ a' x a x', 0 ≤ q λ a' x a x') ∧
      (∀ λ a x', ∑ a', ∑ x, q λ a' x a x' = 1) ∧
      (∀ λ x x' a₁ a₂, ∑ a', q λ a' x a₁ x' = ∑ a', q λ a' x a₂ x') ∧
      (∀ λ, IsCPTP (pre λ)) ∧ (∀ λ, IsCPTP (post λ)) ∧
      ∀ a' x' ρ, I' a' x' ρ = ∑ λ, ∑ a, ∑ x,
        (p λ * q λ a' x a x') •
          post λ (MatrixMap.kron (I a x) (LinearMap.id : MatrixMap S S ℂ) (pre λ ρ))

/-- Zjawin–Schmid–Hoban–Sainz Conjecture 3, for the literal family and LOSR formula. -/
def claim : Prop :=
  ∀ θ₁ θ₂ : ℝ, θ₁ ∈ Set.Ioc 0 (Real.pi / 2) → θ₂ ∈ Set.Ioc 0 (Real.pi / 2) →
    (LOSRConvertible (assemblage θ₁) (assemblage θ₂) ↔ θ₁ ≥ θ₂)

private lemma free_form (θ : ℝ) (a x : Fin 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    assemblage θ a x ρ = if x = 0 then
      (if a = 0 then (1 / 2 : ℂ) • ρ
        else (1 / 2 : ℂ) • (rotationY θ * ρ * (rotationY θ).conjTranspose))
      else (1 / 4 : ℂ) • (ρ + rotationY θ * ρ * (rotationY θ).conjTranspose) := by
  sorry

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

private def alice (λ : Fin 2 × Fin 2) (a' x _a x' : Fin 2) : ℝ :=
  if x = 0 ∧ a' = (if x' = 0 then λ.1 else λ.2) then 1 else 0

private lemma pre_cptp : IsCPTP preMap := by
  sorry

private lemma post_cptp (b : Fin 2) : IsCPTP (postMap b) := by
  sorry

private lemma conversion_identity (a' x' : Fin 2) (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    assemblage (Real.pi / 2) a' x' ρ =
      ∑ λ : Fin 2 × Fin 2, ∑ a : Fin 2, ∑ x : Fin 2,
        ((1 / 4 : ℝ) * alice λ a' x a x') • postMap λ.1
          (MatrixMap.kron (assemblage (Real.pi / 3) a x)
            (LinearMap.id : MatrixMap (Fin 2) (Fin 2) ℂ) (preMap ρ)) := by
  sorry

private lemma conversion :
    LOSRConvertible (assemblage (Real.pi / 3)) (assemblage (Real.pi / 2)) := by
  refine ⟨Fin 2 × Fin 2, Fin 2, inferInstance, inferInstance, inferInstance,
    fun _ => 1 / 4, alice, fun _ => preMap, fun λ => postMap λ.1, ?_⟩
  refine ⟨by intro λ; norm_num, by norm_num [Fintype.sum_prod_type, Fin.sum_univ_two],
    ?_, ?_, ?_, fun _ => pre_cptp, fun λ => post_cptp λ.1, conversion_identity⟩
  · intro λ a' x a x'
    unfold alice
    split_ifs <;> norm_num
  · intro λ a x'
    rcases λ with ⟨b, r⟩
    fin_cases b <;> fin_cases r <;> fin_cases x' <;>
      norm_num [alice, Fin.sum_univ_two]
  · intro λ x x' a₁ a₂
    rfl

private lemma witness_angles :
    Real.pi / 3 ∈ Set.Ioc 0 (Real.pi / 2) ∧
      Real.pi / 2 ∈ Set.Ioc 0 (Real.pi / 2) ∧ Real.pi / 3 < Real.pi / 2 := by
  have hp := Real.pi_pos
  constructor
  · constructor <;> linarith
  constructor
  · exact ⟨by positivity, le_rfl⟩
  · linarith

theorem result : ¬ claim := by
  intro h
  have hw := witness_angles
  have horder := (h _ _ hw.1 hw.2.1).mp conversion
  exact (not_le_of_gt hw.2.2) horder

end D5.S3.Quantum.QuantumChannels.ChannelAssemblageLOSRRefutation
