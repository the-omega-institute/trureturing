/- GID: D5/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence
   generality: I
   mirror-B: D5/B/S3/Quantum/QuantumChannels/HeisenbergChannelCompressionEquivalence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Compatibility under all Heisenberg channels equals compatibility in all subspaces. -/

import D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation
import D5.S3.Quantum.Foundation.FiniteKrausRepresentation
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open D5.S3.Quantum.Foundation.FiniteKrausChannel.PhyslibLeaf
open D5.S3.Quantum.QuantumChannels.ConcealmentKernelNecessityRefutation (IsPOVM)

namespace D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence

/-- A family is jointly measurable if all effects are marginals of one parent POVM. -/
def FamilyJointlyMeasurable {d : ℕ} {X : Type} [Fintype X]
    {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ) : Prop := by
  classical
  exact ∃ G : ((x : X) → Ω x) → Matrix (Fin d) (Fin d) ℂ,
    IsPOVM G ∧ ∀ x b, (∑ a with a x = b, G a) = M x b

/-- Compression compatibility and unital completely positive compatibility agree. -/
def claim : Prop :=
  ∀ (d n : ℕ), 1 ≤ n → n ≤ d →
    ∀ (X : Type) [Fintype X] (Ω : X → Type) [∀ x, Fintype (Ω x)]
      (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ),
      (∀ x, IsPOVM (M x)) →
      ((∀ V : Matrix (Fin d) (Fin n) ℂ, Vᴴ * V = 1 →
        FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V)) ↔
       (∀ Φ : MatrixMap (Fin d) (Fin n) ℂ, Φ.IsCompletelyPositive → Φ 1 = 1 →
        FamilyJointlyMeasurable (fun x b => Φ (M x b))))

private def compressionMap {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℂ) :
    MatrixMap (Fin d) (Fin n) ℂ :=
  MatrixMap.of_kraus (fun _ : Unit => Vᴴ) (fun _ : Unit => Vᴴ)

private theorem compression_channel {d n : ℕ} (V : Matrix (Fin d) (Fin n) ℂ)
    (hV : Vᴴ * V = 1) :
    (compressionMap V).IsCompletelyPositive ∧ compressionMap V 1 = 1 ∧
      ∀ A, compressionMap V A = Vᴴ * A * V := by
  have hA (A : Matrix (Fin d) (Fin d) ℂ) : compressionMap V A = Vᴴ * A * V := by
    simp only [compressionMap, MatrixMap.of_kraus, LinearMap.sum_apply,
      LinearMap.coe_mk, AddHom.coe_mk, Matrix.conjTranspose_conjTranspose,
      Fintype.sum_unique]
  refine ⟨MatrixMap.of_kraus_isCompletelyPositive (fun _ : Unit => Vᴴ), ?_, hA⟩
  rw [hA, Matrix.mul_one, hV]

private theorem heisenberg_kraus {d n : ℕ}
    (Φ : MatrixMap (Fin d) (Fin n) ℂ) (hCP : Φ.IsCompletelyPositive) (hu : Φ 1 = 1) :
    ∃ K : (Fin n × Fin d) → Matrix (Fin d) (Fin n) ℂ,
      (∑ r, (K r)ᴴ * K r) = 1 ∧ ∀ A, Φ A = ∑ r, (K r)ᴴ * A * K r := by
  sorry

private theorem isometric_factorization {d n : ℕ} (hnd : n ≤ d)
    (K : Matrix (Fin d) (Fin n) ℂ) :
    ∃ (V : Matrix (Fin d) (Fin n) ℂ) (C : Matrix (Fin n) (Fin n) ℂ),
      Vᴴ * V = 1 ∧ K = V * C := by
  sorry

private theorem sum_compressed_parents {n : ℕ} {X R : Type} [Fintype X] [Fintype R]
    {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (C : R → Matrix (Fin n) (Fin n) ℂ)
    (N : R → (x : X) → Ω x → Matrix (Fin n) (Fin n) ℂ)
    (hC : (∑ r, (C r)ᴴ * C r) = 1)
    (hN : ∀ r, FamilyJointlyMeasurable (N r)) :
    FamilyJointlyMeasurable (fun x b => ∑ r, (C r)ᴴ * N r x b * C r) := by
  sorry

private theorem channels_of_compressions {d n : ℕ} (hnd : n ≤ d)
    {X : Type} [Fintype X] {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ V : Matrix (Fin d) (Fin n) ℂ, Vᴴ * V = 1 →
      FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V))
    (Φ : MatrixMap (Fin d) (Fin n) ℂ) (hCP : Φ.IsCompletelyPositive) (hu : Φ 1 = 1) :
    FamilyJointlyMeasurable (fun x b => Φ (M x b)) := by
  obtain ⟨K, hK, hΦ⟩ := heisenberg_kraus Φ hCP hu
  choose V C hV hfactor using fun r => isometric_factorization hnd (K r)
  have hC : (∑ r, (C r)ᴴ * C r) = 1 := by
    sorry
  have hp := sum_compressed_parents C (fun r x b => (V r)ᴴ * M x b * V r) hC
    (fun r => hM (V r) (hV r))
  have heq : (fun x b => ∑ r, (C r)ᴴ * ((V r)ᴴ * M x b * V r) * C r) =
      (fun x b => Φ (M x b)) := by
    sorry
  rw [heq] at hp
  exact hp

private theorem compressions_of_channels {d n : ℕ}
    {X : Type} [Fintype X] {Ω : X → Type} [∀ x, Fintype (Ω x)]
    (M : (x : X) → Ω x → Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ Φ : MatrixMap (Fin d) (Fin n) ℂ, Φ.IsCompletelyPositive → Φ 1 = 1 →
      FamilyJointlyMeasurable (fun x b => Φ (M x b)))
    (V : Matrix (Fin d) (Fin n) ℂ) (hV : Vᴴ * V = 1) :
    FamilyJointlyMeasurable (fun x b => Vᴴ * M x b * V) := by
  obtain ⟨hCP, hu, hA⟩ := compression_channel V hV
  have hp := hM (compressionMap V) hCP hu
  have heq : (fun x b => compressionMap V (M x b)) =
      (fun x b => Vᴴ * M x b * V) := funext fun x => funext fun b => hA (M x b)
  rw [heq] at hp
  exact hp

/-- Every isometric compression is compatible exactly when every Heisenberg image is. -/
theorem result : claim := by
  intro d n _ hnd X _ Ω _ M _
  exact ⟨channels_of_compressions hnd M, compressions_of_channels M⟩

end D5.S3.Quantum.QuantumChannels.HeisenbergChannelCompressionEquivalence
