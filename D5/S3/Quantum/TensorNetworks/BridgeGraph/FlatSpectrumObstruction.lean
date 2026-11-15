/- GID: D5/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction
   generality: G
   mirror-B: D5/B/S3/Quantum/TensorNetworks/BridgeGraph/FlatSpectrumObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Kernel isolation for the native width-three scalar-Gram obstruction. -/

import D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker

noncomputable section

namespace D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction

open Matrix Module
open scoped ComplexConjugate

/-- The ordered-cone flat-spectrum assertion, with both Gram identities at equality. -/
def claim : Prop :=
  ∀ (a b c d : ℕ), 0 < a → a ≤ b → 0 < c → c ≤ d →
    a * a + b * b ≤ 3 * a * b → c * c + d * d ≤ 3 * c * d →
    ∃ (M : Fin 3 → Matrix (Fin a) (Fin b) ℂ)
      (N : Fin 3 → Matrix (Fin d) (Fin c) ℂ) (λ : ℝ), 0 < λ ∧
      (b * c ≤ a * d →
        (QuantumMaxFlowBound.flow M N)ᴴ * QuantumMaxFlowBound.flow M N =
          (λ : ℂ) • (1 : Matrix (Fin b × Fin c) (Fin b × Fin c) ℂ)) ∧
      (a * d ≤ b * c →
        QuantumMaxFlowBound.flow M N * (QuantumMaxFlowBound.flow M N)ᴴ =
          (λ : ℂ) • (1 : Matrix (Fin a × Fin d) (Fin a × Fin d) ℂ))

private def otherMap {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (r : Fin 3) :=
  LinearMap.pi (fun s : {s : Fin 3 // s ≠ r} => M s.val)

private theorem isolated_pair {a b : ℕ}
    (M : Fin 3 → EuclideanSpace ℂ (Fin b) →ₗ[ℂ] EuclideanSpace ℂ (Fin a))
    (hM : ∀ x, (∀ r, M r x = 0) → x = 0) (hab : 5 * a < 2 * b)
    (i j : Fin 3) :
    ∃ x y, (∀ r, r ≠ i → M r x = 0) ∧
      (∀ r, r ≠ j → M r y = 0) ∧ inner ℂ (M i x) (M j y) ≠ 0 := by
  classical
  let K (r : Fin 3) := LinearMap.ker (otherMap M r)
  let f (r : Fin 3) := (M r).domRestrict (K r)
  let L (r : Fin 3) := LinearMap.range (f r)
  have memK (r : Fin 3) (x : EuclideanSpace ℂ (Fin b)) :
      x ∈ K r ↔ ∀ s, s ≠ r → M s x = 0 := by
    simp [K, otherMap, LinearMap.mem_ker, funext_iff]
  have hf (r : Fin 3) : Function.Injective (f r) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot.mpr
    intro x hx
    apply Subtype.ext
    apply hM
    intro s
    by_cases hs : s = r
    · subst s
      exact hx
    · exact (memK r x.val).mp x.property s hs
  have hdim (r : Fin 3) : b ≤ finrank ℂ (L r) + 2 * a := by
    have hn := (otherMap M r).finrank_range_add_finrank_ker
    have hr := (otherMap M r).finrank_range_le
    have hc : Fintype.card {s : Fin 3 // s ≠ r} = 2 := by
      simp
    have hp : finrank ℂ ({s : Fin 3 // s ≠ r} → EuclideanSpace ℂ (Fin a)) = 2 * a := by
      simp [Module.finrank_pi_fintype, hc]
    rw [hp] at hr
    have he : finrank ℂ (L r) = finrank ℂ (K r) :=
      LinearMap.finrank_range_of_inj (hf r)
    simp only [finrank_euclideanSpace, Fintype.card_fin] at hn
    dsimp [K] at he
    omega
  by_contra h
  have hz : ∀ x : K i, ∀ y : K j, inner ℂ (f i x) (f j y) = 0 := by
    intro x y
    by_contra hxy
    exact h ⟨x.val, y.val, (memK i x.val).mp x.property,
      (memK j y.val).mp y.property, hxy⟩
  have hle : L j ≤ (L i)ᗮ := by
    rintro _ ⟨y, rfl⟩
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨x, rfl⟩
    exact hz x y
  have hd := Submodule.finrank_mono hle
  have ho := (L i).finrank_add_finrank_orthogonal
  simp only [finrank_euclideanSpace, Fintype.card_fin] at ho
  have hi := hdim i
  have hj := hdim j
  omega

end D5.S3.Quantum.TensorNetworks.BridgeGraph.FlatSpectrumObstruction
