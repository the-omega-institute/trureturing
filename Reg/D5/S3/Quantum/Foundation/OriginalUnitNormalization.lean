import D5.S3.Quantum.Foundation.OriginalUnitNormalization
import Reg.D5.S3.Quantum.Foundation.SectionROGFrame

/-! Whole-source reconstruction through equality on the actual native operands.
The original telescopes and existential witnesses are retained. These source
bridges and positivity proofs do not provide variation, sensitivity, dependence,
source selection or a completed four-slot registration. -/

noncomputable section
universe u v w
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.OriginalUnitSupport
open _root_.D5.S3.Quantum.Foundation.OriginalUnitNormalization
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.SectionROGFrame

namespace Reg.D5.S3.Quantum.Foundation.OriginalUnitNormalization

namespace exists_original_unit_normalization

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitNormalization.exists_original_unit_normalization.{u,v,w})

set_option maxHeartbeats 1200000 in
def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} {V : Type w}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (hcompact : IsCompact {x : V | x ∈ C ∧ u x = 1})
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef),
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ Ψ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, O.readout () ⟨Matrix ι ι 𝕜, Eq⟩ (ρ x) (U * σ x * Uᴴ)) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ h : V, h ∈ C ∧ u h = (n : ℝ) ∧ (σ h).PosDef ∧
          (∀ v : V, ((σ h)⁻¹ * σ v).trace = (u v : 𝕜)) ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ h).det) ∧
          (∀ k ∈ C, u k = (n : ℝ) →
            (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ k).det) →
            k = h) ∧
          let S := CFC.sqrt (σ h)⁻¹
          S.IsHermitian ∧ IsUnit S ∧ S * S = (σ h)⁻¹ ∧
          (∀ v, Ψ v = S * σ v * S) ∧ Ψ h = 1 ∧
          Function.Injective Ψ ∧ (∀ v, (Ψ v).IsHermitian) ∧
          (∀ v, (Ψ v).trace = (u v : 𝕜)) ∧
          (∀ v, v ∈ C ↔ (Ψ v).PosSemidef) ∧
          (∀ v, (Ψ v).rank = (ρ v).rank) ∧
          (∀ v, ρ v = U * (S⁻¹ * Ψ v * S⁻¹) * Uᴴ) ∧
          (1 : Matrix (Fin n) (Fin n) 𝕜) ∈ Ψ.range ∧
          Ψ '' {v : V | v ∈ C ∧ u v = 1} =
            {X | X ∈ Ψ.range ∧ X.PosSemidef ∧ X.trace = 1} ∧
          (∀ x ∈ C,
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) ↔
            (∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (Ψ (y j)).rank = 1) ∧ Ψ x = ∑ j, Ψ (y j))) ∧
          ((∃ p : V, {v : V | v ∈ C ∧ u v = 1} = {p}) →
            (∀ x ∈ C, ∃ (k : ℕ) (y : Fin k → V),
              (∀ j, y j ∈ C ∧ (ρ (y j)).rank = 1) ∧ ρ x = ∑ j, ρ (y j)) → n = 1) ∧
          (n = 1 →
            {v : V | v ∈ C ∧ u v = 1} = {h} ∧
            ({v : V | v ∈ C ∧ u v = 1}).extremePoints ℝ = {h} ∧
            {f : V →ₗ[ℝ] ℝ | (∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v) ∧ f h = 1} = {u} ∧
            {v : V | (v ∈ C ∧ u v = 1) ∧ ∃ f : V →ₗ[ℝ] ℝ,
              (∀ w ∈ C, 0 ≤ f w ∧ f w ≤ u w) ∧ f h = 1 ∧ f v = 0} = ∅ ∧
            {f : V →ₗ[ℝ] ℝ | ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v} =
              {f | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ f = t • u}) ∧
          ∃ e : V ≃ₗ[ℝ] Ψ.range,
            (∀ v, (e v).val = Ψ v) ∧
            let K := {v : V | v ∈ C ∧ u v = 1}
            let Q := {X : Ψ.range | X.val.PosSemidef ∧ X.val.trace = 1}
            let d := e.symm.dualMap
            let O := fun f : V →ₗ[ℝ] ℝ => ∀ v ∈ C, 0 ≤ f v ∧ f v ≤ u v
            let N := fun g : Ψ.range →ₗ[ℝ] ℝ => ∀ X : Ψ.range,
              X.val.PosSemidef → 0 ≤ g X ∧ g X ≤ RCLike.re X.val.trace
            e '' K = Q ∧ e '' K.extremePoints ℝ = Q.extremePoints ℝ ∧
            (∀ F : Set V, Convex ℝ F ↔ Convex ℝ (e '' F)) ∧
            (∀ A B : Set V, IsExtreme ℝ A B ↔ IsExtreme ℝ (e '' A) (e '' B)) ∧
            (∀ A S : Set V,
              e '' {v | ∀ F : Set V, Convex ℝ F → IsExtreme ℝ A F → S ⊆ F → v ∈ F} =
              {X | ∀ G : Set Ψ.range, Convex ℝ G → IsExtreme ℝ (e '' A) G →
                e '' S ⊆ G → X ∈ G}) ∧
            (∀ f, O f ↔ N (d f)) ∧
            (∀ p, d '' {f | O f ∧ f p = 1} = {g | N g ∧ g (e p) = 1}) ∧
            (∀ p x,
              {r : ℝ | ∃ f, O f ∧ f p = 1 ∧ f x = r} =
              {r : ℝ | ∃ g, N g ∧ g (e p) = 1 ∧ g (e x) = r}) ∧
            (∀ p x,
              d '' {f | O f ∧ f p = 1 ∧ ∀ g, O g → g p = 1 → f x ≤ g x} =
              {g | N g ∧ g (e p) = 1 ∧ ∀ j, N j → j (e p) = 1 → g (e x) ≤ j (e x)}) ∧
            NativeGeometry C u Ψ h ∧ OriginalEffectGeometry C u ∧
            NativeAmbientDimensions n ∧ NativeCongruence σ Ψ S

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitNormalization.exists_original_unit_normalization.{u,v,w})

end exists_original_unit_normalization


end Reg.D5.S3.Quantum.Foundation.OriginalUnitNormalization
