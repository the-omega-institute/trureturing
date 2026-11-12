import D5.S3.Quantum.Foundation.OriginalUnitSupport
import Reg.D5.S3.Quantum.Foundation.SectionROGFrame

/-! Whole-source reconstruction through equality on the actual native operands.
The original telescopes and existential witnesses are retained. These source
bridges and positivity proofs do not provide variation, sensitivity, dependence,
source selection or a completed four-slot registration. -/

noncomputable section
universe u v w
open scoped Matrix BigOperators ComplexOrder MatrixOrder
open _root_.D5.S3.Quantum.Foundation.OriginalUnitSupport
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.SectionROGFrame

namespace Reg.D5.S3.Quantum.Foundation.OriginalUnitSupport

namespace exists_original_unit_full_support

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_full_support.{u,v,w})

set_option maxHeartbeats 1200000 in
def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} {V : Type w}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hpos : ∀ x ∈ C, (ρ x).PosSemidef),
    ∃ y : V, y ∈ C ∧ u y = 1 ∧
      (∀ z : ι → 𝕜, (ρ y) *ᵥ z = 0 ↔ ∀ x : V, (ρ x) *ᵥ z = 0) ∧
      O.readout () ⟨Submodule 𝕜 (EuclideanSpace 𝕜 ι), Eq⟩
        (ρ y).toEuclideanLin.range (commonSupport C ρ) ∧
      (∀ z : EuclideanSpace 𝕜 ι, z ∈ commonSupport C ρ → z ≠ 0 →
        0 < RCLike.re (star (z : ι → 𝕜) ⬝ᵥ ((ρ y) *ᵥ (z : ι → 𝕜))))

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_full_support.{u,v,w})

end exists_original_unit_full_support

namespace exists_original_unit_support_compression

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_support_compression.{u,v,w})

set_option maxHeartbeats 1200000 in
def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v} {V : Type w}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι] [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [Nontrivial V]
    (C : PointedCone ℝ V) (hgen : Submodule.span ℝ (C : Set V) = ⊤)
    (u : V →ₗ[ℝ] ℝ) (hu : ∀ x ∈ C, x ≠ 0 → 0 < u x)
    (ρ : V →ₗ[ℝ] Matrix ι ι 𝕜) (hρ : Function.Injective ρ)
    (hsection : ∀ x, x ∈ C ↔ (ρ x).PosSemidef),
    let n := Module.finrank 𝕜 (commonSupport C ρ)
    0 < n ∧ ∃ U : Matrix ι (Fin n) 𝕜,
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧
        (∀ x, O.readout () ⟨Matrix ι ι 𝕜, Eq⟩ (ρ x) (U * σ x * Uᴴ)) ∧ Function.Injective σ ∧
        (∀ x, (σ x).IsHermitian) ∧ (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧
        (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ y : V, y ∈ C ∧ u y = 1 ∧ (σ y).PosDef

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_support_compression.{u,v,w})

end exists_original_unit_support_compression

namespace exists_original_unit_determinant_maximum

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_determinant_maximum.{u,v,w})

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
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, O.readout () ⟨Matrix ι ι 𝕜, Eq⟩ (ρ x) (U * σ x * Uᴴ)) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        IsCompact (σ '' {x : V | x ∈ C ∧ u x = (n : ℝ)}) ∧
        ∃ m : V, m ∈ C ∧ u m = (n : ℝ) ∧ (σ m).PosDef ∧
          0 < RCLike.re (σ m).det ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ m).det) ∧
          (∀ v : V, HasDerivAt (fun t : ℝ => RCLike.re (σ (m + t • v)).det)
            (RCLike.re (σ m).det * RCLike.re ((σ m)⁻¹ * σ v).trace) 0) ∧
          let S := CFC.sqrt (σ m)⁻¹
          S.IsHermitian ∧ IsUnit S ∧ S * S = (σ m)⁻¹ ∧ S * σ m * S = 1

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_determinant_maximum.{u,v,w})

end exists_original_unit_determinant_maximum

namespace exists_original_unit_inverse_trace_stationarity

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_inverse_trace_stationarity.{u,v,w})

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
      ∃ σ : V →ₗ[ℝ] Matrix (Fin n) (Fin n) 𝕜,
        Uᴴ * U = 1 ∧ U.toEuclideanLin.range = commonSupport C ρ ∧
        (∀ x, σ x = Uᴴ * ρ x * U) ∧ (∀ x, O.readout () ⟨Matrix ι ι 𝕜, Eq⟩ (ρ x) (U * σ x * Uᴴ)) ∧
        Function.Injective σ ∧ (∀ x, (σ x).IsHermitian) ∧
        (∀ x, x ∈ C ↔ (σ x).PosSemidef) ∧ (∀ x, (σ x).rank = (ρ x).rank) ∧
        ∃ m : V, m ∈ C ∧ u m = (n : ℝ) ∧ (σ m).PosDef ∧
          (∀ v : V, ((σ m)⁻¹ * σ v).trace = (u v : 𝕜)) ∧
          (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ m).det) ∧
          (∀ k ∈ C, u k = (n : ℝ) →
            (∀ x ∈ C, u x = (n : ℝ) → RCLike.re (σ x).det ≤ RCLike.re (σ k).det) →
            k = m)

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_inverse_trace_stationarity.{u,v,w})

end exists_original_unit_inverse_trace_stationarity

namespace exists_original_unit_normalization

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_normalization.{u,v,w})

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
            (∀ f, O f ↔ N (d f)) ∧
            (∀ p, d '' {f | O f ∧ f p = 1} = {g | N g ∧ g (e p) = 1}) ∧
            (∀ p x,
              {r : ℝ | ∃ f, O f ∧ f p = 1 ∧ f x = r} =
              {r : ℝ | ∃ g, N g ∧ g (e p) = 1 ∧ g (e x) = r}) ∧
            (∀ p x,
              d '' {f | O f ∧ f p = 1 ∧ ∀ g, O g → g p = 1 → f x ≤ g x} =
              {g | N g ∧ g (e p) = 1 ∧ ∀ j, N j → j (e p) = 1 → g (e x) ≤ j (e x)})

set_option maxHeartbeats 1200000 in
theorem source_bridge : sourceScope.{u,v,w} ↔ arena.{u,v,w}.Law relationActual := Iff.rfl

set_option maxHeartbeats 1200000 in
theorem actual_positive : arena.{u,v,w}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.exists_original_unit_normalization.{u,v,w})

end exists_original_unit_normalization

end Reg.D5.S3.Quantum.Foundation.OriginalUnitSupport
