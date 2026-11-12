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

namespace principal_inverse_sqrt_laws

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.principal_inverse_sqrt_laws.{u,v})

def arena : Arena where
  signature := relationSignature.{max u v}
  Law O := ∀ {𝕜 : Type u} {ι : Type v}
    [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) (hA : A.PosDef),
    let S := CFC.sqrt A⁻¹
    S.IsHermitian ∧ IsUnit S ∧
      O.readout () ⟨Matrix ι ι 𝕜, Eq⟩ (S * S) A⁻¹ ∧ S * A * S = 1

theorem source_bridge : sourceScope.{u,v} ↔ arena.{u,v}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u,v}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.OriginalUnitSupport.principal_inverse_sqrt_laws.{u,v})

end principal_inverse_sqrt_laws

end Reg.D5.S3.Quantum.Foundation.OriginalUnitSupport
