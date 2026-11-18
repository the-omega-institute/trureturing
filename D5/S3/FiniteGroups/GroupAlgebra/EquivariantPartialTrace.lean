/- GID: D5/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace
   generality: E
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/EquivariantPartialTrace
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Trace, mathlib/module/Mathlib.RepresentationTheory.Intertwining]
   utility: none
   digest: Equivariant partial trace and tensor stability of trace-zero pairings over arbitrary fields. -/

module

public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Intertwining

/-!
The right partial trace contracts a finite-dimensional tensor factor by its ordinary trace.
It preserves intertwiners and transfers the trace pairing across a tensor product over any field.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe uK uG uA uB uC

namespace LinearMap

variable {K : Type uK} [Field K]
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [AddCommGroup A] [Module K A] [FiniteDimensional K A]
variable [AddCommGroup B] [Module K B]
variable [AddCommGroup C] [Module K C] [FiniteDimensional K C]

/-- Contract the right tensor factor of a linear map using its trace. -/
def rightPartialTrace : (A ⊗[K] C →ₗ[K] B ⊗[K] C) →ₗ[K] (A →ₗ[K] B) :=
  (TensorProduct.rid K (A →ₗ[K] B)).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id (LinearMap.trace K C) ∘ₗ
      (_root_.homTensorHomEquiv K A C B C).symm.toLinearMap

/-- On pure tensor maps, partial trace is scalar multiplication by the right trace. -/
theorem rightPartialTrace_map (f : A →ₗ[K] B) (t : C →ₗ[K] C) :
    rightPartialTrace (TensorProduct.map f t) = LinearMap.trace K C t • f := by
  change (TensorProduct.rid K (A →ₗ[K] B))
    (TensorProduct.map LinearMap.id (LinearMap.trace K C)
      ((_root_.homTensorHomEquiv K A C B C).symm (TensorProduct.map f t))) = _
  have h : TensorProduct.map f t =
      _root_.homTensorHomEquiv K A C B C (f ⊗ₜ[K] t) := by
    simp only [_root_.homTensorHomEquiv_apply, TensorProduct.homTensorHomMap_apply]
  rw [h, LinearEquiv.symm_apply_apply]
  simp

variable [FiniteDimensional K B] in
/-- The trace pairing contracts through the right partial trace. -/
theorem trace_comp_map_eq_trace_rightPartialTrace
    (F : A ⊗[K] C →ₗ[K] B ⊗[K] C) (d : B →ₗ[K] A) :
    LinearMap.trace K (B ⊗[K] C) (F ∘ₗ TensorProduct.map d LinearMap.id) =
      LinearMap.trace K B (rightPartialTrace F ∘ₗ d) := by
  obtain ⟨x, rfl⟩ := (_root_.homTensorHomEquiv K A C B C).surjective F
  induction x using TensorProduct.inductionOn with
  | tmul f t =>
      simp only [_root_.homTensorHomEquiv_apply,
        TensorProduct.homTensorHomMap_apply, ← TensorProduct.map_comp,
        LinearMap.comp_id, rightPartialTrace_map, LinearMap.smul_comp,
        LinearMap.trace_tensorProduct', map_smul, smul_eq_mul, mul_comm]
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_comp] at *
      rw [hx, hy]

/-- Changing the left maps and conjugating the contracted factor commutes with partial trace. -/
theorem rightPartialTrace_conjugate
    (F : A ⊗[K] C →ₗ[K] B ⊗[K] C)
    (a : A →ₗ[K] A) (b : B →ₗ[K] B) (c c' : C →ₗ[K] C)
    (hc : c' ∘ₗ c = LinearMap.id) :
    rightPartialTrace (TensorProduct.map b c ∘ₗ F ∘ₗ TensorProduct.map a c') =
      b ∘ₗ rightPartialTrace F ∘ₗ a := by
  have ht (t : C →ₗ[K] C) :
      LinearMap.trace K C (c ∘ₗ t ∘ₗ c') = LinearMap.trace K C t := by
    rw [← LinearMap.comp_assoc, LinearMap.trace_comp_comm',
      ← LinearMap.comp_assoc, hc, LinearMap.id_comp]
  obtain ⟨x, rfl⟩ := (_root_.homTensorHomEquiv K A C B C).surjective F
  induction x using TensorProduct.inductionOn with
  | tmul f t =>
      simp only [_root_.homTensorHomEquiv_apply,
        TensorProduct.homTensorHomMap_apply, ← TensorProduct.map_comp,
        rightPartialTrace_map, ht, LinearMap.smul_comp, LinearMap.comp_smul]
  | add x y hx hy =>
      simp only [map_add, LinearMap.add_comp, LinearMap.comp_add] at *
      rw [hx, hy]

end LinearMap

namespace Representation.IntertwiningMap

variable {K : Type uK} [Field K] {G : Type uG} [Group G]
variable {A : Type uA} {B : Type uB} {C : Type uC}
variable [AddCommGroup A] [Module K A] [FiniteDimensional K A]
variable [AddCommGroup B] [Module K B]
variable [AddCommGroup C] [Module K C] [FiniteDimensional K C]
variable {ρ : Representation K G A} {σ : Representation K G B}
variable {τ : Representation K G C}

/-- Partial trace of an intertwiner, with equivariance derived from the group actions. -/
def rightPartialTrace (F : (ρ.tprod τ).IntertwiningMap (σ.tprod τ)) :
    ρ.IntertwiningMap σ where
  toLinearMap := LinearMap.rightPartialTrace F.toLinearMap
  isIntertwining' g := by
    have hc : τ g⁻¹ ∘ₗ τ g = LinearMap.id := by
      ext x
      exact τ.inv_self_apply g x
    have hF : TensorProduct.map (σ g) (τ g) ∘ₗ F.toLinearMap ∘ₗ
        TensorProduct.map (ρ g⁻¹) (τ g⁻¹) = F.toLinearMap := by
      rw [← Representation.tprod_apply, ← Representation.tprod_apply,
        ← LinearMap.comp_assoc, ← F.isIntertwining' g, LinearMap.comp_assoc]
      have hi : (ρ.tprod τ) g ∘ₗ (ρ.tprod τ) g⁻¹ = LinearMap.id :=
        LinearMap.ext ((ρ.tprod τ).self_inv_apply g)
      rw [hi, LinearMap.comp_id]
    have hp := LinearMap.rightPartialTrace_conjugate F.toLinearMap
      (ρ g⁻¹) (σ g) (τ g) (τ g⁻¹) hc
    rw [hF] at hp
    have hi : ρ g⁻¹ ∘ₗ ρ g = LinearMap.id := by
      ext x
      exact ρ.inv_self_apply g x
    have h := congrArg (fun f : A →ₗ[K] B => f ∘ₗ ρ g) hp
    simpa only [LinearMap.comp_assoc, hi, LinearMap.comp_id] using h

variable [FiniteDimensional K B] in
/-- A map annihilated by every equivariant trace pairing keeps that property after tensoring.
No inverse of the dimension of the tensor factor is used. -/
theorem trace_pairing_zero_rTensor
    (d : ρ.IntertwiningMap σ)
    (hd : ∀ g : σ.IntertwiningMap ρ,
      LinearMap.trace K A (g.toLinearMap ∘ₗ d.toLinearMap) = 0)
    (F : (σ.tprod τ).IntertwiningMap (ρ.tprod τ)) :
    LinearMap.trace K (A ⊗[K] C)
      (F.toLinearMap ∘ₗ (d.rTensor τ).toLinearMap) = 0 := by
  change LinearMap.trace K (A ⊗[K] C)
    (F.toLinearMap ∘ₗ TensorProduct.map d.toLinearMap LinearMap.id) = 0
  rw [LinearMap.trace_comp_map_eq_trace_rightPartialTrace]
  exact hd F.rightPartialTrace

end Representation.IntertwiningMap
