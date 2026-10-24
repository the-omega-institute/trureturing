/- GID: D5/S3/Quantum/Algebra/InvariantFormProportionality
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/InvariantFormProportionality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.BilinearForm.Properties]
   utility: none
   digest: Scalar commutant forces unique proportionality of invariant bilinear forms. -/

import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Invariant bilinear forms from a scalar commutant. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Quantum.Algebra.InvariantFormProportionality

universe u v w

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- On a representation with scalar commutant, an invariant bilinear form is
a unique scalar multiple of any fixed nonzero nondegenerate invariant form.
The actual work is the equivariance of `B.toDual.symm ∘ C`.
The field need not be algebraically closed when scalar commutant is supplied.

proof_shape: content. Literature: classical Schur/duality argument.
Consumer: the private comparison of original ground pairings in
`ActualChosenFormSymmetry`, used to prove symmetry of the unchanged actualForm.
-/
theorem invariant_forms_proportional_of_scalar_commutant
    (ρ : Representation k Γ V) (B C : LinearMap.BilinForm k V)
    (hB : B.Nondegenerate) (hB0 : B ≠ 0)
    (hBinv : ∀ (g : Γ) (u v : V), B (ρ g u) (ρ g v) = B u v)
    (hCinv : ∀ (g : Γ) (u v : V), C (ρ g u) (ρ g v) = C u v)
    (scalar_commutant : ∀ T : Module.End k V,
      (∀ g : Γ, T * ρ g = ρ g * T) →
        ∃ c : k, T = c • (1 : Module.End k V)) :
    ∃! c : k, C = c • B := by
  let T : Module.End k V := C.symmCompOfNondegenerate B hB
  have comparison (u v : V) : B (T u) v = C u v := by
    exact C.symmCompOfNondegenerate_left_apply hB v u
  have inverse (g : Γ) (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have commutes (g : Γ) : T * ρ g = ρ g * T := by
    apply LinearMap.ext
    intro u
    apply (B.toDual hB).injective
    apply LinearMap.ext
    intro v
    change B (T (ρ g u)) v = B (ρ g (T u)) v
    calc
      B (T (ρ g u)) v = C (ρ g u) v := comparison _ _
      _ = C (ρ g u) (ρ g (ρ g⁻¹ v)) := by rw [inverse g v]
      _ = C u (ρ g⁻¹ v) := hCinv g u (ρ g⁻¹ v)
      _ = B (T u) (ρ g⁻¹ v) := (comparison _ _).symm
      _ = B (ρ g (T u)) (ρ g (ρ g⁻¹ v)) :=
        (hBinv g (T u) (ρ g⁻¹ v)).symm
      _ = B (ρ g (T u)) v := by rw [inverse g v]
  obtain ⟨c, hT⟩ := scalar_commutant T commutes
  have hform : C = c • B := by
    apply LinearMap.ext
    intro u
    apply LinearMap.ext
    intro v
    change C u v = c * B u v
    calc
      C u v = B (T u) v := (comparison _ _).symm
      _ = B ((c • (1 : Module.End k V)) u) v := by rw [hT]
      _ = c * B u v := by
        change B (c • u) v = c * B u v
        rw [LinearMap.BilinForm.smul_left]
  refine ⟨c, hform, ?_⟩
  intro d hd
  have annihilates : (d - c) • B = 0 := by
    rw [sub_smul, ← hd, ← hform, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp annihilates).resolve_right hB0)

#print axioms invariant_forms_proportional_of_scalar_commutant

end D5.S3.Quantum.Algebra.InvariantFormProportionality

end
