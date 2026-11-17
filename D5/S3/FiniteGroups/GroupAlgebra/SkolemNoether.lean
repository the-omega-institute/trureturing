/- GID: D5/S3/FiniteGroups/GroupAlgebra/SkolemNoether
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/GroupAlgebra/SkolemNoether
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Attributed Skolem-Noether automorphism theorem for finite central simple algebras. -/

/-
Classical algebra proofs used for the actual finite-group representation image.
Proof attribution: AxiomMath/Stacks contributors, Apache-2.0 (see upstream/LICENSE).
Pinned revision: 5ed82d14634e8d9576bb844c7bd4e3da66d450e7
Upstream: StacksCore/RingTheory/SkolemNoether.lean
SHA-256: 28e02088adb5705d79804feb8c7c581fa11005fcbd5ccc984b9c394936581a39
The pinned source files contain no individual author or copyright notices.
Retirement: when the Mathlib revision pinned in this repository's lake-manifest.json
provides equivalents of this namespace's `skolemNoether` and `skolemNoether'`,
replace the corresponding fragments with direct Mathlib reuse and remove unused
transplants. Required scope: any field K, finite-dimensional central simple
K-algebra A and simple K-algebra B, with no assumed finiteness of B; any two
K-algebra maps f, g : B →ₐ[K] A are conjugate by a unit of A. In particular every
K-algebra automorphism of A is inner, with no restriction on the characteristic.
-/

import Mathlib.Algebra.Azumaya.Defs
import D5.S3.FiniteGroups.GroupAlgebra.Morita.SimpleRing
import D5.S3.FiniteGroups.GroupAlgebra.SimpleRing.TensorProduct

namespace D5.S3.RingTheory.SkolemNoether

open D5.S3.RingTheory.Morita.SimpleRing

universe u v

open scoped TensorProduct

namespace SkolemNoether

variable (K : Type u) (A B : Type v) [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

/-- The algebra map `B ⊗[K] Aᵐᵒᵖ →ₐ[K] End K A` sending `b ⊗ aᵒᵖ` to `x ↦ f b * x * a`,
twisting the left-multiplication part of `AlgHom.mulLeftRight` by `f`. -/
private def Algebra.tensorMopToEnd (f : B →ₐ[K] A) : B ⊗[K] Aᵐᵒᵖ →ₐ[K] Module.End K A :=
  (AlgHom.mulLeftRight K A).comp (Algebra.TensorProduct.map f (AlgHom.id K Aᵐᵒᵖ))

private lemma Algebra.tensorMopToEnd_tmul (f : B →ₐ[K] A) (b : B) (a : Aᵐᵒᵖ) (x : A) :
    Algebra.tensorMopToEnd K A B f (b ⊗ₜ[K] a) x = f b * x * a.unop := by
  simp [Algebra.tensorMopToEnd, AlgHom.mulLeftRight_apply]

/-- `A`, regarded as a `B ⊗[K] Aᵐᵒᵖ`-module through `f : B →ₐ[K] A`:
`(b ⊗ aᵒᵖ) • x = f b * x * a`. -/
@[nolint unusedArguments]
private def Twist (_ : B →ₐ[K] A) : Type v := A
  deriving AddCommGroup, Module K

namespace Twist

variable (f : B →ₐ[K] A)

private instance : Module (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  Module.compHom A (Algebra.tensorMopToEnd K A B f).toRingHom

/-- The identity map `A → Twist K A B f`. -/
private def mk (x : A) : Twist K A B f := x

/-- The identity map `Twist K A B f → A`. -/
private def val (x : Twist K A B f) : A := x

private lemma val_injective : Function.Injective (val K A B f) := fun _ _ h ↦ h

variable {K A B f}

@[simp] private lemma val_mk (x : A) : val K A B f (mk K A B f x) = x := rfl

@[simp] private lemma mk_val (x : Twist K A B f) : mk K A B f (val K A B f x) = x := rfl

private lemma val_smul (r : B ⊗[K] Aᵐᵒᵖ) (x : Twist K A B f) :
    val K A B f (r • x) = Algebra.tensorMopToEnd K A B f r (val K A B f x) := rfl

@[simp] private lemma val_one_op_smul (a : A) (x : Twist K A B f) :
    val K A B f (((1 : B) ⊗ₜ[K] MulOpposite.op a) • x) = val K A B f x * a := by
  rw [val_smul, Algebra.tensorMopToEnd_tmul, map_one, one_mul, MulOpposite.unop_op]

@[simp] private lemma val_tmul_one_smul (b : B) (x : Twist K A B f) :
    val K A B f ((b ⊗ₜ[K] (1 : Aᵐᵒᵖ)) • x) = f b * val K A B f x := by
  rw [val_smul, Algebra.tensorMopToEnd_tmul, MulOpposite.unop_one, mul_one]

@[simp] private lemma one_op_smul_mk (a x : A) :
    ((1 : B) ⊗ₜ[K] MulOpposite.op a) • mk K A B f x = mk K A B f (x * a) :=
  val_injective K A B f (val_one_op_smul a _)

@[simp] private lemma tmul_one_smul_mk (b : B) (x : A) :
    (b ⊗ₜ[K] (1 : Aᵐᵒᵖ)) • mk K A B f x = mk K A B f (f b * x) :=
  val_injective K A B f (val_tmul_one_smul b _)

variable (K A B f)

private instance : IsScalarTower K (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  .of_algebraMap_smul fun k x ↦ by
    have h : val K A B f (algebraMap K (B ⊗[K] Aᵐᵒᵖ) k • x) = k • val K A B f x := by
      rw [val_smul, AlgHom.commutes]
      exact Module.algebraMap_end_apply K K A k (val K A B f x)
    exact h

private instance [Module.Finite K A] : Module.Finite K (Twist K A B f) :=
  inferInstanceAs (Module.Finite K A)

private instance [Module.Finite K A] : Module.Finite (B ⊗[K] Aᵐᵒᵖ) (Twist K A B f) :=
  Module.Finite.of_restrictScalars_finite K _ _

end Twist

variable {K A B}

/-- A `B ⊗[K] Aᵐᵒᵖ`-linear map between twisted regular representations commutes with right
multiplication, hence is left multiplication by its value at `1`. -/
private lemma val_apply_mk {f g : B →ₐ[K] A}
    (φ : Twist K A B f ≃ₗ[B ⊗[K] Aᵐᵒᵖ] Twist K A B g) (x : A) :
    Twist.val K A B g (φ (Twist.mk K A B f x))
      = Twist.val K A B g (φ (Twist.mk K A B f 1)) * x := by
  simpa using congrArg (Twist.val K A B g)
    (φ.map_smul ((1 : B) ⊗ₜ[K] MulOpposite.op x) (Twist.mk K A B f 1))

private lemma mul_val_symm_eq_one {f g : B →ₐ[K] A}
    (φ : Twist K A B f ≃ₗ[B ⊗[K] Aᵐᵒᵖ] Twist K A B g) :
    Twist.val K A B g (φ (Twist.mk K A B f 1))
      * Twist.val K A B f (φ.symm (Twist.mk K A B g 1)) = 1 := by
  rw [← val_apply_mk φ, Twist.mk_val, LinearEquiv.apply_symm_apply, Twist.val_mk]

end SkolemNoether

open SkolemNoether in
/-- **Skolem–Noether**: two algebra homomorphisms from a simple algebra to a
finite-dimensional central simple algebra are conjugate by a unit. -/
@[stacks 074Q]
private theorem skolemNoether (K : Type u) (A B : Type v) [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] [Algebra.IsCentral K A] [IsSimpleRing A]
    [Ring B] [Algebra K B] [IsSimpleRing B] (f g : B →ₐ[K] A) :
    ∃ x : Aˣ, ∀ b : B, g b = x * f b * x⁻¹ := by
  have hf : Function.Injective f :=
    (IsSimpleRing.injective_ringHom_or_subsingleton_codomain f.toRingHom).resolve_right
      (not_subsingleton A)
  have : Module.Finite K B := .of_injective f.toLinearMap hf
  obtain ⟨φ⟩ := (linearEquiv_iff_finrank_eq_over_simple_ring K (B ⊗[K] Aᵐᵒᵖ)
    (Twist K A B f) (Twist K A B g)).2 rfl
  refine ⟨⟨_, _, mul_val_symm_eq_one φ, mul_val_symm_eq_one φ.symm⟩, fun b ↦ ?_⟩
  rw [Units.eq_mul_inv_iff_mul_eq, ← val_apply_mk φ (f b), ← mul_one (f b),
    ← Twist.tmul_one_smul_mk, map_smul]
  simp

@[stacks 074R]
theorem skolemNoether' (K : Type u) (A : Type v) [Field K] [Ring A] [Algebra K A]
    [Module.Finite K A] [Algebra.IsCentral K A] [IsSimpleRing A] (e : A ≃ₐ[K] A) :
    ∃ x : Aˣ, ∀ a : A, e a = x * a * x⁻¹ := by
  simpa using skolemNoether K A A (AlgHom.id K A) e.toAlgHom

end D5.S3.RingTheory.SkolemNoether
