/- GID: D5/S3/Quantum/Algebra/AuricActualOcticWindow
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/AuricActualOcticWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual arbitrary-field window operators for the octic cut-free theorem. -/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.Tactic

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace D5.S3.Quantum.Algebra.AuricActualOcticWindow

open Module LinearMap
open scoped TensorProduct

variable {F D : Type*} [Field F] [Field D] [Algebra F D]

/-- The original quotient set, including zero whenever the window is nonzero. -/
def quotientSet (W : Submodule F D) : Set D :=
  {a | ∃ u ∈ W, ∃ v ∈ W, v ≠ 0 ∧ a = u / v}

/-- Multiplication in the original field followed by its actual quotient map. -/
def obstruction (W : Submodule F D) (a : D) : W →ₗ[F] D ⧸ W :=
  W.mkQ ∘ₗ (LinearMap.mulLeft F a) ∘ₗ W.subtype

private theorem obstruction_injective (W : Submodule F D) {a : D}
    (ha : a ∉ quotientSet W) : Function.Injective (obstruction W a) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm
  · intro w hw
    have haw : a * (w : D) ∈ W := by
      simpa [obstruction, Submodule.Quotient.eq_zero_iff_mem] using hw
    have hw0 : (w : D) = 0 := by
      by_contra hn
      exact ha ⟨a * w, haw, w, w.property, hn, (mul_div_cancel_right₀ a hn).symm⟩
    simpa using hw0
  · exact bot_le

private def obstructionEquiv [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) : W ≃ₗ[F] D ⧸ W :=
  LinearEquiv.ofBijective (obstruction W a)
    ⟨obstruction_injective W ha,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
        have h := W.finrank_quotient_add_finrank
        omega)).mp (obstruction_injective W ha)⟩

/-- The original operator i_W A_W(a)⁻¹ π_W; no normalization of W is used. -/
private def actualOperator [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) : D →ₗ[F] D :=
  W.subtype ∘ₗ (obstructionEquiv W hD hW a ha).symm.toLinearMap ∘ₗ W.mkQ

private theorem actualOperator_kernel [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    LinearMap.ker (actualOperator W hD hW a ha) = W := by
  ext x
  change (↑((obstructionEquiv W hD hW a ha).symm (W.mkQ x)) : D) = 0 ↔ x ∈ W
  rw [Submodule.coe_eq_zero, (obstructionEquiv W hD hW a ha).symm.map_eq_zero_iff,
    Submodule.Quotient.eq_zero_iff_mem]

private theorem actualOperator_range [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    LinearMap.range (actualOperator W hD hW a ha) = W := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ((obstructionEquiv W hD hW a ha).symm (W.mkQ y)).property
  · intro hx
    obtain ⟨y, hy⟩ := W.mkQ_surjective ((obstructionEquiv W hD hW a ha) ⟨x, hx⟩)
    refine ⟨y, ?_⟩
    change ↑((obstructionEquiv W hD hW a ha).symm (W.mkQ y)) = x
    rw [hy, LinearEquiv.symm_apply_apply]

private theorem actualOperator_square_zero [FiniteDimensional F D] (W : Submodule F D)
    (hD : finrank F D = 8) (hW : finrank F W = 4) (a : D)
    (ha : a ∉ quotientSet W) :
    (actualOperator W hD hW a ha).comp (actualOperator W hD hW a ha) = 0 := by
  ext x
  apply (LinearMap.mem_ker).mp
  rw [actualOperator_kernel]
  exact (actualOperator_range W hD hW a ha).le ⟨x, rfl⟩

end D5.S3.Quantum.Algebra.AuricActualOcticWindow
