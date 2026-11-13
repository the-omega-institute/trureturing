import D5.S3.Quantum.Foundation.NativePSDModel
import Reg.D5.S3.Quantum.Foundation.SectionROGFrame

/-! Exact laws retain the full native carrier, real dual and original all-pure
family. Lawful whole-family intervention and dependence evidence is unfinished. -/

noncomputable section
universe u
open scoped Matrix InnerProductSpace RealInnerProductSpace
open _root_.D5.S3.Quantum.Foundation
open CircuitBalancedConfirmation FacetZeroGluing OrthogonalJointCompletion SectionROGFrame
open RegularAnchorNormalChart RegularAnchorContactCriterion NativePSDModel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.D5.S3.Quantum.Foundation.SectionROGFrame

namespace Reg.D5.S3.Quantum.Foundation.NativePSDModel

namespace confirming_dominates

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.confirming_dominates.{u})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (v : EuclideanSpace ℂ d), ‖v‖ = 1 → ∀ E : HermitianMat d ℂ,
    0 ≤ E → E ≤ 1 → ⟪E, rankOne v⟫_ℝ = 1 →
    O.readout () ⟨HermitianMat d ℂ, (· ≤ ·)⟩ (rankOne v) E

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.confirming_dominates.{u})

end confirming_dominates

namespace whole_mixed_exclusion

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.whole_mixed_exclusion.{u})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (v : EuclideanSpace ℂ d), ‖v‖ = 1 →
    O.readout () ⟨Set (HermitianMat d ℂ), Eq⟩
      (exclusion cone unit (rankOne v))
      {X : HermitianMat d ℂ | 0 ≤ X ∧ X.trace = 1 ∧ ⟪rankOne v, X⟫_ℝ = 0}

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.whole_mixed_exclusion.{u})

end whole_mixed_exclusion

namespace whole_common_unique

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.whole_common_unique.{u})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (v : EuclideanSpace ℂ d), ‖v‖ = 1 → 1 < Fintype.card d →
    ∀ f : HermitianMat d ℂ →ₗ[ℝ] ℝ,
      common cone unit (rankOne v) f ↔
      O.readout () ⟨HermitianMat d ℂ →ₗ[ℝ] ℝ, Eq⟩ f (effect (rankOne v))

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.whole_common_unique.{u})

end whole_common_unique

namespace native_pure_iff

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.native_pure_iff.{u})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {d : Type u} [Fintype d] [DecidableEq d]
    (X : HermitianMat d ℂ), X ∈ pure cone unit ↔
    ∃ v : EuclideanSpace ℂ d, ‖v‖ = 1 ∧
      O.readout () ⟨HermitianMat d ℂ, Eq⟩ (rankOne v) X

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.native_pure_iff.{u})

end native_pure_iff

namespace native_exclusion_injective

abbrev sourceScope : Prop := type_of% (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.native_exclusion_injective.{u})

def arena : Arena where
  signature := relationSignature.{u}
  Law O := ∀ {d : Type u} [Fintype d] [DecidableEq d],
    1 < Fintype.card d → ∀ p q : pure (cone (d := d)) unit,
      exclusion cone unit p = exclusion cone unit q →
      O.readout () ⟨pure (cone (d := d)) unit, Eq⟩ p q

theorem source_bridge : sourceScope.{u} ↔ arena.{u}.Law relationActual := Iff.rfl

theorem actual_positive : arena.{u}.Law relationActual :=
  source_bridge.mp (@_root_.D5.S3.Quantum.Foundation.NativePSDModel.native_exclusion_injective.{u})

end native_exclusion_injective


namespace vzero_unit

abbrev sourceScope : Prop := type_of% _root_.D5.S3.Quantum.Foundation.NativePSDModel.vzero_unit

def arena : Arena where
  signature := relationSignature.{0}
  Law O := O.readout () ⟨ℝ, Eq⟩ ‖vzero‖ 1

theorem source_bridge : sourceScope ↔ arena.Law relationActual := Iff.rfl

theorem actual_positive : arena.Law relationActual :=
  source_bridge.mp _root_.D5.S3.Quantum.Foundation.NativePSDModel.vzero_unit

end vzero_unit

namespace native_EB3

abbrev sourceScope : Prop := type_of% _root_.D5.S3.Quantum.Foundation.NativePSDModel.native_EB3

def arena : Arena where
  signature := relationSignature.{0}
  Law O := ∀ p : pure (cone (d := Fin 3)) unit,
    ∃ f : ThreeSpace →ᵃ[ℝ] HermitianMat (Fin 3) ℂ,
      Function.Injective f ∧
      O.readout () ⟨Set (HermitianMat (Fin 3) ℂ), Eq⟩
        (f '' Metric.closedBall 0 1) (exclusion cone unit p)

theorem source_bridge : sourceScope ↔ arena.Law relationActual := by
  constructor
  · intro h p
    obtain ⟨a⟩ := h p
    exact ⟨a.param, a.injective, a.whole⟩
  · intro h p
    obtain ⟨f, hf, hwhole⟩ := h p
    exact ⟨⟨f, hf, hwhole⟩⟩

theorem actual_positive : arena.Law relationActual :=
  source_bridge.mp _root_.D5.S3.Quantum.Foundation.NativePSDModel.native_EB3

end native_EB3

namespace original_family_inhabited

abbrev sourceScope : Prop :=
  type_of% _root_.D5.S3.Quantum.Foundation.NativePSDModel.original_family_inhabited

def arena : Arena where
  signature := relationSignature.{0}
  Law O := ∃ (p : pure (cone (d := Fin 3)) unit)
      (e : HermitianMat (Fin 3) ℂ →ₗ[ℝ] ℝ)
      (a : FullBall3Chart cone unit p),
      IsClosed (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) ∧
      (∀ X ∈ cone (d := Fin 3), X ≠ 0 → 0 < unit X) ∧
      Submodule.span ℝ (cone (d := Fin 3) : Set (HermitianMat (Fin 3) ℂ)) = ⊤ ∧
      EB3 (cone (d := Fin 3)) unit ∧
      Function.Injective (fun q : pure (cone (d := Fin 3)) unit => exclusion cone unit q) ∧
      common cone unit p e ∧ Regular cone unit p ∧
      ∃ n : NativeChart cone unit p e a,
        O.readout () ⟨NativeChart cone unit p e a, fun x _ => ContactCriterion x⟩ n n

theorem source_bridge : sourceScope ↔ arena.Law relationActual := Iff.rfl

theorem actual_positive : arena.Law relationActual :=
  source_bridge.mp _root_.D5.S3.Quantum.Foundation.NativePSDModel.original_family_inhabited

end original_family_inhabited


end Reg.D5.S3.Quantum.Foundation.NativePSDModel
