import D5.S3.Quantum.Algebra.FullRectangularRecovery
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ComplexOrder
open D5.S3.Quantum.Algebra.FullRectangularRecovery
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Algebra.FullRectangularRecovery
universe u

/-- The algebra and its actual classes are parameters of every source family. -/
structure Parameters where
  A : Type u
  [algebra : CStarAlgebra A]
  [order : PartialOrder A]
  [starOrder : StarOrderedRing A]

attribute [instance] Parameters.algebra Parameters.order Parameters.starOrder

namespace Corner
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.A × p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ z => z.2 ∈ cornerSpace z.1) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (e x : p.A), IsStarProjection e →
    (R.readout () p (e,x) ↔ x = e * x * e)
theorem bridge : (type_of% (@corner_mem_iff.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p e x he
    exact h e he x
  · intro h A _ _ _ e he x
    exact h ⟨A⟩ e x he
end Corner

namespace PositiveReal
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := (p.A →P[ℂ] ℂ) × p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => z.1 z.2) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (φ : p.A →P[ℂ] ℂ) (a : p.A), IsSelfAdjoint a →
    R.readout () p (φ,a) = ((R.readout () p (φ,a)).re : ℂ)
theorem bridge : (type_of% (@positive_real.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end PositiveReal

namespace PositiveBounds
abbrev signature := PositiveReal.signature.{u}
def actual : Realization signature := PositiveReal.actual
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (φ : p.A →P[ℂ] ℂ) (a : p.A), IsSelfAdjoint a →
    -‖a‖ * (R.readout () p (φ,1)).re ≤ (R.readout () p (φ,a)).re ∧
      (R.readout () p (φ,a)).re ≤ ‖a‖ * (R.readout () p (φ,1)).re
theorem bridge : (type_of% (@positive_re_bounds.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end PositiveBounds

namespace Norming
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ a => ‖a‖) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (a : p.A), IsSelfAdjoint a → a ≠ 0 →
    ∃ (φ : p.A →P[ℂ] ℂ) (s : ℝ),
      φ 1 = 1 ∧ φ a = (s : ℂ) ∧ s ^ 2 = R.readout () p a ^ 2
theorem bridge : (type_of% (@exists_norming_state.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end Norming

namespace Multiplication
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := (p.A →P[ℂ] ℂ) × p.A × p.A
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun i _ z => if i then z.1 (z.2.2 * z.2.1) else z.1 (z.2.1 * z.2.2))
  (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (φ : p.A →P[ℂ] ℂ), φ 1 = 1 →
    ∀ (a : p.A), IsSelfAdjoint a → ∀ s : ℝ, φ a = (s : ℂ) → s ^ 2 = ‖a‖ ^ 2 →
      ∀ x : p.A, R.readout false p (φ,a,x) = (s : ℂ) * φ x ∧
        R.readout true p (φ,a,x) = (s : ℂ) * φ x
theorem bridge : (type_of% (@norming_state_multiplication.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    simpa only [actual, realize, Bool.false_eq_true, ↓reduceIte] using (@h p.A _ _ _)
  · intro h A _ _ _
    simpa only [actual, realize, Bool.false_eq_true, ↓reduceIte] using (h ⟨A⟩)
end Multiplication

namespace Sandwich
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := (p.A →P[ℂ] ℂ) × p.A × p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ _ z => z.1 (z.2.1 * z.2.2 * z.2.1)) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (φ : p.A →P[ℂ] ℂ), φ 1 = 1 →
    ∀ (a : p.A), IsSelfAdjoint a → ∀ s : ℝ, φ a = (s : ℂ) → s ^ 2 = ‖a‖ ^ 2 →
      ∀ C : p.A, R.readout () p (φ,a,C) = ((‖a‖ ^ 2 : ℝ) : ℂ) * φ C
theorem bridge : (type_of% (@norming_state_sandwich.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end Sandwich

namespace RowGram
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.A
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ U => U * star U) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (e U : p.A), IsStarProjection e → e * U = U →
    R.readout () p U ∈ cornerSpace e
theorem bridge : (type_of% (@rowGram_mem.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end RowGram

namespace Recovery
abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.A × p.A
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ z => ‖z.1 * z.2‖) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law R := ∀ (p : Parameters.{u}) (e f a U : p.A) (he : IsStarProjection e)
    (hf : IsStarProjection f) (ha : IsSelfAdjoint a) (hae : a = e * a * e)
    (hU : U = e * U * f) (κ : ℝ), 0 < κ →
    (∀ ω : CornerState e he,
      ‖ω.functional ⟨a, (corner_mem_iff e he a).2 hae⟩‖ ^ 2 ≤ κ *
        (ω.functional ⟨U * star U, rowGram_mem e U he (by
          have hee : e * e = e := he.isIdempotentElem
          calc
            e * U = e * (e * U * f) := congrArg (e * ·) hU
            _ = e * U * f := by simp only [← mul_assoc, hee]
            _ = U := hU.symm)⟩).re) →
    ‖a‖ ^ 2 / Real.sqrt κ ≤ R.readout () p (a,U)
theorem bridge : (type_of% (@full_rectangular_recovery.{u})) ↔ arena.Law actual := by
  constructor
  · intro h p
    exact @h p.A _ _ _
  · intro h A _ _ _
    exact h ⟨A⟩
end Recovery

end Reg.D5.S3.Quantum.Algebra.FullRectangularRecovery
