import D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy

open _root_.D5.S3.Arith.FibonacciAtomic
open Geometry.FiniteSourceMass
open Geometry.FiniteSourceHardy
open ActualTreeReadoutAcquisition (Address)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

/-- Each original clause has its actual unbounded parameter type. -/
abbrev State := (ℕ × Address) ⊕ ((Σ _ : ℕ × ℕ, H) ⊕ (ℕ × ℕ))

@[reducible] def signature : Signature where
  Params := Unit
  State _ := State
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

private def left : State → ℝ
  | .inl ⟨n,p⟩ => mass n p
  | .inr (.inl ⟨⟨n,h⟩,z⟩) => ‖J n (z-P h z)‖^2
  | .inr (.inr ⟨n,h⟩) => ‖(J n).comp (ContinuousLinearMap.id ℝ H-P h)‖

private def right : State → ℝ
  | .inl ⟨_,p⟩ => 2*Real.goldenRatio*a^p.length
  | .inr (.inl ⟨⟨_,h⟩,z⟩) => (2*Real.goldenRatio*a^(h+1)/(1-a))*‖z‖^2
  | .inr (.inr ⟨_,h⟩) => Real.sqrt (2*Real.goldenRatio*a^(h+1)/(1-a))

def actual : Realization signature := realize signature
  (fun i _ s => if i then right s else left s) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ s : State, R.readout false () s ≤ R.readout true () s

def leftBad : Realization signature := realize signature
  (fun i _ s => if i then right s else right s+1) (fun e => nomatch e)
def rightBad : Realization signature := realize signature
  (fun i _ s => if i then left s-1 else left s) (fun e => nomatch e)

private theorem left_bad : ¬ arena.Law leftBad := by
  intro h
  have he := h (.inl (0,[]))
  change right (.inl (0,[]))+1 ≤ right (.inl (0,[])) at he
  linarith
private theorem right_bad : ¬ arena.Law rightBad := by
  intro h
  have he := h (.inl (0,[]))
  change left (.inl (0,[])) ≤ left (.inl (0,[]))-1 at he
  linarith

/-- The complete coefficient, squared-tail and operator-norm telescope. -/
def familyRegistration : Registration arena (type_of% finite_source_hardy) := {
  actual := actual
  bridge := by
    constructor
    · intro h s
      rcases s with ⟨n,p⟩ | (⟨⟨n,k⟩,z⟩ | ⟨n,k⟩)
      · exact h.1 n p
      · exact h.2.1 n k z
      · exact h.2.2 n k
    · intro h
      exact ⟨fun n p => h (.inl (n,p)),
        fun n k z => h (.inr (.inl ⟨(n,k),z⟩)),
        fun n k => h (.inr (.inr (n,k)))⟩
  variation := ⟨by
    intro s
    rcases s with ⟨n,p⟩ | (⟨⟨n,k⟩,z⟩ | ⟨n,k⟩)
    · exact finite_source_hardy.1 n p
    · exact finite_source_hardy.2.1 n k z
    · exact finite_source_hardy.2.2 n k,
    leftBad, left_bad⟩
  sensitivity := ⟨by
    intro i
    cases i with
    | false =>
      refine ⟨leftBad, ?_, rfl, left_bad⟩
      intro j hj
      cases j
      · exact False.elim (hj rfl)
      · rfl
    | true =>
      refine ⟨rightBad, ?_, rfl, right_bad⟩
      intro j hj
      cases j
      · rfl
      · exact False.elim (hj rfl), fun e => nomatch e⟩
  dependence := by
    intro i
    cases i with
    | false =>
      refine ⟨(), .inl (0,[]), .inl (0,[false]), ?_⟩
      change mass 0 [] ≠ mass 0 [false]
      rw [(finite_source_masses.2.2.2.2.2.2.2.2 0).1,
        finite_source_masses.2.2.1 0 [false] (by rfl)]
      norm_num
    | true =>
      refine ⟨(), .inl (0,[]), .inr (.inl ⟨(0,0),(0:H)⟩), ?_⟩
      change 2*Real.goldenRatio*a^0 ≠ (2*Real.goldenRatio*a^1/(1-a))*‖(0:H)‖^2
      simp only [pow_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,mul_one]
      positivity
}

end Reg.D5.S3.Arith.FibonacciAtomic.Geometry.FiniteSourceHardy
