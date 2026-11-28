import D5.S3.Quantum.Gauge.E8RootSystemUnification4D
import Reg.Support.UnitSixO.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E8RootSystemUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots
set_option maxRecDepth 2048
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem zeroNotRoot : (0 : E8Ambient) ∉ e8Roots := by
  intro h
  have hh := e8Roots_simply_laced h
  norm_num at hh

private theorem simpleNonzero : e8SimpleRoot 0 ≠ 0 := by
  intro h
  exact zeroNotRoot (h ▸ e8_dynkin_simple_roots.1 0)

abbrev cardSignature : Signature := signature Unit (fun _ => Finset E8Ambient) (fun _ => ℕ)

abbrev cardArena : Arena where
  signature := cardSignature
  Law R := R.readout () () e8Roots = 240

def cardFamily : Registration cardArena (type_of% (@e8Roots_card)) :=
  unitFamily% cardArena (@e8Roots_card) (realize cardSignature (fun _ _ r => r.card) (fun e => nomatch e))
    (realize cardSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (fun h => (by decide : (0 : ℕ) ≠ 240) h)
    (by
      exact ⟨(), ∅, {0}, by simp [realize]⟩)

def cardRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8Roots_card) (Realization cardSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8Roots_card.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.cardFamily
    cardArena cardFamily (realize cardSignature (fun _ _ r => r.card) (fun e => nomatch e))
    #[]
    #[{ path := unitPath% e8Roots_card Finset.card 1 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

abbrev dimensionSignature : Signature := signature Unit (fun _ => Finset E8Ambient) (fun _ => ℕ)

abbrev dimensionArena : Arena where
  signature := dimensionSignature
  Law R := 8 + R.readout () () e8Roots = 248

def dimensionFamily : Registration dimensionArena (type_of% (@e8_lie_algebra_dimension)) :=
  unitFamily% dimensionArena (@e8_lie_algebra_dimension) (realize dimensionSignature (fun _ _ r => r.card) (fun e => nomatch e))
    (realize dimensionSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (fun h => (by decide : (8 : ℕ) + 0 ≠ 248) h)
    (by
      exact ⟨(), ∅, {0}, by simp [realize]⟩)

def dimensionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_lie_algebra_dimension) (Realization dimensionSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_lie_algebra_dimension.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.dimensionFamily
    dimensionArena dimensionFamily (realize dimensionSignature (fun _ _ r => r.card) (fun e => nomatch e))
    #[]
    #[{ path := unitPath% e8_lie_algebra_dimension Finset.card 1 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

abbrev normSignature : Signature := signature Unit (fun _ => E8Ambient) (fun _ => ℝ)

abbrev normArena : Arena where
  signature := normSignature
  Law R := ∀ {α : E8Ambient} (hα : α ∈ e8Roots),
    R.readout () () α = 2

def normFamily : Registration normArena (type_of% (@e8Roots_simply_laced)) :=
  unitFamily% normArena (@e8Roots_simply_laced) (realize normSignature (fun _ _ α => ⟪α, α⟫_ℝ) (fun e => nomatch e))
    (realize normSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h (e8_dynkin_simple_roots.1 0)
      change (0 : ℝ) = 2 at hh
      norm_num at hh)
    (by
      refine ⟨(), 0, e8SimpleRoot 0, ?_⟩
      change ⟪(0 : E8Ambient), 0⟫_ℝ ≠ ⟪e8SimpleRoot 0, e8SimpleRoot 0⟫_ℝ
      rw [e8Roots_simply_laced (e8_dynkin_simple_roots.1 0)]
      norm_num)

def normRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8Roots_simply_laced) (Realization normSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8Roots_simply_laced.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.normFamily
    normArena normFamily (realize normSignature (fun _ _ α => ⟪α, α⟫_ℝ) (fun e => nomatch e))
    #[]
    #[{ path := unitPath% e8Roots_simply_laced inner 5 0
        stateBinder := 0
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]

abbrev productsSignature : Signature := signature E8Ambient (fun _ => E8Ambient) (fun _ => ℝ)

abbrev productsArena : Arena where
  signature := productsSignature
  Law R := ∀ {α β : E8Ambient}
    (hα : α ∈ e8Roots) (hβ : β ∈ e8Roots),
    R.readout () α β ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪α, β⟫_ℝ = 2 ↔ α = β) ∧ (⟪α, β⟫_ℝ = -2 ↔ α = -β)

def productsFamily : Registration productsArena (type_of% (@e8Roots_crystallographic_inner_products)) :=
  unitFamily% productsArena (@e8Roots_crystallographic_inner_products) (realize productsSignature (fun _ α β => ⟪α, β⟫_ℝ) (fun e => nomatch e))
    (realize productsSignature (fun _ _ _ => 3) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (e8_dynkin_simple_roots.1 0) (e8_dynkin_simple_roots.1 0)).1
      change (3 : ℝ) ∈ ({-2, -1, 0, 1, 2} : Set ℝ) at hh
      norm_num at hh)
    (by
      refine ⟨e8SimpleRoot 0, 0, e8SimpleRoot 0, ?_⟩
      change ⟪e8SimpleRoot 0, (0 : E8Ambient)⟫_ℝ ≠ ⟪e8SimpleRoot 0, e8SimpleRoot 0⟫_ℝ
      rw [e8Roots_simply_laced (e8_dynkin_simple_roots.1 0)]
      norm_num)

def productsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8Roots_crystallographic_inner_products) (Realization productsSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8Roots_crystallographic_inner_products.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.productsFamily
    productsArena productsFamily (realize productsSignature (fun _ α β => ⟪α, β⟫_ℝ) (fun e => nomatch e))
    #[0]
    #[{ path := unitPath% e8Roots_crystallographic_inner_products inner 5 0
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]

abbrev reflectionSignature : Signature := signature E8Ambient (fun _ => E8Ambient) (fun _ => E8Ambient)

abbrev reflectionArena : Arena where
  signature := reflectionSignature
  Law R := ∀ {α β : E8Ambient}
    (hα : α ∈ e8Roots) (hβ : β ∈ e8Roots),
    R.readout () α β ∈ e8Roots ∧ -α ∈ e8Roots

def reflectionFamily : Registration reflectionArena (type_of% (@e8Roots_weyl_reflection_closed)) :=
  unitFamily% reflectionArena (@e8Roots_weyl_reflection_closed) (realize reflectionSignature (fun _ α β => β - ⟪α, β⟫_ℝ • α) (fun e => nomatch e))
    (realize reflectionSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      exact zeroNotRoot (h (e8_dynkin_simple_roots.1 0) (e8_dynkin_simple_roots.1 0)).1)
    (by
      refine ⟨0, 0, e8SimpleRoot 0, ?_⟩
      simpa [realize] using simpleNonzero.symm)

def reflectionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8Roots_weyl_reflection_closed) (Realization reflectionSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8Roots_weyl_reflection_closed.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.reflectionFamily
    reflectionArena reflectionFamily (realize reflectionSignature (fun _ α β => β - ⟪α, β⟫_ℝ • α) (fun e => nomatch e))
    #[0]
    #[{ path := unitPath% e8Roots_weyl_reflection_closed HSub.hSub 6 0
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }]

abbrev simpleSignature : Signature := signature Unit (fun _ => Fin 8) (fun _ => E8Ambient)

abbrev simpleArena : Arena where
  signature := simpleSignature
  Law R := (∀ i, R.readout () () i ∈ e8Roots) ∧
    (∀ i j, ⟪e8SimpleRoot i, e8SimpleRoot j⟫_ℝ = (e8Cartan i j : ℝ)) ∧
    e8Cartan.det = 1 ∧
    LinearIndependent ℝ e8SimpleRoot ∧
    (∀ α ∈ e8Roots, ∃ c : Fin 8 → ℤ, α = ∑ i, (c i : ℝ) • e8SimpleRoot i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0))) ∧
    (∀ i : Fin 6, e8SimpleRoot (i.castLE (by decide)) =
      _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6SimpleRoot i)

def simpleFamily : Registration simpleArena (type_of% (@e8_dynkin_simple_roots)) :=
  unitFamily% simpleArena (@e8_dynkin_simple_roots) (realize simpleSignature (fun _ _ => e8SimpleRoot) (fun e => nomatch e))
    (realize simpleSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      exact zeroNotRoot (h.1 0))
    (by
      refine ⟨(), 0, 1, ?_⟩
      change e8SimpleRoot 0 ≠ e8SimpleRoot 1
      intro h
      have hh := e8_dynkin_simple_roots.2.1 0 1
      rw [← h, e8Roots_simply_laced (e8_dynkin_simple_roots.1 0)] at hh
      norm_num [e8Cartan, OmegaMath.ExceptionalEight.cartan] at hh)

def simpleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e8_dynkin_simple_roots) (Realization simpleSignature) Unit Unit :=
  unitBindE8% `D5.S3.Quantum.Gauge.E8RootSystemUnification4D.e8_dynkin_simple_roots.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots.simpleFamily
    simpleArena simpleFamily (realize simpleSignature (fun _ _ => e8SimpleRoot) (fun e => nomatch e))
    #[]
    #[{ path := unitPath% e8_dynkin_simple_roots e8SimpleRoot 0 0
        stateBinder := 0
        functionOperand := true
        stateOperand := none
        booleanPredicate := false }]

end
end Reg.D5.S3.Quantum.Gauge.E8RootSystemUnification4D.Roots
