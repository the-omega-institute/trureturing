import Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Common

/-! Typed source observations and whole-family interventions. -/

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Gauge.E6TrinificationUnification4D
open _root_.Reg.Support.SingleDependentReadout (signature)
open LeanInformationAudit
open scoped BigOperators InnerProductSpace

namespace Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots
set_option maxRecDepth 2048
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

private theorem zeroNotRoot : (0 : E6Ambient) ∉ e6Roots := by
  intro h
  have hh := e6Roots_simply_laced h
  norm_num at hh

private theorem simpleNonzero : e6SimpleRoot 0 ≠ 0 := by
  intro h
  exact zeroNotRoot (h ▸ e6_dynkin_simple_roots.1 0)

private theorem rankSpaceNonzero : H6 ≠ ⊥ := by
  intro h
  have hh := e6Roots_in_rank6_subspace.2
  rw [h] at hh
  norm_num at hh


abbrev cardSignature : Signature := signature Unit (fun _ => Finset E6Ambient) (fun _ => ℕ)

abbrev cardArena : Arena where
  signature := cardSignature
  Law R := R.readout () () e6Roots = 72

def cardFamily : Registration cardArena (type_of% (@e6Roots_card)) :=
  e6Family% cardArena (@e6Roots_card) (realize cardSignature (fun _ _ r => r.card) (fun e => nomatch e))
    (by
      exact ⟨(), ∅, {0}, by simp [realize]⟩)
    (realize cardSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      change (0 : ℕ) = 72 at h
      omega)

def cardRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6Roots_card) (Realization cardSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6Roots_card.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.cardFamily
    cardArena cardFamily (realize cardSignature (fun _ _ r => r.card) (fun e => nomatch e))
    #[] (e6Path% e6Roots_card Finset.card 2 0) 0 false (some #["arg"])

abbrev dimensionSignature : Signature := signature Unit (fun _ => Finset E6Ambient) (fun _ => ℕ)

abbrev dimensionArena : Arena where
  signature := dimensionSignature
  Law R := Module.finrank ℝ H6 + R.readout () () e6Roots = 78

def dimensionFamily : Registration dimensionArena (type_of% (@e6_lie_algebra_dimension)) :=
  e6Family% dimensionArena (@e6_lie_algebra_dimension) (realize dimensionSignature (fun _ _ r => r.card) (fun e => nomatch e))
    (by
      exact ⟨(), ∅, {0}, by simp [realize]⟩)
    (realize dimensionSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      change Module.finrank ℝ H6 + 0 = 78 at h
      rw [e6Roots_in_rank6_subspace.2] at h
      omega)

def dimensionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6_lie_algebra_dimension) (Realization dimensionSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6_lie_algebra_dimension.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.dimensionFamily
    dimensionArena dimensionFamily (realize dimensionSignature (fun _ _ r => r.card) (fun e => nomatch e))
    #[] (e6Path% e6_lie_algebra_dimension Finset.card 2 0) 0 false (some #["arg"])

abbrev normSignature : Signature := signature Unit (fun _ => E6Ambient) (fun _ => ℝ)

abbrev normArena : Arena where
  signature := normSignature
  Law R := ∀ {α : E6Ambient} (hα : α ∈ e6Roots),
    R.readout () () α = 2

def normFamily : Registration normArena (type_of% (@e6Roots_simply_laced)) :=
  e6Family% normArena (@e6Roots_simply_laced) (realize normSignature (fun _ _ α => ⟪α, α⟫_ℝ) (fun e => nomatch e))
    (by
      refine ⟨(), 0, e6SimpleRoot 0, ?_⟩
      change ⟪(0 : E6Ambient), 0⟫_ℝ ≠ ⟪e6SimpleRoot 0, e6SimpleRoot 0⟫_ℝ
      rw [e6Roots_simply_laced (e6_dynkin_simple_roots.1 0)]
      norm_num)
    (realize normSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      have hh := h (e6_dynkin_simple_roots.1 0)
      change (0 : ℝ) = 2 at hh
      norm_num at hh)

def normRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6Roots_simply_laced) (Realization normSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6Roots_simply_laced.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.normFamily
    normArena normFamily (realize normSignature (fun _ _ α => ⟪α, α⟫_ℝ) (fun e => nomatch e))
    #[] (e6Path% e6Roots_simply_laced inner 5 0) 0 false none

abbrev productsSignature : Signature := signature E6Ambient (fun _ => E6Ambient) (fun _ => ℝ)

abbrev productsArena : Arena where
  signature := productsSignature
  Law R := ∀ {α β : E6Ambient}
    (hα : α ∈ e6Roots) (hβ : β ∈ e6Roots),
    R.readout () α β ∈ ({-2, -1, 0, 1, 2} : Set ℝ) ∧
    (⟪α, β⟫_ℝ = 2 ↔ α = β) ∧ (⟪α, β⟫_ℝ = -2 ↔ α = -β)

def productsFamily : Registration productsArena (type_of% (@e6Roots_crystallographic_inner_products)) :=
  e6Family% productsArena (@e6Roots_crystallographic_inner_products) (realize productsSignature (fun _ α β => ⟪α, β⟫_ℝ) (fun e => nomatch e))
    (by
      refine ⟨e6SimpleRoot 0, 0, e6SimpleRoot 0, ?_⟩
      change ⟪e6SimpleRoot 0, (0 : E6Ambient)⟫_ℝ ≠ ⟪e6SimpleRoot 0, e6SimpleRoot 0⟫_ℝ
      rw [e6Roots_simply_laced (e6_dynkin_simple_roots.1 0)]
      norm_num)
    (realize productsSignature (fun _ _ _ => 3) (fun e => nomatch e))
    (by
      intro h
      have hh := (h (e6_dynkin_simple_roots.1 0) (e6_dynkin_simple_roots.1 0)).1
      change (3 : ℝ) ∈ ({-2, -1, 0, 1, 2} : Set ℝ) at hh
      norm_num at hh)

def productsRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6Roots_crystallographic_inner_products) (Realization productsSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6Roots_crystallographic_inner_products.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.productsFamily
    productsArena productsFamily (realize productsSignature (fun _ α β => ⟪α, β⟫_ℝ) (fun e => nomatch e))
    #[0] (e6Path% e6Roots_crystallographic_inner_products inner 5 0) 1 false none

abbrev reflectionSignature : Signature := signature E6Ambient (fun _ => E6Ambient) (fun _ => E6Ambient)

abbrev reflectionArena : Arena where
  signature := reflectionSignature
  Law R := ∀ {α β : E6Ambient}
    (hα : α ∈ e6Roots) (hβ : β ∈ e6Roots),
    R.readout () α β ∈ e6Roots ∧ -α ∈ e6Roots

def reflectionFamily : Registration reflectionArena (type_of% (@e6Roots_weyl_reflection_closed)) :=
  e6Family% reflectionArena (@e6Roots_weyl_reflection_closed) (realize reflectionSignature (fun _ α β => β - ⟪α, β⟫_ℝ • α) (fun e => nomatch e))
    (by
      refine ⟨0, 0, e6SimpleRoot 0, ?_⟩
      simpa [realize] using simpleNonzero.symm)
    (realize reflectionSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      exact zeroNotRoot (h (e6_dynkin_simple_roots.1 0) (e6_dynkin_simple_roots.1 0)).1)

def reflectionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6Roots_weyl_reflection_closed) (Realization reflectionSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6Roots_weyl_reflection_closed.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.reflectionFamily
    reflectionArena reflectionFamily (realize reflectionSignature (fun _ α β => β - ⟪α, β⟫_ℝ • α) (fun e => nomatch e))
    #[0] (e6Path% e6Roots_weyl_reflection_closed HSub.hSub 6 0) 1 false none

abbrev simpleSignature : Signature := signature Unit (fun _ => Fin 6) (fun _ => E6Ambient)

abbrev simpleArena : Arena where
  signature := simpleSignature
  Law R := (∀ i, R.readout () () i ∈ e6Roots) ∧
    (∀ i j, ⟪e6SimpleRoot i, e6SimpleRoot j⟫_ℝ = (e6Cartan i j : ℝ)) ∧
    e6Cartan.det = 3 ∧
    LinearIndependent ℝ e6SimpleRoot ∧
    (∀ α ∈ e6Roots, ∃ c : Fin 6 → ℤ, α = ∑ i, (c i : ℝ) • e6SimpleRoot i ∧
      ((∀ i, 0 ≤ c i) ∨ (∀ i, c i ≤ 0)))

def simpleFamily : Registration simpleArena (type_of% (@e6_dynkin_simple_roots)) :=
  e6Family% simpleArena (@e6_dynkin_simple_roots) (realize simpleSignature (fun _ _ => e6SimpleRoot) (fun e => nomatch e))
    (by
      refine ⟨(), 0, 1, ?_⟩
      change e6SimpleRoot 0 ≠ e6SimpleRoot 1
      intro h
      have hh := e6_dynkin_simple_roots.2.1 0 1
      rw [← h, e6Roots_simply_laced (e6_dynkin_simple_roots.1 0)] at hh
      norm_num [e6Cartan, OmegaMath.ExceptionalSix.cartan] at hh)
    (realize simpleSignature (fun _ _ _ => 0) (fun e => nomatch e))
    (by
      intro h
      exact zeroNotRoot (h.1 0))

def simpleRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6_dynkin_simple_roots) (Realization simpleSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6_dynkin_simple_roots.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.simpleFamily
    simpleArena simpleFamily (realize simpleSignature (fun _ _ => e6SimpleRoot) (fun e => nomatch e))
    #[] (e6Path% e6_dynkin_simple_roots e6SimpleRoot 0 0) 0 true none

abbrev spanSignature : Signature := signature Unit (fun _ => Set E6Ambient) (fun _ => Submodule ℝ E6Ambient)

abbrev spanArena : Arena where
  signature := spanSignature
  Law R := R.readout () () (e6Roots : Set E6Ambient) = H6

def spanFamily : Registration spanArena (type_of% (@e6_root_span)) :=
  e6Family% spanArena (@e6_root_span) (realize spanSignature (fun _ _ s => Submodule.span ℝ s) (fun e => nomatch e))
    (by
      refine ⟨(), ∅, (e6Roots : Set E6Ambient), ?_⟩
      change Submodule.span ℝ (∅ : Set E6Ambient) ≠ Submodule.span ℝ (e6Roots : Set E6Ambient)
      rw [Submodule.span_empty, e6_root_span]
      exact rankSpaceNonzero.symm)
    (realize spanSignature (fun _ _ _ => ⊥) (fun e => nomatch e))
    (by
      intro h
      exact rankSpaceNonzero h.symm)

def spanRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@e6_root_span) (Realization spanSignature) Unit Unit :=
  e6Bind% `D5.S3.Quantum.Gauge.E6TrinificationUnification4D.e6_root_span.__information_unit
    `Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots.spanFamily
    spanArena spanFamily (realize spanSignature (fun _ _ s => Submodule.span ℝ s) (fun e => nomatch e))
    #[] (e6Path% e6_root_span Submodule.span 6 0) 0 false (some #["arg"])

end
end Reg.D5.S3.Quantum.Gauge.E6TrinificationUnification4D.Roots
