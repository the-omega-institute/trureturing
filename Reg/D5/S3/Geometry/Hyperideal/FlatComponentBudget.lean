import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Hyperideal.FlatComponentBudget
import Reg.Support.DependentFamily
import Reg.D5.S3.Geometry.Hyperideal.NativeFlatAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped BigOperators
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget
open _root_.D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
namespace Reg.D5.S3.Geometry.Hyperideal.FlatComponentBudget
universe u

abbrev Source := Σ T : Type u, Σ _finite : Fintype T,
  Σ p : RawFacePairing T, p.GlobalEdge → ℝ

abbrev SourceBare := Σ T : Type u, Σ p : RawFacePairing T, p.GlobalEdge → ℝ

abbrev SourceSet := Σ T : Type u, Σ _finite : Fintype T,
  Σ p : RawFacePairing T, Σ _ell : p.GlobalEdge → ℝ, Finset T

namespace Multiplicity
abbrev signature : Signature where
  Params := SourceSet.{u}
  State s := s.2.2.1.GlobalEdge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ s e => by
    letI := s.2.1
    exact m s.2.2.1 s.2.2.2.1 s.2.2.2.2 e)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hsum : AngleSums p ell) (C : Finset T) (e : p.GlobalEdge),
    R.readout () ⟨T,finite,p,ell,C⟩ e ≤ 2

theorem actual_law : arena.Law actual := by
  intro T finite p ell hsum C e
  exact m_le_two p ell hsum C e
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.m_le_two.{u})) ↔
      arena.{u}.Law actual.{u} := Iff.rfl
end Multiplicity

namespace GlobalMultiplicity
abbrev signature : Signature where
  Params := Source.{u}
  State s := s.2.2.1.GlobalEdge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ s e => by
    letI := s.2.1
    exact m s.2.2.1 s.2.2.2 (flats s.2.2.1 s.2.2.2) e)
  (fun e => nomatch e)
end GlobalMultiplicity

namespace Support
abbrev arena : Arena where
  signature := GlobalMultiplicity.signature.{u}
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (_hsum : AngleSums p ell) (e : p.GlobalEdge)
    (_hm : R.readout () ⟨T,finite,p,ell⟩ e = 2)
    (i j : T × Fin 6) (_hi : label p i = e) (_hj : label p j = e),
    Relation.EqvGen (fun a b => p.edgeStep a b ∧ Flat p ell a.1 ∧ Flat p ell b.1) i j ∧
      SameFlatComponent p ell i.1 j.1

theorem actual_law : arena.Law GlobalMultiplicity.actual := by
  intro T finite p ell hell hsum e hm i j hi hj
  exact saturated_support p ell hell hsum e hm i j hi hj
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.saturated_support.{u})) ↔
      arena.{u}.Law GlobalMultiplicity.actual.{u} := Iff.rfl
end Support

namespace Budget
abbrev signature : Signature where
  Params := SourceBare.{u}
  State s := s.2.1.GlobalEdge
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ s e => weight s.2.1 s.2.2 e)
  (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (C : Finset T) (_hC : ∀ t ∈ C, Flat p ell t)
    (_hCne : C.Nonempty),
    letI : Fintype p.GlobalEdge := Fintype.ofFinite _
    (C.card : ℝ)*Real.log 16 + 2*∑ e : p.GlobalEdge,
      (m p ell C e : ℝ)*correction p ell e ≤
      ∑ e : p.GlobalEdge, (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*weight p ell e ∧
    (C.card : ℝ)*Real.log 16 <
      ∑ e : p.GlobalEdge, (3*(m p ell C e : ℝ)-(n p ell C e : ℝ))*R.readout () ⟨T,p,ell⟩ e

theorem actual_law : arena.Law actual := by
  intro T finite p ell hell C hC hCne
  exact native_component_budget p ell hell C hC hCne
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.native_component_budget.{u})) ↔
      arena.{u}.Law actual.{u} := Iff.rfl


private def rejected : Realization signature := realize signature
  (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := (h (T := NativeFlatAudit.Block.{u}) NativeFlatAudit.pairing.{u} NativeFlatAudit.ell NativeFlatAudit.positive
    ({⟨0⟩} : Finset NativeFlatAudit.Block.{u}) (by intro t _; exact NativeFlatAudit.flat t)
    (by simp)).2
  have hlog := Real.log_pos (by norm_num : (1:ℝ) < 16)
  simp only [rejected,realize,mul_zero,Finset.sum_const_zero,
    Finset.card_singleton,Nat.cast_one,one_mul] at hh
  linarith

def budget_family : Registration arena.{u}
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.native_component_budget.{u})) where
  actual := actual
  bridge := source_bridge.{u}
  variation := ⟨actual_law.{u},rejected.{u},rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    refine ⟨⟨NativeFlatAudit.Block.{u},NativeFlatAudit.pairing.{u},NativeFlatAudit.ell⟩,
      NativeFlatAudit.pairing.edgeLabel ⟨0⟩ 0,NativeFlatAudit.pairing.edgeLabel ⟨0⟩ 1,?_⟩
    exact NativeFlatAudit.weight_dependence

#print axioms budget_family

end Budget

namespace Genuine
abbrev arena : Arena where
  signature := GlobalMultiplicity.signature.{u}
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (_hsum : AngleSums p ell) (e : p.GlobalEdge)
    (_hm : R.readout () ⟨T,finite,p,ell⟩ e = 1),
    ∃ i : T × Fin 6, label p i = e ∧ ¬ Flat p ell i.1

theorem actual_law : arena.Law GlobalMultiplicity.actual := by
  intro T finite p ell hell hsum e hm
  exact genuine_of_single_pi p ell hell hsum e hm
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.genuine_of_single_pi.{u})) ↔
      arena.{u}.Law GlobalMultiplicity.actual.{u} := Iff.rfl
end Genuine

namespace Exposure
abbrev arena : Arena where
  signature := GlobalMultiplicity.signature.{u}
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (_hsum : AngleSums p ell)
    (_hdegree : ∀ e, 6 ≤ degree p e) (t : T) (_ht : Flat p ell t),
    ∃ e : p.GlobalEdge, R.readout () ⟨T,finite,p,ell⟩ e = 1 ∧
      m p ell (component p ell t) e = 1 ∧ n p ell (component p ell t) e ≤ 2 ∧
      ∃ i : T × Fin 6, label p i = e ∧ ¬ Flat p ell i.1

theorem actual_law : arena.Law GlobalMultiplicity.actual := by
  intro T finite p ell hell hsum hdegree t ht
  exact component_exposed_label p ell hell hsum hdegree t ht
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.component_exposed_label.{u})) ↔
      arena.{u}.Law GlobalMultiplicity.actual.{u} := Iff.rfl
end Exposure

namespace Components
abbrev signature : Signature where
  Params := Source.{u}
  State s := s.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ s := Finset s.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ s t => by
    letI := s.2.1
    exact component s.2.2.1 s.2.2.2 t)
  (fun e => nomatch e)
end Components

namespace Endpoints
abbrev arena : Arena where
  signature := Components.signature.{u}
  Law R := ∀ {T : Type u} [finite : Fintype T]
    (p : RawFacePairing T) (ell : p.GlobalEdge → ℝ)
    (_hell : ∀ e, 0 < ell e) (_hsum : AngleSums p ell)
    (_hdegree : ∀ e, 6 ≤ degree p e) (t : T) (_ht : Flat p ell t),
    ∃ e₀ e₁ : p.GlobalEdge, e₀ ≠ e₁ ∧
      Endpoint p ell (R.readout () ⟨T,finite,p,ell⟩ t) e₀ ∧
      Endpoint p ell (component p ell t) e₁

theorem actual_law : arena.Law Components.actual := by
  intro T finite p ell hell hsum hdegree t ht
  exact component_endpoints p ell hell hsum hdegree t ht
theorem source_bridge :
    (type_of% (@_root_.D5.S3.Geometry.Hyperideal.FlatComponentBudget.component_endpoints.{u})) ↔
      arena.{u}.Law Components.actual.{u} := Iff.rfl
end Endpoints

end Reg.D5.S3.Geometry.Hyperideal.FlatComponentBudget
