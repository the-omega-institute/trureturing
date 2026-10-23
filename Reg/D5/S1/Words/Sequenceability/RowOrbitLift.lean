import D5.S1.Words.Sequenceability.RowOrbitLift
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Field.ZMod

/-! Source-bound orbit and edge-label audits of the complete row-lift statements. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u
namespace Reg.D5.S1.Words.Sequenceability.RowOrbitLift

open _root_.D5.S1.Words.Sequenceability.RowOrbitLift
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

abbrev RowParams := Σ K : Type u, Σ f : Field K, @Units K f.toMonoid × K × K

abbrev rowSignature : Signature where
  Params := RowParams.{u}
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rowActual : Realization rowSignature.{u} :=
  realize rowSignature (fun _ p b => by
    letI := p.2.1
    exact (rowReturn p.2.2.1 p.2.2.2.1).SameCycle p.2.2.2.2 b)
    (fun e => nomatch e)

def rowBad : Realization rowSignature.{u} :=
  realize rowSignature (fun _ _ _ => False) (fun e => nomatch e)

abbrev rowArena : Arena where
  signature := rowSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] (r : Kˣ),
    (∀ z : Kˣ, ∃ n : ℕ, r ^ n = z) → ∀ c a b : K,
      R.readout () ⟨K, f, r, c, a⟩ b ↔ (a = c ↔ b = c)

private theorem natural_generator (K : Type u) [Field K] [Finite K] :
    ∃ r : Kˣ, ∀ z : Kˣ, ∃ n : ℕ, r ^ n = z := by
  obtain ⟨r, hr⟩ := IsCyclic.exists_generator (α := Kˣ)
  refine ⟨r, fun z => ?_⟩
  exact (Submonoid.mem_powers_iff z r).mp (mem_powers_iff_mem_zpowers.mpr (hr z))

private theorem row_bad_law : ¬ rowArena.{u}.Law rowBad := by
  intro h
  let K := ULift.{u} (ZMod 5)
  obtain ⟨r, hr⟩ := natural_generator K
  exact (h K r hr 0 0 0).mpr Iff.rfl

def rowFamily : Registration rowArena.{u} (type_of% (@row_same_cycle_iff.{u})) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨@row_same_cycle_iff.{u}, rowBad, row_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rowBad, ?_, rfl, row_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 5)
    refine ⟨⟨K, inferInstance, 1, 0, 0⟩, 0, 1, ?_⟩
    intro he
    have hzero : (rowReturn (1 : Kˣ) 0).SameCycle 0 0 := .refl _ _
    have hone : (rowReturn (1 : Kˣ) 0).SameCycle 0 1 := Eq.mp he hzero
    exact zero_ne_one (hone.eq_of_left (by simp [Function.IsFixedPt, rowReturn]))

def rowAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@row_same_cycle_iff.{u}) (Realization rowSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.RowOrbitLift.row_same_cycle_iff.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.RowOrbitLift.rowFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena⟩
  objectArena := .source ⟨rowArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena ⟨rowFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature rowActual.readout rowActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.RowOrbitLift
    definition := none
    coordinates := #[0, 3, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev LiftParams := Σ K : Type u, Σ f : Field K, @Units K f.toMonoid × K

abbrev liftSignature : Signature where
  Params := LiftParams.{u}
  State p := Fin 4 × p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := ZMod 5 × p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def liftActual : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p v => by
    letI := p.2.1
    exact edgeLabel p.2.2.1 p.2.2.2 v) (fun e => nomatch e)

def liftBad : Realization liftSignature.{u} :=
  realize liftSignature (fun _ p _ => by
    letI := p.2.1
    exact (0, 0)) (fun e => nomatch e)

abbrev liftArena : Arena where
  signature := liftSignature.{u}
  Law R := ∀ (K : Type u) [f : Field K] [Finite K] [CharP K 5] (c : K),
    ∃ r : Kˣ, (r : K) + 1 ≠ 0 ∧
      (∀ v w : Fin 4 × K, (lift r c).SameCycle v w ↔
        (initialRow v = c ↔ initialRow w = c)) ∧
      Set.BijOn (R.readout () ⟨K, f, r, c⟩) Set.univ {v | v.1 ≠ 0} ∧
      Set.BijOn (@vertex K) Set.univ {v | v.1 ≠ 0} ∧
      (∀ h : K, (lift r c ^ 4) (0, h) = (0, rowReturn r c h))

private theorem lift_bad_law : ¬ liftArena.{u}.Law liftBad := by
  intro h
  let K := ULift.{u} (ZMod 5)
  obtain ⟨r, _, _, hlabel, _, _⟩ := h K 0
  exact hlabel.1 (show (0, (0 : K)) ∈ Set.univ from trivial) rfl

def liftFamily : Registration liftArena.{u}
    (type_of% (@exists_characteristic_five_lift.{u})) where
  actual := liftActual
  bridge := Iff.rfl
  variation := ⟨exists_characteristic_five_lift, liftBad, lift_bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨liftBad, ?_, rfl, lift_bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    let K := ULift.{u} (ZMod 5)
    refine ⟨⟨K, inferInstance, 1, 0⟩, (0, 0), (1, 0), ?_⟩
    intro he
    have h := congrArg Prod.fst he
    have h' : (2 : ZMod 5) - 1 = 4 - 2 := by
      simpa [liftActual, realize, edgeLabel, lift, vertex, column] using h
    exact (by decide : (2 : ZMod 5) - 1 ≠ 4 - 2) h'

def liftAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_characteristic_five_lift.{u}) (Realization liftSignature.{u}) Unit Unit where
  unitName := `D5.S1.Words.Sequenceability.RowOrbitLift.exists_characteristic_five_lift.__information_unit
  realizationName := `Reg.D5.S1.Words.Sequenceability.RowOrbitLift.liftFamily
  realizationSource := none
  generated := false
  arena := .source ⟨liftArena⟩
  objectArena := .source ⟨liftArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source liftArena ⟨liftFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize liftSignature liftActual.readout liftActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Words.Sequenceability.RowOrbitLift
    definition := none
    coordinates := #[0, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "fn", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S1.Words.Sequenceability.RowOrbitLift
