import LeanInformationAuditInterface.Contract.Registration
import D5.S0.Computability.Coding.PrefixHull
import Reg.Support.DependentFamily

/-! Source-bound observation of membership in the literal least right-unitary hull.
The source telescope retains arbitrary universes and all finite labelled input families. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S0.Computability.Coding.PrefixHull

noncomputable section
universe u

namespace Reg.D5.S0.Computability.Coding.PrefixHull

structure Input where
  α : Type u
  n : ℕ
  f : Fin n → List α

abbrev signature : Signature where
  Params := Input.{u}
  State p := List p.α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature
  (fun _ p w => ∀ M : Set (List p.α),
    [] ∈ M →
    (∀ x y, x ∈ M → y ∈ M → x ++ y ∈ M) →
    (∀ x y, x ∈ M → x ++ y ∈ M → y ∈ M) →
    (∀ i, p.f i ∈ M) → w ∈ M)
  (fun e => nomatch e)

def rejected : Realization signature.{u} := realize signature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {α : Type u} {n : ℕ} (f : Fin n → List α),
    let H : Set (List α) := {w | ∀ M : Set (List α),
      [] ∈ M →
      (∀ x y, x ∈ M → y ∈ M → x ++ y ∈ M) →
      (∀ x y, x ∈ M → x ++ y ∈ M → y ∈ M) →
      (∀ i, f i ∈ M) → w ∈ M}
    ∃ m : ℕ, m ≤ n ∧ ∃ g : Fin m → List α,
      ∃ c : Fin n → List (Fin m),
        (∀ i, g i ≠ []) ∧
        (∀ i j, List.IsPrefix (g i) (g j) → i = j) ∧
        (∀ i, f i = (c i).flatMap g) ∧
        ∀ w : List α, r.readout () ⟨α, n, f⟩ w ↔
          ∃ s : List (Fin m), w = s.flatMap g

private theorem bridge :
    (type_of% (@finite_prefix_basis_least_right_unitary_hull.{u})) ↔
      arena.{u}.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨m, hm, g, c, hne, hp, hc, hgen⟩ :=
    h (α := ULift.{u} PUnit) (n := 0) Fin.elim0
  exact (hgen []).mpr ⟨[], rfl⟩

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : Input.{u} := ⟨ULift.{u} PUnit, 0, Fin.elim0⟩
  have hnil : actual.readout i p [] := by
    intro M hnil hmul hru hf
    exact hnil
  have hnonempty : ¬ actual.readout i p [⟨PUnit.unit⟩] := by
    intro h
    have hbad := h {w : List (ULift.{u} PUnit) | w = []} rfl
      (by
        intro x y hx hy
        change x = [] at hx
        change y = [] at hy
        subst x
        subst y
        rfl)
      (by
        intro x y hx hxy
        change x = [] at hx
        change x ++ y = [] at hxy
        subst x
        simpa using hxy)
      (by intro j; exact Fin.elim0 j)
    exact List.cons_ne_nil _ _ hbad
  refine ⟨p, [], [⟨PUnit.unit⟩], ?_⟩
  intro he
  exact hnonempty (Eq.mp he hnil)

def family : Registration arena.{u}
    (type_of% (@finite_prefix_basis_least_right_unitary_hull.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @finite_prefix_basis_least_right_unitary_hull.{u},
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finite_prefix_basis_least_right_unitary_hull.{u})
    (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S0.Computability.Coding.PrefixHull.finite_prefix_basis_least_right_unitary_hull.__information_unit
  realizationName := `Reg.D5.S0.Computability.Coding.PrefixHull.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Computability.Coding.PrefixHull
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Computability.Coding.PrefixHull
