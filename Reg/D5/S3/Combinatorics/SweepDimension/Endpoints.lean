import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.SweepDimension.Endpoints
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Combinatorics.SweepDimension.Endpoints

open _root_.D5.S3.Combinatorics.SweepDimension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

/-- The original carrier and its finite presentation remain parameters. -/
structure Parameters where
  carrier : Type u
  finite : Fintype carrier
  decEq : DecidableEq carrier

/-- The varying observation is theta as a function of the original partial order. -/
abbrev signature : Signature.{u+1,u,0,0,0} where
  Params := Parameters.{u}
  State p := PartialOrder p.carrier
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def observation (p : Parameters.{u}) (o : PartialOrder p.carrier) : ℕ := by
  letI := p.finite
  letI := p.decEq
  letI := o
  exact Basic.theta (α := p.carrier)

noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ p o => observation p o) (fun e => nomatch e)

noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ p o => observation p o + 1) (fun e => nomatch e)

noncomputable def arena : Arena.{u+1,u,0,0,0} where
  signature := signature.{u}
  Law R := ∀ (p : Parameters.{u}) (o : PartialOrder p.carrier),
    letI := p.finite
    letI := p.decEq
    letI := o
    ∀ _hn : 2 ≤ Fintype.card p.carrier,
    Upper.sweepDimension (α := p.carrier) = R.readout () p o ∧
    (Upper.sweepDimension (α := p.carrier) = max 2 (FiniteDilworth.maxAntichainSize p.carrier) ↔
      IsChain (· ≤ ·) (Set.univ : Set p.carrier) ∨
      IsAntichain (· ≤ ·) (Set.univ : Set p.carrier)) ∧
    (Upper.sweepDimension (α := p.carrier) = 2 * FiniteDilworth.maxAntichainSize p.carrier ↔
      ∃ A B : Finset p.carrier, IsAntichain (· ≤ ·) (A : Set p.carrier) ∧
        IsAntichain (· ≤ ·) (B : Set p.carrier) ∧ Disjoint A B ∧
        A.card = FiniteDilworth.maxAntichainSize p.carrier ∧
        B.card = FiniteDilworth.maxAntichainSize p.carrier)

theorem actual_bridge : (type_of% @_root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result.{u}) ↔
    arena.{u}.Law actual.{u} := by
  constructor
  · intro h p o hn
    exact @h p.carrier p.finite p.decEq o hn
  · intro h α f d o hn
    exact h ⟨α, f, d⟩ o hn

theorem rejected_law : ¬arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let p : Parameters.{u} := ⟨ULift.{u} (Fin 2), inferInstance, inferInstance⟩
  let o : PartialOrder p.carrier := inferInstance
  letI := p.finite
  letI := p.decEq
  letI := o
  have hn : 2 ≤ Fintype.card p.carrier := by simp [p]
  have hb := (h p o hn).1
  have ha := (_root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result (α := p.carrier) hn).1
  change Upper.sweepDimension (α := p.carrier) = observation p o + 1 at hb
  change Upper.sweepDimension (α := p.carrier) = observation p o at ha
  omega

def discreteOrder (X : Type u) : PartialOrder X where
  le := Eq
  le_refl := fun _ => rfl
  le_trans := fun _ _ _ => Eq.trans
  le_antisymm := fun _ _ h _ => h

theorem theta_discrete (X : Type u) [Fintype X] [DecidableEq X]
    (hn : 2 ≤ Fintype.card X) :
    letI := discreteOrder X
    Basic.theta (α := X) = Fintype.card X := by
  letI := discreteOrder X
  have hanti : IsAntichain (· ≤ ·) (Set.univ : Set X) := by
    intro a _ b _ hne h
    exact hne h
  have hlo : Fintype.card X ≤ FiniteDilworth.maxAntichainSize X := by
    simpa using FiniteDilworth.card_le_maxAntichainSize (A := (Finset.univ : Finset X))
      (by simpa using hanti)
  obtain ⟨A, _, hc⟩ := FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize (α := X)
  have hhi := Finset.card_le_univ A
  have hw : FiniteDilworth.maxAntichainSize X = Fintype.card X := by omega
  have hr := _root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result (α := X) hn
  have he := hr.2.1.mpr (Or.inr hanti)
  rw [hw, max_eq_right hn] at he
  omega

theorem theta_linear (X : Type u) [Fintype X] [DecidableEq X] [LinearOrder X]
    (hn : 2 ≤ Fintype.card X) : Basic.theta (α := X) = 2 := by
  have hchain : IsChain (· ≤ ·) (Set.univ : Set X) := by
    intro a _ b _ _
    exact le_total a b
  obtain ⟨A, hA, hc⟩ := FiniteDilworth.exists_isAntichain_card_eq_maxAntichainSize (α := X)
  have hAc : A.card ≤ 1 := Finset.card_le_one_iff.mpr (by
    intro a b ha hb
    by_contra hne
    rcases le_total a b with h | h
    · exact hA ha hb hne h
    · exact hA hb ha (Ne.symm hne) h)
  have hw : FiniteDilworth.maxAntichainSize X ≤ 2 := by omega
  have hr := _root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result (α := X) hn
  have he := hr.2.1.mpr (Or.inl hchain)
  rw [max_eq_left hw] at he
  omega

noncomputable def registration : Registration arena.{u}
    (type_of% @_root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result.{u}) where
  actual := actual
  bridge := actual_bridge.{u}
  variation := ⟨actual_bridge.{u}.mp @_root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result,
    rejected.{u}, rejected_law.{u}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (@Subsingleton.elim Unit _ j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    let p : Parameters.{u} := ⟨ULift.{u} (Fin 3), inferInstance, Classical.decEq _⟩
    let chain : PartialOrder p.carrier := inferInstance
    let disc : PartialOrder p.carrier := discreteOrder p.carrier
    refine ⟨p, chain, disc, ?_⟩
    have hn : 2 ≤ Fintype.card p.carrier := by simp [p]
    have hchain : observation p chain = 2 := theta_linear p.carrier hn
    have hdisc : observation p disc = 3 := by
      simpa [observation, disc, p] using theta_discrete p.carrier hn
    change observation p chain ≠ observation p disc
    omega

noncomputable def registration_1 : Contract.Registration
    (@_root_.D5.S3.Combinatorics.SweepDimension.Endpoints.result.{u})
    (type_of% (realize signature.{u} (fun _ p o => observation p o) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.SweepDimension.Endpoints.result.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.SweepDimension.Endpoints.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ p o => observation p o) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SweepDimension.Endpoints
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.Combinatorics.SweepDimension.Endpoints
