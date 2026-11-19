import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.QuandleMarkovColoring
import Reg.Support.DependentFamily
import Reg.Support.UniverseSingleReadout

open LeanInformationAudit
open _root_.D5.S3.Quantum.Algebra.Knot.WeightedPathArtinRepresentation
open _root_.D5.S3.Topology.QuandleMarkovColoring
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

noncomputable section

namespace Reg.D5.S3.Topology.QuandleMarkovColoring

universe u

/-- Retain the original color type and both structure arguments. -/
structure NativeData where
  Q : Type u
  quandle : Quandle Q
  finite : Finite Q

def data (Q : Type u) [Quandle Q] [Finite Q] : NativeData where
  Q := Q
  quandle := inferInstance
  finite := inferInstance

abbrev signature : Signature where
  Params := NativeData.{u}
  State _ := PositiveBraid
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b => by
    letI := p.quandle
    letI := p.finite
    exact coloringCount p.Q b) (fun e => nomatch e)

-- Strand count fails stabilization, while actual reads the coloring count.
def rejected : Realization signature := realize signature
  (fun _ _ b => b.1.val) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law r := ∀ {Q : Type u} [Quandle Q] [Finite Q]
    {b c : PositiveBraid} (_ : MarkovEquivalent b c),
    r.readout () (data Q) b = r.readout () (data Q) c

def actual_law : arena.Law actual := by
  intro Q _ _ b c h
  change coloringCount Q b = coloringCount Q c
  exact quandle_coloring_markov_invariant h

private abbrev upQuandle (Q : Type*) [Quandle Q] : Quandle (ULift.{u} Q) where
  act x y := ⟨Shelf.act x.down y.down⟩
  invAct x y := ⟨Rack.invAct x.down y.down⟩
  self_distrib := by intro x y z; apply ULift.ext; exact Shelf.self_distrib
  left_inv := by intro x y; apply ULift.ext; exact Rack.invAct_act_eq _ _
  right_inv := by intro x y; apply ULift.ext; exact Rack.act_invAct_eq _ _
  fix := by intro x; apply ULift.ext; exact Quandle.fix

private def testData : NativeData.{u} where
  Q := ULift.{u} (Quandle.Dihedral 2)
  quandle := upQuandle (Quandle.Dihedral 2)
  finite := inferInstanceAs (Finite (ULift.{u} (ZMod 2)))

private def identityBraid (n : ℕ) (hn : 0 < n) : PositiveBraid := ⟨⟨n, hn⟩, 1⟩

def rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  intro h
  have hh := @h testData.Q testData.quandle testData.finite
    (identityBraid 1 (by omega))
    ⟨⟨2, by omega⟩, strandInclusion 1 1 * lastGenerator 1 (by omega)⟩
    (.rel _ _ (MarkovStep.positive 1 (by omega) 1))
  norm_num [rejected, realize, identityBraid] at hh

/-- The actual observation distinguishes the one- and two-strand identity braids. -/
private theorem test_identity (n : ℕ) (hn : 0 < n) :
    actual.{u}.readout () testData.{u} (identityBraid n hn) = 2 ^ n := by
  simp only [actual, realize, coloringCount, identityBraid, ClosedColorings, map_one,
    Equiv.Perm.one_apply, eq_self_iff_true, Nat.card_subtype_true]
  change Nat.card (Fin n → ULift.{u} (Quandle.Dihedral 2)) = 2 ^ n
  rw [Nat.card_fun, Nat.card_ulift]
  simp [Quandle.Dihedral, Nat.card_eq_fintype_card, ZMod.card]

def family : Registration arena (type_of% (@quandle_coloring_markov_invariant.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨testData, identityBraid 1 (by omega), identityBraid 2 (by omega), ?_⟩
    have hi : i = () := Subsingleton.elim _ _
    subst i
    rw [test_identity, test_identity]
    norm_num

#print axioms family

def registration_1.{audit_u} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@quandle_coloring_markov_invariant.{audit_u})
    (Realization signature.{audit_u}) Unit Unit where
  unitName := `D5.S3.Topology.QuandleMarkovColoring.quandle_coloring_markov_invariant.__information_unit
  realizationName := `Reg.D5.S3.Topology.QuandleMarkovColoring.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{audit_u}⟩
  objectArena := .source ⟨arena.{audit_u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{audit_u} ⟨family.{audit_u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{audit_u}
    (fun _ p b => by
      letI := p.quandle
      letI := p.finite
      exact coloringCount p.Q b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.QuandleMarkovColoring
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }, {
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration_1

namespace AdjacentSlots

abbrev signature : Signature :=
  _root_.Reg.Support.UniverseSingleReadout.signature ℕ (fun n => Fin (n - 1)) Fin

def actual : Realization signature :=
  realize signature (fun _ _ i => leftSlot i) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ i => rightSlot i) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (i : Fin (n - 1)), R.readout () n i ≠ rightSlot i

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (n := 2) ⟨0, by decide⟩ rfl

def family : Registration arena (type_of% @slots_ne) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@slots_ne, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro role
    cases role
    refine ⟨3, ⟨0, by decide⟩, ⟨1, by decide⟩, ?_⟩
    change leftSlot (n := 3) ⟨0, by decide⟩ ≠ leftSlot ⟨1, by decide⟩
    decide

def audit : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@slots_ne) (Realization signature) Unit Unit where
  unitName := `D5.S3.Topology.QuandleMarkovColoring.slots_ne.__information_unit
  realizationName := `Reg.D5.S3.Topology.QuandleMarkovColoring.AdjacentSlots.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ i => leftSlot i) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Topology.QuandleMarkovColoring
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false
    }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end AdjacentSlots

end Reg.D5.S3.Topology.QuandleMarkovColoring
