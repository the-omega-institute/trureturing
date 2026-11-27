import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary

set_option autoImplicit false

namespace Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
open scoped BigOperators

namespace Bond

@[instance_reducible] private def finiteRole : Fintype Bool where
  elems := ⟨[false, true], by simp⟩
  complete := by intro role; cases role <;> simp

abbrev signature : Signature where
  Params := Nat
  State p := Fin (2 * p)
  Role := Bool
  finiteRole := finiteRole
  nonemptyRole := inferInstance
  Output _ p := Fin p
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ c => pair c) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {p : Nat} (c d : Fin (2 * p)),
    R.readout false p c ≠ R.readout true p d ↔ c ≠ d ∧ c.val + d.val ≠ 2 * p - 1

private def rejected (changed : Bool) : Realization signature :=
  realize signature
    (fun role _ c => if role = changed then ⟨0, by have := c.isLt; omega⟩ else pair c)
    (fun e => nomatch e)

private theorem rejected_law (changed : Bool) : ¬ arena.Law (rejected changed) := by
  intro h
  cases changed
  · exact ((h (p := 2) 1 0).mpr (by decide)) (by decide)
  · exact ((h (p := 2) 0 1).mpr (by decide)) (by decide)

def family : Registration arena (type_of% (@bond_iff)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@bond_iff, rejected false, rejected_law false⟩
  sensitivity := by
    constructor
    · intro changed
      refine ⟨rejected changed, ?_, rfl, rejected_law changed⟩
      intro role h
      funext p c
      simp [actual, rejected, realize, h]
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨2, 0, 1, ?_⟩
    change pair (p := 2) 0 ≠ pair (p := 2) 1
    decide

noncomputable def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@bond_iff) (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.bond_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.Bond.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => pair c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
    definition := none
    coordinates := #[0]
    readouts := #[
      { path := #["body", "body", "body", "fn", "arg", "fn", "arg"]
        stateBinder := 1
        functionOperand := false
        stateOperand := none
        booleanPredicate := false },
      { path := #["body", "body", "body", "fn", "arg", "arg"]
        stateBinder := 2
        functionOperand := false
        stateOperand := none
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Bond

namespace FreeCount

universe u
noncomputable section

abbrev Parameters := Σ V : Type u, Σ _ : Nat, Σ _ : Fintype V, Σ _ : LinearOrder V, SimpleGraph V

abbrev signature : Signature where
  Params := Parameters.{u}
  State x := AtMost x.2.2.2.2 x.2.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ x P =>
    letI := x.2.2.1
    letI := x.2.2.2.1
    Nat.card (Free (((partitionEquiv x.2.2.2.2 x.2.1).symm P).val : x.1 → Fin x.2.1)))
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} {p : Nat} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (P : AtMost G p),
    R.readout () ⟨V, p, inferInstance, inferInstance, G⟩ P = Fintype.card V - Nat.card P.val.parts

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem card_parts {V : Type u} {K : Type} {G : SimpleGraph V}
    (C : G.Coloring K) (h : Function.Surjective (C : V → K)) :
    Nat.card C.toPartition.parts = Nat.card K :=
  Nat.card_congr ((Setoid.quotientEquivClasses (Setoid.ker (C : V → K))).symm.trans
    (Setoid.quotientKerEquivOfSurjective (C : V → K) h))

abbrev vertices := ULift.{u} (Fin 2)
abbrev graph : SimpleGraph vertices.{u} := ⊥
abbrev sample : Parameters.{u} := ⟨vertices, 2, inferInstance, inferInstance, graph⟩

private def oneColor : graph.{u}.Coloring Unit :=
  SimpleGraph.Coloring.mk (fun _ => ()) (fun h => False.elim h)

private def twoColors : graph.{u}.Coloring (Fin 2) :=
  SimpleGraph.Coloring.mk ULift.down (fun h => False.elim h)

private theorem one_parts : Nat.card oneColor.{u}.toPartition.parts = 1 := by
  rw [card_parts oneColor (fun x => ⟨ULift.up 0, Subsingleton.elim _ x⟩), Nat.card_unique]

private theorem two_parts : Nat.card twoColors.{u}.toPartition.parts = 2 := by
  rw [card_parts twoColors (fun x => ⟨ULift.up x, rfl⟩), Nat.card_fin]

def oneBlock : AtMost graph.{u} 2 :=
  ⟨oneColor.toPartition, by rw [one_parts]; decide⟩

def twoBlocks : AtMost graph.{u} 2 :=
  ⟨twoColors.toPartition, by rw [two_parts]⟩

theorem one_free : actual.readout () sample.{u} oneBlock = 1 := by
  change Nat.card (Free (((partitionEquiv graph.{u} 2).symm oneBlock).val : vertices.{u} → Fin 2)) = 1
  rw [free_card, show Nat.card oneBlock.{u}.val.parts = 1 from one_parts]
  simp [vertices]

theorem zero_free : actual.readout () sample.{u} twoBlocks = 0 := by
  change Nat.card (Free (((partitionEquiv graph.{u} 2).symm twoBlocks).val : vertices.{u} → Fin 2)) = 0
  rw [free_card, show Nat.card twoBlocks.{u}.val.parts = 2 from two_parts]
  simp [vertices]

theorem observed : actual.readout () sample.{u} oneBlock ≠ actual.readout () sample.{u} twoBlocks := by
  rw [one_free, zero_free]
  decide

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hz := h graph.{u} oneBlock
  change 0 = Fintype.card vertices.{u} - Nat.card oneBlock.{u}.val.parts at hz
  rw [show Nat.card oneBlock.{u}.val.parts = 1 from one_parts] at hz
  simp [vertices] at hz

def family : Registration arena.{u} (type_of% (@free_card.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@free_card.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      rintro ⟨⟩ h
      exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨sample, oneBlock, twoBlocks, observed⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@free_card.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.free_card.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.FreeCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x P =>
    letI := x.2.2.1
    letI := x.2.2.2.1
    Nat.card (Free (((partitionEquiv x.2.2.2.2 x.2.1).symm P).val : x.1 → Fin x.2.1)))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end FreeCount

namespace LegalCount

universe u
noncomputable section

open _root_.D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233177Canonical (Canonical)

abbrev Parameters := Σ V : Type u, Σ _ : LinearOrder V, SimpleGraph V

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := Nat
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ x p =>
    letI := x.2.1
    Nat.card (Legal x.2.2 p)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [Nonempty V] (p : Nat),
    R.readout () ⟨V, inferInstance, G⟩ p =
      ∑ k ∈ Finset.Icc 1 (min p (Fintype.card V)),
        2 ^ (Fintype.card V - k) * _root_.D5.S3.Combinatorics.Graph.Coloring.IndependentPartitionExpansion.stirling G k

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev vertices := PUnit.{u + 1}
abbrev graph : SimpleGraph vertices.{u} := ⊥
abbrev sample : Parameters.{u} := ⟨vertices, inferInstance, graph⟩

private def zeroWord : Legal graph.{u} 1 := by
  refine ⟨fun _ => 0, ⟨?_, ?_⟩, ?_⟩
  · intro i b hb
    exact (Fin.not_lt_zero b hb).elim
  · intro i hi
    rfl
  · intro i j h
    exact h.elim

theorem zero_legal : actual.readout () sample.{u} 0 = 0 := by
  change Nat.card (Legal graph.{u} 0) = 0
  let : IsEmpty (Legal graph.{u} 0) := ⟨fun f => Fin.elim0 (f.val PUnit.unit)⟩
  simp

theorem one_legal : actual.readout () sample.{u} 1 = 1 := by
  change Nat.card (Legal graph.{u} 1) = 1
  let : Nonempty (Legal graph.{u} 1) := ⟨zeroWord⟩
  let : Subsingleton (Legal graph.{u} 1) := ⟨by
    intro f g
    apply Subtype.ext
    funext i
    have hfirst (a : Legal graph.{u} 1) : First (pair ∘ a.val) i := by
      intro j h
      exact (lt_irrefl i (Subsingleton.elim j i ▸ h)).elim
    have hv (a : Legal graph.{u} 1) : a.val i = 0 := by
      have hs := a.property.1.2 i (hfirst a)
      have hp : pair (a.val i) = (0 : Fin 1) := Subsingleton.elim _ _
      exact (colourEquiv 1).injective (Prod.ext hp hs)
    rw [hv f, hv g]⟩
  exact Nat.card_unique

theorem observed : actual.readout () sample.{u} 0 ≠ actual.readout () sample.{u} 1 := by
  rw [zero_legal, one_legal]
  decide

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact observed.{u} (zero_legal.{u}.trans ((h graph.{u} 1).trans (card_eq_sum graph.{u} 1).symm))

def family : Registration arena.{u} (type_of% (@card_eq_sum.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@card_eq_sum.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · rintro ⟨⟩
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      rintro ⟨⟩ h
      exact (h rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    rintro ⟨⟩
    exact ⟨sample, 0, 1, observed⟩

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
    (@card_eq_sum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.card_eq_sum.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary.LegalCount.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ x p =>
    letI := x.2.1
    Nat.card (Legal x.2.2 p)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end LegalCount
end Reg.D5.S3.Combinatorics.TraceAvoidingArrays.HardinGraphNormalization.Complementary
