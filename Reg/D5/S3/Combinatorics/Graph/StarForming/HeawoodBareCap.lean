import D5.S3.Combinatorics.Graph.StarForming.HeawoodBareCap
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

noncomputable section
open Classical LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.StarForming.Cubic

namespace Reg.D5.S3.Combinatorics.Graph.StarForming.HeawoodBareCap

abbrev signature : Signature where
  Params := Fin 16384
  State _ := Finset (Fin 14)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observation : ∀ (_ : Unit) (_ : Fin 16384), Finset (Fin 14) → ℕ :=
  fun _ _ C => (barePorts C).card

def noAnchor : ∀ (_ : Empty) (_ : Fin 16384), Finset (Fin 14) :=
  fun e => nomatch e

def bad : Realization signature := realize signature (fun _ _ _ => 0) noAnchor

abbrev arena : Arena where
  signature := signature
  Law r := ∀ (C : Finset (Fin 14)) (mask : Fin 16384)
    (_hmask : ∀ v, chosen mask.val v=true ↔ v ∈ C),
    bareCount mask.val=r.readout () mask C

abbrev SourceClaim : Prop := ∀ (C : Finset (Fin 14)) (mask : Fin 16384)
    (_hmask : ∀ v, chosen mask.val v=true ↔ v ∈ C),
    bareCount mask.val=(barePorts C).card

private theorem bad_law : ¬ arena.Law bad := by
  intro h
  have hm : ∀ v : Fin 14, chosen (0 : ℕ) v=true ↔ v ∈ (∅ : Finset (Fin 14)) := by
    decide +kernel
  have hh := h ∅ 0 hm
  change bareCount 0=0 at hh
  have hb : bareCount 0=2 := by decide +kernel
  omega

def family : Registration arena SourceClaim where
  actual := realize signature observation noAnchor
  bridge := Iff.rfl
  variation := ⟨bareCount_eq,bad,bad_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨bad,?_,rfl,bad_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨0,∅,Finset.univ,?_⟩
    change (barePorts ∅).card≠(barePorts Finset.univ).card
    have h0 : barePorts ∅=({0,8} : Finset (Fin 14)) := by
      ext v
      simp [barePorts]
    have h1 : barePorts Finset.univ=∅ := by
      ext v
      simp [barePorts]
    rw [h0,h1]
    decide +kernel

noncomputable def bareCountRegistration :
    Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
      (@_root_.D5.S3.Combinatorics.Graph.StarForming.Cubic.bareCount_eq)
      (Realization signature) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.StarForming.Cubic.bareCount_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.StarForming.HeawoodBareCap.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature observation noAnchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.StarForming.HeawoodBareCap
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["body","body","body","arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg","arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.StarForming.HeawoodBareCap
