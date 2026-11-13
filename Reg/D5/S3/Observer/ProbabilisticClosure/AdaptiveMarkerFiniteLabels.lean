import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels

/-! Source-family audit of finite-label causal realization. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerStoppingTails
open _root_.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels

namespace Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels

universe u

@[reducible] def signature : Signature where
  Params := Word
  State := Labels
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Source
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => completion z) Empty.elim

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {Seed : Type u} [MeasurableSpace Seed]
    (p : Policy Seed) (seed : Seed) (w : Word),
    terminalFirstTrue w → policyConformity p seed w → ∀ z : Labels w,
    noAdjacentOnes (R.readout () w z) ∧
    (∀ s (i : Fin (sideTotal w s + 1)),
      endpoint (R.readout () w z) s i = z.bit s i) ∧
    (∀ k, k ≤ w.length → actualRun p seed (R.readout () w z) k =
      ⟨(actions w k).reverse, (replies w k).reverse, decide (k = w.length)⟩) ∧
    actualRun p seed (R.readout () w z) w.length =
      ⟨(w.map Prod.fst).reverse, (w.map Prod.snd).reverse, true⟩ ∧
    actualQueryCount p seed (R.readout () w z) w.length = w.length ∧
    stoppingTime p seed (R.readout () w z) = (w.length : WithTop ℕ)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (true, (fun _ => true, fun _ => true))) Empty.elim

def emptyLabels (root : Bool) : Labels [] where
  bit := fun _ _ => root
  root := rfl
  no11 := by intro s i hi; simp [sideTotal] at hi
  response := by intro k; exact Fin.elim0 k

def singletonLabels : Labels [(false, true)] where
  bit := fun _ _ => false
  root := rfl
  no11 := by intro s i hi; simp
  response := by
    intro k
    fin_cases k
    rfl

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro law
  let p : Policy (ULift.{u} Unit) :=
    ⟨fun _ _ _ => false, fun _ _ => measurable_const⟩
  have ht : terminalFirstTrue [(false, true)] := by
    constructor
    · decide
    · intro k
      fin_cases k
      rfl
  have hp : policyConformity p ⟨()⟩ [(false, true)] := by
    intro k
    fin_cases k
    rfl
  have h := (law p ⟨()⟩ [(false, true)] ht hp singletonLabels).1 false 0
  exact h ⟨rfl, rfl⟩

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨[], emptyLabels false, emptyLabels true, ?_⟩
  intro h
  have := congrArg Prod.fst h
  cases this

def family : Registration arena.{u} (type_of% (@finite_label_realization.{u})) where
  actual := realize signature (fun _ _ z => completion z) Empty.elim
  bridge := Iff.rfl
  variation := ⟨@finite_label_realization.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_label_realization.{u}) (Realization signature) Type Unit where
  unitName := `Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels.unit
  realizationName := `Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => completion z) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Observer.ProbabilisticClosure.AdaptiveMarkerFiniteLabels
