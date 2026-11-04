import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HereditaryFlip.Metric

/-! Source-family observations for hereditary finite-support flip geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric

open LeanInformationAudit
open _root_.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped symmDiff

universe u
noncomputable section

abbrev FamilyData := Σ V : Type u, DecidableEq V × Set (Finset V)
abbrev PairParams := Σ p : FamilyData.{u}, {B : Finset p.1 // B ∈ p.2.2}
abbrev Vertex (p : PairParams.{u}) := {A : Finset p.1.1 // A ∈ p.1.2.2}

abbrev pairSignature : Signature where
  Params := PairParams.{u}
  State := Vertex
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def pairActual : Realization pairSignature.{u} := realize pairSignature
  (fun _ p A => letI : DecidableEq p.1.1 := p.1.2.1; (A.val ∆ p.2.val).card)
  (fun e => nomatch e)

def pairRaised : Realization pairSignature.{u} := realize pairSignature
  (fun _ p A => pairActual.readout () p A + 1) (fun e => nomatch e)

def pairZero : Realization pairSignature.{u} := realize pairSignature
  (fun _ _ _ => 0) (fun e => nomatch e)

def base : PairParams.{u} :=
  ⟨⟨ULift.{u} Bool, Classical.decEq _, Set.univ⟩, ⟨∅, Set.mem_univ _⟩⟩
def zero : Vertex base.{u} := ⟨∅, Set.mem_univ _⟩
def one : Vertex base.{u} := ⟨{ULift.up false}, Set.mem_univ _⟩

private theorem pairDependence : ObservationalDependence pairSignature.{u} pairActual := by
  intro i
  refine ⟨base, zero, one, ?_⟩
  change (0 : ℕ) ≠ 1
  decide

private theorem one_dist_zero :
    (@flipGraph base.{u}.1.1 base.1.2.1 base.1.2.2).dist one base.2 = 1 := by
  letI : DecidableEq base.{u}.1.1 := base.1.2.1
  have h := @dist_eq base.{u}.1.1 base.1.2.1 base.1.2.2 isLowerSet_univ one base.2
  calc
    _ = (one.val ∆ base.2.val).card := h
    _ = 1 := by rfl

private theorem singleSensitivity {A : Arena.{u + 1, u, 0, 0, 0}}
    (actual bad : Realization A.signature)
    (hrole : A.signature.Role = Unit) (hanchor : A.signature.Anchor = Empty)
    (hbad : ¬ A.Law bad) : Sensitivity A actual := by
  constructor
  · intro i
    refine ⟨bad, ?_, ?_, hbad⟩
    · intro j hji
      haveI : Subsingleton A.signature.Role := Equiv.subsingleton (Equiv.cast hrole)
      exact (hji (Subsingleton.elim _ _)).elim
    · funext e
      have he : Empty := Eq.mp hanchor e
      exact nomatch he
  · intro e
    have he : Empty := Eq.mp hanchor e
    exact nomatch he

abbrev lowerArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ (p : PairParams.{u}) (A : Vertex p), letI : DecidableEq p.1.1 := p.1.2.1;
    ∀ q : (flipGraph p.1.2.2).Walk A p.2, R.readout () p A ≤ q.length

private theorem lowerBad : ¬ lowerArena.{u}.Law pairRaised := by
  intro h
  have hh := h base zero (.nil : (@flipGraph base.1.1 base.1.2.1 base.1.2.2).Walk zero base.2)
  change (1 : ℕ) ≤ 0 at hh
  exact Nat.not_succ_le_zero 0 hh

def lowerFamily : Registration lowerArena.{u} (type_of% (@walk_lower_bound.{u})) where
  actual := pairActual
  bridge := by
    constructor
    · intro h p A q
      exact @h p.1.1 p.1.2.1 p.1.2.2 A p.2 q
    · intro h V inst F A B q
      exact h ⟨⟨V, inst, F⟩, B⟩ A q
  variation := ⟨fun p A q => @walk_lower_bound p.1.1 p.1.2.1 p.1.2.2 A p.2 q, pairRaised, lowerBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl lowerBad
  dependence := pairDependence

abbrev shortestArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ (p : PairParams.{u}), IsLowerSet p.1.2.2 → ∀ A : Vertex p, letI : DecidableEq p.1.1 := p.1.2.1;
    ∃ q : (flipGraph p.1.2.2).Walk A p.2, q.length = R.readout () p A

private theorem shortestBad : ¬ shortestArena.{u}.Law pairZero := by
  intro h
  obtain ⟨p, hp⟩ := h base isLowerSet_univ one
  have hh := SimpleGraph.dist_le p
  rw [one_dist_zero] at hh
  change p.length = 0 at hp
  omega

def shortestFamily : Registration shortestArena.{u} (type_of% (@exists_shortest_walk.{u})) where
  actual := pairActual
  bridge := by
    constructor
    · intro h p hf A
      exact @h p.1.1 p.1.2.1 p.1.2.2 hf A p.2
    · intro h V inst F hf A B
      exact h ⟨⟨V, inst, F⟩, B⟩ hf A
  variation := ⟨fun p hf A => @exists_shortest_walk p.1.1 p.1.2.1 p.1.2.2 hf A p.2, pairZero, shortestBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl shortestBad
  dependence := pairDependence

abbrev distanceArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ (p : PairParams.{u}), IsLowerSet p.1.2.2 → ∀ A : Vertex p, letI : DecidableEq p.1.1 := p.1.2.1;
    (flipGraph p.1.2.2).dist A p.2 = R.readout () p A

private theorem distanceBad : ¬ distanceArena.{u}.Law pairRaised := by
  intro h
  have hh := h base isLowerSet_univ zero
  change (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist zero zero = 1 at hh
  rw [SimpleGraph.dist_self] at hh
  change (0 : ℕ) = 1 at hh
  exact Nat.zero_ne_one hh

def distanceFamily : Registration distanceArena.{u} (type_of% (@dist_eq.{u})) where
  actual := pairActual
  bridge := by
    constructor
    · intro h p hf A
      exact @h p.1.1 p.1.2.1 p.1.2.2 hf A p.2
    · intro h V inst F hf A B
      exact h ⟨⟨V, inst, F⟩, B⟩ hf A
  variation := ⟨fun p hf A => @dist_eq p.1.1 p.1.2.1 p.1.2.2 hf A p.2, pairRaised, distanceBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl distanceBad
  dependence := pairDependence

abbrev TripleParams := Σ p : PairParams.{u}, Vertex p

abbrev tripleSignature : Signature where
  Params := TripleParams.{u}
  State p := Vertex p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def tripleActual : Realization tripleSignature.{u} := realize tripleSignature
  (fun _ p A => letI : DecidableEq p.1.1.1 := p.1.1.2.1;
    (flipGraph p.1.1.2.2).dist A p.1.2) (fun e => nomatch e)

def tripleRaised : Realization tripleSignature.{u} := realize tripleSignature
  (fun _ p A => tripleActual.readout () p A + 1) (fun e => nomatch e)

abbrev intervalArena : Arena where
  signature := tripleSignature.{u}
  Law R := ∀ (p : TripleParams.{u}), IsLowerSet p.1.1.2.2 → ∀ A : Vertex p.1, letI : DecidableEq p.1.1.1 := p.1.1.2.1;
    (flipGraph p.1.1.2.2).dist A p.2 + (flipGraph p.1.1.2.2).dist p.2 p.1.2 =
      R.readout () p A ↔ A.val ∩ p.1.2.val ⊆ p.2.val ∧ p.2.val ⊆ A.val ∪ p.1.2.val

private theorem intervalBad : ¬ intervalArena.{u}.Law tripleRaised := by
  letI : DecidableEq base.{u}.1.1 := base.1.2.1
  intro h
  have hh := (h ⟨base, zero⟩ isLowerSet_univ zero).mpr
    ⟨Finset.inter_subset_left, Finset.subset_union_left⟩
  change (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist zero zero +
      (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist zero zero =
      (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist zero zero + 1 at hh
  rw [SimpleGraph.dist_self] at hh
  change (0 : ℕ) = 1 at hh
  exact Nat.zero_ne_one hh

def intervalFamily : Registration intervalArena.{u} (type_of% (@interval_iff.{u})) where
  actual := tripleActual
  bridge := by
    constructor
    · intro h p hf A
      exact @h p.1.1.1 p.1.1.2.1 p.1.1.2.2 hf A p.1.2 p.2
    · intro h V inst F hf A B M
      exact h ⟨⟨⟨V, inst, F⟩, B⟩, M⟩ hf A
  variation := ⟨fun p hf A => @interval_iff p.1.1.1 p.1.1.2.1 p.1.1.2.2 hf A p.1.2 p.2, tripleRaised, intervalBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl intervalBad
  dependence := by
    intro i
    refine ⟨⟨base, zero⟩, zero, one, ?_⟩
    change (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist zero zero ≠
      (@flipGraph base.1.1 base.1.2.1 base.1.2.2).dist one base.2
    rw [SimpleGraph.dist_self, one_dist_zero]
    decide

abbrev CarrierData := Σ V : Type u, DecidableEq V

abbrev connectedSignature : Signature where
  Params := CarrierData.{u}
  State p := Set (Finset p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def connectedActual : Realization connectedSignature.{u} := realize connectedSignature
  (fun _ p F => letI : DecidableEq p.1 := p.2; (flipGraph F).Connected) (fun e => nomatch e)

def connectedFalse : Realization connectedSignature.{u} := realize connectedSignature
  (fun _ _ _ => False) (fun e => nomatch e)

abbrev connectedArena : Arena where
  signature := connectedSignature.{u}
  Law R := ∀ (p : CarrierData.{u}) (F : Set (Finset p.1)), IsLowerSet F → ∅ ∈ F → R.readout () p F

private theorem connectedBad : ¬ connectedArena.{u}.Law connectedFalse := by
  intro h
  exact h ⟨ULift Bool, Classical.decEq _⟩ Set.univ isLowerSet_univ (Set.mem_univ _)

def connectedFamily : Registration connectedArena.{u} (type_of% (@connected.{u})) where
  actual := connectedActual
  bridge := by
    constructor
    · intro h p F hf h0
      exact @h p.1 p.2 F hf h0
    · intro h V inst F hf h0
      exact h ⟨V, inst⟩ F hf h0
  variation := ⟨fun p F hf h0 => @connected p.1 p.2 F hf h0, connectedFalse, connectedBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl connectedBad
  dependence := by
    classical
    intro i
    refine ⟨⟨ULift Bool, Classical.decEq _⟩, Set.univ, (∅ : Set (Finset (ULift.{u} Bool))), ?_⟩
    intro heq
    change (@flipGraph (ULift.{u} Bool) (Classical.decEq _) Set.univ).Connected =
      (@flipGraph (ULift.{u} Bool) (Classical.decEq _) ∅).Connected at heq
    have hc := @connected (ULift.{u} Bool) (Classical.decEq _) Set.univ
      isLowerSet_univ (Set.mem_univ _)
    have bad : (@flipGraph (ULift.{u} Bool) (Classical.decEq _) ∅).Connected := Eq.mp heq hc
    obtain ⟨A⟩ := bad.nonempty
    exact A.property

noncomputable def lowerRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@walk_lower_bound.{u}) (Realization pairSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.walk_lower_bound.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.lowerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature
    (fun _ p A => letI : DecidableEq p.1.1 := p.1.2.1; (A.val ∆ p.2.val).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def shortestRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@exists_shortest_walk.{u}) (Realization pairSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.exists_shortest_walk.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.shortestFamily
  realizationSource := none
  generated := false
  arena := .source ⟨shortestArena⟩
  objectArena := .source ⟨shortestArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source shortestArena ⟨shortestFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature
    (fun _ p A => letI : DecidableEq p.1.1 := p.1.2.1; (A.val ∆ p.2.val).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def distanceRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@dist_eq.{u}) (Realization pairSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.dist_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.distanceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨distanceArena⟩
  objectArena := .source ⟨distanceArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source distanceArena ⟨distanceFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairSignature
    (fun _ p A => letI : DecidableEq p.1.1 := p.1.2.1; (A.val ∆ p.2.val).card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
    definition := none
    coordinates := #[0, 1, 2, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def intervalRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@interval_iff.{u}) (Realization tripleSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.interval_iff.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.intervalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨intervalArena⟩
  objectArena := .source ⟨intervalArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source intervalArena ⟨intervalFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize tripleSignature
    (fun _ p A => letI : DecidableEq p.1.1.1 := p.1.1.2.1;
      (flipGraph p.1.1.2.2).dist A p.1.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
    definition := none
    coordinates := #[0, 1, 2, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def connectedRegistration :
    Contract.Registration.{_,_,_,0,0,0,_,_,0,0,0,0}
      (@connected.{u}) (Realization connectedSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.connected.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric.connectedFamily
  realizationSource := none
  generated := false
  arena := .source ⟨connectedArena⟩
  objectArena := .source ⟨connectedArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source connectedArena ⟨connectedFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize connectedSignature
    (fun _ p F => letI : DecidableEq p.1 := p.2; (flipGraph F).Connected)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.Graph.HereditaryFlip.Metric
