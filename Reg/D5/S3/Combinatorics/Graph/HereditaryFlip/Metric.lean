import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HereditaryFlip.Metric

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

def pairSignature : Signature where
  Params := PairParams.{u}
  State := Vertex
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def pairActual : Realization pairSignature.{u} := realize pairSignature
  (fun _ p A => letI := p.1.2.1; (A.val ∆ p.2.val).card)
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
  simp [pairActual, realize, zero, one, base]

private theorem one_dist_zero :
    (flipGraph base.1.2.2).dist one base.2 = 1 := by
  rw [dist_eq isLowerSet_univ]
  simp [one, base]

private theorem singleSensitivity {A : Arena.{u+1,u,0,0,0}}
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

def lowerArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ p A, letI := p.1.2.1;
    ∀ q : (flipGraph p.1.2.2).Walk A p.2, R.readout () p A ≤ q.length

private theorem lowerBad : ¬ lowerArena.{u}.Law pairRaised := by
  intro h
  have hh := h base zero SimpleGraph.Walk.nil
  simpa [pairRaised, pairActual, realize, base, zero] using hh

def lowerFamily : Registration lowerArena.{u} (type_of% (@walk_lower_bound.{u})) where
  actual := pairActual
  bridge := by
    constructor
    · intro h p A q
      exact @h p.1.1 p.1.2.1 p.1.2.2 A p.2 q
    · intro h V inst F A B q
      exact h ⟨⟨V, inst, F⟩, B⟩ A q
  variation := ⟨fun p A q => walk_lower_bound q, pairRaised, lowerBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl lowerBad
  dependence := pairDependence

def shortestArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ p, IsLowerSet p.1.2.2 → ∀ A, letI := p.1.2.1;
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
  variation := ⟨fun p hf A => exists_shortest_walk hf A p.2, pairZero, shortestBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl shortestBad
  dependence := pairDependence

def distanceArena : Arena where
  signature := pairSignature.{u}
  Law R := ∀ p, IsLowerSet p.1.2.2 → ∀ A, letI := p.1.2.1;
    (flipGraph p.1.2.2).dist A p.2 = R.readout () p A

private theorem distanceBad : ¬ distanceArena.{u}.Law pairRaised := by
  intro h
  have hh := h base isLowerSet_univ zero
  simpa [pairRaised, pairActual, realize, base, zero] using hh

def distanceFamily : Registration distanceArena.{u} (type_of% (@dist_eq.{u})) where
  actual := pairActual
  bridge := by
    constructor
    · intro h p hf A
      exact @h p.1.1 p.1.2.1 p.1.2.2 hf A p.2
    · intro h V inst F hf A B
      exact h ⟨⟨V, inst, F⟩, B⟩ hf A
  variation := ⟨fun p hf A => dist_eq hf A p.2, pairRaised, distanceBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl distanceBad
  dependence := pairDependence

abbrev TripleParams := Σ p : PairParams.{u}, Vertex p

def tripleSignature : Signature where
  Params := TripleParams.{u}
  State p := Vertex p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def tripleActual : Realization tripleSignature.{u} := realize tripleSignature
  (fun _ p A => pairActual.readout () p.1 A) (fun e => nomatch e)

def tripleRaised : Realization tripleSignature.{u} := realize tripleSignature
  (fun _ p A => tripleActual.readout () p A + 1) (fun e => nomatch e)

def intervalArena : Arena where
  signature := tripleSignature.{u}
  Law R := ∀ p, IsLowerSet p.1.1.2.2 → ∀ A, letI := p.1.1.2.1;
    (flipGraph p.1.1.2.2).dist A p.2 + (flipGraph p.1.1.2.2).dist p.2 p.1.2 =
      R.readout () p A ↔ A.val ∩ p.1.2.val ⊆ p.2.val ∧ p.2.val ⊆ A.val ∪ p.1.2.val

private theorem intervalBad : ¬ intervalArena.{u}.Law tripleRaised := by
  intro h
  have hh := (h ⟨base, zero⟩ isLowerSet_univ zero).mpr (by simp [zero, base])
  simpa [tripleRaised, tripleActual, pairActual, realize, base, zero] using hh

def intervalFamily : Registration intervalArena.{u} (type_of% (@interval_iff.{u})) where
  actual := tripleActual
  bridge := by
    constructor
    · intro h p hf A
      exact @h p.1.1.1 p.1.1.2.1 p.1.1.2.2 hf A p.1.2 p.2
    · intro h V inst F hf A B M
      exact h ⟨⟨⟨V, inst, F⟩, B⟩, M⟩ hf A
  variation := ⟨fun p hf A => interval_iff hf A p.1.2 p.2, tripleRaised, intervalBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl intervalBad
  dependence := by
    intro i
    refine ⟨⟨base, zero⟩, zero, one, ?_⟩
    simp [tripleActual, pairActual, realize, zero, one, base]

abbrev CarrierData := Σ V : Type u, DecidableEq V

def connectedSignature : Signature where
  Params := CarrierData.{u}
  State p := Set (Finset p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def connectedActual : Realization connectedSignature.{u} := realize connectedSignature
  (fun _ p F => letI := p.2; (flipGraph F).Connected) (fun e => nomatch e)

def connectedFalse : Realization connectedSignature.{u} := realize connectedSignature
  (fun _ _ _ => False) (fun e => nomatch e)

def connectedArena : Arena where
  signature := connectedSignature.{u}
  Law R := ∀ p F, IsLowerSet F → ∅ ∈ F → R.readout () p F

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
  variation := ⟨fun p F hf h0 => connected hf h0, connectedFalse, connectedBad⟩
  sensitivity := singleSensitivity _ _ rfl rfl connectedBad
  dependence := by
    intro i
    refine ⟨⟨ULift Bool, Classical.decEq _⟩, Set.univ, ∅, ?_⟩
    intro heq
    have hc : (flipGraph (Set.univ : Set (Finset (ULift.{u} Bool)))).Connected :=
      connected isLowerSet_univ (Set.mem_univ _)
    have bad : (flipGraph (∅ : Set (Finset (ULift.{u} Bool)))).Connected := Eq.mp heq hc
    obtain ⟨A⟩ := bad.nonempty
    exact A.property
