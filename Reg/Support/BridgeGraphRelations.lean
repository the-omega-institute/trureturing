import Reg.Support.DependentFamily
import Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open _root_.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound
open Reg.D5.S3.Quantum.TensorNetworks.BridgeGraph.QuantumMaxFlowBound

namespace Reg.Support.BridgeGraphRelations

abbrev integerSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

abbrev rationalSignature : Signature where
  Params := Unit
  State _ := ℚ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def integerActual : Realization integerSignature :=
  realize integerSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def integerLeActual : Realization integerSignature :=
  realize integerSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def integerRejected : Realization integerSignature :=
  realize integerSignature (fun _ _ _ _ => False) (fun e => nomatch e)
def rationalActual : Realization rationalSignature :=
  realize rationalSignature (fun _ _ x y => x = y) (fun e => nomatch e)
def rationalLeActual : Realization rationalSignature :=
  realize rationalSignature (fun _ _ x y => x ≤ y) (fun e => nomatch e)
def rationalLtActual : Realization rationalSignature :=
  realize rationalSignature (fun _ _ x y => x < y) (fun e => nomatch e)
def rationalRejected : Realization rationalSignature :=
  realize rationalSignature (fun _ _ _ _ => False) (fun e => nomatch e)

theorem integerDependence : ObservationalDependence integerSignature integerActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℤ) = 0) = ((1 : ℤ) = 0) at he
  have hn : (1 : ℤ) = 0 := he ▸ rfl
  exact (by decide : ¬ (1 : ℤ) = 0) hn

theorem integerLeDependence : ObservationalDependence integerSignature integerLeActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℤ) ≤ 0) = ((1 : ℤ) ≤ 0) at he
  have hn : (1 : ℤ) ≤ 0 := he ▸ le_rfl
  exact (by decide : ¬ (1 : ℤ) ≤ 0) hn

theorem rationalDependence : ObservationalDependence rationalSignature rationalActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℚ) = 0) = ((1 : ℚ) = 0) at he
  have hn : (1 : ℚ) = 0 := he ▸ rfl
  exact (by decide : ¬ (1 : ℚ) = 0) hn

theorem rationalLeDependence : ObservationalDependence rationalSignature rationalLeActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℚ) ≤ 0) = ((1 : ℚ) ≤ 0) at he
  have hn : (1 : ℚ) ≤ 0 := he ▸ le_rfl
  exact (by decide : ¬ (1 : ℚ) ≤ 0) hn

theorem rationalLtDependence : ObservationalDependence rationalSignature rationalLtActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 1
  change ((0 : ℚ) < 1) = ((1 : ℚ) < 1) at he
  have hn : (1 : ℚ) < 1 := he ▸ (by norm_num : (0 : ℚ) < 1)
  exact (by decide : ¬ (1 : ℚ) < 1) hn

abbrev witnessPredicateSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ → ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def witnessPredicateActual : Realization witnessPredicateSignature :=
  realize witnessPredicateSignature
    (fun _ _ a b c d => RationalWitness a b c d) (fun e => nomatch e)
def witnessPredicateRejected : Realization witnessPredicateSignature :=
  realize witnessPredicateSignature (fun _ _ _ _ _ _ => False) (fun e => nomatch e)

theorem witnessPredicateDependence :
    ObservationalDependence witnessPredicateSignature witnessPredicateActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun (congrFun (congrFun h 4) 1) 4
  change RationalWitness 0 4 1 4 = RationalWitness 1 4 1 4 at he
  exact obstructedWitness (he ▸ zeroWitness 4 1 4)

end Reg.Support.BridgeGraphRelations
