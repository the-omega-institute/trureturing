/- GID: D5/S3/Combinatorics/Graph/StarForming/CompensationExamples
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/CompensationExamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex]
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.claim; result=D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.result; claim=D5/S3/Combinatorics/Graph/StarForming/CompensationExamples.claim
   digest: Actual connected balanced-accounting obstruction and larger dissociation. -/

import D5.S3.Combinatorics.Graph.StarForming.RegularCompensation
import D5.S3.Combinatorics.Graph.StarForming.CoverConnectivity

/-! The explicit connected twenty-eight-vertex obstruction in
CUBIC_EQUALITY_PATH_NORMAL_FORM at subquorum-colorings
48728b42d39ab3de5de251c61da5a404ec418a69, Apache-2.0. The two displayed
unaugmented exchanges are distinguished from the later augmented exchanges.
The written normal-form list interchanges leaves8 and10 and resources9 and11:
in this exact adjacency,9 has selected degree one and11 has selected degree two.
The canonical extraction uses actual failure0=9, reserved leaf8 and extra leaf10.
The graph, selected sixteen-set and larger fifteen-set are unchanged.
No exact beta upper bound or optimizer result is assumed. -/
namespace D5.S3.Combinatorics.Graph.StarForming.CompensationExamples
open StarFormingDissociationRefutation DegreeCapacity
set_option maxRecDepth 200000

def neighbors (v : Fin 28) : List (Fin 28) :=
  match v.val with
  | 0 => [1,8,10]
  | 1 => [0,2,12]
  | 2 => [1,3,13]
  | 3 => [2,4,14]
  | 4 => [3,5,16]
  | 5 => [4,6,17]
  | 6 => [5,7,18]
  | 7 => [6,20,22]
  | 8 => [0,9,27]
  | 9 => [8,16,21]
  | 10 => [0,11,27]
  | 11 => [10,13,25]
  | 12 => [1,15,25]
  | 13 => [2,11,24]
  | 14 => [3,15,26]
  | 15 => [12,14,17]
  | 16 => [4,9,24]
  | 17 => [5,15,25]
  | 18 => [6,19,27]
  | 19 => [18,21,23]
  | 20 => [7,21,26]
  | 21 => [9,19,20]
  | 22 => [7,23,26]
  | 23 => [19,22,24]
  | 24 => [13,16,23]
  | 25 => [11,12,17]
  | 26 => [14,20,22]
  | _ => [8,10,18]

def graph : SimpleGraph (Fin 28) where
  Adj v w := w∈neighbors v
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_∈_))

def selection : Finset (Fin 28) := {0,1,2,3,4,5,6,7,8,10,14,18,20,22,24,25}
def unaugmentedLeft : Finset (Fin 28) := {0,2,4,6,8,13,14,15,16,18,20,21,22,25}
def unaugmentedRight : Finset (Fin 28) := {1,3,5,7,8,9,10,12,14,17,18,19,20,24}
def largerDissociation : Finset (Fin 28) := {0,2,4,5,7,9,10,12,13,14,18,21,23,25,26}
def highs : Finset (Fin 28) := {0,1,2,3,4,5,6,7}
def extraLeaves : Finset (Fin 28) := {10,22}
def color (v : Fin 28) : Bool := decide (v∈({0,2,4,6,9,11,12,14,17,19,20,22,24,27} : Finset (Fin 28)))
def failure (v : Fin 28) : Fin 28 :=
  match v.val with
  | 0 => 9
  | 1 => 12
  | 2 => 13
  | 3 => 15
  | 4 => 16
  | 5 => 17
  | 6 => 19
  | 7 => 21
  | 8 => 9
  | 10 => 11
  | 14 => 15
  | 18 => 19
  | 20 => 21
  | 22 => 23
  | 24 => 24
  | 25 => 25
  | _ => 0

private theorem forms : Regular.Forms graph.Adj (·∈selection) := by
  unfold Regular.Forms Regular.TwoAt
  decide +kernel
private theorem failures : ∀ d : Fin 28, d∈selection →
    ¬ (failure d∈selection ∧ failure d≠d) ∧
    ¬Regular.TwoAt graph.Adj (fun v => v∈selection ∧ v≠d) (failure d) := by
  unfold Regular.TwoAt
  decide +kernel

/-- The source sixteen-set is an actual inclusion-minimal forming selection. -/
theorem minimal : IsMinimalStarForming graph 2 selection := by
  apply (regular_minimal_iff graph selection).mp
  apply CoverPullback.minimal_of_single_deletions forms
  intro d hd hf
  exact (failures d hd).2 (hf (failure d) (failures d hd).1)

/-- Actual cubic degree, proper bipartition and balanced selected isolates. -/
theorem class_and_balance :
    (∀ v, degree graph v=3) ∧
    (∀ v w, graph.Adj v w → color v≠color w) ∧
    isolates graph selection=({24,25} : Finset (Fin 28)) ∧
    ((isolates graph selection).filter (fun v => color v=true)).card=1 ∧
    ((isolates graph selection).filter (fun v => color v=false)).card=1 := by
  decide +kernel

private theorem root (v : Fin 28) : graph.Reachable 0 v := by
  fin_cases v
  · exact SimpleGraph.Reachable.rfl
  · exact (show graph.Adj 0 1 from by decide +kernel).reachable
  · exact ((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)).trans ((show graph.Adj 3 4 from by decide +kernel).reachable)
  · exact (((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)).trans ((show graph.Adj 3 4 from by decide +kernel).reachable)).trans ((show graph.Adj 4 5 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 27 from by decide +kernel).reachable)).trans ((show graph.Adj 27 18 from by decide +kernel).reachable)).trans ((show graph.Adj 18 6 from by decide +kernel).reachable)
  · exact (((((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)).trans ((show graph.Adj 9 21 from by decide +kernel).reachable)).trans ((show graph.Adj 21 20 from by decide +kernel).reachable)).trans ((show graph.Adj 20 7 from by decide +kernel).reachable)
  · exact (show graph.Adj 0 8 from by decide +kernel).reachable
  · exact ((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)
  · exact (show graph.Adj 0 10 from by decide +kernel).reachable
  · exact ((show graph.Adj 0 10 from by decide +kernel).reachable).trans ((show graph.Adj 10 11 from by decide +kernel).reachable)
  · exact ((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 12 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 13 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)).trans ((show graph.Adj 3 14 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 12 from by decide +kernel).reachable)).trans ((show graph.Adj 12 15 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)).trans ((show graph.Adj 9 16 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 12 from by decide +kernel).reachable)).trans ((show graph.Adj 12 15 from by decide +kernel).reachable)).trans ((show graph.Adj 15 17 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 27 from by decide +kernel).reachable)).trans ((show graph.Adj 27 18 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)).trans ((show graph.Adj 9 21 from by decide +kernel).reachable)).trans ((show graph.Adj 21 19 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)).trans ((show graph.Adj 9 21 from by decide +kernel).reachable)).trans ((show graph.Adj 21 20 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 9 from by decide +kernel).reachable)).trans ((show graph.Adj 9 21 from by decide +kernel).reachable)
  · exact ((((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)).trans ((show graph.Adj 3 14 from by decide +kernel).reachable)).trans ((show graph.Adj 14 26 from by decide +kernel).reachable)).trans ((show graph.Adj 26 22 from by decide +kernel).reachable)
  · exact (((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 13 from by decide +kernel).reachable)).trans ((show graph.Adj 13 24 from by decide +kernel).reachable)).trans ((show graph.Adj 24 23 from by decide +kernel).reachable)
  · exact ((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 13 from by decide +kernel).reachable)).trans ((show graph.Adj 13 24 from by decide +kernel).reachable)
  · exact (((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 12 from by decide +kernel).reachable)).trans ((show graph.Adj 12 25 from by decide +kernel).reachable)
  · exact (((((show graph.Adj 0 1 from by decide +kernel).reachable).trans ((show graph.Adj 1 2 from by decide +kernel).reachable)).trans ((show graph.Adj 2 3 from by decide +kernel).reachable)).trans ((show graph.Adj 3 14 from by decide +kernel).reachable)).trans ((show graph.Adj 14 26 from by decide +kernel).reachable)
  · exact ((show graph.Adj 0 8 from by decide +kernel).reachable).trans ((show graph.Adj 8 27 from by decide +kernel).reachable)

/-- The counterexample is connected, so its debt is not caused by cancellation
between different graph components. -/
theorem preconnected : graph.Preconnected := fun v w => (root v).symm.trans (root w)

/-- The actual high graph is the eight-vertex path, with four vertices of
selected degree two and four of selected degree three. -/
theorem high_path :
    CertificateBound.high graph selection=highs ∧
    (∀ v w : Fin 8, graph.Adj ⟨v.val,by omega⟩ ⟨w.val,by omega⟩ ↔
      v.val+1=w.val ∨ w.val+1=v.val) ∧
    (highs.filter (fun v => selectedDegree graph selection v=2)).card=4 ∧
    (highs.filter (fun v => selectedDegree graph selection v=3)).card=4 := by
  decide +kernel

/-- The displayed original high witnesses have zero surplus, and the only
unused outside degree-two resources are the two extra-leaf witnesses.
This is finite graph accounting with the explicit original witness choices. -/
theorem zero_accounting :
    (∀ h∈highs, 3-selectedDegree graph selection (failure h)=
      selectedDegree graph selection h-1) ∧
    ((Finset.univ\selection)\highs.image failure)=({11,23,26,27} : Finset (Fin 28)) ∧
    (∀ v∈({11,23} : Finset (Fin 28)), selectedDegree graph selection v=2) ∧
    (∀ v∈({26,27} : Finset (Fin 28)), selectedDegree graph selection v=3) ∧
    extraLeaves.card=2 := by
  decide +kernel

/-- Both original unaugmented exchanges are dissociation fourteen-sets; the
source fifteen-set is a larger actual dissociation selection. -/
theorem exchanges :
    IsKIndependent graph 2 unaugmentedLeft ∧ unaugmentedLeft.card=14 ∧
    IsKIndependent graph 2 unaugmentedRight ∧ unaugmentedRight.card=14 ∧
    IsKIndependent graph 2 largerDissociation ∧ largerDissociation.card=15 ∧
    selection.card=16 := by
  have h (S : Finset (Fin 28)) : IsKIndependent graph 2 S ↔
      ∀ v∈S, ∀ a∈S, ∀ b∈S, graph.Adj v a → graph.Adj v b → a=b :=
    SubQuorum.DoubleStarGrafting.independent_iff graph S
  have hL : ∀ v a b : Fin 28, v∈unaugmentedLeft → a∈unaugmentedLeft →
      b∈unaugmentedLeft → graph.Adj v a → graph.Adj v b → a=b := by decide +kernel
  have hR : ∀ v a b : Fin 28, v∈unaugmentedRight → a∈unaugmentedRight →
      b∈unaugmentedRight → graph.Adj v a → graph.Adj v b → a=b := by decide +kernel
  have hD : ∀ v a b : Fin 28, v∈largerDissociation → a∈largerDissociation →
      b∈largerDissociation → graph.Adj v a → graph.Adj v b → a=b := by decide +kernel
  exact ⟨(h _).mpr (fun v hv a ha b hb => hL v a b hv ha hb),by decide +kernel,
    (h _).mpr (fun v hv a ha b hb => hR v a b hv ha hb),by decide +kernel,
    (h _).mpr (fun v hv a ha b hb => hD v a b hv ha hb),by decide +kernel,by decide +kernel⟩

/-- Balanced zero accounting and connectedness do not make either original
exchange maximum. The actual cubic compensation slack is at least two. -/
theorem positive_slack : 15≤beta graph 2 ∧
    unaugmentedLeft.card<beta graph 2 ∧ unaugmentedRight.card<beta graph 2 ∧
    2≤3*Fintype.card (Fin 28)+2*beta graph 2-7*selection.card := by
  have hb : 15≤beta graph 2 := by
    rw [←exchanges.2.2.2.2.2.1]
    exact Finset.le_sup (Finset.mem_filter.mpr ⟨by simp,exchanges.2.2.2.2.1⟩)
  rw [exchanges.2.1,exchanges.2.2.2.1,exchanges.2.2.2.2.2.2]
  norm_num
  omega

/-- The displayed balanced zero-accounting candidate is asserted to make
its original exchanges maximum. This is the precise assertion refuted here. -/
def claim : Prop :=
  IsMinimalStarForming graph 2 selection → graph.Preconnected →
  ((∀ v, degree graph v=3) ∧
    (∀ v w, graph.Adj v w → color v≠color w) ∧
    isolates graph selection=({24,25} : Finset (Fin 28)) ∧
    ((isolates graph selection).filter (fun v => color v=true)).card=1 ∧
    ((isolates graph selection).filter (fun v => color v=false)).card=1) →
  (CertificateBound.high graph selection=highs ∧
    (∀ v w : Fin 8, graph.Adj ⟨v.val,by omega⟩ ⟨w.val,by omega⟩ ↔
      v.val+1=w.val ∨ w.val+1=v.val) ∧
    (highs.filter (fun v => selectedDegree graph selection v=2)).card=4 ∧
    (highs.filter (fun v => selectedDegree graph selection v=3)).card=4) →
  ((∀ h∈highs, 3-selectedDegree graph selection (failure h)=
      selectedDegree graph selection h-1) ∧
    ((Finset.univ\selection)\highs.image failure)=({11,23,26,27} : Finset (Fin 28)) ∧
    (∀ v∈({11,23} : Finset (Fin 28)), selectedDegree graph selection v=2) ∧
    (∀ v∈({26,27} : Finset (Fin 28)), selectedDegree graph selection v=3) ∧
    extraLeaves.card=2) →
  (IsKIndependent graph 2 unaugmentedLeft ∧ unaugmentedLeft.card=14 ∧
    IsKIndependent graph 2 unaugmentedRight ∧ unaugmentedRight.card=14 ∧ selection.card=16) →
  beta graph 2≤14

/-- Actual finite graph evidence refutes the maximum-exchange inference. -/
theorem result : ¬claim := by
  intro h
  have hu := h minimal preconnected class_and_balance high_path zero_accounting
    ⟨exchanges.1,exchanges.2.1,exchanges.2.2.1,exchanges.2.2.2.1,
      exchanges.2.2.2.2.2.2⟩
  have hl := positive_slack.1
  omega

end D5.S3.Combinatorics.Graph.StarForming.CompensationExamples
