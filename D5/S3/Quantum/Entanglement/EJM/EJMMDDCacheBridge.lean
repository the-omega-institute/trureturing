/- GID: D5/S3/Quantum/Entanglement/EJM/EJMMDDCacheBridge
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMMDDCacheBridge
   mirror-E: none(waiver:actual-value-diagram-certificate)
   anchors: []
   utility: none
   digest: Reverse coordinate prefixes preserve the actual earned cache action and bound every concrete diagram output by the original local score. -/

/- WIP for the same complete EJM certificate. The actual diagrams' ordering
and complete numerical simulation receipts are not yet supplied. These
conditional bridges assert no table equality or complete global acceptance. -/

import D5.S0.Certificates.FiniteMDDCacheSimulation
import D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge
open D5.S0.Certificates.FiniteSymmetryBoundReplay
open D5.S0.Certificates.FiniteMDDCacheSimulation
open D5.S3.Quantum.Entanglement.EJM.EJMCacheState
open D5.S3.Quantum.Entanglement.EJM.EJMCacheSoundness
open D5.S3.Quantum.Entanglement.EJM.EJMCertificateData (F1 F2)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry (triangleCentered singletonCentered)

/-- These ordering laws are obligations for every literal DD branch, not
assumptions about its score. All child levels and actual coordinates survive. -/
structure OrderedDiagram (n N : ℕ) where
  nodes : Fin N → Node N (Fin n) (Fin 4)
  level : Fin N → ℕ
  branch_lt : ∀ index i children, nodes index = .branch i children → level index < n
  branch_coordinate : ∀ index i children, nodes index = .branch i children →
    i.val = n - 1 - level index
  branch_child : ∀ index i children, nodes index = .branch i children →
    ∀ a, level (children a) = level index + 1

/-- The ordering check reads all four actual literal children of a branch. -/
def checkOrderedAt {n N : ℕ} (nodes : Fin N → Node N (Fin n) (Fin 4))
    (level : Fin N → ℕ) (index : Fin N) : Bool :=
  match nodes index with
  | .leaf _ => true
  | .branch i children => decide (level index < n ∧
      i.val = n - 1 - level index ∧ ∀ a, level (children a) = level index + 1)

private theorem checked_branch_laws {n N : ℕ}
    (nodes : Fin N → Node N (Fin n) (Fin 4)) (level : Fin N → ℕ)
    (accepted : ∀ index, checkOrderedAt nodes level index = true)
    (index : Fin N) (i : Fin n) (children : Fin 4 → Fin N)
    (branch : nodes index = .branch i children) :
    level index < n ∧ i.val = n - 1 - level index ∧
      ∀ a, level (children a) = level index + 1 := by
  apply of_decide_eq_true
  simpa only [checkOrderedAt, branch] using accepted index

/-- Only a complete per-node ordering receipt constructs the ordered diagram
consumed by actual-cache transport. Numerical checks may be split into blocks. -/
def checked_ordered_diagram {n N : ℕ}
    (nodes : Fin N → Node N (Fin n) (Fin 4)) (level : Fin N → ℕ)
    (accepted : ∀ index, checkOrderedAt nodes level index = true) : OrderedDiagram n N where
  nodes := nodes
  level := level
  branch_lt := fun index i children branch =>
    (checked_branch_laws nodes level accepted index i children branch).1
  branch_coordinate := fun index i children branch =>
    (checked_branch_laws nodes level accepted index i children branch).2.1
  branch_child := fun index i children branch =>
    (checked_branch_laws nodes level accepted index i children branch).2.2

/-- In reverse order, all lower numbered coordinates remain unknown. -/
def ReversePrefix {n : ℕ} (depth : ℕ) (p : Partial (Fin n) (Fin 4)) : Prop :=
  ∀ i, i.val < n - depth → p i = none

private theorem reverse_prefix_update {n : ℕ} (depth : ℕ)
    (p : Partial (Fin n) (Fin 4)) (hprefix : ReversePrefix depth p)
    (i : Fin n) (coordinate : i.val = n - 1 - depth) (a : Fin 4) :
    ReversePrefix (depth + 1) (Function.update p i (some a)) := by
  intro j future
  have different : j ≠ i := by
    intro same
    have equal := congrArg Fin.val same
    omega
  rw [Function.update_of_ne different]
  apply hprefix j
  omega

def TriangleValidAt {N : ℕ} (diagram : OrderedDiagram 10 N) (fuel : ℕ)
    (index : Fin N) (current : CachedLocal 41294)
    (p : Partial (Fin 10) (Fin 4)) : Prop :=
  fuel + diagram.level index = 11 ∧
    ReversePrefix (diagram.level index) p ∧ TriangleValid current p

def SingletonValidAt {N : ℕ} (diagram : OrderedDiagram 9 N) (fuel : ℕ)
    (index : Fin N) (current : CachedLocal 8689)
    (p : Partial (Fin 9) (Fin 4)) : Prop :=
  fuel + diagram.level index = 10 ∧
    ReversePrefix (diagram.level index) p ∧ SingletonValid current p

/-- Unknownness is earned from the fixed reverse prefix. The existing step
theorem supplies all actual row/action transport, including all 288 actions. -/
theorem triangle_diagram_step {N : ℕ} (diagram : OrderedDiagram 10 N)
    (fuel : ℕ) (index : Fin N) (current : CachedLocal 41294)
    (p : Partial (Fin 10) (Fin 4)) (i : Fin 10) (children : Fin 4 → Fin N)
    (branch : diagram.nodes index = .branch i children)
    (valid : TriangleValidAt diagram (fuel + 1) index current p) (a : Fin 4) :
    TriangleValidAt diagram fuel (children a) (triangleStep current i a)
      (Function.update p i (some a)) := by
  have depth_lt := diagram.branch_lt index i children branch
  have coordinate := diagram.branch_coordinate index i children branch
  have child_level := diagram.branch_child index i children branch a
  have unknown : p i = none := valid.2.1 i (by omega)
  refine ⟨by have h := valid.1; omega, ?_, ?_⟩
  · rw [child_level]
    exact reverse_prefix_update (diagram.level index) p valid.2.1 i coordinate a
  · exact triangle_step_valid current p valid.2.2 i a unknown

theorem singleton_diagram_step {N : ℕ} (diagram : OrderedDiagram 9 N)
    (fuel : ℕ) (index : Fin N) (current : CachedLocal 8689)
    (p : Partial (Fin 9) (Fin 4)) (i : Fin 9) (children : Fin 4 → Fin N)
    (branch : diagram.nodes index = .branch i children)
    (valid : SingletonValidAt diagram (fuel + 1) index current p) (a : Fin 4) :
    SingletonValidAt diagram fuel (children a) (singletonStep current i a)
      (Function.update p i (some a)) := by
  have depth_lt := diagram.branch_lt index i children branch
  have coordinate := diagram.branch_coordinate index i children branch
  have child_level := diagram.branch_child index i children branch a
  have unknown : p i = none := valid.2.1 i (by omega)
  refine ⟨by have h := valid.1; omega, ?_, ?_⟩
  · rw [child_level]
    exact reverse_prefix_update (diagram.level index) p valid.2.1 i coordinate a
  · exact singleton_step_valid current p valid.2.2 i a unknown

/-- The simulation leaf readout is the actual scaled mirror lower. Its bound
comes only from the complete local acceptance and earned action association. -/
theorem checked_triangle_diagram_lower {N : ℕ} (diagram : OrderedDiagram 10 N)
    (root : Fin N) (root_level : diagram.level root = 0)
    (accepted : checkSimulation diagram.nodes triangleStep (fun current => current.row.lower)
      11 root (initial.triangle 0) = true) (event : Event (Fin 10) (Fin 4)) :
    ∃ value, eval diagram.nodes 11 root event = some value ∧
      value ≤ triangleCentered F1 event := by
  apply checked_simulation_lower_bound (triangleCentered F1) diagram.nodes
    triangleStep (fun current => current.row.lower) (TriangleValidAt diagram)
    (fun _ _ current p event valid compatible =>
      triangle_valid_lower current p event valid.2.2 compatible)
    (triangle_diagram_step diagram) 11 root (initial.triangle 0) (fun _ => none) accepted
  · refine ⟨by omega, ?_, ?_⟩
    · intro i _
      rfl
    · exact (initial_associated).1 0
  · intro i a impossible
    cases impossible

theorem checked_singleton_diagram_lower {N : ℕ} (diagram : OrderedDiagram 9 N)
    (root : Fin N) (root_level : diagram.level root = 0)
    (accepted : checkSimulation diagram.nodes singletonStep (fun current => current.row.lower)
      10 root (initial.singleton 0) = true) (event : Event (Fin 9) (Fin 4)) :
    ∃ value, eval diagram.nodes 10 root event = some value ∧
      value ≤ singletonCentered F2 event := by
  apply checked_simulation_lower_bound (singletonCentered F2) diagram.nodes
    singletonStep (fun current => current.row.lower) (SingletonValidAt diagram)
    (fun _ _ current p event valid compatible =>
      singleton_valid_lower current p event valid.2.2 compatible)
    (singleton_diagram_step diagram) 10 root (initial.singleton 0) (fun _ => none) accepted
  · refine ⟨by omega, ?_, ?_⟩
    · intro i _
      rfl
    · exact (initial_associated).2 0
  · intro i a impossible
    cases impossible

#print axioms triangle_diagram_step
#print axioms checked_ordered_diagram
#print axioms singleton_diagram_step
#print axioms checked_triangle_diagram_lower
#print axioms checked_singleton_diagram_lower

end D5.S3.Quantum.Entanglement.EJM.EJMMDDCacheBridge
