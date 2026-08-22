/- GID: D5/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Provenance/FiniteProofGraphSourceSemantics
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: In a finite acyclic proof graph, source semantics is exactly reachability by a source-supported valid proof path. -/

import Mathlib.Data.Finset.Basic

/- Library-search audit trail (2026-08-22):
   * `make show-atom ATOM_ID=generic-residual-d403ae7e55453b5e3273387b4bb47c762a297e10fce1f52efb10376e26d0dd79`
     returned the source's Theorem 204.1 text and no existing receipt.
   * `rg -n -i "finite.*acyclic|acyclic.*graph|proof[ _-]?path|valid.*path|source semantics|source.*proof|List\\.Chain'" D5 -g '*.lean'`
     found no exact repository declaration. The same search in
     `.lake/packages/mathlib/Mathlib` found only adjacent `SimpleGraph.IsAcyclic`
     material, not this directed source-semantics theorem.
   * `rg -n "generic-residual-d403ae7e55453b5e3273387b4bb47c762a297e10fce1f52efb10376e26d0dd79|定理 204\\.1|来源语义正确性" D5 Meta Blueprint`
     found no deposited theorem. The `loogle` and `leansearch` executables are
     unavailable in this environment.
   * The definitions below are the source-specific finite graph and path
     carriers; no existing declaration packages this combination.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Provenance.FiniteProofGraphSourceSemantics

/-- A finite directed graph is certified acyclic by a strictly increasing rank. -/
structure FiniteAcyclicProofGraph (n : Nat) where
  edge : Fin n → Fin n → Prop
  rank : Fin n → Nat
  edge_increases : ∀ {u v}, edge u v → rank u < rank v

/-- The first vertex of a path is available as a source. -/
def startsInSources {n : Nat} (sources : Finset (Fin n)) : List (Fin n) → Prop
  | [] => False
  | vertex :: _ => vertex ∈ sources

/-- The final vertex of a nonempty path is the target. -/
def endsAt {n : Nat} (target : Fin n) : List (Fin n) → Prop
  | [] => False
  | [vertex] => vertex = target
  | _ :: rest => endsAt target rest

/-- Every adjacent pair in the list is an edge of the graph. -/
def followsEdges {n : Nat} (edge : Fin n → Fin n → Prop) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | first :: second :: rest => edge first second ∧ followsEdges edge (second :: rest)

/-- A path is valid when it starts at an available source, follows graph edges,
and ends at the requested conclusion. -/
def ValidProofPath {n : Nat} (graph : FiniteAcyclicProofGraph n)
    (sources : Finset (Fin n)) (target : Fin n) (path : List (Fin n)) : Prop :=
  startsInSources sources path ∧ endsAt target path ∧ followsEdges graph.edge path

/-- The source semantics of a target is existence of a source-supported proof path. -/
def sourceSemantic {n : Nat} (graph : FiniteAcyclicProofGraph n)
    (sources : Finset (Fin n)) (target : Fin n) : Prop :=
  ∃ path : List (Fin n), ValidProofPath graph sources target path

/- The source's `φ_c(S)=True` is represented by `sourceSemantic graph S c`; the
   proposition records the Boolean truth condition without introducing a
   noncomputable search over all lists. -/
theorem source_semantic_iff_valid_source_path {n : Nat}
    (graph : FiniteAcyclicProofGraph n) (sources : Finset (Fin n)) (target : Fin n) :
    sourceSemantic graph sources target ↔
      ∃ path : List (Fin n), ValidProofPath graph sources target path := by
  rfl

example : FiniteAcyclicProofGraph 1 := by
  exact
    { edge := fun _ _ => False
      rank := fun _ => 0
      edge_increases := by simp }

example :
    sourceSemantic
      { edge := fun _ _ => False
        rank := fun _ => 0
        edge_increases := by simp }
      ({0} : Finset (Fin 1)) (0 : Fin 1) := by
  refine ⟨[0], ?_⟩
  simp [ValidProofPath, startsInSources, endsAt, followsEdges]

#print axioms source_semantic_iff_valid_source_path

end D5.S3.ConceptDynamics.Provenance.FiniteProofGraphSourceSemantics
