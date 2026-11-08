/- GID: D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree
   generality: I
   mirror-B: D5/B/S3/StatisticalMechanics/VertexModels/PonciniRasmussenCertificateTree
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenMinpolyRefutation.result; premises=D5/S3/StatisticalMechanics/VertexModels/PonciniRasmussenNineHorner.annihilation
   digest: Shared parity-indexed trees for the exact nine-strand certificate data. -/

/-
admission_basis: open-problem-resolution (#27843; Refuted)
escape_witness: none (the settlement of the external open problem is the new content)
Qualified-name abbreviations:
PonciniRasmussenCertificateTree = D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree
PonciniRasmussenNineDiagrams = D5.S3.StatisticalMechanics.PonciniRasmussenNineDiagrams
PonciniRasmussenNineEdges = D5.S3.StatisticalMechanics.PonciniRasmussenNineEdges
PonciniRasmussenNineHorner = D5.S3.StatisticalMechanics.PonciniRasmussenNineHorner

Direct frozen dependencies (declaration statement_ids):
none (direct prerequisites are unfrozen or pinned upstream)
Tree: proof_shape=bind-only; consumers=PonciniRasmussenCertificateTree.get,
  PonciniRasmussenNineDiagrams.rawData, PonciniRasmussenNineDiagrams.transitions,
  PonciniRasmussenNineHorner.rows, PonciniRasmussenNineHorner.v0
get: proof_shape=bind-only; consumers=PonciniRasmussenNineDiagrams.raw,
  PonciniRasmussenNineDiagrams.transition, PonciniRasmussenNineHorner.sparseHamiltonian,
  PonciniRasmussenNineHorner.state, PonciniRasmussenNineEdges.incoming
-/
import Lean

set_option autoImplicit false

namespace D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree

inductive Tree (α : Type) where
  | leaf : α → Tree α
  | node : Tree α → Tree α → Tree α

def get {α : Type} : Tree α → Nat → α
  | .leaf a, _ => a
  | .node l r, j => if j % 2 = 0 then get l (j/2) else get r (j/2)

open Lean Elab Term
syntax "prb1_tree_data% " term : term
elab_rules : term <= expectedType
  | `(prb1_tree_data% $t) => withEnableInfoTree false (elabTerm t (some expectedType))

end D5.S3.StatisticalMechanics.PonciniRasmussenCertificateTree
