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
  PonciniRasmussenNineHorner.rows,
  PonciniRasmussenNineHorner.v0,
  PonciniRasmussenNineHorner.v1,
  PonciniRasmussenNineHorner.v2,
  PonciniRasmussenNineHorner.v3,
  PonciniRasmussenNineHorner.v4,
  PonciniRasmussenNineHorner.v5,
  PonciniRasmussenNineHorner.v6,
  PonciniRasmussenNineHorner.v7,
  PonciniRasmussenNineHorner.v8,
  PonciniRasmussenNineHorner.v9,
  PonciniRasmussenNineHorner.v10,
  PonciniRasmussenNineHorner.v11,
  PonciniRasmussenNineHorner.v12,
  PonciniRasmussenNineHorner.v13,
  PonciniRasmussenNineHorner.v14,
  PonciniRasmussenNineHorner.v15,
  PonciniRasmussenNineHorner.v16,
  PonciniRasmussenNineHorner.v17,
  PonciniRasmussenNineHorner.v18,
  PonciniRasmussenNineHorner.v19,
  PonciniRasmussenNineHorner.v20,
  PonciniRasmussenNineHorner.v21,
  PonciniRasmussenNineHorner.v22,
  PonciniRasmussenNineHorner.v23,
  PonciniRasmussenNineHorner.v24,
  PonciniRasmussenNineHorner.v25,
  PonciniRasmussenNineHorner.v26,
  PonciniRasmussenNineHorner.v27,
  PonciniRasmussenNineHorner.v28,
  PonciniRasmussenNineHorner.v29,
  PonciniRasmussenNineHorner.v30,
  PonciniRasmussenNineHorner.v31,
  PonciniRasmussenNineHorner.v32,
  PonciniRasmussenNineHorner.v33,
  PonciniRasmussenNineHorner.v34,
  PonciniRasmussenNineHorner.v35,
  PonciniRasmussenNineHorner.v36,
  PonciniRasmussenNineHorner.v37,
  PonciniRasmussenNineHorner.v38,
  PonciniRasmussenNineHorner.v39,
  PonciniRasmussenNineHorner.v40,
  PonciniRasmussenNineHorner.v41,
  PonciniRasmussenNineHorner.v42,
  PonciniRasmussenNineHorner.v43,
  PonciniRasmussenNineHorner.v44,
  PonciniRasmussenNineHorner.v45,
  PonciniRasmussenNineHorner.v46,
  PonciniRasmussenNineHorner.v47,
  PonciniRasmussenNineHorner.v48,
  PonciniRasmussenNineHorner.v49,
  PonciniRasmussenNineHorner.v50,
  PonciniRasmussenNineHorner.v51,
  PonciniRasmussenNineHorner.v52,
  PonciniRasmussenNineHorner.v53,
  PonciniRasmussenNineHorner.v54,
  PonciniRasmussenNineHorner.v55,
  PonciniRasmussenNineHorner.v56,
  PonciniRasmussenNineHorner.v57,
  PonciniRasmussenNineHorner.v58
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
