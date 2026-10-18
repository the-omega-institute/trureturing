/- GID: D5/S3/Quantum/Entanglement/EJM/EJMOriginalDAGEncoding
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/EJMOriginalDAGEncoding
   mirror-E: none(waiver:actual-complete-original-dag-input)
   anchors: []
   utility: none
   digest: Balanced literal storage decodes exact complete-original-DAG words without importing local score tables. -/

/- Untrusted exact certificate input. Source generation and native binding do
not assert Lean acceptance. Actual bound and symmetry predicates must be
checked at every reached partial context of the complete original domain. -/

import Mathlib.Data.Nat.Basic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Quantum.Entanglement.EJM.EJMOriginalDAGEncoding

inductive PackedTree where
  | empty
  | node (index word : ℕ) (left right : PackedTree)

def PackedTree.get : PackedTree → ℕ → ℕ
  | .empty, _ => 0
  | .node index word left right, j =>
    if j = index then word else if j < index then left.get j else right.get j

end D5.S3.Quantum.Entanglement.EJM.EJMOriginalDAGEncoding
