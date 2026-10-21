/- GID: D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierDataTypes
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierDataTypes
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: none
   digest: Pure seven-field cut rows, balanced tables and exact coordinate lookup. -/

import Init

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! Pure storage and lookup for original cut rows. Acceptance is defined separately. -/

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier

/-- All seven original binary fields are retained, including reserved zero. -/
structure CutRow where
  depth : Nat
  kind : Nat
  reserved : Nat
  index : Nat
  code : Nat
  subtreeContexts : Nat
  domain : Nat
deriving DecidableEq

/-- Balanced lookup is by full prefix depth and code; index is checked after
lookup. The tree shape and ordering are not trusted as mathematical evidence. -/
inductive CutTable where
  | empty
  | leaf (cut : CutRow)
  | branch (pivotDepth pivotCode : Nat) (left right : CutTable)

def CutTable.lookup : CutTable → Nat → Nat → Option CutRow
  | .empty, _, _ => none
  | .leaf cut, depth, code =>
      if cut.depth = depth ∧ cut.code = code then some cut else none
  | .branch pivotDepth pivotCode left right, depth, code =>
      if depth < pivotDepth ∨ (depth = pivotDepth ∧ code < pivotCode) then
        left.lookup depth code
      else right.lookup depth code

end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
