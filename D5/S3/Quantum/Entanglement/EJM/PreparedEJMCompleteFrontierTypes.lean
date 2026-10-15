/- Prepared source only; no Lean invocation or acceptance claim.
The data are untrusted until the explicit kernel goals in the generated
consumer modules pass. No native subtree size is a theorem premise. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMAdaptiveResponseBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
open D5.S0.Certificates
open FiniteSymmetryBoundReplay (Partial Event Compatible)
open EJMOriginalReplayAssembly (prefixCache prefixPartial coordinate)
open EJMCacheState (Cache step lower)
open EJMPartialBoundData (scale)
open EJMCertificateData (F1 F2)
open EJMInflationScore (score)

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

def CutTable.count : CutTable → Nat
  | .empty => 0
  | .leaf _ => 1
  | .branch _ _ left right => left.count + right.count

def CutTable.domainSum : CutTable → Nat
  | .empty => 0
  | .leaf cut => cut.domain
  | .branch _ _ left right => left.domainSum + right.domainSum

/-- Count the literal original nodes, with all four edges and their occurrence
multiplicity. It is independent of score/cache acceptance, so shared shape may
share this count, but never an actual-context replay receipt. -/
def subtreeContexts : Nat → Fin EJMOriginalGlobalDAGData.Size → Nat
  | 0, _ => 0
  | fuel + 1, index =>
      match EJMOriginalGlobalDAGData.nodes (fuel + 1) index with
      | .bound | .symmetry _ => 1
      | .split _ children =>
          1 + subtreeContexts fuel (children 0) + subtreeContexts fuel (children 1) +
            subtreeContexts fuel (children 2) + subtreeContexts fuel (children 3)

/-- Every stored field that can affect selection is checked. In particular,
the stored subtree size is compared against the original executable DAG; a
producer's `size ≤ 4096` assertion does not stand in for this equality. -/
def metadata (cut : CutRow) : Bool :=
  if hindex : cut.index < EJMOriginalGlobalDAGData.Size then
    decide (cut.reserved = 0 ∧ cut.depth ≤ 20 ∧ cut.code < 4 ^ cut.depth ∧
      cut.kind < 3 ∧ cut.kind = EJMOriginalGlobalDAGData.word cut.index % 4 ∧
      cut.domain = 4 ^ (20 - cut.depth) ∧ 0 < cut.subtreeContexts ∧
      cut.subtreeContexts ≤ 4096 ∧
      cut.subtreeContexts = subtreeContexts (21 - cut.depth) ⟨cut.index, hindex⟩)
  else false

/-- A raw symmetry suffix supplies rank descent, not a local score bound.
This response depends on the actual prefix, and therefore transports through
the decoder's partial equality without equating associated caches. -/
def CanonicalResponse (cut : CutRow) : Prop :=
  ∀ e : Event (Fin 20) (Fin 4), Compatible (prefixPartial cut.depth cut.code) e →
    score F1 F2 e < scale →
      ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e

theorem canonical_valid (depth code : Nat) (within : depth ≤ 20) :
    EJMOriginalCachedGlobalReplay.Valid (21 - depth)
      (prefixCache depth code) (prefixPartial depth code) := by
  exact PreparedEJMAdaptiveResponseBridge.canonical_valid depth code within

theorem response_of_raw (cut : CutRow) (within : cut.depth ≤ 20)
    (hindex : cut.index < EJMOriginalGlobalDAGData.Size)
    (accepted : EJMOriginalReplayAssembly.Accepted cut.depth cut.code ⟨cut.index, hindex⟩) :
    CanonicalResponse cut := by
  intro e hp hbad
  exact PreparedEJMAdaptiveResponseBridge.accepted_suffix_bad_event_response
    cut.depth cut.code ⟨cut.index, hindex⟩ within accepted e hp hbad

theorem response_of_semantic (cut : CutRow)
    (semantic : ∀ e : Event (Fin 20) (Fin 4),
      Compatible (prefixPartial cut.depth cut.code) e → scale ≤ score F1 F2 e) :
    CanonicalResponse cut := by
  intro e hp hbad
  exact False.elim ((not_lt_of_ge (semantic e hp)) hbad)

/-- The concrete all-cut theorem must fill every leaf with an actual proof.
This proposition never treats native metadata or a root-acceptance assumption
as a substitute for a missing cut receipt. -/
def CutTable.Responses : CutTable → Prop
  | .empty => True
  | .leaf cut => CanonicalResponse cut
  | .branch _ _ left right => left.Responses ∧ right.Responses

theorem lookup_response (table : CutTable) : table.Responses →
    ∀ (depth code : Nat) (cut : CutRow), table.lookup depth code = some cut →
      CanonicalResponse cut := by
  induction table with
  | empty =>
      intro ready depth code cut chosen
      cases chosen
  | leaf row =>
      intro ready depth code cut chosen
      simp only [CutTable.lookup] at chosen
      split_ifs at chosen with same
      · have equality : row = cut := Option.some.inj chosen
        subst cut
        exact ready
      · cases chosen
  | branch pivotDepth pivotCode left right ihLeft ihRight =>
      intro ready depth code cut chosen
      simp only [CutTable.lookup] at chosen
      split_ifs at chosen with earlier
      · exact ihLeft ready.1 depth code cut chosen
      · exact ihRight ready.2 depth code cut chosen

#print axioms response_of_raw
#print axioms lookup_response
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
