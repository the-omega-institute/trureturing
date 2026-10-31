/- GID: D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierSelector
   generality: I
   mirror-B: D5/B/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierSelector
   mirror-E: none(waiver:exact-original-context-mathematical-source)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.original_score_lower_bound; instance=D5/S3/Quantum/Entanglement/EJM/PreparedEJMCompleteFrontierRoot.accepted_original_root
   digest: The selector decodes a valid actual partial assignment, looks up its full depth and code, and checks the node index and retained metadata. -/

/- Prepared, uncompiled complete-table selector.
The executable selector reads the actual prefix and verifies the complete
stored cut metadata. Its soundness requires the concrete all-cut Responses
theorem, which is generated from separate actual original suffix receipts.
It never equates associated caches, reuses a shape's acceptance, or infers a
local score bound from raw symmetry acceptance. -/
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTable
import D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontierTypes
import D5.S3.Quantum.Entanglement.EJM.Frontier.EJMOriginalPrefixDecoder

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
open EJMOriginalCachedGlobalReplay (Valid)

/-- Look up the exact original depth/code, then check index and every retained
metadata field. Positive original fuel bounds the decoder to twenty coordinates.
All 52,867 cuts remain represented; no semantic subset replaces the cut table. -/
def selected (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (p : Partial (Fin 20) (Fin 4)) : Option CutRow :=
  if 0 < fuel ∧ fuel ≤ 21 then
    match TransientEJMOriginalPrefixDecoder.readPrefix (21 - fuel) p with
    | none => none
    | some code =>
        match cutTable.lookup (21 - fuel) code with
        | none => none
        | some cut =>
            if cut.depth = 21 - fuel ∧ cut.code = code ∧
                cut.index = index.val ∧ metadata cut = true then some cut else none
  else none

def frontier (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (_cache : Cache) (p : Partial (Fin 20) (Fin 4)) : Bool :=
  (selected fuel index p).isSome

/-- Valid recovers only the actual partial assignment. There is deliberately
no cache equality in the conclusion or in the proof. -/
theorem selected_spec (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (cache : Cache) (p : Partial (Fin 20) (Fin 4)) (cut : CutRow)
    (valid : Valid fuel cache p) (chosen : selected fuel index p = some cut) :
    p = prefixPartial cut.depth cut.code ∧
      cutTable.lookup cut.depth cut.code = some cut := by
  by_cases window : 0 < fuel ∧ fuel ≤ 21
  · cases readEq : TransientEJMOriginalPrefixDecoder.readPrefix (21 - fuel) p with
    | none => simp [selected, window, readEq] at chosen
    | some code =>
        cases lookupEq : cutTable.lookup (21 - fuel) code with
        | none => simp [selected, window, readEq, lookupEq] at chosen
        | some row =>
            by_cases checked : row.depth = 21 - fuel ∧ row.code = code ∧
                row.index = index.val ∧ metadata row = true
            · have rowEq : row = cut := by
                simpa [selected, window, readEq, lookupEq, checked] using chosen
              subst cut
              have within : row.depth ≤ 20 := by omega
              have fuelEq : 21 - row.depth = fuel := by omega
              have validAt : Valid (21 - row.depth) cache p := by
                simpa only [fuelEq] using valid
              have readAt : TransientEJMOriginalPrefixDecoder.readPrefix row.depth p =
                  some row.code := by
                simpa only [checked.1, checked.2.1] using readEq
              have partialEq :=
                ((TransientEJMOriginalPrefixDecoder.readPrefix_eq_some_iff
                  row.depth row.code p cache within validAt).mp readAt).2
              refine ⟨partialEq, ?_⟩
              simpa only [checked.1, checked.2.1] using lookupEq
            · simp [selected, window, readEq, lookupEq, checked] at chosen
  · simp [selected, window] at chosen

/-- Every marked valid context consumes its actual table receipt. Canonical
raw receipts provide a bad-event response using their own canonical cache;
only the compatible partial assignment is transported to this call. -/
theorem frontier_responses (ready : cutTable.Responses)
    (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size) (cache : Cache)
    (p : Partial (Fin 20) (Fin 4)) (valid : Valid fuel cache p)
    (marked : frontier fuel index cache p = true) (e : Event (Fin 20) (Fin 4))
    (compatible : Compatible p e) (bad : score F1 F2 e < scale) :
    ∃ e', score F1 F2 e' < scale ∧ FiniteLexSymmetry.rank e' < FiniteLexSymmetry.rank e := by
  cases chosen : selected fuel index p with
  | none => simp only [frontier, chosen, Option.isSome_none, Bool.false_eq_true] at marked
  | some cut =>
      obtain ⟨partialEq, lookupEq⟩ := selected_spec fuel index cache p cut valid chosen
      have response := lookup_response cutTable ready cut.depth cut.code cut lookupEq
      apply response e
      · simpa only [← partialEq] using compatible
      · exact bad

theorem checked_of_selected (fuel : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (cache : Cache) (p : Partial (Fin 20) (Fin 4)) (cut : CutRow)
    (positive : 0 < fuel) (chosen : selected fuel index p = some cut) :
    FiniteAdaptiveSemanticFrontierReplay.check EJMOriginalGlobalDAGData.nodes
      step lower EJMGlobalScoreSymmetry.dominates scale frontier fuel index cache p = true := by
  have marked : frontier fuel index cache p = true := by simp only [frontier, chosen, Option.isSome_some]
  cases fuel with
  | zero => omega
  | succ fuel => simp only [FiniteAdaptiveSemanticFrontierReplay.check, marked, ite_true]

theorem accepted_of_selected (depth code : Nat) (index : Fin EJMOriginalGlobalDAGData.Size)
    (cut : CutRow) (within : depth ≤ 20)
    (chosen : selected (21 - depth) index (prefixPartial depth code) = some cut) :
    TransientEJMOriginalAdaptiveFrontierBridge.Accepted frontier depth code index := by
  exact checked_of_selected (21 - depth) index (prefixCache depth code)
    (prefixPartial depth code) cut (by omega) chosen

#print axioms selected_spec
#print axioms frontier_responses
end D5.S3.Quantum.Entanglement.EJM.PreparedEJMCompleteFrontier
