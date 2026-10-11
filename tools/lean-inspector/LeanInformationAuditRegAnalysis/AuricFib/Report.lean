import LeanInformationAuditRegAnalysis.AuricFib.Macro
import LeanInformationAuditRegAnalysis.AuricFib.Generic

namespace LeanInformationAudit.AuricFib
open Lean

private def disposition (status reason : String) : Json := Json.mkObj [
  ("status", toJson status), ("reason", toJson reason), ("is_lean_proof", toJson false),
  ("proof_escape", toJson "unchanged; downstream analysis only"),
  ("physical_source_law", toJson "unknown; input validation is not source certification"),
  ("multiwindow_continuation", toJson "unknown; no multiwindow joint contract"),
  ("cost_and_research_value", toJson "not assessed; no aggregate score")]

private def readingReasons (hasLaw : Bool) (continuation request : Json) : Json := Id.run do
  let available := fun reason => Json.mkObj [("kind", toJson "available"), ("reason", toJson reason)]
  let unknown := Json.mkObj [("kind", toJson "unknown"),
    ("reason", toJson "single-window source law unacquired; finite state counts do not supply it")]
  let unknown := (request.getObjVal? "law_acquisition").toOption.getD unknown
  let law := if hasLaw then available "exact declared or empirical law; physical law and IID unverified" else unknown
  let conditional := if !hasLaw then unknown else
    if (continuation.getObjVal? "conditional_reply_law").toOption == some Json.null then
      Json.mkObj [("kind", toJson "not-applicable"), ("reason", toJson "conditioning event has zero mass")]
    else available "positive conditioning mass; apex handled without division by r"
  return Json.mkObj [
    ("arena",
      available "complete five-state Window domain, including rejected and zero-mass states"),
    ("source_contract",
      available "compiled native adapter with explicit initialized specialization"),
    ("atom_readout", available "complete native mode order null,2,5,25,3"),
    ("seam_readout", available "actual high-to-low native reader"),
    ("kernel", available "actual source readouts; bidirectional finite kernel"),
    ("escape_pairs", available "complete ordered off-diagonal five-state census"),
    ("escape_rate", available "complete finite N=5; denominator 20"),
    ("unique_capture", available "complete leave-one-out census"),
    ("layered_spectrum",
      available "initial and all ordered successor layers, including collapsed layers"),
    ("continuation_target", available "total same-state high suffix, including rejection"),
    ("pyramid_coordinates", law), ("association_coordinate", law), ("residuals", law),
    ("conditional_reply_law", conditional),
    ("physical_source_law", Json.mkObj [("kind", toJson "unknown"),
      ("reason",
        toJson "normalization or an empirical archive does not certify a physical law or IID")]),
    ("multiwindow_joint_law", Json.mkObj [("kind", toJson "unknown"),
      ("reason", toJson "single-window law provides no multiwindow joint-law contract")])]

/-- All SPEC 9 fields remain visible even when the input cannot be analyzed. -/
def unavailableReport (status reason arenaKind : String) : Json := Json.mkObj [
  ("arena", Json.mkObj [("kind", toJson arenaKind),
    ("cardinality", Json.null), ("ordered_pair_denominator", Json.null)]),
  ("source_contract", Json.null), ("atom_readout", Json.null), ("seam_readout", Json.null),
  ("pyramid_coordinates", Json.null), ("association_coordinate", Json.null),
  ("continuation_target", Json.null), ("kernel", Json.null), ("escape_pairs", Json.null),
  ("escape_rate", Json.null), ("unique_capture", Json.null), ("layered_spectrum", Json.null),
  ("residuals", Json.null), ("disposition", Json.mkObj (
    (disposition status reason).getObj?.toOption.get!.toArray.toList ++
    [("readings", Json.mkObj ((["arena", "source_contract", "atom_readout", "seam_readout",
      "pyramid_coordinates", "association_coordinate", "continuation_target", "kernel",
      "escape_pairs", "escape_rate", "unique_capture", "layered_spectrum", "residuals"] : List String).map
      fun field => (field, Json.mkObj [
        ("kind", toJson (if arenaKind == "unbounded" && field == "escape_rate"
          then "not-applicable" else "unavailable")), ("reason", toJson reason)]))) ]))]

def analyze (request : Json) : Except String Json := do
  if (request.getObjValAs? String "arena").toOption == some "typed-source" then
    return ← Generic.analyze request
  requireKeys request ["source_contract", "law", "archive", "initial_readouts", "layers", "arena", "binding", "law_acquisition"]
  if let some arena := (request.getObjVal? "arena").toOption then
    let arena ← arena.getStr?
    if arena = "unbounded" then
      requireKeys request ["arena"]
      return unavailableReport "deferred"
        "unbounded arena has no finite denominator or supported joint contract" arena
    unless arena = "native-single-window" do throw "unsupported arena"
  let input ← parseSource request
  let schedule ← parseSchedule request
  let macroResult ← input.law.mapM (macroAnalysis input)
  let responseFields := match macroResult with
    | some result => (result.response.getObj?.toOption.map (·.toArray.toList)).getD []
    | none => [("conditioning_event_mass", Json.null), ("conditional_reply_law", Json.null),
        ("product_completion_conditional_reply_law", Json.null),
        ("unconditional_reply_law", Json.null), ("unconditional_rejection_mass", Json.null),
        ("conditional_rejection_mass", Json.null)]
  let continuation := Json.mkObj <| [
    ("reader", toJson "high-to-low rawMachine(0)"),
    ("initial_seam", toJson false), ("initial_composition", toJson ["0", "0"]),
    ("suffix", toJson ["5"]), ("same_state_continuation", toJson true),
    ("guard", toJson "reject iff prior seam and suffix high bit are true"),
    ("reply_domain", toJson "Option integer; null is the retained absorbing rejection"),
    ("condition", toJson "A: first actual integer reply is odd"),
    ("target", toJson "indicator of A and rejected same-state high suffix"),
    ("conditional_mass_requirement",
      toJson "Y+Z>0; apex uses its unique law without division by r")]
      ++ responseFields
  return Json.mkObj [
    ("arena", Json.mkObj [("kind", toJson "native-single-window"),
      ("state_type",
        toJson "complete five-mode Window; initialized native continuation state is derived"),
      ("cardinality", toJson nativeArena.card),
      ("ordered_pair_denominator", toJson (nativeArena.card * (nativeArena.card-1))),
      ("finiteness_boundary", toJson
        "complete duplicate-free library StateEnumeration; all five atoms including zero-mass cells"),
      ("pair_measure",
        toJson "uniform ordered off-diagonal state pairs; independent of the source-law masses")]),
    ("source_contract", Json.mkObj ((sourceJson input).getObj?.toOption.get!.toArray.toList ++
      [("binding", (request.getObjVal? "binding").toOption.getD Json.null),
       ("law_acquisition", (request.getObjVal? "law_acquisition").toOption.getD Json.null)])),
    ("atom_readout", Json.mkObj [("mode_order", toJson ["null", "2", "5", "25", "3"]),
      ("positions", toJson ["x=low 2", "y=high 5", "z=middle 3"]), ("states", nativeRows)]),
    ("seam_readout", Json.mkObj [("direction", toJson "high-to-low"),
      ("update", toJson "native rawTransition; next seam equals current low bit on acceptance"),
      ("values", toJson (modes.map seam))]),
    ("pyramid_coordinates", macroResult.map (·.coordinates) |>.getD Json.null),
    ("association_coordinate", macroResult.map (·.association) |>.getD Json.null),
    ("continuation_target", continuation), ("kernel", kernelJson),
    ("escape_pairs", pairsJson (nativeCatalog.escapePairs nativeCatalog.fullIndexSet)),
    ("escape_rate", (pairRate (some nativeArena.card) fused.full).getD Json.null),
    ("unique_capture", uniqueJson), ("layered_spectrum", layersJson schedule),
    ("residuals", macroResult.map (·.residuals) |>.getD Json.null),
    ("disposition", Json.mkObj (((disposition (if input.law.isSome then "deferred" else "open")
      (if input.law.isSome then
        "exact finite execution report; not a Lean proof or a certified physical law"
      else
        "finite micro analysis computed; source-law acquisition contract or nonempty archive is missing")).getObj?.toOption.get!.toArray.toList) ++
      [("readings", readingReasons input.law.isSome continuation request)]))]

end LeanInformationAudit.AuricFib
