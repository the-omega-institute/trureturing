import LeanInformationAuditRegAnalysis.AuricFib.Report

/-! Production projection of compiled acquisition. Family and task verdicts
are acquired from constructor evidence before serialization in FibLaw. -/
namespace LeanInformationAudit.AuricFib
open Lean

private def replace (object : Json) (key : String) (value : Json) : Except String Json := do
  let fields ← object.getObj?
  return Json.mkObj ((fields.toArray.toList.filter (·.1 != key)) ++ [(key, value)])

private def remove (object : Json) (keys : List String) : Except String Json := do
  return Json.mkObj ((← object.getObj?).toArray.toList.filter fun (key, _) => !keys.contains key)

private def explanation (kind reason : String) : Json :=
  Json.mkObj [("kind", toJson kind), ("reason", toJson reason)]

/-- Called only by the compiler artifact producer. The public JSON arithmetic
entry retains its unverified scope, even for a replay of a compiled request. -/
def qualifyCompiled (request reading : Json) : Except String Json := do
  let mut reading := reading
  let mut disposition ← reading.getObjVal? "disposition"
  if (← disposition.getObjValAs? String "status") == "refuted" then return reading
  let mut readings ← disposition.getObjVal? "readings"
  let mut source ← reading.getObjVal? "source_contract"
  let arena := (request.getObjValAs? String "arena").toOption.getD "native-single-window"
  if arena == "law-family" then
    source ← remove source ["supplied_binding"]
    source ← replace source "kind" (toJson "law-family")
    source ← replace source "binding" (← request.getObjVal? "binding")
    disposition ← replace disposition "reason"
      (toJson "compiled mass-valued law family; ordinary audit obligations remain independent")
    for field in ["arena", "source_contract", "atom_readout", "kernel"] do
      readings ← replace readings field (explanation "available"
        "full source binding, atom bijection and actual mass readout equality")
    for field in ["seam_readout", "guard", "reply", "R_guard", "native_continuation", "conditional_reply_law"] do
      readings ← replace readings field (explanation "not-applicable" "law family declares no native Window execution")
    let acquisition ← request.getObjVal? "acquisition"
    for field in ["escape_pairs", "escape_rate", "unique_capture"] do
      readings ← replace readings field (explanation
        (if (← acquisition.getObjValAs? String "kind") == "infinite" then "not-applicable" else "unavailable")
        (← acquisition.getObjValAs? String "reason"))
    readings ← replace readings "layered_spectrum" (explanation "available"
      "qualitative family capture; finite counts acquired separately")
    -- Pure projection: no decoded fact-kind test, numerical classification or
    -- family-status decision is made from JSON here.
    let compiled ← request.getObjVal? "compiled_capture"
    let capture ← compiled.getObjVal? "family"
    reading ← replace reading "association_coordinate"
      (← replace (← reading.getObjVal? "association_coordinate") "family_capture" capture)
    reading ← replace reading "layered_spectrum"
      (← replace (← reading.getObjVal? "layered_spectrum") "family_capture" capture)
    readings ← replace readings "family_capture" (← compiled.getObjVal? "reading")
    let point ← request.getObjVal? "point"
    let pointReason ← request.getObjValAs? String "point_unavailable_reason"
    for field in ["pyramid_coordinates", "association_coordinate", "residuals"] do
      readings ← replace readings field (explanation
        (if point != Json.null then "available" else if pointReason.isEmpty then "unknown" else "unavailable")
        (if point != Json.null then "exact rational point with domain membership and pointwise source-law equality"
          else if pointReason.isEmpty then "law defined; no certified rational point supplied" else pointReason))
    if (← request.getObjVal? "task") != Json.null then
      readings ← replace readings "continuation_target" (explanation "available"
        "explicit rational atom task; no native continuation")
      let mut task ← reading.getObjVal? "continuation_target"
      task ← replace task "family_capture" (← compiled.getObjVal? "task")
      task ← replace task "uses_delta" (← compiled.getObjVal? "uses_delta")
      reading ← replace reading "continuation_target" task
  else if arena == "native-single-window" then
    source ← remove source ["supplied_binding", "supplied_law_acquisition"]
    source ← replace source "binding" (← request.getObjVal? "binding")
    source ← replace source "law_acquisition" ((request.getObjVal? "law_acquisition").toOption.getD Json.null)
    readings ← replace readings "source_contract" (explanation "available"
      "compiled native adapter with explicit initialized specialization")
    let hasLaw := (← source.getObjVal? "pushforward_law") != Json.null
    disposition ← replace disposition "reason" (toJson (if hasLaw then
      "exact finite execution report; not a Lean proof or a certified physical law"
      else "finite micro analysis computed; source-law acquisition contract or nonempty archive is missing"))
    if hasLaw then
      for field in ["pyramid_coordinates", "association_coordinate", "residuals"] do
        readings ← replace readings field (explanation "available"
          "exact declared or empirical law; physical law and IID unverified")
      if (← (← reading.getObjVal? "continuation_target").getObjVal? "conditional_reply_law") != Json.null then
        readings ← replace readings "conditional_reply_law" (explanation "available"
          "positive conditioning mass; apex handled without division by r")
    else if (← source.getObjVal? "law_acquisition") != Json.null then
      for field in ["pyramid_coordinates", "association_coordinate", "residuals", "conditional_reply_law"] do
        readings ← replace readings field (← source.getObjVal? "law_acquisition")
  else if arena == "typed-source" then
    let acquisition ← request.getObjVal? "acquisition"
    let kind ← acquisition.getObjValAs? String "kind"
    let reason ← acquisition.getObjValAs? String "reason"
    let finite := kind == "finite"
    disposition ← replace disposition "reason" (toJson
      "source-bound downstream analysis; ordinary audit obligations remain independent")
    for (field, state, why) in [
        ("arena", if finite || kind == "infinite" then "available" else "unavailable", reason),
        ("source_contract", "available", "full compiled source correspondence; probability law unknown"),
        ("continuation_target", "available", "same-source total task; numerical outputs require acquired presentation"),
        ("kernel", "available", "structural equality kernels exist for the full actual family"),
        ("layered_spectrum", "available", "source-bound weak refinement; counts require finite acquisition")] do
      readings ← replace readings field (explanation state why)
    for field in ["escape_pairs", "unique_capture"] do
      readings ← replace readings field (explanation
        (if finite then "available" else if kind == "infinite" then "not-applicable" else "unavailable")
        (if finite then "complete certified domain and bidirectional table reflection" else reason))
    let n := ((← reading.getObjVal? "arena").getObjValAs? Nat "cardinality").toOption
    readings ← replace readings "escape_rate" (explanation
      (if n.any (· > 1) then "available" else if kind == "infinite" || n.isSome then "not-applicable" else "unavailable")
      (if n.any (· > 1) then "N(N-1) ordered off-diagonal pairs"
        else if kind == "infinite" || n.isSome then "finite pair rate requires complete finite N>1" else reason))
    source ← remove source ["supplied_binding", "supplied_acquisition"]
    source ← replace source "kind" (toJson "typed-source")
    source ← replace source "binding" (← request.getObjVal? "binding")
    source ← replace source "acquisition" acquisition
    reading ← replace reading "continuation_target" (← replace (← reading.getObjVal? "continuation_target") "scope"
      (toJson (if finite then "same actual source realization; complete finite total task" else "same actual source realization; total task")))
    let mut domain ← reading.getObjVal? "arena"
    domain ← replace domain "kind" (toJson (if finite then "certified-finite-presentation" else kind))
    if finite then
      domain ← replace domain "scope_boundary" (toJson
        "counts refer only to the certified whole fiber, restriction or quotient; original theorem remains universal")
      reading ← replace reading "kernel" (← replace (← reading.getObjVal? "kernel") "scope"
        (toJson "certified readout kernels and supplied layers; no exponential lattice claimed"))
    else domain ← replace domain "reason" (toJson reason)
    reading ← replace reading "arena" domain
  reading ← replace reading "source_contract" source
  disposition ← replace disposition "readings" readings
  replace reading "disposition" disposition

end LeanInformationAudit.AuricFib
