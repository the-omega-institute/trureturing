import LeanInformationAuditRegAnalysis.AuricFib.Macro

/-! Exact rational law-family arithmetic without native execution semantics. -/

namespace LeanInformationAudit.AuricFib.Law
open Lean

private def explanation (kind reason : String) : Json :=
  Json.mkObj [("kind", toJson kind), ("reason", toJson reason)]

/-- Literal law arithmetic is separate from compiled proof qualification.
No native state machine, reply map or guard is assigned to a law family. -/
def analyze (request : Json) : Except String Json := do
  requireKeys request ["arena", "binding", "plan", "acquisition", "law_family",
    "point", "point_unavailable_reason", "facts", "task", "compiled_capture"]
  let point ← request.getObjVal? "point"
  let task ← request.getObjVal? "task"
  let hasTask := task != Json.null
  let f ← if hasTask then (← task.getArr?).mapM parseRational else pure #[0, 0, 0, 0, 0]
  unless f.size == 5 do throw "fib.law_task_requires_five_values"
  let result : Option MacroResult ← if point == Json.null then pure none else do
    let law ← validateLaw (← (← point.getObjVal? "law" >>= Json.getArr?).mapM parseCell)
    let input : SourceInput := ⟨"law-family-point", "supplied rational point", some law, none⟩
    pure (some (← lawAnalysis input law f))
  let unknown := explanation "unknown" "no certified rational point acquired"
  let na := explanation "not-applicable" "law family has no native Window execution or continuation"
  let unverified := explanation "unavailable"
    "supplied metadata; compiled source and proof evidence unverified"
  let numeric := if result.isSome then
    explanation "available" "exact supplied rational point arithmetic" else unknown
  let capture := Json.mkObj [("status", toJson "unknown"),
    ("reason", toJson "no compiled family separation or identifiability witness acquired"),
    ("simplex_width_implies_strict", toJson false)]
  let residuals := result.map (·.residuals) |>.getD (Json.mkObj [])
  let residuals := Json.mkObj <| (← residuals.getObj?).toArray.toList.filter (fun (key, _) =>
    hasTask || !(["J_f", "target_values", "target_expectation",
      "product_completion_target_expectation",
      "target_min", "target_max", "target_range_width", "R_f"] : List String).contains key)
  let associationFields := result.map (·.association.getObj?.toOption.get!.toArray.toList)
  let association := Json.mkObj (associationFields.getD [] ++
    [("family_capture", capture), ("family_facts", ← request.getObjVal? "facts")])
  return Json.mkObj [
    ("arena", Json.mkObj [("kind", toJson "law-family"), ("cardinality", Json.null),
      ("ordered_pair_denominator", Json.null),
      ("scope", toJson "laws on the parameter domain; five atoms are mass cells")]),
    ("source_contract", Json.mkObj [("kind", toJson "unverified-input"), ("binding", Json.null),
      ("supplied_binding", ← request.getObjVal? "binding"),
      ("law_family", ← request.getObjVal? "law_family"), ("point", point),
      ("physical_law_certified", toJson false), ("iid_assumed", toJson false)]),
    ("atom_readout", Json.mkObj [("mode_order", toJson ["null", "2", "5", "25", "3"]),
      ("pairing", ← (← request.getObjVal? "law_family").getObjVal? "mode_pairing")]),
    ("seam_readout", Json.null),
    ("pyramid_coordinates", result.map (·.coordinates) |>.getD Json.null),
    ("association_coordinate", association),
    ("continuation_target", if hasTask then Json.mkObj [("atom_values", task),
      ("scope", toJson "explicit rational atom task; law expectation; no native continuation")]
      else Json.null),
    ("kernel", Json.mkObj [("coarse", toJson "equality of X,Y,Z within the declared family"),
      ("refined", toJson "coarse equality and equal delta")]),
    ("escape_pairs", Json.null), ("escape_rate", Json.null), ("unique_capture", Json.null),
    ("layered_spectrum", Json.mkObj [("family_capture", capture), ("finite_counts", Json.null)]),
    ("residuals", residuals),
    ("disposition", Json.mkObj [("status", toJson "open"), ("is_lean_proof", toJson false),
      ("reason", toJson "supplied law-family data; compiled source and proofs unverified"),
      ("proof_escape", toJson "unchanged; downstream analysis only"),
      ("readings", Json.mkObj [
        ("arena", unverified), ("source_contract", unverified), ("atom_readout", unverified),
        ("seam_readout", na), ("guard", na), ("reply", na), ("R_guard", na),
        ("native_continuation", na), ("conditional_reply_law", na),
        ("pyramid_coordinates", numeric),
        ("association_coordinate", numeric),
        ("family_capture", explanation "unknown" "no compiled family witness acquired"),
        ("continuation_target", if hasTask then
          explanation "available" "supplied rational atom task" else
          explanation "unknown" "no atom task supplied"),
        ("kernel", unverified), ("escape_pairs", unverified), ("escape_rate", unverified),
        ("unique_capture", unverified), ("layered_spectrum", unverified),
        ("residuals", numeric)])])]

end LeanInformationAudit.AuricFib.Law
