import LeanInformationAuditRegAnalysis.AuricFib.Census

namespace LeanInformationAudit.AuricFib.Generic
open Lean
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.CIRPT

attribute [local instance] Arena.stateFintype Arena.stateDecidableEq

private def explanation (kind reason : String) : Json :=
  Json.mkObj [("kind", toJson kind), ("reason", toJson reason)]

private def dispositions (kind reason : String) (n : Option Nat) : Json :=
  let finite := kind == "finite"
  let countKind := if finite then "available" else if kind == "infinite" then "not-applicable" else "unavailable"
  let countReason := if finite then "complete certified domain and bidirectional table reflection" else reason
  let rateKind := if n.any (· > 1) then "available" else if kind == "infinite" || n.isSome then "not-applicable" else "unavailable"
  Json.mkObj [
    ("status", toJson (if finite then "deferred" else "open")),
    ("reason",
      toJson "source-bound downstream analysis; ordinary audit obligations remain independent"),
    ("is_lean_proof", toJson false), ("proof_escape", toJson "unchanged; downstream analysis only"),
    ("readings", Json.mkObj [
      ("arena",
        explanation (if finite || kind == "infinite" then "available" else "unavailable") reason),
      ("source_contract",
        explanation "available" "full compiled source correspondence; probability law unknown"),
      ("source_law", explanation "unknown" "no source probability law supplied or certified"),
      ("atom_readout",
        explanation "not-applicable" "generic contract declares no FIB atom semantics"),
      ("seam_readout",
        explanation "not-applicable" "generic contract declares no native seam semantics"),
      ("pyramid_coordinates",
        explanation "not-applicable" "generic contract declares no FIB semantics"),
      ("association_coordinate",
        explanation "not-applicable" "generic contract declares no FIB law semantics"),
      ("continuation_target",
        explanation "available" "same-source total task; numerical outputs require acquired presentation"),
      ("kernel",
        explanation "available" "structural equality kernels exist for the full actual family"),
      ("escape_pairs", explanation countKind countReason),
      ("escape_rate",
        explanation rateKind (if n.any (· > 1) then "N(N-1) ordered off-diagonal pairs"
        else if kind == "infinite" || n.isSome then "finite pair rate requires complete finite N>1" else reason)),
      ("unique_capture", explanation countKind countReason),
      ("layered_spectrum",
        explanation "available" "source-bound weak refinement; counts require finite acquisition"),
      ("residuals", explanation "not-applicable" "no FIB law or response semantics declared")])]

private def natural (object : Json) (field : String) : Except String Nat :=
  object.getObjValAs? Nat field

private def selected (initial : Array Nat) (additions : Array (Array Nat)) (position : Nat) : Array Nat :=
  initial ++ (additions.extract 0 position).flatten

private abbrev finiteArena (n : Nat) : Arena := Arena.ofFintype (Fin n)

/-- A reflected equivalence row is a code for its actual source fiber. Runtime
validation checks equality of these codes against every certified table cell. -/
private def catalog (n : Nat) (tables : Array (Array (Array Bool))) : Catalog (finiteArena n) :=
  Catalog.ofVector fun i : Fin tables.size => {
    primitives := {
      Index := Fin 1, indexFintype := inferInstance, indexDecidableEq := inferInstance,
      atom := fun _ => ⟨.cut, cutKernel (fun state : Fin n => (tables[i.val]!)[state.val]!.toList)⟩ }
    Statement := True, proof := True.intro }

private def enumeration (n : Nat) : Arena.StateEnumeration (finiteArena n) where
  states := List.finRange n
  nodup := List.nodup_finRange n
  complete := by
    change (List.finRange n).toFinset = (Finset.univ : Finset (Fin n))
    simp

private def pairList {n : Nat} (pairs : Finset (Fin n × Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun a => (List.finRange n).filterMap fun b =>
    if (a, b) ∈ pairs then some (a, b) else none

private def pairsJson {n : Nat} (pairs : Finset (Fin n × Fin n)) : Json :=
  toJson ((pairList pairs).map fun (a, b) => [a.val, b.val])

private def selectionSet (size : Nat) (xs : Array Nat) : Finset (Fin size) :=
  ((List.finRange size).filter fun i => xs.contains i.val).toFinset

private def validateMatrices (n : Nat) (tables : Array (Array (Array Bool))) : Except String Unit := do
  for table in tables do
    unless table.size == n && table.all (·.size == n) do throw "fib.table_shape"
    for i in [:n] do
      for j in [:n] do
        unless (table[i]!)[j]! == (table[i]! == table[j]!) do
          throw "fib.table_kernel_reflection"

/-- Canonical generic analysis consumes only compiler-acquired certified data.
The input is not a new proof or ordinary registration status. -/
def analyze (request : Json) : Except String Json := do
  requireKeys request ["arena", "binding", "plan", "acquisition", "finite"]
  let binding ← request.getObjVal? "binding"
  let plan ← request.getObjVal? "plan"
  let roles ← plan.getObjValAs? (Array Json) "roles"
  let available ← plan.getObjValAs? Bool "available"
  let initial ← if !available then pure #[] else plan.getObjValAs? (Array Nat) "initial"
  let additions ← if !available then pure #[] else plan.getObjValAs? (Array (Array Nat)) "additions"
  let task ← if !available then pure 0 else natural plan "task"
  unless !available || (task < roles.size &&
      (selected initial additions additions.size).all (· < roles.size)) do
    throw "fib.plan_role_scope"
  let acquisition ← request.getObjVal? "acquisition"
  let kind ← acquisition.getObjValAs? String "kind"
  let reason ← acquisition.getObjValAs? String "reason"
  unless #["finite", "infinite", "unavailable"].contains kind do throw "fib.acquisition_kind"
  let source := Json.mkObj [("kind", toJson "typed-source"), ("binding", binding),
    ("acquisition", acquisition), ("law", Json.null),
    ("physical_law_certified",
      toJson false), ("source_law", explanation "unknown" "no probability law acquired")]
  let emptyArena := Json.mkObj [("kind", toJson kind), ("cardinality", Json.null),
    ("ordered_pair_denominator", Json.null), ("reason", toJson reason)]
  let mut arena := emptyArena
  let mut continuation := Json.mkObj [("task", if available then toJson task else Json.null), ("outputs", Json.null),
    ("scope", toJson "same actual source realization; total task"), ("plan", plan)]
  let mut kernel := Json.mkObj [("structural", plan), ("finite_tables", Json.null)]
  let mut spectrum := Json.mkObj [("structural", plan), ("layers", Json.null),
    ("unresolved", Json.null)]
  let mut pairs := Json.null
  let mut rate := Json.null
  let mut unique := Json.null
  let mut cardinality := none
  if kind == "finite" then
    unless available do throw "fib.finite_plan_unavailable"
    let finite ← request.getObjVal? "finite"
    let n ← natural finite "cardinality"
    cardinality := some n
    let states ← finite.getObjValAs? (Array Json) "states"
    let outputs ← finite.getObjValAs? (Array (Array Json)) "outputs"
    let taskOutputs ← finite.getObjValAs? (Array Json) "task_outputs"
    let tables ← finite.getObjValAs? (Array (Array (Array Bool))) "kernels"
    let layerTables ← finite.getObjValAs? (Array (Array (Array Bool))) "layers"
    unless states.size == n && outputs.size == roles.size && outputs.all (·.size == n) &&
        taskOutputs.size == n && tables.size == roles.size && layerTables.size == additions.size + 1 do
      throw "fib.finite_presentation_shape"
    validateMatrices n tables
    validateMatrices n layerTables
    for position in [:layerTables.size] do
      let chosen := selected initial additions position
      for i in [:n] do
        for j in [:n] do
          unless ((layerTables[position]!)[i]!)[j]! == chosen.all (fun r => ((tables[r]!)[i]!)[j]!) do
            throw "fib.layer_source_reflection"
    let catalog := catalog n tables
    let selectedAt := fun position => selectionSet tables.size (selected initial additions position)
    let fused := catalog.fusedCounts (enumeration n) (Catalog.finIndexEnumeration tables.size)
    pairs := pairsJson (catalog.escapePairs catalog.fullIndexSet)
    rate := (pairRate (some n) fused.full).getD Json.null
    unique := toJson ((List.finRange tables.size).map fun i => Json.mkObj [
      ("readout", toJson i.val), ("count", toJson (fused.unique i)),
      ("pairs", pairsJson (catalog.uniqueCapturePairs i)),
      ("rate", (pairRate (some n) (fused.unique i)).getD Json.null),
      ("leave_one_out_count", toJson (fused.without i)),
      ("leave_one_out_pairs", pairsJson (catalog.escapePairs (catalog.without i)))])
    let residual := fun position => catalog.escapePairs (selectedAt position)
    let allPairs := catalog.escapePairs ∅
    let layers := (List.range (additions.size + 1)).map fun position =>
      let captured := (if position == 0 then allPairs else residual (position - 1)) \ residual position
      Json.mkObj [("position", toJson position), ("readouts", toJson (selected initial additions position)),
        ("count", toJson captured.card), ("pairs", pairsJson captured),
        ("rate", (pairRate (some n) captured.card).getD Json.null),
        ("collapsed",
          toJson (position > 0 && layerTables[position]! == layerTables[position - 1]!))]
    let final := residual additions.size
    let addresses := (pairList allPairs).map fun (a, b) => Json.mkObj [
      ("pair", toJson [a.val, b.val]),
      ("first_layer", toJson ((List.range layerTables.size).find? fun position =>
        !((layerTables[position]!)[a.val]!)[b.val]!))]
    spectrum := Json.mkObj [("structural", plan), ("layers", toJson layers),
      ("unresolved", Json.mkObj [("count", toJson final.card), ("pairs", pairsJson final),
        ("rate", (pairRate (some n) final.card).getD Json.null)]),
      ("first_capture", toJson addresses), ("partition_count", toJson allPairs.card),
      ("ordered_pair_denominator", toJson (n * (n - 1)))]
    kernel := Json.mkObj [("structural", plan), ("readout_order", toJson roles),
      ("finite_tables", toJson tables), ("outputs", toJson outputs),
      ("full_relation", toJson ((List.finRange n).map fun a => (List.finRange n).map fun b =>
        (catalog.generatedKernel catalog.fullIndexSet).relationB a b)),
      ("complete_lattice_materialized", toJson false),
      ("scope",
        toJson "certified readout kernels and supplied layers; no exponential lattice claimed")]
    continuation := Json.mkObj [("task", toJson task), ("outputs", toJson taskOutputs),
      ("scope",
        toJson "same actual source realization; complete finite total task"), ("plan", plan)]
    arena := Json.mkObj [("kind", toJson "certified-finite-presentation"),
      ("cardinality", toJson n), ("ordered_pair_denominator", toJson (n * (n - 1))),
      ("presentation", finite),
      ("scope_boundary",
        toJson "counts refer only to the certified whole fiber, restriction or quotient; original theorem remains universal")]
  return Json.mkObj [
    ("arena", arena), ("source_contract", source), ("atom_readout", Json.null),
    ("seam_readout", Json.null), ("pyramid_coordinates", Json.null),
    ("association_coordinate", Json.null), ("continuation_target", continuation),
    ("kernel", kernel), ("escape_pairs", pairs), ("escape_rate", rate),
    ("unique_capture", unique), ("layered_spectrum", spectrum), ("residuals", Json.null),
    ("disposition", dispositions kind reason cardinality)]

end LeanInformationAudit.AuricFib.Generic
