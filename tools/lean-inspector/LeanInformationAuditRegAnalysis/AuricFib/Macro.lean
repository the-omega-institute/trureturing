import LeanInformationAuditRegAnalysis.AuricFib.Source

namespace LeanInformationAudit.AuricFib
open Lean

structure MacroResult where
  coordinates : Json
  association : Json
  residuals : Json
  response : Json

private def quantity (status : String) (value : Option Rat) : Json :=
  Json.mkObj [("status", toJson status), ("value", value.map rationalJson |>.getD Json.null)]

/-- Push a finite source law through the actual total Option reply map. -/
def replyLaw (law : Array Rat) (condition : Bool) : Option Json := Id.run do
  let eventMass := modes.foldl (fun total a =>
    if !condition || parityEvent a then total + law[modeIndex a]! else total) 0
  if eventMass = 0 then return none
  let values := ((modes.filter fun a => !condition || parityEvent a).map suffixReply).eraseDups
  return some <| Json.arr <| values.toArray.map fun reply =>
    let mass := modes.foldl (fun total a =>
      if suffixReply a = reply && (!condition || parityEvent a)
      then total + law[modeIndex a]! else total) 0
    Json.mkObj [("reply", toJson (reply.map toString)),
      ("mass", rationalJson (mass / eventMass))]

/-- Formula evaluation consumes an already validated exact source law. -/
def macroAnalysis (input : SourceInput) (law : Array Rat) : Except String MacroResult := do
  let p0 := law[0]!
  let p2 := law[1]!
  let p5 := law[2]!
  let k := law[3]!
  let z := law[4]!
  let x := p2 + k
  let y := p5 + k
  let r := 1 - z
  let m := y + z
  let low := max 0 (x + y - r)
  let high := min x y
  let width := min (min x y) (min (r - x) (r - y))
  let delta := r * k - x * y
  let cellsDet := p0 * k - p2 * p5
  unless 0 ≤ x && 0 ≤ y && 0 ≤ z && x + z ≤ 1 && y + z ≤ 1 do
    throw "internal pyramid-domain inconsistency"
  unless low ≤ k && k ≤ high && width = high - low && delta = cellsDet do
    throw "internal association identity inconsistency"
  let apex := r = 0
  let kstar := if apex then 0 else x * y / r
  let completion := if apex then law else #[r-x-y+kstar, x-kstar, y-kstar, kstar, z]
  discard <| validateLaw completion
  let recoveredK := if apex then 0 else (delta + x*y) / r
  let recovered := #[r-x-y+recoveredK, x-recoveredK, y-recoveredK, recoveredK, z]
  unless recovered = law do throw "internal law reconstruction inconsistency"
  let f := modes.toArray.map targetIndicator
  let jf := f[3]! - f[1]! - f[2]! + f[0]!
  let expectation (p : Array Rat) := modes.foldl
    (fun total a => total + p[modeIndex a]! * targetIndicator a) 0
  let target := expectation law
  let targetStar := expectation completion
  let endpointLow := expectation #[r-x-y+low, x-low, y-low, low, z]
  let endpointHigh := expectation #[r-x-y+high, x-high, y-high, high, z]
  let rf := if apex then 0 else jf * delta / r
  unless rf = target - targetStar do throw "internal target residual inconsistency"
  let guardResidual := if m = 0 then none else
    some (if apex then 0 else delta / (r * m))
  let rejectedJoint (p : Array Rat) := modes.foldl (fun total a =>
    if parityEvent a && !guardAccepts a then total + p[modeIndex a]! else total) 0
  if let some residual := guardResidual then
    unless residual = (rejectedJoint law - rejectedJoint completion) / m do
      throw "internal guard-response inconsistency"
  let response := Json.mkObj [
    ("conditioning_event_mass", rationalJson m),
    ("conditional_reply_law", (replyLaw law true).getD Json.null),
    ("product_completion_conditional_reply_law", (replyLaw completion true).getD Json.null),
    ("unconditional_reply_law", (replyLaw law false).getD Json.null),
    ("unconditional_rejection_mass", rationalJson x),
    ("conditional_rejection_mass", if m = 0 then Json.null else rationalJson (k / m))]
  return {
    coordinates := Json.mkObj [("X", rationalJson x), ("Y", rationalJson y),
      ("Z", rationalJson z), ("r", rationalJson r),
      ("domain", toJson "X,Y,Z>=0; X+Z<=1; Y+Z<=1")]
    association := Json.mkObj [
      ("kappa", rationalJson k), ("delta", rationalJson delta),
      ("determinant_from_cells", rationalJson cellsDet),
      ("kappa_min", rationalJson low), ("kappa_max", rationalJson high),
      ("delta_min", rationalJson (r*low-x*y)), ("delta_max", rationalJson (r*high-x*y)),
      ("joint_table", Json.arr ((#[#[p0, p5], #[p2, k]]).map fun row =>
        Json.arr (row.map rationalJson))),
      ("product_completion", Json.arr (completion.map rationalJson)),
      ("reconstructed_law", Json.arr (recovered.map rationalJson)),
      ("conditional_endpoint_independent", if apex then Json.null else toJson (delta == 0)),
      ("acquisition", toJson (if input.kind = "empirical-archive" then
        "empirical-archive-pushforward" else "declared-source-pushforward")),
      ("interpretation", toJson "law statistic; conditional on positive bottom mass only")]
    residuals := Json.mkObj [
      ("fiber_width", rationalJson width), ("J_f", rationalJson jf),
      ("target_values", Json.arr (f.map rationalJson)),
      ("target_expectation", rationalJson target),
      ("product_completion_target_expectation", rationalJson targetStar),
      ("target_min", rationalJson (min endpointLow endpointHigh)),
      ("target_max", rationalJson (max endpointLow endpointHigh)),
      ("target_range_width", rationalJson (abs jf * width)),
      ("R_f", quantity (if apex then "apex" else "positive-bottom-mass") (some rf)),
      ("R_guard", quantity (if m = 0 then "zero-conditioning-mass" else if apex then
        "apex" else "positive-bottom-and-conditioning-mass") guardResidual),
      ("global_fiber_width_upper", rationalJson (1/2)),
      ("fixed_Z_fiber_width_upper", rationalJson (r/2)),
      ("global_delta_bounds", Json.arr (#[(-1/4 : Rat), 1/4].map rationalJson)),
      ("fixed_Z_delta_bounds", Json.arr (#[-r*r/4, r*r/4].map rationalJson))]
    response := response }

end LeanInformationAudit.AuricFib
