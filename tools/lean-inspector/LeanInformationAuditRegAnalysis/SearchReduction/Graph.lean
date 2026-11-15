import Lean
import Mathlib.Tactic.ToExpr
import LeanInformationAuditRegAnalysis.SearchReduction.CertificateSyntax
import Lean.Elab.Tactic.Omega
import Lean.Elab.Tactic.Simp

/-!
  Proof-graph reduction model.

  This module is deliberately part of the production analysis package.  The
  test models import it, while the runner imports it directly; this keeps the
  graph semantics independent of test fixtures and makes the Lean values (and
  not their JSON projections) the source of the verdict.
-/

namespace LeanInformationAudit.SearchReduction

open Lean Meta

inductive Failure where
  | missing | isolation | execution | heartbeat | timeout | cancelled | undecided
  deriving DecidableEq, Repr, ToExpr

inductive Run where
  | found | exhausted | incomplete (reason : Failure)
  deriving DecidableEq, Repr, ToExpr

inductive Verdict where
  | bindOnly | nonBindOnly | insufficient
  deriving DecidableEq, Repr, ToExpr

def unionRun : Run → Run → Run
  | .found, _ | _, .found => .found
  | .incomplete reason, _ => .incomplete reason
  | _, .incomplete reason => .incomplete reason
  | .exhausted, .exhausted => .exhausted

def classify (targetChecked presentation : Bool) (base : Run)
    (structureChecked structureClean : Bool) (paired : Run) : Verdict :=
  match targetChecked, presentation, base, structureChecked, structureClean, paired with
  | false, _, _, _, _, _ => .insufficient
  | true, true, _, _, _, _ => .bindOnly
  | true, false, .found, _, _, _ => .bindOnly
  | true, false, .exhausted, true, true, .found => .nonBindOnly
  | _, _, _, _, _, _ => .insufficient

def classifyCertified (targetChecked : Bool) (presentation base : Run)
    (structureChecked structureClean : Bool) (paired : Run) : Verdict :=
  match presentation with
  | .found => classify targetChecked true base structureChecked structureClean paired
  | .exhausted => classify targetChecked false base structureChecked structureClean paired
  | .incomplete _ => classify targetChecked false
      (if base == .found then .found else .incomplete .undecided)
      structureChecked structureClean paired

inductive Closure where
  | zero | partial_
  deriving DecidableEq, Repr, ToExpr

inductive EdgeCost where
  | zero | one | unknown
  deriving DecidableEq, Repr, ToExpr

/-- A guard requires exhaustive negative completion; budget misses never
discharge it, even though the same recorded query has numerical price one. -/
def RQuery.guardRun : RQuery → Run
  | .hit _ => .found
  | .miss .exhaustive => .exhausted
  | _ => .incomplete .undecided

def RQuery.cost (q : RQuery) : EdgeCost :=
  match q.price with
  | some 0 => .zero
  | some _ => .one
  | none => .unknown

theorem fault_not_priced (reason : String) : (RQuery.fault reason).price = none := rfl
theorem notRun_not_priced : RQuery.notRun.price = none := rfl
theorem zero_price_iff_hit (q : RQuery) :
    q.price = some 0 ↔ ∃ certificate, q = .hit certificate := by
  cases q <;> simp [RQuery.price]
theorem one_price_iff_miss (q : RQuery) :
    q.price = some 1 ↔ ∃ stop, q = .miss stop := by
  cases q <;> simp [RQuery.price]
theorem hit_miss_exclusive (certificate : ObviousCertificate) (stop : RStop) :
    RQuery.hit certificate ≠ .miss stop := by simp
theorem miss_fault_exclusive (stop : RStop) (reason : String) :
    RQuery.miss stop ≠ .fault reason := by simp
theorem budget_miss_does_not_complete_guard (stop : RStop)
    (budget : (RQuery.miss stop).budget = true) :
    (RQuery.miss stop).guardRun = .incomplete .undecided := by
  cases stop <;> simp_all [RQuery.budget, RQuery.guardRun]

structure QueryRecord where
  role : String
  target : UInt64
  premises : List UInt64
  terminal : RQuery
  encounteredSearchKappa : Bool := false
  encounteredCoveragePrefixG : Bool := false
  encounteredFaults : Array String := #[]
  deriving Inhabited, ToExpr

inductive Bound where
  | finite (value : Nat)
  | top
  deriving DecidableEq, Repr, ToExpr

structure Interval where
  lower : Bound
  upper : Bound
  deriving DecidableEq, Repr, ToExpr

structure GraphVertex where
  id : Nat
  type : Expr := .sort .zero
  seed : Bool := false
  structureSeed : Bool := false
  structureProof? : Option Expr := none
  origin : Expr := .sort .zero
  opaqueDecl : Bool := false
  targetPart : Bool := false
  independentLookup : Run := .incomplete .undecided
  independentLookupDetail : String := "not-queried"
  reverseLookup : Run := .incomplete .undecided
  reverseLookupDetail : String := "not-queried"
  deriving Inhabited, ToExpr

structure GraphEdge where
  conclusion : Nat
  premises : List Nat := []
  cost : EdgeCost := .unknown
  source : Option Name := none
  analytic : List Nat := []
  usedPremises : List Nat := []
  pairedUsedPremises : List Nat := []
  givenUsedPremises : List Nat := []
  pairedGivenUsedPremises : List Nat := []
  pairedCost : EdgeCost := .unknown
  visibleCost : EdgeCost := .unknown
  pairedVisibleCost : EdgeCost := .unknown
  zeroProof : Option Expr := none
  pairedZeroProof : Option Expr := none
  certificate? : Option ObviousCertificate := none
  pairedCertificate? : Option ObviousCertificate := none
  detail : String := ""
  window : Nat := 1
  sharedData? : Option Bool := none
  query : RQuery := .notRun
  pairedQuery : RQuery := .notRun
  deriving Inhabited, ToExpr

/-- Statement visibility depends only on seed membership and the analytic
relation, preserving the author's premise order. -/
def statementPremises (edge : GraphEdge) (seeds : List Nat) : List Nat :=
  edge.premises.filter fun p => seeds.contains p || edge.analytic.contains p

structure ProofGraph where
  vertices : List GraphVertex := []
  edges : List GraphEdge := []
  root : Nat := 0
  complete : Bool := true
  issues : List String := []
  deriving Inhabited, ToExpr

structure ProbeResult where
  outcome : Run := .incomplete .undecided
  checked : Bool := false
  premises : List Nat := []
  proof? : Option Expr := none
  certificate? : Option ObviousCertificate := none
  detail : String := ""
  query : RQuery := .notRun
  deriving Inhabited, ToExpr

/-- The production attachment preserves the actual support and checked term;
the opposing arm receives no negative information from this operation. -/
def attachCertificate (edge : GraphEdge) (paired : Bool)
    (certificate : ObviousCertificate) (proof : Expr) (used : List Nat) : GraphEdge :=
  if paired then {edge with
    pairedCost := .zero, pairedZeroProof := some proof,
    pairedCertificate? := some certificate, pairedUsedPremises := used,
    pairedQuery := .hit certificate}
  else {edge with
    cost := .zero, zeroProof := some proof,
    certificate? := some certificate, usedPremises := used, query := .hit certificate}

structure GraphReading where
  graph : ProofGraph := {}
  baseline : Interval := ⟨.top, .top⟩
  paired : Interval := ⟨.top, .top⟩
  baselineK1 : Interval := ⟨.top, .top⟩
  pairedK1 : Interval := ⟨.top, .top⟩
  baselineVisible : Interval := ⟨.top, .top⟩
  pairedVisible : Interval := ⟨.top, .top⟩
  selectedSeeds : List Nat := []
  baselineProof? : Option Expr := none
  pairedProof? : Option Expr := none
  k : Nat := 2
  baselineProbe : ProbeResult := {}
  pairedProbe : ProbeResult := {}
  pairedUsesSeed : Bool := false
  presentationCertified : Bool := false
  presentationComplete : Bool := false
  witnessEdges : List Nat := []
  proofHardSeeds : List Nat := []
  selectedSeedDepths : List (Nat × Interval) := []
  targetPartComplete : Bool := true
  noAuxiliary : Bool := false
  priorReferenceSuccess : Bool := false
  isolated : Bool := false
  structureChecked : Bool := false
  structureClean : Bool := false
  lookupEnabled : Bool := true
  lookupBasisComplete : Bool := true
  negativeCalls : Nat := 0
  reverseNegativeCalls : Nat := 0
  certificatePool : Array CertificateNomination := #[]
  certificateBindings : Array (Name × CertificateNomination) := #[]
  queryAnswerMemoization : Bool := false
  rejection? : Option String := none
  queryRecords : List QueryRecord := []
  deriving Inhabited, ToExpr

def NoHit (run : Run) : Prop := run = .exhausted

def boundLe : Bound → Bound → Prop
  | .finite a, .finite b => a ≤ b
  | .finite _, .top => True
  | .top, .top => True
  | .top, .finite _ => False

instance : LE Bound := ⟨boundLe⟩

def boundAdd : Bound → Nat → Bound
  | .top, _ => .top
  | .finite n, k => .finite (n + k)

def boundMax (xs : List Bound) : Bound :=
  xs.foldl (fun acc x => match acc, x with
    | .top, _ | _, .top => .top
    | .finite a, .finite b => .finite (max a b)) (.finite 0)

def costLower : EdgeCost → Nat
  | .zero => 0
  | .one => 1
  | .unknown => 0

def costUpper : EdgeCost → Nat
  | .zero => 0
  | .one => 1
  | .unknown => 1

def edgeBound (weight : EdgeCost → Nat) (edge : GraphEdge)
    (distance : Nat → Bound) : Bound :=
  boundAdd (boundMax (edge.premises.map distance)) (weight edge.cost)

def minBound (xs : List Bound) : Bound :=
  xs.foldl (fun best x => match best, x with
    | .top, y => y
    | y, .top => y
    | .finite a, .finite b => .finite (min a b)) .top

def vertexIds (graph : ProofGraph) : List Nat := graph.vertices.map GraphVertex.id

def isSeed (graph : ProofGraph) (v : Nat) : Bool :=
  (graph.vertices.find? (fun x => x.id == v)).map (·.seed) |>.getD false

def incoming (graph : ProofGraph) (v : Nat) : List GraphEdge :=
  graph.edges.filter (·.conclusion == v)

/- A bounded unrolling is sufficient because extracted proof graphs are acyclic;
  the fuel is the number of vertices and therefore also gives the memory bound.
  Unknown local reconstruction is represented by the [0,1] pair. -/
def depthFuel (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : Nat → Nat → Bound
  | 0, v => if seeds.contains v then .finite 0 else .top
  | fuel + 1, v =>
      if seeds.contains v then .finite 0
      else minBound ((incoming graph v).map fun edge =>
        edgeBound weight edge (depthFuel graph weight seeds fuel))

structure DPCell where
  distance : Bound := .top
  edge? : Option Nat := none
  deriving Inhabited, DecidableEq

def better (a b : Bound) : Bool :=
  match a, b with
  | .finite a, .finite b => a < b
  | .finite _, .top => true
  | _, _ => false

def initialTable (graph : ProofGraph) (seeds : List Nat) : Array DPCell :=
  graph.vertices.toArray.map fun v =>
    if seeds.contains v.id then {distance := .finite 0} else {}

def relaxEdge (weight : EdgeCost → Nat) (previous table : Array DPCell)
    (entry : GraphEdge × Nat) : Array DPCell :=
  let (edge, index) := entry
  let candidate := edgeBound weight edge (fun v => (previous[v]?.getD {}).distance)
  let current := table[edge.conclusion]?.getD {}
  if better candidate current.distance then
    table.set! edge.conclusion {distance := candidate, edge? := some index}
  else table

/-- Synchronous Bellman rounds retain one value and one backpointer per node.
No proof tree is materialized or recursively recomputed by the DP. -/
def dpRounds (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : Nat → Array DPCell
  | 0 => initialTable graph seeds
  | fuel + 1 => graph.edges.zipIdx.foldl
      (relaxEdge weight (dpRounds graph weight seeds fuel)) (initialTable graph seeds)

private def dpStep (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) (previous : Array DPCell) : Array DPCell :=
  graph.edges.zipIdx.foldl (relaxEdge weight previous) (initialTable graph seeds)

/-- Once a complete synchronous table repeats, all remaining rounds repeat it.
The same finite-round semantics therefore needs no redundant stable rounds. -/
def dpUntilStable (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : Nat → Array DPCell → Array DPCell
  | 0, previous => previous
  | fuel + 1, previous =>
      let next := dpStep graph weight seeds previous
      if next = previous then previous else dpUntilStable graph weight seeds fuel next

private theorem dpRounds_fixed (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) (start : Nat)
    (fixed : dpRounds graph weight seeds (start + 1) = dpRounds graph weight seeds start)
    (fuel : Nat) :
    dpRounds graph weight seeds (start + fuel) = dpRounds graph weight seeds start := by
  induction fuel with
  | zero => simp
  | succ fuel ih =>
    have h : start + (fuel + 1) = (start + fuel) + 1 := by omega
    rw [h, dpRounds, ih]
    exact fixed

theorem dpUntilStable_eq_dpRounds (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) (fuel start : Nat) :
    dpUntilStable graph weight seeds fuel (dpRounds graph weight seeds start) =
      dpRounds graph weight seeds (start + fuel) := by
  induction fuel generalizing start with
  | zero => simp [dpUntilStable]
  | succ fuel ih =>
    simp only [dpUntilStable]
    change (if dpRounds graph weight seeds (start + 1) = dpRounds graph weight seeds start
      then dpRounds graph weight seeds start
      else dpUntilStable graph weight seeds fuel (dpRounds graph weight seeds (start + 1))) = _
    split
    · rename_i fixed
      exact (dpRounds_fixed graph weight seeds start fixed (fuel + 1)).symm
    · rw [ih]
      congr 1
      omega

def dpTable (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : Array DPCell :=
  dpUntilStable graph weight seeds graph.vertices.length (initialTable graph seeds)

theorem dpTable_eq_dpRounds (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) :
    dpTable graph weight seeds = dpRounds graph weight seeds graph.vertices.length := by
  simpa only [dpTable, dpRounds, Nat.zero_add] using
    (dpUntilStable_eq_dpRounds graph weight seeds graph.vertices.length 0)

def depth (graph : ProofGraph) (weight : EdgeCost → Nat) (seeds : List Nat) : Nat → Bound :=
  let table := dpTable graph weight seeds
  fun v => (table[v]?.getD {}).distance

/-- Follow the selected AND edges, retaining shared premises once. -/
def optimalSeeds (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : List Nat := Id.run do
  let table := dpTable graph weight seeds
  let mut pending := [graph.root]
  let mut seen := []
  let mut used := []
  for _ in [:graph.vertices.length + (graph.edges.map (·.premises.length)).sum + 1] do
    match pending with
    | [] => break
    | v :: rest =>
      pending := rest
      if seen.contains v then continue
      seen := v :: seen
      if seeds.contains v then used := v :: used
      else if let some index := (table[v]?.getD {}).edge? then
        if let some edge := graph.edges[index]? then
          pending := edge.premises ++ pending
  return used

def intervalDP (graph : ProofGraph) (seeds : List Nat) : Nat → Interval := fun v =>
  ⟨depth graph costLower seeds v, depth graph costUpper seeds v⟩

/-- One deterministic two-layer cut per author edge; added cuts are not expanded. -/
def k2Frontier (graph : ProofGraph) : List GraphEdge :=
  graph.edges.filterMap fun edge => Id.run do
    let mut frontier := []
    for p in edge.premises do
      match (incoming graph p).head? with
      | some parent => frontier := frontier ++ parent.premises
      | none => frontier := frontier ++ [p]
    frontier := frontier.eraseDups
    if frontier == edge.premises then return none
    return some {
      conclusion := edge.conclusion, premises := frontier, window := 2,
      source := edge.source, detail := "two-layer-declaration-frontier"}

def graphInterval (graph : ProofGraph) (seeds : List Nat) : Interval :=
  intervalDP graph seeds graph.root

def finite (b : Bound) : Bool := match b with | .finite _ => true | .top => false

def strictDrop (base paired : Interval) : Bool :=
  match base.lower, paired.upper with
  | .finite l, .finite u => l > u
  | _, _ => false

def upperIsZero (i : Interval) : Bool :=
  match i.upper with | .finite 0 => true | _ => false

def closureOf (i : Interval) : Closure :=
  if upperIsZero i then .zero else .partial_

/-- A shortcut exists in an arm only with a checked zero certificate. Author
edges retain their exhausted or unknown price. -/
def edgeActive (edge : GraphEdge) (paired := false) (allGiven := false) : Bool :=
  edge.window == 1 || (if allGiven then
    (if paired then edge.pairedVisibleCost else edge.visibleCost)
    else if paired then edge.pairedCost else edge.cost) == .zero

/-- Eligible auxiliary seeds actually reached by the paired backpointers. -/
def selectedStructureSeed (graph : ProofGraph) (selected : List Nat) (id : Nat) : Bool :=
  selected.contains id && (graph.vertices.find? (·.id == id)).any (fun v =>
    v.structureSeed && !v.seed && !v.targetPart)

/-- A hard-proof witness needs both positive graph depth and a completed
independent lookup. A zero-depth or lookup-provable helper is not such a witness. -/
def proofHardEligible (graph : ProofGraph) (selected : List Nat) (id : Nat)
    (baselineDepth : Bound) : Bool :=
  selectedStructureSeed graph selected id &&
    (graph.vertices.find? (·.id == id)).any (fun v => v.independentLookup == .exhausted) &&
    match baselineDepth with
    | .finite n => n ≥ 1
    | .top => false

def usesStructureSeed (reading : GraphReading) : Bool :=
  reading.selectedSeeds.any (selectedStructureSeed reading.graph reading.selectedSeeds)

structure DecisionState where
  graphComplete : Bool
  targetPartComplete : Bool
  noAuxiliary : Bool
  presentationCertified : Bool
  priorReferenceSuccess : Bool
  baseline : Interval
  presentationComplete : Bool
  isolated : Bool
  structureChecked : Bool
  structureClean : Bool
  baselineProbe : Run
  paired : Interval
  usesSeed : Bool

def decisionState (reading : GraphReading) : DecisionState := {
  graphComplete := reading.graph.complete
  targetPartComplete := reading.targetPartComplete
  noAuxiliary := reading.noAuxiliary
  presentationCertified := reading.presentationCertified
  priorReferenceSuccess := reading.priorReferenceSuccess
  baseline := reading.baseline
  presentationComplete := reading.presentationComplete
  isolated := reading.isolated
  structureChecked := reading.structureChecked
  structureClean := reading.structureClean
  baselineProbe := reading.baselineProbe.outcome
  paired := reading.paired
  usesSeed := usesStructureSeed reading }

def classifyState (state : DecisionState) : Verdict :=
  if state.presentationCertified || state.priorReferenceSuccess ||
      upperIsZero state.baseline then .bindOnly
  else if state.graphComplete && state.targetPartComplete &&
      !state.noAuxiliary && state.presentationComplete && state.isolated &&
      state.structureChecked && state.structureClean &&
      finite state.baseline.lower && state.baselineProbe == .exhausted &&
      finite state.baseline.upper && finite state.paired.upper &&
      strictDrop state.baseline state.paired && state.usesSeed then
    .nonBindOnly
  else .insufficient

/-- An actual price change consumes a selected synthetic structure seed. -/
def isWitnessEdge (graph : ProofGraph) (selected : List Nat) (edge : GraphEdge) : Bool :=
  edge.cost == .one && edge.pairedCost == .zero &&
    edge.pairedUsedPremises.any (fun p =>
      (graph.vertices.find? (·.id == p)).any fun v =>
        v.structureSeed && !v.seed && !v.targetPart &&
          !edge.analytic.contains p && selected.contains p)

/-- A reverse NoHit discharges only the target-part exclusion. It is never
an edge price. Independent success already prevents this exclusion. -/
def targetPartDecision (independent reverse : Run) : Run :=
  match independent, reverse with
  | .found, _ => .exhausted
  | .exhausted, .found => .found
  | _, .exhausted => .exhausted
  | _, _ => .incomplete .undecided

/-- Reverse negatives belong to the lazy decision set after the numeric and
root guards can grant a positive. They can also settle an unknown independent run. -/
def needsReverseNegative (decisive : Bool) (independent reverse : Run) : Bool :=
  decisive && independent != .found &&
    match reverse with | .incomplete _ => true | _ => false

/-- Exclusion evidence follows the final selected route, including any route
chosen after an earlier seed was excluded. Unqueried selected seeds block. -/
def targetPartReady (graph : ProofGraph) (selected : List Nat) : Bool :=
  selected.all fun id =>
    if selectedStructureSeed graph selected id then
      (graph.vertices.find? (·.id == id)).any fun v =>
        match targetPartDecision v.independentLookup v.reverseLookup with
        | .incomplete _ => false
        | _ => true
    else true

def classifyGraph (reading : GraphReading) : Verdict :=
  if reading.presentationCertified || reading.priorReferenceSuccess ||
      upperIsZero reading.baseline then .bindOnly
  else if reading.graph.complete && reading.targetPartComplete &&
      !reading.noAuxiliary &&
      reading.presentationComplete && reading.isolated && reading.structureChecked &&
      reading.structureClean && finite reading.baseline.lower &&
      reading.baselineProbe.outcome == .exhausted &&
      finite reading.baseline.upper &&
      finite reading.paired.upper && strictDrop reading.baseline reading.paired &&
      usesStructureSeed reading then .nonBindOnly
  else .insufficient

theorem classifyGraph_eq_classifyState (reading : GraphReading) :
    classifyGraph reading = classifyState (decisionState reading) := by
  simp [classifyGraph, classifyState, decisionState]

theorem early_stop_verdict_eq (early full : GraphReading)
    (same : decisionState early = decisionState full) :
    classifyGraph early = classifyGraph full := by
  rw [classifyGraph_eq_classifyState, classifyGraph_eq_classifyState, same]

def classifyClosure (reading : GraphReading) : Option Closure :=
  if classifyGraph reading == .nonBindOnly then some (closureOf reading.paired) else none

inductive Disposition where
  | bindOnly | reductionR | noGainR | reject | incomplete
  deriving DecidableEq, Repr, ToExpr

def guardsComplete (r : GraphReading) : Bool :=
  r.graph.complete && r.targetPartComplete && r.presentationComplete &&
    r.isolated && r.structureChecked && r.structureClean

def classifyDisposition (r : GraphReading) : Disposition :=
  if classifyGraph r == .bindOnly then .bindOnly
  else if r.rejection?.isSome then .reject
  else if !guardsComplete r then .incomplete
  else if classifyGraph r == .nonBindOnly then .reductionR
  else if finite r.baseline.upper && finite r.paired.lower &&
      !better r.paired.lower r.baseline.upper then .noGainR
  else .incomplete

/-- Conservatively include every consumed one-price graph record and the
baseline root miss; no minimal-dependency analysis is assumed. -/
def budgetBasis (r : GraphReading) : Bool :=
  (r.baselineProbe.outcome == .exhausted && r.baselineProbe.query.budget) || r.graph.edges.any (fun e =>
    (e.cost == .one && e.query.budget) ||
    (e.pairedCost == .one && e.pairedQuery.budget))

theorem unfinished_guards_not_reduction (r : GraphReading)
    (unfinished : guardsComplete r = false) :
    classifyDisposition r ≠ .reductionR := by
  unfold classifyDisposition
  split
  · simp
  · split
    · simp
    · simp [unfinished]

theorem miss_does_not_supply_zero (stop : RStop) :
    (RQuery.miss stop).cost ≠ .zero := by simp [RQuery.cost, RQuery.price]

end LeanInformationAudit.SearchReduction
