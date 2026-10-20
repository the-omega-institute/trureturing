import Lean
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
  deriving DecidableEq, Repr

inductive Run where
  | found | exhausted | incomplete (reason : Failure)
  deriving DecidableEq, Repr

inductive Verdict where
  | bindOnly | nonBindOnly | insufficient
  deriving DecidableEq, Repr

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
  deriving DecidableEq, Repr

inductive EdgeCost where
  | zero | one | unknown
  deriving DecidableEq, Repr

inductive Bound where
  | finite (value : Nat)
  | top
  deriving DecidableEq, Repr

structure Interval where
  lower : Bound
  upper : Bound
  deriving DecidableEq, Repr

structure GraphVertex where
  id : Nat
  type : Expr := .sort .zero
  seed : Bool := false
  structureSeed : Bool := false
  structureProof? : Option Expr := none
  origin : Expr := .sort .zero
  scope : Array Expr := #[]
  lctx : LocalContext := {}
  instances : LocalInstances := #[]
  position : List Nat := []
  deriving Inhabited

inductive SpinePlan where
  | app (head : Expr) (data : Array (Option Expr)) (children : List (Option SpinePlan))

structure GraphEdge where
  conclusion : Nat
  premises : List Nat := []
  cost : EdgeCost := .unknown
  source : Option Name := none
  head : Option Expr := none
  plan? : Option SpinePlan := none
  authorData : Array (Option Expr) := #[]
  pairedCost : EdgeCost := .unknown
  visibleCost : EdgeCost := .unknown
  pairedVisibleCost : EdgeCost := .unknown
  zeroProof : Option Expr := none
  pairedZeroProof : Option Expr := none
  detail : String := ""
  window : Nat := 1
  deriving Inhabited

structure ProofGraph where
  vertices : List GraphVertex := []
  edges : List GraphEdge := []
  root : Nat := 0
  complete : Bool := true
  issues : List String := []
  deriving Inhabited

structure ProbeResult where
  outcome : Run := .incomplete .undecided
  checked : Bool := false
  proof? : Option Expr := none
  detail : String := ""
  deriving Inhabited

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
  priorReferenceSuccess : Bool := false
  isolated : Bool := false
  structureChecked : Bool := false
  structureClean : Bool := false
  deriving Inhabited

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
  deriving Inhabited

private def better (a b : Bound) : Bool :=
  match a, b with
  | .finite a, .finite b => a < b
  | .finite _, .top => true
  | _, _ => false

/-- Synchronous Bellman rounds retain one value and one backpointer per node.
No proof tree is materialized or recursively recomputed by the DP. -/
def dpTable (graph : ProofGraph) (weight : EdgeCost → Nat)
    (seeds : List Nat) : Array DPCell := Id.run do
  let initial := graph.vertices.toArray.map fun v =>
    if seeds.contains v.id then {distance := .finite 0 : DPCell} else {}
  let mut table := initial
  for _ in [:graph.vertices.length] do
    let previous := table
    table := initial
    for (edge, index) in graph.edges.zipIdx do
      let candidate := edgeBound weight edge (fun v => (previous[v]?.getD {}).distance)
      let current := table[edge.conclusion]?.getD {}
      if better candidate current.distance then
        table := table.set! edge.conclusion {distance := candidate, edge? := some index}
  return table

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
  for _ in [:graph.vertices.length + graph.edges.length + 1] do
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
    let mut children := []
    let proofs := edge.authorData.toList.countP Option.isNone
    let headLeaves := edge.premises.take (edge.premises.length - proofs)
    frontier := headLeaves
    for p in edge.premises.drop headLeaves.length do
      match (incoming graph p).head? with
      | some parent =>
        if let some head := parent.head then
          frontier := frontier ++ parent.premises
          children := children ++ [some (.app head parent.authorData [])]
        else
          frontier := frontier ++ [p]
          children := children ++ [none]
      | none =>
        frontier := frontier ++ [p]
        children := children ++ [none]
    if frontier == edge.premises then return none
    let plan? := edge.head.map (fun head => SpinePlan.app head edge.authorData children)
    return some {
      conclusion := edge.conclusion, premises := frontier, plan?, window := 2,
      detail := "two-layer-frontier"}

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

def classifyGraph (reading : GraphReading) : Verdict :=
  if reading.presentationCertified || reading.priorReferenceSuccess ||
      upperIsZero reading.baseline then .bindOnly
  else if reading.graph.complete &&
      reading.graph.edges.all (fun e => e.cost != .unknown && e.pairedCost != .unknown) && reading.isolated && reading.structureChecked &&
      reading.structureClean && finite reading.baseline.lower &&
      finite reading.baseline.upper && finite reading.paired.lower &&
      finite reading.paired.upper && strictDrop reading.baseline reading.paired &&
      reading.pairedUsesSeed then .nonBindOnly
  else .insufficient

def classifyClosure (reading : GraphReading) : Option Closure :=
  if classifyGraph reading == .nonBindOnly then some (closureOf reading.paired) else none

end LeanInformationAudit.SearchReduction
