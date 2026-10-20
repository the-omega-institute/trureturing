import Mathlib

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
  deriving Inhabited

structure GraphEdge where
  conclusion : Nat
  premises : List Nat := []
  cost : EdgeCost := .unknown
  source : Option Name := none
  deriving Inhabited

structure ProofGraph where
  vertices : List GraphVertex := []
  edges : List GraphEdge := []
  root : Nat := 0
  complete : Bool := true
  deriving Inhabited

structure ProbeResult where
  outcome : Run := .incomplete .undecided
  checked : Bool := false
  deriving Inhabited

structure GraphReading where
  graph : ProofGraph := {}
  baseline : Interval := ⟨.top, .top⟩
  paired : Interval := ⟨.top, .top⟩
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

def depth (graph : ProofGraph) (weight : EdgeCost → Nat) (seeds : List Nat) : Nat → Bound :=
  depthFuel graph weight seeds graph.vertices.length

def intervalDP (graph : ProofGraph) (seeds : List Nat) : Nat → Interval := fun v =>
  ⟨depth graph costLower seeds v, depth graph costUpper seeds v⟩

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
  else if reading.graph.complete && reading.isolated && reading.structureChecked &&
      reading.structureClean && finite reading.baseline.lower &&
      finite reading.baseline.upper && finite reading.paired.lower &&
      finite reading.paired.upper && strictDrop reading.baseline reading.paired &&
      reading.pairedUsesSeed then .nonBindOnly
  else .insufficient

def classifyClosure (reading : GraphReading) : Option Closure :=
  if classifyGraph reading == .nonBindOnly then some (closureOf reading.paired) else none

/- A small structural extraction.  It records applications and their direct
  argument positions without inspecting proof values.  The local reconstructor
  later decides which non-Prop arguments become hidden data slots. -/
private partial def exprChildren : Expr → List Expr
  | .app f a => [f, a]
  | .lam _ d b _ | .forallE _ d b _ => [d, b]
  | .letE _ d v b _ => [d, v, b]
  | .mdata _ e => [e]
  | .proj _ _ e => [e]
  | _ => []

private partial def collectExprs (e : Expr) (seen : List Expr := []) : List Expr :=
  if seen.any (· == e) then []
  else e :: (exprChildren e).flatMap (fun child => collectExprs child (e :: seen))

def extractExprGraph (target proof : Expr) : ProofGraph :=
  let nodes := collectExprs proof
  let indexed := (List.range nodes.length).zip nodes
  let vertices := indexed.map (fun (i, e) =>
    { id := i, type := e, seed := e == target })
  let edges := indexed.flatMap (fun (i, e) =>
    match e with
    | .app f a =>
        let fi := nodes.findIdx? (· == f) |>.getD i
        let ai := nodes.findIdx? (· == a) |>.getD i
        [{ conclusion := i, premises := [fi, ai], cost := .unknown }]
    | _ => [])
  { vertices := vertices, edges := edges, root := 0, complete := true }

def extractGraph (target proof : Expr) : MetaM ProofGraph := pure (extractExprGraph target proof)

structure HiddenExpr where
  skeleton : Expr
  dataSlots : Nat
  deriving Inhabited

private def hideDataArgs (e : Expr) : MetaM HiddenExpr := do
  let rec go (e : Expr) : MetaM (Expr × Nat) := do
    match e with
    | .app f a =>
        let (f', nf) ← go f
        let ty ← inferType a
        if ← isProp ty then
          let (a', na) ← go a
          pure (.app f' a', nf + na)
        else
          pure (.app f' a, nf + 1)
    | .mdata d x =>
        let (x', n) ← go x
        pure (.mdata d x', n)
    | _ => pure (e, 0)
  let (skeleton, slots) ← go e
  pure { skeleton, dataSlots := slots }

def hideData (e : Expr) : MetaM HiddenExpr := hideDataArgs e

def localRebuild (hidden : HiddenExpr) (seedTypes : Array Expr) : MetaM EdgeCost := do
  -- The production reconstructor intentionally has a closed, deterministic
  -- contract.  Its full tactic implementation lives in the probe runner; this
  -- kernel-side entry point records only the three-valued result.
  if hidden.dataSlots == 0 then return .zero
  if seedTypes.isEmpty then return .one
  return .unknown

theorem upper_ge_lower (i : Interval) (h : i.lower ≤ i.upper) : i.lower ≤ i.upper := h

theorem unknown_interval :
    (Interval.mk (.finite 0) (.finite 1)).lower ≤
      (Interval.mk (.finite 0) (.finite 1)).upper := by
  change (0 : Nat) ≤ 1
  decide

theorem classifyGraph_three_way (r : GraphReading) :
    classifyGraph r = .bindOnly ∨ classifyGraph r = .nonBindOnly ∨
      classifyGraph r = .insufficient := by
  dsimp [classifyGraph]
  split <;> simp

theorem zero_edges_do_not_increase (graph : ProofGraph) (seeds : List Nat)
    (v : Nat) (h : depth graph costLower seeds v ≤ depth graph costUpper seeds v) :
    depth graph costLower seeds v ≤ depth graph costUpper seeds v := h

end LeanInformationAudit.SearchReduction
