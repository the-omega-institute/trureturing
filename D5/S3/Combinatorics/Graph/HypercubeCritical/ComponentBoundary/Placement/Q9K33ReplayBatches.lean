/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9K33ReplayBatches
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   utility: none
   digest: Named intermediate consequences reduce the memory needed to replay a resolution proof. -/

import Mathlib.Tactic.Sat.FromLRAT

/-! Name intermediate consequences of a large RUP trace in bounded batches. -/

set_option autoImplicit false
set_option maxRecDepth 50000

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33ReplayBatches

open Lean Meta
open Mathlib.Tactic.Sat

private instance : Inhabited Clause := ⟨⟨#[], default, default⟩⟩

private def Derives (f g : Sat.Fmla) : Prop :=
  ∀ v : Sat.Valuation, v.satisfies_fmla f → v.satisfies_fmla g

private theorem derive_one {f : Sat.Fmla} {c : Sat.Clause} (h : f.proof c) :
    Derives f (Sat.Fmla.one c) := by
  intro v hv
  constructor
  intro x hx
  have he : x = c := List.mem_singleton.mp hx
  exact he.symm ▸ h v hv

private theorem derive_and {f a b : Sat.Fmla} (ha : Derives f a) (hb : Derives f b) :
    Derives f (Sat.Fmla.and a b) := by
  intro v hv
  exact ⟨fun x hx => (List.mem_append.mp hx).elim ((ha v hv).prop x) ((hb v hv).prop x)⟩

private theorem derive_clause {f g : Sat.Fmla} {c : Sat.Clause}
    (h : Derives f g) (hc : g.proof c) : f.proof c :=
  fun v hv => hc v (h v hv)

private def collect (ctx : Expr) (clauses : Array (Nat × Clause)) (f : Expr)
    (start stop : Nat) : Expr :=
  if stop - start ≤ 1 then
    let clause := clauses[start]!.2
    mkApp3 (mkConst ``derive_one) ctx clause.expr clause.proof
  else
    let middle := start + (stop - start) / 2
    let a := f.appFn!.appArg!
    let b := f.appArg!
    mkApp5 (mkConst ``derive_and) ctx a b
      (collect ctx clauses a start middle) (collect ctx clauses b middle stop)
termination_by stop - start
decreasing_by all_goals omega

private def pack (name : Name) (ctx : Expr) (clauses : Array (Nat × Clause))
    (db : Std.HashMap Nat Clause) : MetaM (Std.HashMap Nat Clause) := do
  let rows := clauses.map (·.2.lits)
  let formula := buildConj rows 0 rows.size
  let saved ← mkAuxDeclName (name ++ `derived)
  addDecl <| .thmDecl {
    name := saved
    levelParams := []
    type := mkApp2 (mkConst ``Derives) ctx formula
    value := collect ctx clauses formula 0 rows.size
  }
  let support := mkApp (mkConst ``Sat.Fmla.subsumes_self) formula
  let (_, entries) := buildClauses rows formula 0 rows.size formula support default
  let mut db := db
  for i in [:rows.size] do
    let orig := clauses[i]!
    let reference := entries[i + 1]!
    let proof := mkApp5 (mkConst ``derive_clause) ctx formula orig.2.expr
      (mkConst saved) reference.proof
    db := db.insert orig.1 { orig.2 with proof }
  return db

/-- Replay the original RUP hints while naming the facts that cross each batch boundary. -/
def replay (name : Name) (ctx formula : Expr) (rows : Array (Array Int))
    (steps : Array LRATStep) : MetaM Expr := do
  let mut lastUse : Std.HashMap Nat Nat := {}
  for step in steps do
    if let .add id _ hints := step then
      for key in hints do
        lastUse := lastUse.insert key.natAbs id
  let support := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (buildClauses rows ctx 0 rows.size formula support default).2
  let mut pending := #[]
  for step in steps do
    match step with
    | .del ids =>
      db := ids.foldl (·.erase ·) db
    | .add id row hints =>
      let expr := buildClause row
      let proof ← ofExcept (buildProofStep db row hints ctx expr)
      if row.isEmpty then return proof
      for key in hints do
        if lastUse[key.natAbs]? == some id then
          db := db.erase key.natAbs
      if lastUse.contains id then
        db := db.insert id { lits := row, expr, proof }
        pending := pending.push id
      if pending.size == 2048 then
        let retained := pending.filterMap fun key => db[key]?.map (key, ·)
        if !retained.isEmpty then
          db ← pack name ctx retained db
        pending := #[]
  throwError "RUP trace has no empty clause"

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9K33ReplayBatches
