/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitCover
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Tactic.Sat.FromLRAT]
   utility: none
   digest: The rooted even contact layer has eighteen patterns. A coordinate swap and the exchange of the two roots partition them into six orbits. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Sat.FromLRAT

/-! Finite coverage of the rooted even layer of the five-axis nine-mask case. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitCover

abbrev Word := BitVec 9
abbrev Axis := Fin 5
abbrev Pattern := Finset Word × Finset Word

def evenWords : List Word := [0, 3, 5, 6, 9, 10, 12, 15, 17, 18, 20, 23, 24, 27, 29, 30]
def oddWords : List Word := [1, 2, 4, 7, 8, 11, 13, 14, 16, 19, 21, 22, 25, 26, 28, 31]

/-- SAT indices are zero-based. The DIMACS variables are 1–16 on the left
and 17–32 on the right, in increasing word order on each side. -/
def atom (s : Bool) (x : Word) : Nat := evenWords.idxOf x + (if s then 16 else 0)

def step (x : Word) (i : Axis) : Word := x ^^^ BitVec.ofNat 9 (2 ^ i.val)

def otherAxes (i : Axis) : List Axis := ([0, 1, 2, 3, 4] : List Axis).filter (· != i)

abbrev pos (s : Bool) (x : Word) : Sat.Literal := .pos (atom s x)
abbrev neg (s : Bool) (x : Word) : Sat.Literal := .neg (atom s x)

inductive Row where
  | root (side : Bool)
  | separation (x mask : Word)
  | translate (x : Word) (i j p q : Axis) (side : Bool)
  | upper (z : Word) (side : Bool) (j a b c : Axis)
  | lower (z : Word) (side : Bool) (j i : Axis)

def Row.clause : Row → Sat.Clause
  | .root s => [pos s (if s then 3 else 0)]
  | .separation x m => [neg false x, neg true (x ^^^ m)]
  | .translate x i j p q s =>
      let y := step (step x i) j
      [neg false x, neg true y, pos s (step (step (if s then y else x) p) q)]
  | .upper z s j a b c =>
      [neg (!s) (step z j), neg s (step z a), neg s (step z b), neg s (step z c)]
  | .lower z s j i => [neg (!s) (step z j), neg s (step z i)] ++
      (otherAxes i).map (fun k => pos s (step z k))

def Row.Valid : Row → Prop
  | .root _ => True
  | .separation x m => x ∈ evenWords ∧ (m = 0 ∨ m = 6)
  | .translate x i j p q _ => x ∈ evenWords ∧ (i = 1 ∨ i = 2) ∧
      ({j, p, q} : Finset Axis) = {0, 3, 4}
  | .upper z _ _ a b c => z ∈ oddWords ∧ a < b ∧ b < c
  | .lower z _ _ _ => z ∈ oddWords

instance (r : Row) : Decidable r.Valid := by
  cases r <;> unfold Row.Valid <;> infer_instance

/-- The geometry supplies these clauses on the two occupancy subsets. -/
def Tableau (v : Sat.Valuation) : Prop := ∀ r : Row, r.Valid → v.satisfies r.clause

def Pattern.on (p : Pattern) (s : Bool) : Finset Word := if s then p.2 else p.1

open Row in
private def inputRows : List Row := [
  root false, root true, separation 0 0, separation 0 6,
  separation 3 0, separation 5 6, separation 9 0, separation 9 6,
  separation 12 6, separation 17 6, separation 18 0, separation 18 6,
  separation 20 0, separation 20 6, separation 23 0, separation 24 0,
  separation 24 6, separation 27 0, separation 29 6, translate 0 1 0 3 4 false,
  translate 0 1 0 3 4 true, translate 30 1 0 3 4 false, translate 0 2 0 3 4 true, translate 6 2 0 3 4 false,
  translate 24 2 0 3 4 true, translate 30 2 0 3 4 false, translate 0 1 3 0 4 false, translate 9 1 3 0 4 true,
  translate 15 1 3 0 4 true, translate 24 1 3 0 4 false, translate 0 2 3 0 4 false, translate 0 2 3 0 4 true,
  translate 9 2 3 0 4 true, translate 15 2 3 0 4 false, translate 15 2 3 0 4 true, translate 24 2 3 0 4 false,
  translate 0 2 4 0 3 true, translate 23 2 4 0 3 false, lower 1 false 1 0, lower 2 false 0 1,
  upper 2 true 1 0 3 4, lower 2 true 1 0, lower 4 false 0 2, upper 7 true 0 1 2 4,
  upper 7 true 3 1 2 4, lower 7 true 4 2, upper 8 false 1 0 3 4, lower 8 true 3 0,
  lower 8 true 3 1, lower 11 false 3 0, lower 13 false 4 0, upper 14 true 3 0 1 2,
  lower 14 true 3 2, upper 14 true 4 0 1 2, lower 14 true 4 2, upper 16 false 1 0 3 4,
  upper 16 false 2 0 3 4, lower 16 true 3 0, lower 16 true 3 1, lower 16 true 3 2,
  lower 19 false 0 2, lower 19 false 2 0, lower 21 false 0 1, lower 21 false 1 0,
  lower 22 true 3 2, lower 22 true 4 2, upper 25 true 0 1 2 3, upper 25 true 0 1 2 4,
  lower 25 true 4 1, upper 26 false 0 1 2 3, upper 26 false 0 1 2 4, lower 26 false 0 1,
  lower 26 false 4 1, upper 28 false 0 1 2 3, upper 28 false 0 1 2 4, lower 28 false 0 2,
  upper 28 true 2 0 3 4, lower 28 true 2 0, lower 31 false 2 0, lower 31 false 4 3,
  upper 31 true 0 1 2 3]

private def patterns : List Pattern := [
  ({0, 6, 9, 12, 15, 24, 30}, {3, 17, 18, 23, 27}),
  ({0, 6, 9, 15, 24, 30}, {3, 5, 18, 20, 27, 29}),
  ({0, 6, 9, 15, 24, 30}, {3, 17, 18, 23, 27}),
  ({0, 6, 17, 20, 23, 24, 30}, {3, 9, 10, 15, 27}),
  ({0, 6, 17, 23, 24, 30}, {3, 5, 10, 12, 27, 29}),
  ({0, 6, 17, 23, 24, 30}, {3, 9, 10, 15, 27}),
  ({0, 9, 10, 12, 24}, {3, 5, 18, 20, 23, 27, 29}),
  ({0, 9, 10, 12, 24}, {3, 5, 18, 20, 27, 29}),
  ({0, 9, 10, 12, 24}, {3, 17, 18, 23, 27}),
  ({0, 9, 10, 12, 24}, {3, 17, 18, 27}),
  ({0, 9, 10, 24}, {3, 17, 18, 23, 27}),
  ({0, 9, 10, 24}, {3, 17, 18, 27}),
  ({0, 17, 18, 20, 24}, {3, 5, 10, 12, 15, 27, 29}),
  ({0, 17, 18, 20, 24}, {3, 5, 10, 12, 27, 29}),
  ({0, 17, 18, 20, 24}, {3, 9, 10, 15, 27}),
  ({0, 17, 18, 20, 24}, {3, 9, 10, 27}),
  ({0, 17, 18, 24}, {3, 9, 10, 15, 27}),
  ({0, 17, 18, 24}, {3, 9, 10, 27})]

def representatives : List Pattern := [
  ({0, 6, 9, 12, 15, 24, 30}, {3, 17, 18, 23, 27}),
  ({0, 6, 9, 15, 24, 30}, {3, 5, 18, 20, 27, 29}),
  ({0, 6, 9, 15, 24, 30}, {3, 17, 18, 23, 27}),
  ({0, 9, 10, 12, 24}, {3, 17, 18, 23, 27}),
  ({0, 9, 10, 12, 24}, {3, 17, 18, 27}),
  ({0, 9, 10, 24}, {3, 17, 18, 27})]

/-- Swap the two axes outside the root and missing masks. -/
def swapAxes (p : Pattern) : Pattern :=
  let swapWord (x : Word) := if x.getLsbD 3 = x.getLsbD 4 then x else x ^^^ 24
  (p.1.image swapWord, p.2.image swapWord)

/-- Exchange the supports and translate both by the root displacement. -/
def swapRoots (p : Pattern) : Pattern := (p.2.image (· ^^^ 3), p.1.image (· ^^^ 3))

def orbit (p : Pattern) : List Pattern := [p, swapAxes p, swapRoots p, swapAxes (swapRoots p)]

set_option maxHeartbeats 0 in
private theorem pattern_orbits : patterns.toFinset = (representatives.flatMap orbit).toFinset := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem orbit_sizes :
    (representatives.map fun r => (orbit r).toFinset.card) = [4, 2, 4, 2, 4, 2] ∧
      (representatives.flatMap orbit).toFinset.card = 18 := by
  decide +kernel

def Matches (v : Sat.Valuation) (p : Pattern) : Prop :=
  ∀ (s : Bool) (w : Word), w ∈ evenWords → (v (atom s w) ↔ w ∈ p.on s)

private def blockLit (p : Pattern) (s : Bool) (w : Word) : Sat.Literal :=
  if w ∈ p.on s then neg s w else pos s w

private def block (p : Pattern) : Sat.Clause :=
  evenWords.map (blockLit p false) ++ evenWords.map (blockLit p true)

theorem satisfies_of_falsified {v : Sat.Valuation} {c : List Sat.Literal}
    (h : ¬ ∀ l ∈ c, v.neg l) : v.satisfies c := by
  induction c with
  | nil => exact h (by simp)
  | cons l ls ih =>
    intro hl
    apply ih
    intro hls
    apply h
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hl
    · exact hls a ha

private theorem satisfies_block {v : Sat.Valuation} {p : Pattern} (h : ¬ Matches v p) :
    v.satisfies (block p) := by
  apply satisfies_of_falsified
  intro hf
  apply h
  intro s w hw
  have hm : blockLit p s w ∈ (evenWords.map (blockLit p false) ++ evenWords.map (blockLit p true)) := by
    apply List.mem_append.mpr
    cases s
    · exact Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩)
    · exact Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hl := hf _ hm
  by_cases hp : w ∈ p.on s
  · simpa [blockLit, hp, Sat.Valuation.neg] using hl
  · simpa [blockLit, hp, Sat.Valuation.neg] using hl

private def formula : Sat.Fmla := inputRows.map Row.clause ++ patterns.map block

-- The expected type checks the entire input CNF against the semantic rows.
open Lean Elab Term in
elab "five_axis_lrat" certificate:term:max : term => do
  let .lit (.strVal contents) ← elabTermEnsuringType certificate (mkConst ``String)
    | throwError "Expected literal certificate data"
  let data ← Lean.ofExcept (Json.parse contents)
  let input ← Lean.ofExcept ((data.getObjVal? "cnf").bind Json.getStr?)
  let trace ← Lean.ofExcept ((data.getObjVal? "lrat").bind Json.getStr?)
  let (_, _, _, proof) ← Mathlib.Tactic.Sat.fromLRATAux input trace (← mkAuxName `orbitCover)
  return proof

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem refute : formula.proof [] := by
  exact five_axis_lrat
    (include_str "../../../../../../../Evidence/D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9FiveAxisOrbitCover.result.json")

private theorem valid_inputs : ∀ r ∈ inputRows, r.Valid := by
  have h : inputRows.all (fun r => decide r.Valid) = true := by decide +kernel
  intro r hr
  exact of_decide_eq_true (List.all_eq_true.mp h r hr)

open Classical in
/-- All occupancy valuations of the finite tableau belong to one of the six
orbits of the rooted layer. -/
theorem covers {v : Sat.Valuation} (h : Tableau v) :
    ∃ r ∈ representatives, ∃ p ∈ orbit r, Matches v p := by
  have hp : ∃ p ∈ patterns, Matches v p := by
    by_contra hn
    apply refute v
    constructor
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
      exact h r (valid_inputs r hr)
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact satisfies_block (fun hm => hn ⟨p, hp, hm⟩)
  obtain ⟨p, hp, hm⟩ := hp
  have hflat : p ∈ representatives.flatMap orbit := by
    simpa only [List.mem_toFinset] using
      (show p ∈ (representatives.flatMap orbit).toFinset by
        rw [← pattern_orbits]
        simpa only [List.mem_toFinset] using hp)
  obtain ⟨r, hr, hp⟩ := List.mem_flatMap.mp hflat
  exact ⟨r, hr, p, hp, hm⟩

#print axioms covers

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitCover
