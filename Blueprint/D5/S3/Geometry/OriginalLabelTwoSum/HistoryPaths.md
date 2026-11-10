# HistoryPaths

## Abstract

Every distinct labelled path has an actual tagged noncover output via the two-leaf LINK recursion.

The literal AllMWheel.pathEdges and the original two-leaf length-three recursion remain the construction. Explicit equality transports make the same constructed output accessible to induction. pathRowsOutput_critical_profile proves that the actual output is strong for length n>=3, with no critical at residue one, one top of cardinality 2*(n/3)-1 at residue zero, and one of cardinality 2*(n/3) at residue two. Lengths zero and one remain VOID, length two remains UNIT. The recursive tops are computed data, not a supplied desired certificate or profile.

 No full universal history or broad-goal completion is asserted.

**Definition 1.1 (pathRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

def pathRows (vs : List V) : Rows V where

  ground := vs.toFinset

  chords := {q : Finset V // q ∈ pathEdges vs}

  row q := q.1

  row_supported q := edge_supported vs q.1 q.2

**Definition 1.2 (pathRowsOutput).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

def pathRowsOutput (vs : List V) (hd : vs.Nodup) :

    Output (pathRows vs).ground (pathRows vs).root :=

  changeOutput (pathOutput vs hd) (pathRows_root vs).symm

**Definition 1.3 (pathCriticalTops).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathCriticalTops`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathCriticalTops` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

def pathCriticalTops : List V → Finset (Finset V)

  | [] => ∅

  | [_] => ∅

  | [_,_] => ∅

  | [_,_,c] => {{c}}

  | [_,_,_,_] => ∅

  | [a,_,c,_,_] => {{a,c}}

  | a::_::c::d::e::f::vs =>

      (pathCriticalTops (d::e::f::vs)).image (fun q => ({a,c} : Finset V) ∪ q)

**Definition 1.4 (PathCriticalProfile).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.PathCriticalProfile`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.PathCriticalProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

def PathCriticalProfile (n : Nat) (D : Finset (Finset V)) : Prop :=

  (n % 3 = 1 → D = ∅) ∧

  (n % 3 = 0 → ∃ q, D = {q} ∧ q.card = 2 * (n / 3) - 1) ∧

  (n % 3 = 2 → ∃ q, D = {q} ∧ q.card = 2 * (n / 3))

**Theorem 1.5 (pathRowsOutput_critical_profile).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput_critical_profile`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput_critical_profile` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

theorem pathRowsOutput_critical_profile (vs : List V) (hd : vs.Nodup)

    (hn : 3 ≤ vs.length) :

    ∃ c : Certificate (pathRows vs).ground (pathRows vs).root,

      pathRowsOutput vs hd = .strong c ∧

      PathCriticalProfile vs.length c.critical := by

  have hs : (pathRowsOutput vs hd).criticalState = .strong (pathCriticalTops vs) := by

    rw [pathRowsOutput, changeOutput_criticalState, pathOutput_state]

    match vs with

    | [] => simp at hn

    | [a] => simp at hn

    | [a,b] => simp at hn

    | a::b::c::vs => rfl

  generalize he : pathRowsOutput vs hd = o at hs

  cases o with

  | void h => cases hs

  | unit h => cases hs

  | strong c =>

      have hc : c.critical = pathCriticalTops vs := by

        exact CriticalState.strong.inj hs

      exact ⟨c, rfl, hc.symm ▸ pathCriticalTops_profile vs hd hn⟩

**Theorem 1.6 (pathRows_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

### Source text

Literal source, not elaborated statement metadata. Namespace D5.S3.Geometry.OriginalLabelTwoSum.HistoryPaths; noncomputable section; open Set Finset. Imports: D5.S3.Geometry.OriginalLabelTwoSum.HistoryLeafCap, D5.S3.Geometry.OriginalLabelTwoSum.AllMWheel.PathWord. Exact public declaration and proof/source body:

theorem pathRows_mem (vs : List V) (s : Finset V) :

    s ∈ (pathRows vs).root ↔

      s ⊆ vs.toFinset ∧ ∃ q ∈ pathEdges vs, Disjoint q s := by

  rw [pathRows_root]

  rfl

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.PathCriticalProfile`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathCriticalTops`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRowsOutput_critical_profile`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/HistoryPaths.pathRows_mem`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord](AllMWheel/PathWord.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/HistoryLeafCap](HistoryLeafCap.md)
