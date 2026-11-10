# AllMWheelDocument

## Abstract

Literal all-m wheel paths and actual ordered-path Word consumers.

The sole Symbol/Word/Contract/native Sequence authority is the selected repaired P02 owner. All eight Word fields, constructors and projections are inherited there unchanged. This document describes only concrete declarations present in this source owner. The cycle word, ghost-retaining fill0, every-residue fill1, Gamma criterion, B1/Q1, parent and physical constructions have separate contracts; an unrestricted arbitrary-plane supplier is not assumed. The source scopes below specify the lexical parameters.

**Definition 1.1 (Label).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.Label`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.Label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

abbrev Label (m : Nat) := Fin (m + 1)

**Definition 1.2 (label).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.label`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.label` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def label (m : Nat) (i : Fin m) : Label m

**Definition 1.3 (ground).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.ground`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.ground` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def ground (m : Nat) : Finset (Label m)

**Definition 1.4 (firstLabel).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.firstLabel`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.firstLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def firstLabel (m : Nat) (hm : 3 ≤ m) : Label m

**Definition 1.5 (secondLabel).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.secondLabel`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.secondLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def secondLabel (m : Nat) (hm : 3 ≤ m) : Label m

**Definition 1.6 (lastLabel).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.lastLabel`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.lastLabel` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def lastLabel (m : Nat) : Label m

**Definition 1.7 (rimIndex).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimIndex`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimIndex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def rimIndex (m : Nat) (hm : 0 < m) (i : Fin m) : Fin m

**Definition 1.8 (rimEdge).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimEdge`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimEdge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def rimEdge (m : Nat) (hm : 0 < m) (i : Fin m) : Finset (Label m)

**Definition 1.9 (rimRows).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimRows`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimRows` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def rimRows (m : Nat) (hm : 0 < m) : Rows (Label m)

**Definition 1.10 (wheelRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.wheelRoot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.wheelRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def wheelRoot (m : Nat) (hm : 0 < m) : Family (Label m)

**Definition 1.11 (interfaceRow).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.interfaceRow`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.interfaceRow` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def interfaceRow (m : Nat) (hm : 3 ≤ m) : Fin m

**Definition 1.12 (pathRoot).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRoot`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRoot` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def pathRoot (m : Nat) (hm : 3 ≤ m) : Family (Label m)

**Definition 1.13 (rim).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rim`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rim` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def rim (m : Nat) (hm : 3 ≤ m) : Finset (Label m)

**Definition 1.14 (tailGround).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailGround`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailGround` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def tailGround (m : Nat) (hm : 3 ≤ m) : Finset (Label m)

**Definition 1.15 (A0).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A0`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def A0 (m : Nat) (hm : 3 ≤ m) : Family (Label m)

**Definition 1.16 (A1).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A1`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def A1 (m : Nat) (hm : 3 ≤ m) : Family (Label m)

**Definition 1.17 (starDualCarrier).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.starDualCarrier`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.starDualCarrier` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

def starDualCarrier {V : Type*} [DecidableEq V] (W : Finset V) (K : Family V) :

    Set (Finset V)

**Definition 1.18 (dualIdentity).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.dualIdentity`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.dualIdentity` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def dualIdentity {V : Type*} [DecidableEq V] (W : Finset V) (K L : Family V) : Prop

**Definition 1.19 (labelInterval).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def labelInterval (m lo : Nat) : (n : Nat) → lo + n ≤ m + 1 → List (Label m)

**Theorem 1.20 (labelInterval_length).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem labelInterval_length (m lo n : Nat) (h : lo + n ≤ m + 1) :

    (labelInterval m lo n h).length = n

**Theorem 1.21 (mem_labelInterval).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mem_labelInterval`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mem_labelInterval` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem mem_labelInterval (m lo n : Nat) (h : lo + n ≤ m + 1) (x : Label m) :

    x ∈ labelInterval m lo n h ↔ lo ≤ x.val ∧ x.val < lo + n

**Theorem 1.22 (labelInterval_nodup).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem labelInterval_nodup (m lo n : Nat) (h : lo + n ≤ m + 1) :

    (labelInterval m lo n h).Nodup

**Theorem 1.23 (labelInterval_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem labelInterval_edges (m lo n : Nat) (h : lo + n ≤ m + 1)

    (e : Finset (Label m)) :

    e ∈ pathEdges (labelInterval m lo n h) ↔

      ∃ x y : Label m, lo ≤ x.val ∧ y.val = x.val + 1 ∧

        y.val < lo + n ∧ e = {x, y}

**Definition 1.24 (pathRootPath).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def pathRootPath (m : Nat) (hm : 3 ≤ m) : List (Label m)

**Definition 1.25 (cyclePath).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def cyclePath (m : Nat) (hm : 3 ≤ m) : List (Label m)

**Definition 1.26 (cyclePathTail).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def cyclePathTail (m : Nat) (hm : 3 ≤ m) : List (Label m)

**Definition 1.27 (cyclePathLast).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def cyclePathLast (m : Nat) (hm : 3 ≤ m) : List (Label m)

**Theorem 1.28 (pathRootPath_length).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem pathRootPath_length (m : Nat) (hm : 3 ≤ m) :

    (pathRootPath m hm).length = m

**Theorem 1.29 (cyclePath_length).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePath_length (m : Nat) (hm : 3 ≤ m) :

    (cyclePath m hm).length = m - 3

**Theorem 1.30 (cyclePathTail_length).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePathTail_length (m : Nat) (hm : 3 ≤ m) :

    (cyclePathTail m hm).length = m - 4

**Theorem 1.31 (cyclePathLast_length).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_length`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_length` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePathLast_length (m : Nat) (hm : 3 ≤ m) :

    (cyclePathLast m hm).length = m - 3

**Theorem 1.32 (pathRootPath_nodup).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

theorem pathRootPath_nodup (m : Nat) (hm : 3 ≤ m) : (pathRootPath m hm).Nodup

**Theorem 1.33 (cyclePath_nodup).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

theorem cyclePath_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePath m hm).Nodup

**Theorem 1.34 (cyclePathTail_nodup).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

theorem cyclePathTail_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePathTail m hm).Nodup

**Theorem 1.35 (cyclePathLast_nodup).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_nodup`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_nodup` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

theorem cyclePathLast_nodup (m : Nat) (hm : 3 ≤ m) : (cyclePathLast m hm).Nodup

**Theorem 1.36 (pathRootPath_vertices).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem pathRootPath_vertices (m : Nat) (hm : 3 ≤ m) :

    (pathRootPath m hm).toFinset = ground m

**Theorem 1.37 (cyclePath_vertices).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePath_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :

    x ∈ (cyclePath m hm).toFinset ↔ 3 ≤ x.val ∧ x.val < m

**Theorem 1.38 (cyclePathTail_vertices).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePathTail_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :

    x ∈ (cyclePathTail m hm).toFinset ↔ 4 ≤ x.val ∧ x.val < m

**Theorem 1.39 (cyclePathLast_vertices).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_vertices`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_vertices` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cyclePathLast_vertices (m : Nat) (hm : 3 ≤ m) (x : Label m) :

    x ∈ (cyclePathLast m hm).toFinset ↔ 2 ≤ x.val ∧ x.val + 1 < m

**Theorem 1.40 (pathRootPath_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem pathRootPath_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :

    e ∈ pathEdges (pathRootPath m hm) ↔

      (∃ x y : Label m, 2 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val ≤ m ∧ e = {x, y}) ∨

        e = {lastLabel m, firstLabel m hm}

**Theorem 1.41 (cyclePath_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem cyclePath_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :

    e ∈ pathEdges (cyclePath m hm) ↔

      ∃ x y : Label m, 3 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val < m ∧ e = {x, y}

**Theorem 1.42 (cyclePathTail_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem cyclePathTail_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :

    e ∈ pathEdges (cyclePathTail m hm) ↔

      ∃ x y : Label m, 4 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val < m ∧ e = {x, y}

**Theorem 1.43 (cyclePathLast_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem cyclePathLast_edges (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :

    e ∈ pathEdges (cyclePathLast m hm) ↔

      ∃ x y : Label m, 2 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val + 1 < m ∧ e = {x, y}

**Definition 1.44 (pathRootWordData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootWordData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootWordData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

def pathRootWordData (m : Nat) (hm : 3 ≤ m) :

    Word (ground m) (pathFamily (pathRootPath m hm))

**Definition 1.45 (cycleTailWordData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleTailWordData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleTailWordData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

def cycleTailWordData (m : Nat) (hm : 3 ≤ m) :

    Word (cyclePathTail m hm).toFinset (pathFamily (cyclePathTail m hm))

**Definition 1.46 (cycleLastWordData).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleLastWordData`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleLastWordData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

def cycleLastWordData (m : Nat) (hm : 3 ≤ m) :

    Word (cyclePathLast m hm).toFinset (pathFamily (cyclePathLast m hm))

**Definition 1.47 (cycleEdges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def cycleEdges (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m))

**Theorem 1.48 (cycleEdges_mem).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem cycleEdges_mem (m : Nat) (hm : 3 ≤ m) (e : Finset (Label m)) :

    e ∈ cycleEdges m hm ↔

      (∃ x y : Label m, 1 ≤ x.val ∧ y.val = x.val + 1 ∧ y.val ≤ m ∧ e = {x, y}) ∨

        e = {lastLabel m, firstLabel m hm}

**Theorem 1.49 (pathRootPath_row_edges).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_row_edges`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_row_edges` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem pathRootPath_row_edges (m : Nat) (hm : 3 ≤ m) :

    pathEdges (pathRootPath m hm) =

      ((Finset.univ : Finset (Fin m)).erase (interfaceRow m hm)).image

        (rimEdge m (by omega))

**Definition 1.50 (cycleIndependentOn).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleIndependentOn`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleIndependentOn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def cycleIndependentOn (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m))

**Definition 1.51 (mapSecond).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapSecond`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapSecond` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def mapSecond (m : Nat) (hm : 3 ≤ m) : Symbol (Label m) → Symbol (Label m)

**Definition 1.52 (mapLast).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapLast`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapLast` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def mapLast (m : Nat) (hm : 3 ≤ m) : Symbol (Label m) → Symbol (Label m)

**Definition 1.53 (cycleWord).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Actual three-block cycle list consumes the two canonical path Word records. Full cyclic Word validity and all downstream native/filling obligations remain open.

def cycleWord (m : Nat) (hm : 3 ≤ m) : List (Symbol (Label m))

**Definition 1.54 (tailWord).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def tailWord (m : Nat) (hm : 3 ≤ m) : List (Symbol (Label m))

**Theorem 1.55 (cycleWord_eq).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem cycleWord_eq (m : Nat) (hm : 3 ≤ m) :

    cycleWord m hm =

      (orderedFaces (pathIndependentOn (cyclePath m hm))).map

        (fun T => .pair T (firstLabel m hm)) ++

      (pathWord (cyclePathTail m hm)).map (adjoinSymbol (secondLabel m hm)) ++

      (pathWord (cyclePathLast m hm)).map (adjoinSymbol (lastLabel m))

**Theorem 1.56 (tailWord_eq).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord_eq`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord_eq` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

@[simp] theorem tailWord_eq (m : Nat) (hm : 3 ≤ m) :

    tailWord m hm = pathWord (cyclePathTail m hm)

**Definition 1.57 (labelsCongruent).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelsCongruent`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelsCongruent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def labelsCongruent (m r lo : Nat) : Finset (Label m)

**Definition 1.58 (tailCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailCritical`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def tailCritical (m : Nat) (hm : 3 ≤ m) : Finset (Label m)

**Definition 1.59 (cycleCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleCritical`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Closed labelled target only; no critical-symbol identification theorem is claimed. Residue two uses original last label m as required by the last cycle block.

def cycleCritical (m : Nat) (hm : 3 ≤ m) : Finset (Finset (Label m))

**Definition 1.60 (eta0).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta0`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta0` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def eta0 (m : Nat) (hm : 3 ≤ m) : Finset (Label m)

**Definition 1.61 (eta1).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta1`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta1` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def eta1 (m : Nat) (hm : 3 ≤ m) : Finset (Label m)

**Definition 1.62 (goodResidue).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.goodResidue`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.goodResidue` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def goodResidue (m : Nat) : Prop

**Definition 1.63 (criticalCardProfile).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.criticalCardProfile`

*Formalization.* `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.criticalCardProfile` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

def criticalCardProfile (m : Nat) : Nat × Nat × Nat × Nat

**Theorem 1.64 (pathRootPath_noCritical).**

Lean statement: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_noCritical`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_noCritical` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal source declaration. The appended scope/header is source-derived; it is not an elaborated telescope or an acceptance receipt.

### Source text

theorem pathRootPath_noCritical (m : Nat) (hm : 3 ≤ m) (hg : goodResidue m) :

    ∀ q ∈ pathWord (pathRootPath m hm), ¬ q.isCritical

## References

- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A0`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.A1`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.Label`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.criticalCardProfile`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleCritical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleEdges_mem`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleIndependentOn`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleLastWordData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_length`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_nodup`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathLast_vertices`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_length`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_nodup`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePathTail_vertices`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_length`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_nodup`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cyclePath_vertices`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleTailWordData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.cycleWord_eq`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.dualIdentity`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta0`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.eta1`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.firstLabel`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.goodResidue`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.ground`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.interfaceRow`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.label`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_length`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelInterval_nodup`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.labelsCongruent`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.lastLabel`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapLast`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mapSecond`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.mem_labelInterval`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRoot`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_length`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_noCritical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_nodup`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_row_edges`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootPath_vertices`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.pathRootWordData`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rim`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimEdge`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimIndex`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.rimRows`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.secondLabel`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.starDualCarrier`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailCritical`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailGround`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.tailWord_eq`
- Truth anchor: `D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel.wheelRoot`
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/AllMWheel/PathWord](AllMWheel/PathWord.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/RowIteration](RowIteration.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/WheelSupplier](WheelSupplier.md)
