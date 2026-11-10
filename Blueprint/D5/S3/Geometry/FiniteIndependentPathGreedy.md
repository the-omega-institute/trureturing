# FiniteIndependentPathGreedy

## Abstract

Augmented independent paths have an exact unbounded three-coordinate greedy recurrence.

The full augmented path family and an unbounded three-coordinate survivor recurrence, with distinct 0/1/2 bases, literal insertion transport, a modulo-three closed recursive selection, and independent-path membership. Lexical section variables are recorded faithfully. Lean may omit unused variables.

**Definition 1.1 (paths).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.paths`

*Formalization.* `D5/S3/Geometry/FiniteIndependentPathGreedy.paths` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.paths.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def paths : List V → Finset (Finset V)

**Theorem 1.2 (remaining_paths_three).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_three`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_three.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_paths_three (v w z : V) (vs : List V)

    (hd : (v :: w :: z :: vs).Nodup) :

    remaining (paths (v :: w :: z :: vs)) v = (paths vs).image (insert w)

**Theorem 1.3 (remaining_paths_two).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_two`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_two` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_two.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_paths_two (v w : V) (hvw : v ≠ w) :

    remaining (paths [v, w]) v = {{w}}

**Theorem 1.4 (remaining_paths_one).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.remaining_paths_one.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remaining_paths_one (v : V) : remaining (paths [v]) v = ∅

**Definition 1.5 (pathCritical).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.pathCritical`

*Formalization.* `D5/S3/Geometry/FiniteIndependentPathGreedy.pathCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.pathCritical.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pathCritical : List V → Finset (Finset V)

**Theorem 1.6 (survivors_paths).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.survivors_paths.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_paths (vs : List V) (hd : vs.Nodup) :

    survivors (paths vs) vs = pathCritical vs

**Definition 1.7 (pathChosen).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.pathChosen`

*Formalization.* `D5/S3/Geometry/FiniteIndependentPathGreedy.pathChosen` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.pathChosen.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def pathChosen : List V → Finset V

**Theorem 1.8 (survivors_paths_closed).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths_closed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths_closed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.survivors_paths_closed.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_paths_closed (vs : List V) (hd : vs.Nodup) :

    survivors (paths vs) vs =

      if vs.length % 3 = 1 then ∅ else {pathChosen vs}

**Definition 1.9 (IndependentAlong).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.IndependentAlong`

*Formalization.* `D5/S3/Geometry/FiniteIndependentPathGreedy.IndependentAlong` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.IndependentAlong.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def IndependentAlong : List V → Finset V → Prop

**Theorem 1.10 (mem_paths_iff).**

Lean statement: `D5/S3/Geometry/FiniteIndependentPathGreedy.mem_paths_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteIndependentPathGreedy.mem_paths_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteIndependentPathGreedy.mem_paths_iff.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem mem_paths_iff (vs : List V) (hd : vs.Nodup) (a : Finset V) :

    a ∈ paths vs ↔ (∀ x ∈ a, x ∈ vs) ∧ IndependentAlong vs a

## References

- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.IndependentAlong`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.mem_paths_iff`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.pathChosen`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.pathCritical`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.paths`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_one`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_three`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.remaining_paths_two`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths`
- Truth anchor: `D5/S3/Geometry/FiniteIndependentPathGreedy.survivors_paths_closed`
- Dependency: [D5/S3/Geometry/FiniteGreedyFamilyTransport](FiniteGreedyFamilyTransport.md)
