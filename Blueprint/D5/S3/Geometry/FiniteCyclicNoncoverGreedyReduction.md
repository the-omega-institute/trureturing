# FiniteCyclicNoncoverGreedyReduction

## Abstract

The original first round has an isolated vertex and an endpoint-constrained independent complement path; true survivor bases retain arbitrary original labels.

The literal original NC(C_n) first round, native no/yes restrictions, direct injective label transport and genuine n=3/4/5 survivor bases. The all-n formulas and critical data are treated in the subsequent native and survivor modules. Lexical section variables are recorded faithfully. Lean may omit unused variables.

**Definition 1.1 (TailIndependent).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.TailIndependent`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.TailIndependent` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.TailIndependent.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def TailIndependent {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) (a : Finset V) : Prop

**Definition 1.2 (tailFaces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tailFaces`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tailFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.tailFaces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def tailFaces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) : Finset (Finset V)

**Theorem 1.3 (first_round).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_round`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_round` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_round.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem first_round {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    remaining (faceSet (noncover (show 0 < n by omega) s)) (point hn s) =

      insert {point hn s} (tailFaces hn s)

**Theorem 1.4 (tail_omits_point).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tail_omits_point`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tail_omits_point` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.tail_omits_point.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem tail_omits_point {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V)

    {a : Finset V} (ha : a ∈ tailFaces hn s) : point hn s ∉ a

**Theorem 1.5 (first_noBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_noBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_noBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_noBranch_faces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem first_noBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    ((nativeRelative (noncover (show 0 < n by omega) s)).noBranch (point hn s)).F =

      tailFaces hn s

**Theorem 1.6 (first_yesBranch_faces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_yesBranch_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_yesBranch_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.first_yesBranch_faces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem first_yesBranch_faces {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    ((nativeRelative (noncover (show 0 < n by omega) s)).yesBranch (point hn s)).F =

      {{point hn s}}

**Definition 1.7 (indexFaces).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.indexFaces`

*Formalization.* `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.indexFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.indexFaces.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def indexFaces (n : Nat) (hn : 0 < n) : Finset (Finset (Fin n))

**Theorem 1.8 (remainingFaces_map).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.remainingFaces_map`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.remainingFaces_map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.remainingFaces_map.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem remainingFaces_map {n : Nat} (hn : 3 ≤ n) (s : Fin n ↪ V) :

    remainingFaces hn s =

      (computeSurvivors (indexFaces n (show 0 < n by omega)) (List.finRange n)).image

        (Finset.map s)

**Theorem 1.9 (survivors_three).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_three`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_three` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_three.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_three (s : Fin 3 ↪ V) :

    remainingFaces (by omega) s =

      insert {point (by omega) s} {criticalA 1 (by omega) s, criticalB 1 (by omega) s}

**Theorem 1.10 (survivors_four).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_four`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_four` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_four.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_four (s : Fin 4 ↪ V) :

    remainingFaces (by omega) s = insert {point (by omega) s} {criticalOne 1 s}

**Theorem 1.11 (survivors_five).**

Lean statement: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_five`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_five` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact source endpoint D5.S3.Geometry.FiniteCyclicNoncoverGreedyReduction.survivors_five.

### Source text

Lexical source context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem survivors_five (s : Fin 5 ↪ V) :

    remainingFaces (by omega) s = insert {point (by omega) s} {criticalTwo 1 (by omega) s}

## References

- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.TailIndependent`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_noBranch_faces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_round`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.first_yesBranch_faces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.indexFaces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.remainingFaces_map`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_five`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_four`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.survivors_three`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tailFaces`
- Truth anchor: `D5/S3/Geometry/FiniteCyclicNoncoverGreedyReduction.tail_omits_point`
- Dependency: [D5/S3/Geometry/FiniteCyclicNoncoverCollapse](FiniteCyclicNoncoverCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteIndependentPathGreedy](FiniteIndependentPathGreedy.md)
