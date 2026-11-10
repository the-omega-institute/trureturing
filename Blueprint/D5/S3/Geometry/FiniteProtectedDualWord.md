# FiniteProtectedDualWord

## Abstract

Ordered raw face partitions produce «protected» native collapses on the unchanged ground, including ghosts, VOID and UNIT.

The raw authority is OriginalLabelTwoSum.Family = LowerSet (Finset V). Empty raw membership, original ambient ghosts and the Fintype native instances are preserved. The full word is partitioned into disjoint pairs and possibly empty criticals with earlier-face dependencies. Protection is upward within K and whole-symbol, contains all criticals, and only emitted uppers must be proper. Current carries a true ordered decomposition. Existing native CollapsePair and Sequence witnesses are constructed with exact deletion and terminal equality.

**Definition 1.1 (Symbol).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.Symbol`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.Symbol` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raw pair and critical symbols, including empty critical faces.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

inductive Symbol (V : Type*) where

  | pair (L : Finset V) (v : V)

  | critical (S : Finset V)

  deriving DecidableEq

**Definition 1.2 (Symbol.faces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.faces`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.faces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact raw faces owned by each symbol.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def faces : Symbol V → Finset (Finset V)

**Definition 1.3 (Symbol.isCritical).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.isCritical`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.isCritical` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Critical-symbol predicate used by the empty-protection consumer.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def isCritical : Symbol V → Prop

**Theorem 1.4 (Symbol.pair_faces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.pair_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteProtectedDualWord.pair_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact two-face expansion of a pair symbol.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem pair_faces (L : Finset V) (v : V) :

    (Symbol.pair L v).faces = {L, insert v L}

**Theorem 1.5 (Symbol.critical_faces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.critical_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteProtectedDualWord.critical_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact singleton expansion of a critical symbol.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

@[simp] theorem critical_faces (S : Finset V) :

    (Symbol.critical S).faces = {S}

**Definition 1.6 (emittedOne).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.emittedOne`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.emittedOne` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only unprotected pairs emit their two faces.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def emittedOne (H : Finset (Finset V)) : Symbol V → Finset (Finset V)

**Definition 1.7 (emittedFaces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.emittedFaces`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.emittedFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite union of exactly the emissions in the given list.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def emittedFaces (H : Finset (Finset V)) : List (Symbol V) → Finset (Finset V)

**Definition 1.8 (rawDual).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.rawDual`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.rawDual` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existing finite dualTable on the raw LowerSet membership table, with proved downward closure.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def rawDual (W : Finset V) (K : Family V) : Family V

**Definition 1.9 (RawFaces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.RawFaces`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.RawFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonempty current faces are supported in W and have an outside-K or not-yet-emitted complement.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def RawFaces (W : Finset V) (K : Family V)

    (R : Finset (Finset V)) (s : Finset V) : Prop

**Definition 1.10 (rawEndpoint).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.rawEndpoint`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.rawEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Raw exact endpoint, with upward protection only inside K.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def rawEndpoint (W : Finset V) (K : Family V) (H : Finset (Finset V))

    (hUp : ∀ {T U}, T ∈ H → U ∈ K → T ⊆ U → U ∈ H) : Family V

**Definition 1.11 (protectedEndpoint).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native projection after constructing the raw endpoint.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def protectedEndpoint (W : Finset V) (K : Family V) (H : Finset (Finset V))

    (hUp : ∀ {T U}, T ∈ H → U ∈ K → T ⊆ U → U ∈ H) :

    PreAbstractSimplicialComplex V

**Definition 1.12 (Word).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.Word`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.Word` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Full raw partition and ordered dependencies, with no desired native output premise.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Word (W : Finset V) (K : Family V) where

  word : List (Symbol V)

  supported : OriginalLabelTwoSum.Supported W K

  pair_data : ∀ L v, Symbol.pair L v ∈ word →

    L ∈ K ∧ insert v L ∈ K ∧ v ∉ L

  critical_data : ∀ S, Symbol.critical S ∈ word → S ∈ K

  partition : word.Pairwise (fun σ τ => Disjoint σ.faces τ.faces)

  covers : ∀ s, s ∈ K ↔ ∃ i : Fin word.length, s ∈ (word.get i).faces

  pair_dependency : ∀ («prefix» suffix : List (Symbol V)) L v,

    word = «prefix» ++ Symbol.pair L v :: suffix →

    ∀ T, T ⊂ insert v L → T ≠ L → ∃ σ ∈ «prefix», T ∈ σ.faces

  critical_dependency : ∀ («prefix» suffix : List (Symbol V)) S,

    word = «prefix» ++ Symbol.critical S :: suffix →

    ∀ T, T ⊂ S → ∃ σ ∈ «prefix», T ∈ σ.faces

**Definition 1.13 (Contract).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.Contract`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.Contract` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Upward, whole-symbol and all-critical protection; only emitted uppers must be proper.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

structure Contract (W : Finset V) (K : Family V) extends Word W K where

  «protected» : Finset (Finset V)

  protected_subset : ∀ T ∈ «protected», T ∈ K

  protected_upward : ∀ {T U}, T ∈ «protected» → U ∈ K → T ⊆ U → U ∈ «protected»

  protected_pair : ∀ L v, Symbol.pair L v ∈ word →

    (L ∈ «protected» ↔ insert v L ∈ «protected»)

  critical_protected : ∀ S, Symbol.critical S ∈ word → S ∈ «protected»

  emitted_proper : ∀ L v, Symbol.pair L v ∈ word → L ∉ «protected» → insert v L ⊂ W

**Definition 1.14 (Contract.current).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.current`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.current` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Downward closure derived at an actual word=prefix++suffix decomposition.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Contract W K)

def current («prefix» suffix : List (Symbol V))

    (hword : d.word = «prefix» ++ suffix) : PreAbstractSimplicialComplex V

**Definition 1.15 (Contract.nativePair).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.nativePair`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.nativePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Existing native CollapsePair with lower W\U, upper W\L and all actual cofaces proved.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Contract W K)

def nativePair («prefix» suffix : List (Symbol V)) (L : Finset V) (v : V)

    (hword : d.word = «prefix» ++ Symbol.pair L v :: suffix) (hL : L ∉ d.«protected») :

    CollapsePair V

**Theorem 1.16 (Contract.protectedEndpoint_mem).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Exact union of the nonempty finite raw dual and nonempty protected complements.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Contract W K)

theorem protectedEndpoint_mem (s : Finset V) :

    s ∈ protectedEndpoint W K d.«protected» d.protected_upward ↔

      s ∈ project (rawDual W K) ∨

        (s.Nonempty ∧ ∃ T ∈ d.«protected», s = W \ T)

**Definition 1.17 (Contract.protectedDualWordSequence).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.protectedDualWordSequence`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.protectedDualWordSequence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Constructive universal P02 witness using only existing Sequence.refl, Sequence.step and equality transport.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Contract W K)

def protectedDualWordSequence :

    Sequence (simplex W) (protectedEndpoint W K d.«protected» d.protected_upward)

**Definition 1.18 (criticalFaces).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.criticalFaces`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.criticalFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Finite collection of the word criticals, retaining the empty face.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

def criticalFaces : List (Symbol V) → Finset (Finset V)

**Definition 1.19 (Word.noCritical_unprotected).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.noCritical_unprotected`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.noCritical_unprotected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

No-critical data constructs empty protection and an actual native Sequence to the raw dual projection.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Word W K)

def noCritical_unprotected

    (hcrit : ∀ σ ∈ d.word, ¬ σ.isCritical)

    (hproper : ∀ L v, Symbol.pair L v ∈ d.word → insert v L ⊂ W) :

    Sequence (simplex W) (project (rawDual W K))

**Definition 1.20 (Word.maximalCritical_protected).**

Lean statement: `D5/S3/Geometry/FiniteProtectedDualWord.maximalCritical_protected`

*Formalization.* `D5/S3/Geometry/FiniteProtectedDualWord.maximalCritical_protected` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Maximality derives upward protection; disjoint partition derives whole symbols; the universal engine constructs the native Sequence.

### Source text

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {W : Finset V} {K : Family V} (d : Word W K)

def maximalCritical_protected

    (hmax : ∀ S, Symbol.critical S ∈ d.word → ∀ T ∈ K, S ⊆ T → T = S)

    (hproper : ∀ L v, Symbol.pair L v ∈ d.word → insert v L ⊂ W) :

    Sequence (simplex W)

      (protectedEndpoint W K (criticalFaces d.word) (by

        intro S T hS hT hST

        have hc := (mem_criticalFaces d.word S).mp hS

        rw [hmax S hc T hT hST]

        exact hS))

## References

- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.Contract`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.RawFaces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.Symbol`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.Word`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.criticalFaces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.critical_faces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.current`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.emittedFaces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.emittedOne`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.faces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.isCritical`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.maximalCritical_protected`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.nativePair`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.noCritical_unprotected`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.pair_faces`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.protectedDualWordSequence`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.protectedEndpoint_mem`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.rawDual`
- Truth anchor: `D5/S3/Geometry/FiniteProtectedDualWord.rawEndpoint`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/OriginalLabelTwoSum/Raw](OriginalLabelTwoSum/Raw.md)
