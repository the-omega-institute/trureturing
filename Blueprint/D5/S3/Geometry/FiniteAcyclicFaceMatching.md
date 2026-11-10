# FiniteAcyclicFaceMatching

## Abstract

Disjoint nonempty face pairs and the directed Hasse graph admit finite source extraction.

The source section has V : Type*, Fintype V and DecidableEq V; each raw statement retains its lexical source binders and namespace. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Definition 1.1 (Walk).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Walk`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Walk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A positive-length directed walk, with its direction explicit.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

inductive Walk {α : Type*} (r : α → α → Prop) : α → α → Prop

  | one {a b} : r a b → Walk r a b

  | cons {a b c} : r a b → Walk r b c → Walk r a c

**Theorem 1.2 (Walk.trans).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.trans`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.trans` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Walk.trans.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem trans {α : Type*} {r : α → α → Prop} {a b c : α}

    (h : Walk r a b) (k : Walk r b c) : Walk r a c

**Theorem 1.3 (Walk.map).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.map`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.map` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Walk.map.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem map {α β : Type*} {r : α → α → Prop} {q : β → β → Prop}

    (f : α → β) (hf : ∀ a b, r a b → q (f a) (f b))

    {a b : α} (h : Walk r a b) : Walk q (f a) (f b)

**Definition 1.4 (Acyclic).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Acyclic`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Acyclic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Acyclic.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Acyclic {α : Type*} (r : α → α → Prop) : Prop

**Theorem 1.5 (finite_source).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.finite_source`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.finite_source` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every nonempty induced finite subgraph of a DAG has an actual source. The minimizing statistic is the number of strict ancestors in the finite set. An incoming edge makes this ancestor set strictly smaller, not merely weakly smaller. No prechosen topological order is required.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem finite_source {α : Type*} [DecidableEq α] (F : Finset α)

    (r : α → α → Prop) (ha : Acyclic r) (hne : F.Nonempty) :

    ∃ s ∈ F, ∀ t ∈ F, ¬ r t s

**Definition 1.6 (Cover).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Cover`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Cover` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A cover adds exactly one ORIGINAL vertex.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Cover (a b : Finset V) : Prop

**Definition 1.7 (upper).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.upper.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def upper (e : Finset V × V) : Finset V

**Definition 1.8 (Incident).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Incident`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Incident` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Incident.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Incident (s : Finset V) (e : Finset V × V) : Prop

**Definition 1.9 (Pairing).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Pairing`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Pairing` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Only finite combinatorial data: disjoint actual codimension-one pairs. In particular this structure has no collapse, core, map, or SDR field.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

structure Pairing (K : PreAbstractSimplicialComplex V) where

  pairs : Finset (Finset V × V)

  lower_nonempty : ∀ e ∈ pairs, e.1.Nonempty

  apex_notMem : ∀ e ∈ pairs, e.2 ∉ e.1

  upper_mem : ∀ e ∈ pairs, upper e ∈ K

  disjoint : ∀ e ∈ pairs, ∀ f ∈ pairs, ∀ s,

    Incident s e → Incident s f → e = f

**Theorem 1.10 (Pairing.lower_mem).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.lower_mem.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem lower_mem {e : Finset V × V} (he : e ∈ M.pairs) : e.1 ∈ K

**Theorem 1.11 (Pairing.lower_ne_upper).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_ne_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_ne_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.lower_ne_upper.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem lower_ne_upper {e : Finset V × V} (he : e ∈ M.pairs) :

    e.1 ≠ upper e

**Definition 1.12 (Pairing.Unmatched).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Unmatched`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Unmatched` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.Unmatched.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def Unmatched (s : Finset V) : Prop

**Definition 1.13 (Pairing.Edge).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Edge`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Edge` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Matched covers point UP; every other cover points DOWN.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def Edge (a b : Finset V) : Prop

**Definition 1.14 (Pairing.IsAcyclic).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.IsAcyclic`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.IsAcyclic` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.IsAcyclic.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def IsAcyclic : Prop

**Definition 1.15 (Pairing.Saturated).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Saturated`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.Saturated` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.Saturated.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def Saturated (L : PreAbstractSimplicialComplex V) : Prop

**Theorem 1.16 (Pairing.saturated_self).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.saturated_self`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.saturated_self` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.saturated_self.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem saturated_self : M.Saturated K

**Theorem 1.17 (Pairing.upper_edge).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper_edge`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper_edge` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.upper_edge.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem upper_edge {e : Finset V × V} (he : e ∈ M.pairs) :

    M.Edge e.1 (upper e)

**Theorem 1.18 (Pairing.source_lower).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A source outside a saturated target must be a LOWER of a matching pair. The conclusion includes the actual source assertion in the finite difference.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem source_lower (hacyc : M.IsAcyclic)

    {L T : PreAbstractSimplicialComplex V} (hLK : L ≤ K) (hTL : T ≤ L)

    (hL : M.Saturated L) (hT : M.Saturated T)

    (hcrit : ∀ s ∈ L, M.Unmatched s → s ∈ T)

    (hne : L ≠ T) :

    ∃ e ∈ M.pairs, e.1 ∈ L ∧ e.1 ∉ T ∧

      ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1

**Theorem 1.19 (Pairing.source_free).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_free`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_free` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The source condition proves freeness in the WHOLE current complex. For every vertex of a strict coface outside the lower, its immediate coface would point down into the source unless it is the designated upper. This also rules out every coface of higher codimension.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem source_free {L T : PreAbstractSimplicialComplex V}

    (hLK : L ≤ K) (hTL : T ≤ L) (e : Finset V × V) (he : e ∈ M.pairs)

    (hlL : e.1 ∈ L) (hlT : e.1 ∉ T)

    (hsource : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) :

    ∀ t ∈ L, e.1 ⊂ t → t = upper e

**Definition 1.20 (Pairing.sourcePair).**

Lean statement: `D5/S3/Geometry/FiniteAcyclicFaceMatching.sourcePair`

*Formalization.* `D5/S3/Geometry/FiniteAcyclicFaceMatching.sourcePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Construct the native owner pair; no new pair or sequence owner is defined.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def sourcePair {L T : PreAbstractSimplicialComplex V} (hLK : L ≤ K)

    (hTL : T ≤ L) (hL : M.Saturated L) (e : Finset V × V)

    (he : e ∈ M.pairs) (hlL : e.1 ∈ L) (hlT : e.1 ∉ T)

    (hs : ∀ s ∈ L, s ∉ T → ¬ M.Edge s e.1) : CollapsePair V

## References

- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Acyclic`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Cover`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Edge`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Incident`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.IsAcyclic`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Pairing`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Saturated`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Unmatched`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.Walk`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.finite_source`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_mem`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.lower_ne_upper`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.map`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.saturated_self`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.sourcePair`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_free`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.source_lower`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.trans`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper`
- Truth anchor: `D5/S3/Geometry/FiniteAcyclicFaceMatching.upper_edge`
- Dependency: [D5/S3/Geometry/FiniteVertexDominationCollapse](FiniteVertexDominationCollapse.md)
