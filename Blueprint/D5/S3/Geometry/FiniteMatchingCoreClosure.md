# FiniteMatchingCoreClosure

## Abstract

Iterated matching closure has bounded dimension and a maximal critical antichain with full proper boundaries.

The source sections have V : Type*, Fintype V and DecidableEq V. The Pairing extension block is declared in D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing; its entries below give that lexical namespace and open declarations. The source module remains D5/S3/Geometry/FiniteMatchingCoreClosure.lean. Lean may omit unused section variables. Structures and the Walk inductive include their full explicit field/constructor contracts. This matching module supplies finite source extraction; the cyclic recurrence is proved in its separate owner. The collapse consumers use the same native face and coordinate types.

**Definition 1.1 (iterate).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.iterate.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def iterate (f : Finset (Finset V) → Finset (Finset V))

    (S : Finset (Finset V)) : Nat → Finset (Finset V)

**Theorem 1.2 (iterate_stable).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate_stable`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate_stable` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Inflation alone forces stabilization by the number of possible faces. This is a bound for an arbitrary finite closure algorithm, not an enumeration of small complexes or a hypothesis that the desired endpoint exists.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

theorem iterate_stable (f : Finset (Finset V) → Finset (Finset V))

    (hf : ∀ S, S ⊆ f S) (S : Finset (Finset V)) :

    f (iterate f S (Fintype.card (Finset V))) =

      iterate f S (Fintype.card (Finset V))

**Definition 1.3 (Downward).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.Downward`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.Downward` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.Downward.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

def Downward (S : Finset (Finset V)) : Prop

**Definition 1.4 (Pairing.seed).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.seed` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.seed.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def seed (_M : Pairing K) (Q : Finset (Finset V)) : Finset (Finset V)

**Definition 1.5 (Pairing.expand).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.expand.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def expand (S : Finset (Finset V)) : Finset (Finset V)

**Theorem 1.6 (Pairing.mem_seed).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_seed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_seed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.mem_seed.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_seed (Q : Finset (Finset V)) (s : Finset V) :

    s ∈ M.seed Q ↔ s.Nonempty ∧ ∃ q ∈ Q, s ⊆ q

**Theorem 1.7 (Pairing.mem_expand).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_expand`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_expand` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.mem_expand.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

@[simp] theorem mem_expand (S : Finset (Finset V)) (s : Finset V) :

    s ∈ M.expand S ↔ s ∈ S ∨

      (s.Nonempty ∧ ∃ e ∈ M.pairs, e.1 ∈ S ∧ s ⊆ upper e)

**Theorem 1.8 (Pairing.expand_inflationary).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_inflationary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_inflationary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.expand_inflationary.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem expand_inflationary (S : Finset (Finset V)) : S ⊆ M.expand S

**Theorem 1.9 (Pairing.seed_downward).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_downward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_downward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.seed_downward.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem seed_downward (Q : Finset (Finset V)) : Downward (M.seed Q)

**Theorem 1.10 (Pairing.expand_downward).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_downward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_downward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.expand_downward.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem expand_downward {S : Finset (Finset V)} (hS : Downward S) :

    Downward (M.expand S)

**Definition 1.11 (Pairing.stage).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.stage` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.stage.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def stage (Q : Finset (Finset V)) (n : Nat) : Finset (Finset V)

**Definition 1.12 (Pairing.closureFaces).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closureFaces`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.closureFaces` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.closureFaces.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def closureFaces (Q : Finset (Finset V)) : Finset (Finset V)

**Theorem 1.13 (Pairing.closure_fixed).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.closure_fixed.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem closure_fixed (Q : Finset (Finset V)) :

    M.expand (M.closureFaces Q) = M.closureFaces Q

**Theorem 1.14 (Pairing.stage_downward).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_downward`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_downward` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.stage_downward.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem stage_downward (Q : Finset (Finset V)) (n : Nat) :

    Downward (M.stage Q n)

**Theorem 1.15 (Pairing.stage_nonempty).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.stage_nonempty.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem stage_nonempty (Q : Finset (Finset V)) (n : Nat) :

    ∀ s ∈ M.stage Q n, s.Nonempty

**Theorem 1.16 (Pairing.stage_le_ambient).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_le_ambient`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_le_ambient` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.stage_le_ambient.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem stage_le_ambient (Q : Finset (Finset V)) (hQ : ∀ q ∈ Q, q ∈ K)

    (n : Nat) : ∀ s ∈ M.stage Q n, s ∈ K

**Definition 1.17 (Pairing.closure).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.closure` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Native nonempty complex; the missing empty face is not a point.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def closure (Q : Finset (Finset V)) : PreAbstractSimplicialComplex V

**Theorem 1.18 (Pairing.closure_le).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.closure_le.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem closure_le (Q : Finset (Finset V)) (hQ : ∀ q ∈ Q, q ∈ K) :

    M.closure Q ≤ K

**Theorem 1.19 (Pairing.seed_le_stage).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_le_stage`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_le_stage` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.seed_le_stage.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem seed_le_stage (Q : Finset (Finset V)) (n : Nat) :

    M.seed Q ⊆ M.stage Q n

**Theorem 1.20 (Pairing.seed_mem_closure).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_mem_closure`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_mem_closure` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.seed_mem_closure.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem seed_mem_closure (Q : Finset (Finset V)) {q : Finset V}

    (hq : q ∈ Q) (hqn : q.Nonempty) : q ∈ M.closure Q

**Theorem 1.21 (Pairing.closure_saturated).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.closure_saturated.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem closure_saturated (Q : Finset (Finset V)) : M.Saturated (M.closure Q)

**Theorem 1.22 (Pairing.closure_le_saturated).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Leastness also certifies that no gratuitous faces are introduced.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem closure_le_saturated (Q : Finset (Finset V))

    (T : PreAbstractSimplicialComplex V) (hT : M.Saturated T)

    (hQ : ∀ q ∈ Q, q ∈ T) : M.closure Q ≤ T

**Definition 1.23 (Pairing.DimensionInvariant).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.DimensionInvariant`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.DimensionInvariant` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The second invariant is essential: a face at the top allowed dimension can never be a matched LOWER, even if it was introduced as an upper.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

def DimensionInvariant (D : Nat) (S : Finset (Finset V)) : Prop

**Theorem 1.24 (Pairing.seed_dimension).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.seed_dimension.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem seed_dimension (Q : Finset (Finset V)) (D : Nat)

    (hcard : ∀ q ∈ Q, q.card ≤ D)

    (hcrit : ∀ q ∈ Q, M.Unmatched q) : M.DimensionInvariant D (M.seed Q)

**Theorem 1.25 (Pairing.expand_dimension).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.expand_dimension.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem expand_dimension (D : Nat) {S : Finset (Finset V)}

    (hS : M.DimensionInvariant D S) : M.DimensionInvariant D (M.expand S)

**Theorem 1.26 (Pairing.closure_dimension).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing.closure_dimension.

### Source text

Exact attempted Lean contract:Exact lexical source context (not a compiled telescope):

namespace D5.S3.Geometry.FiniteAcyclicFaceMatching.Pairing

open FiniteAcyclicFaceMatching FiniteElementaryCollapse

open FiniteRelativeSimplicialCollapse FiniteMatchingCoreClosure

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} (M : Pairing K)

Definitions and proofs are in the paired Lean module.

theorem closure_dimension (Q : Finset (Finset V)) (D : Nat)

    (hcard : ∀ q ∈ Q, q.card ≤ D)

    (hcrit : ∀ q ∈ Q, M.Unmatched q) :

    ∀ s ∈ M.closure Q, s.card ≤ D

**Definition 1.27 (CriticalData).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.CriticalData`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.CriticalData` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Exact unmatched data. None of the fields asserts a collapse or topology. The singleton point is separate from the distinct same-cardinality critical faces. Their common cardinality D is positive, including the discrete case.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

Definitions and proofs are in the paired Lean module.

structure CriticalData {K : PreAbstractSimplicialComplex V} (M : Pairing K) where

  p : V

  critical : Finset (Finset V)

  D : Nat

  positive : 0 < D

  point_mem : ({p} : Finset V) ∈ K

  critical_mem : ∀ s ∈ critical, s ∈ K

  point_not_critical : ({p} : Finset V) ∉ critical

  cardinality : ∀ s ∈ critical, s.card = D

  unmatched : ∀ s ∈ K, M.Unmatched s ↔ s = {p} ∨ s ∈ critical

**Definition 1.28 (CriticalData.seeds).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.seeds.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

def seeds : Finset (Finset V)

**Definition 1.29 (CriticalData.X).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.X` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.X.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

def X : PreAbstractSimplicialComplex V

**Theorem 1.30 (CriticalData.seeds_mem).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.seeds_mem.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem seeds_mem : ∀ s ∈ A.seeds, s ∈ K

**Theorem 1.31 (CriticalData.seeds_unmatched).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_unmatched`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_unmatched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.seeds_unmatched.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem seeds_unmatched : ∀ s ∈ A.seeds, M.Unmatched s

**Theorem 1.32 (CriticalData.seeds_card).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_card`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_card` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.seeds_card.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem seeds_card : ∀ s ∈ A.seeds, s.card ≤ A.D

**Theorem 1.33 (CriticalData.X_le).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.X_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.X_le.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem X_le : A.X ≤ K

**Theorem 1.34 (CriticalData.X_saturated).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.X_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.X_saturated.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem X_saturated : M.Saturated A.X

**Theorem 1.35 (CriticalData.X_dimension).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_dimension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.X_dimension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.X_dimension.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem X_dimension : ∀ s ∈ A.X, s.card ≤ A.D

**Theorem 1.36 (CriticalData.critical_nonempty).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.critical_nonempty.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem critical_nonempty {s : Finset V} (hs : s ∈ A.critical) : s.Nonempty

**Theorem 1.37 (CriticalData.critical_in_X).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_in_X`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_in_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.critical_in_X.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem critical_in_X {s : Finset V} (hs : s ∈ A.critical) : s ∈ A.X

**Theorem 1.38 (CriticalData.point_in_X).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_X`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.point_in_X.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem point_in_X : ({A.p} : Finset V) ∈ A.X

**Theorem 1.39 (CriticalData.critical_maximal).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_maximal`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_maximal` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every critical simplex is maximal in the ACTUAL closure.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem critical_maximal {s t : Finset V} (hs : s ∈ A.critical)

    (ht : t ∈ A.X) (hst : s ⊆ t) : s = t

**Theorem 1.40 (CriticalData.critical_antichain).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_antichain`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_antichain` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.critical_antichain.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem critical_antichain {s t : Finset V} (hs : s ∈ A.critical)

    (ht : t ∈ A.critical) (hst : s ⊆ t) : s = t

**Definition 1.41 (CriticalData.C).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.C`

*Formalization.* `D5/S3/Geometry/FiniteMatchingCoreClosure.C` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Delete only the maximal unmatched critical faces, not their boundaries.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

def C : PreAbstractSimplicialComplex V

**Theorem 1.42 (CriticalData.mem_C).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_C`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.mem_C.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem mem_C (s : Finset V) : s ∈ A.C ↔ s ∈ A.X ∧ s ∉ A.critical

**Theorem 1.43 (CriticalData.C_le_X).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.C_le_X`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.C_le_X` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.C_le_X.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem C_le_X : A.C ≤ A.X

**Theorem 1.44 (CriticalData.point_in_C).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_C`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.point_in_C.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem point_in_C : ({A.p} : Finset V) ∈ A.C

**Theorem 1.45 (CriticalData.vertex_le_C).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_le_C`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_le_C` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.vertex_le_C.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem vertex_le_C : vertexComplex A.p ≤ A.C

**Theorem 1.46 (CriticalData.proper_boundary).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.proper_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.proper_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Includes the augmented empty subface without treating it as a point.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem proper_boundary {s t : Finset V} (hs : s ∈ A.critical) (hts : t ⊂ s) :

    AugmentedFace A.C t

**Theorem 1.47 (CriticalData.X_core_equation).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_core_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.X_core_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.X_core_equation.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem X_core_equation (s : Finset V) :

    s ∈ A.X ↔ s ∈ A.C ∨ s ∈ A.critical

**Theorem 1.48 (CriticalData.X_cell_equation).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_cell_equation`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.X_cell_equation` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Literal simplex-attachment equation on the same original ground.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem X_cell_equation (s : Finset V) :

    s ∈ A.X ↔ s ∈ A.C ∨ (s.Nonempty ∧ ∃ t ∈ A.critical, s ⊆ t)

**Theorem 1.49 (CriticalData.boundary_in_core_iff).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.boundary_in_core_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.boundary_in_core_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.boundary_in_core_iff.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem boundary_in_core_iff {s t : Finset V} (hs : s ∈ A.critical) (hts : t ⊆ s) :

    AugmentedFace A.C t ↔ t ≠ s

**Theorem 1.50 (CriticalData.critical_unmatched).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_unmatched`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_unmatched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.critical_unmatched.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem critical_unmatched {s : Finset V} (hs : s ∈ A.critical) : M.Unmatched s

**Theorem 1.51 (CriticalData.point_unmatched).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_unmatched`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.point_unmatched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.point_unmatched.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem point_unmatched : M.Unmatched {A.p}

**Theorem 1.52 (CriticalData.C_saturated).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.C_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.C_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.C_saturated.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem C_saturated : M.Saturated A.C

**Theorem 1.53 (CriticalData.vertex_saturated).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_saturated`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_saturated` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.vertex_saturated.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem vertex_saturated : M.Saturated (vertexComplex A.p)

**Theorem 1.54 (CriticalData.core_unmatched).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.core_unmatched`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.core_unmatched` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The exact source contract below specifies D5.S3.Geometry.FiniteMatchingCoreClosure.CriticalData.core_unmatched.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem core_unmatched {s : Finset V} (hs : s ∈ A.C) :

    M.Unmatched s ↔ s = {A.p}

**Theorem 1.55 (CriticalData.discrete_when_D_one).**

Lean statement: `D5/S3/Geometry/FiniteMatchingCoreClosure.discrete_when_D_one`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteMatchingCoreClosure.discrete_when_D_one` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In dimension zero the closure is literally discrete; no empty lower pair is used. This is a conclusion of the cardinal invariant, not a special axiom.

### Source text

Exact attempted Lean contract:Source variable context (not a compiled telescope):

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {K : PreAbstractSimplicialComplex V} {M : Pairing K} (A : CriticalData M)

Definitions and proofs are in the paired Lean module.

theorem discrete_when_D_one (hD : A.D = 1) {s : Finset V} (hs : s ∈ A.X) :

    ∃ v, s = {v}

## References

- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.C`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.C_le_X`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.C_saturated`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.CriticalData`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.DimensionInvariant`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.Downward`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_cell_equation`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_core_equation`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_dimension`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_le`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.X_saturated`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.boundary_in_core_iff`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closureFaces`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_dimension`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_le_saturated`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.closure_saturated`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.core_unmatched`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_antichain`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_in_X`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_maximal`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.critical_unmatched`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.discrete_when_D_one`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_dimension`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_downward`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.expand_inflationary`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.iterate_stable`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_C`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_expand`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.mem_seed`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_C`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_in_X`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.point_unmatched`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.proper_boundary`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_dimension`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_downward`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_le_stage`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seed_mem_closure`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_card`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_mem`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.seeds_unmatched`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_downward`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_le_ambient`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.stage_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_le_C`
- Truth anchor: `D5/S3/Geometry/FiniteMatchingCoreClosure.vertex_saturated`
- Dependency: [D5/S3/Geometry/FiniteMatchingCollapse](FiniteMatchingCollapse.md)
