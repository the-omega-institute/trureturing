# Finite original-label elementary collapse

## Abstract

An explicit coordinate free-face deformation fixes the entire retained realization on the original labels.

## Source text

/- GID: D5/S3/Geometry/FiniteElementaryCollapse

   generality: G

   mirror-B: D5/B/S3/Geometry/FiniteElementaryCollapse

   mirror-E: none(waiver:finite-elementary-collapse)

   anchors: [mathlib/module/Mathlib.Data.Finset.Lattice.Fold, mathlib/module/Mathlib.Topology.Order.Lattice]

   utility: none

   digest: An explicit coordinate free-face deformation fixes the entire retained realization on the original labels. -/

Let V be a finite type with decidable equality, and let P : CollapsePair V. A point is a nonnegative vector of total mass one supported on an actual nonempty face. Ghost labels remain coordinates with value zero, not extra vertices.

The barycentric construction follows section 2 of the relative-cancellation proof, source SHA256 f9888966c4313557587f6c91f7a185a8aa6de6473219536205db6600e64553ad, which credits the cancellation proposal. The result here is the local elementary deformation; neither a link-collapse sequence nor theta cancellation is asserted.

**Definition 1.1 (A genuine free pair).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.CollapsePair`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.CollapsePair` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

CollapsePair stores only an ambient nonempty-face complex, a nonempty lower face, an apex outside it, the upper-face membership, and the sole strict coface condition. Freeness is quantified over every ambient face; no realization, retraction, equivalence, or desired conclusion is a field. Finite original labels may include ghosts, and no purity or connectedness assumption is added.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair

### Source text

Exact authored Lean header: structure CollapsePair (V : Type*) [Fintype V] [DecidableEq V] where

  ambient : PreAbstractSimplicialComplex V

  lower : Finset V

  apex : V

  lower_nonempty : lower.Nonempty

  apex_notMem : apex ∉ lower

  upper_mem : insert apex lower ∈ ambient

  free : ∀ s ∈ ambient, lower ⊂ s → s = insert apex lower

**Remark 1.2 (Original ambient complex).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.ambient`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.ambient` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The ambient projection returns the given PreAbstractSimplicialComplex V. All coordinates, faces and subsequent retained complexes use this same V, including ghost labels.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.ambient

Exact authored Lean field: ambient : PreAbstractSimplicialComplex V

**Remark 1.3 (The designated lower face).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.lower`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.lower` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The lower projection returns the finite set used by freeness, the minimum and deletion. Its actual nonemptiness is recorded separately by lower_nonempty; it is never replaced by an augmented empty face.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower

Exact authored Lean field: lower : Finset V

**Remark 1.4 (The original apex label).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.apex`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.apex` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The apex projection returns a label of the same V, not a fresh tag or a point in a changed realization. The apex_notMem field and upper_mem determine its role in the mass transfer.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.apex

Exact authored Lean field: apex : V

**Remark 1.5 (Nonempty lower-face evidence).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.lower_nonempty`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.lower_nonempty` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This proof-valued structure field supplies lower.Nonempty. It licenses the finite attained minimum.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower_nonempty

Exact authored Lean field: lower_nonempty : lower.Nonempty

**Remark 1.6 (Disjoint mass-transfer coordinates).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.apex_notMem`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.apex_notMem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This proof-valued field records apex ∉ lower. It ensures the apex receives all removed mass without also being one of the subtracted coordinates, and the attaining lower label is different from the apex.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.apex_notMem

Exact authored Lean field: apex_notMem : apex ∉ lower

**Remark 1.7 (The actual upper simplex exists).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.upper_mem`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.upper_mem` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This proof-valued field is membership of insert apex lower in ambient. It supplies the containing simplex for every active intermediate point, even when the original lower face has zero apex coordinate.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.upper_mem

Exact authored Lean field: upper_mem : insert apex lower ∈ ambient

**Remark 1.8 (Every strict coface is the specified upper).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.free`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.free` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For each ambient s, lower ⊂ s implies s = insert apex lower. This is purely combinatorial freeness, used both to identify the exact deleted faces and to keep the deformation inside upper. It assumes no topological result.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.free

Exact authored Lean field: free : ∀ s ∈ ambient, lower ⊂ s → s = insert apex lower

**Definition 1.9 (The exact upper face).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.upper`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.upper` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

upper is insert apex lower on the original labels. The apex is outside lower, so these are distinct nonempty faces, with one additional vertex upstairs. This abbreviation introduces no replacement carrier.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.upper

Exact authored Lean header: abbrev upper : Finset V

**Theorem 1.10 (Lower-face membership from downward closure).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.lower_mem`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.lower_mem` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The inclusion lower ⊆ insert apex lower and lower_nonempty let the ambient relative lower-set law derive lower membership from upper_mem. No separate lower-face assumption is required.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.lower_mem

Exact authored Lean header: theorem lower_mem : P.lower ∈ P.ambient

**Definition 1.11 (The literal retained complex).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.retained`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.retained` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The retained faces are exactly those s in ambient for which lower is not a subset of s. This family is closed under nonempty subfaces because any lower subset of a smaller face would also be a subset of the larger face. It retains all other faces and components on the same original labels. For every s t : Finset V, if hs : s ∈ P.retained, hts : t ⊆ s and ht : t.Nonempty, then t ∈ P.retained directly by (P.retained.isRelLowerSet_faces hs).2 hts ht. The nonempty hypothesis is essential: the empty face is never inserted into the geometric complex.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained

Exact authored Lean header: def retained : PreAbstractSimplicialComplex V

**Theorem 1.12 (Exactly two faces are removed).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.mem_retained_iff`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.mem_retained_iff` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For each s, retained membership is equivalent to ambient membership with s unequal to lower and upper. To prove the converse, an ambient face containing lower is either lower itself or, by freeness when strict, upper. Thus the definition does not accidentally delete additional cofaces.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.mem_retained_iff

### Source text

Exact authored Lean header: theorem mem_retained_iff (s : Finset V) :

    s ∈ P.retained ↔ s ∈ P.ambient ∧ s ≠ P.lower ∧ s ≠ P.upper

**Theorem 1.13 (The actual subcomplex inclusion).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.retained_le`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.retained_le` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Every retained face is an ambient face by its first conjunct. This is the order proof used to form the literal realizationInclusion, rather than an unrelated embedding of a homeomorphic space.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained_le

Exact authored Lean header: theorem retained_le : P.retained ≤ P.ambient

**Theorem 1.14 (Every retained face remains nonempty).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.retained_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.retained_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The nonempty-face axiom of the retained PreAbstractSimplicialComplex supplies s.Nonempty for every retained member. This theorem does not assert that the whole retained face collection or its realization is inhabited.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retained_nonempty

Exact authored Lean header: theorem retained_nonempty {s : Finset V} (hs : s ∈ P.retained) : s.Nonempty

**Theorem 1.15 (No geometric empty face).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.empty_not_mem_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.empty_not_mem_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

An alleged empty retained face contradicts retained_nonempty. There is no augmented empty-face point and no default inhabitant of the label type.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.empty_not_mem_retained

Exact authored Lean header: @[simp] theorem empty_not_mem_retained : (∅ : Finset V) ∉ P.retained

**Definition 1.16 (The attained lower-face minimum).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.minimum`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.minimum` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

minimum(x) is the infimum over the genuinely nonempty finite set lower, taken at the original lower labels only. For a probability vector it is nonnegative and no larger than any lower coordinate; an attaining label exists. On a retained face, a missing lower label has coordinate zero, forcing the minimum to vanish. No ambient ghost is added to the minimum.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.minimum

Exact authored Lean header: def minimum (x : V → ℝ) : ℝ

**Definition 1.17 (Mass transfer to the original apex).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.endpoint`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.endpoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At the endpoint, subtract minimum(x) at every lower vertex and add lower.card * minimum(x) at the apex; every other coordinate stays x(v). The disjointness apex ∉ lower prevents overlap between those operations. Nonnegativity follows from the minimum bound, and the removed total mass is exactly the mass added. This global formula has no normalization denominator. For a singleton lower it transfers that single coordinate to the apex.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.endpoint

Exact authored Lean header: def endpoint (x : V → ℝ) (v : V) : ℝ

**Theorem 1.18 (An endpoint in the exact retained realization).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.endpoint_mem_retained`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.endpoint_mem_retained` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Choose an ambient face witnessing x. If it contains lower, freeness puts it inside upper, and the whole straight segment stays in that upper simplex; otherwise the minimum is zero and x is fixed. First, mix_mem_ambient at t=1 puts the endpoint in the ambient realization. Obtain a new ambient face witnessing this endpoint, not necessarily the input face. The endpoint probability vector has support contained in this fresh face and nonempty by total mass one; downward closure therefore makes that support an ambient face. A lower label attaining the minimum has endpoint coordinate zero because it is not the apex, so the support omits a lower label and is an actual retained face. This includes an input face equal to the removed lower face, even when the apex coordinate starts zero. The target is the exact retained realization, not a homotopy-equivalent substitute.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.endpoint_mem_retained

### Source text

Exact authored Lean header: theorem endpoint_mem_retained (x : Space P.ambient) :

    P.endpoint x.val ∈ realization P.retained

**Definition 1.19 (Unchanged coordinate inclusion).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.inclusion`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.inclusion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

inclusion is FiniteConeUnionWedge.realizationInclusion retained_le. It simply keeps the vector in V → ℝ with a larger membership proof, including the same zero coordinates at ghost labels.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.inclusion

Exact authored Lean header: abbrev inclusion : C(Space P.retained, Space P.ambient)

**Definition 1.20 (The continuous coordinate retraction).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.retraction`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.retraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Equip endpoint(x.val) with endpoint_mem_retained to define the map to Space retained. The finite minimum is continuous, and each fixed-label coordinate uses only addition, subtraction and constant multiplication, proving continuity before restriction to the actual subspaces.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retraction

Exact authored Lean header: def retraction : C(Space P.ambient, Space P.retained)

**Theorem 1.21 (All retained points are fixed).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.retraction_inclusion`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteElementaryCollapse.retraction_inclusion` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every y in the full retained realization, choose its retained face witness. Some lower vertex is missing, so minimum(y)=0 and endpoint(y)=y. Subtype extensionality gives retraction(inclusion(y))=y. This fixes all retained points, including additional components; it is not only a vertex equation.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.retraction_inclusion

### Source text

Exact authored Lean header: theorem retraction_inclusion (y : Space P.retained) :

    P.retraction (P.inclusion y) = y

**Definition 1.22 (Strong deformation relative to the whole retained space).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.collapseHomotopy`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.collapseHomotopy` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The straight homotopy runs from identity to inclusion.comp retraction. If a witnessing face contains lower, its vertices lie in upper by the free-pair cases; both endpoints and their convex segment lie in the upper simplex. If it misses a lower label, minimum(x)=0 and the segment is constant. The relative condition uses this second argument for every ambient point already in the retained realization, at every time. For every t : I, x : Space P.ambient and v : V, (P.collapseHomotopy (t, x)).val v = x.val v + (if v = P.apex then (t : ℝ) * (P.lower.card : ℝ) * P.minimum x.val else 0) - (if v ∈ P.lower then (t : ℝ) * P.minimum x.val else 0). Both conditionals use the fixed original labels, independently of any chosen face witness. This equality follows directly by changing the left side to mix t x.val (P.endpoint x.val) v, unfolding mix and endpoint, and ring normalization in every conditional case; it holds globally, including t=0 and t=1.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.collapseHomotopy

### Source text

Exact authored Lean header: def collapseHomotopy :

    (ContinuousMap.id (Space P.ambient)).HomotopyRel

      (P.inclusion.comp P.retraction)

      {x | x.val ∈ realization P.retained}

**Definition 1.23 (The actual inclusion is the inverse).**

Lean statement: `D5/S3/Geometry/FiniteElementaryCollapse.collapseEquiv`

*Formalization.* `D5/S3/Geometry/FiniteElementaryCollapse.collapseEquiv` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is retraction and the inverse is inclusion. The left inverse up to homotopy uses the reverse of collapseHomotopy; the right composite is exactly identity by retraction_inclusion. This packages the explicit relative deformation without changing coordinates or assuming an abstract equivalence.

Lean name: D5.S3.Geometry.FiniteElementaryCollapse.CollapsePair.collapseEquiv

Exact authored Lean header: def collapseEquiv : Space P.ambient ≃ₕ Space P.retained

## References

- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.CollapsePair`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.ambient`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.apex`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.apex_notMem`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.collapseEquiv`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.collapseHomotopy`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.empty_not_mem_retained`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.endpoint`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.endpoint_mem_retained`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.free`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.inclusion`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.lower`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.lower_mem`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.lower_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.mem_retained_iff`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.minimum`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.retained`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.retained_le`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.retained_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.retraction`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.retraction_inclusion`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.upper`
- Truth anchor: `D5/S3/Geometry/FiniteElementaryCollapse.upper_mem`
- Dependency: [D5/S3/Geometry/FiniteCoordinateTruncation](FiniteCoordinateTruncation.md)
