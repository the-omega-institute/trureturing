# Whole subcomplex cylinder and homotopy extension

## Abstract

A coordinate collar retracts the entire bottom-or-subcomplex cylinder and gives arbitrary-target homotopy extension.

## Source text

/- GID: D5/S3/Geometry/FiniteSubcomplexCylinder

   generality: G

   mirror-B: D5/B/S3/Geometry/FiniteSubcomplexCylinder

   mirror-E: none(waiver:finite-subcomplex-cylinder)

   anchors: [mathlib/module/Mathlib.Topology.Compactness.Compact, mathlib/module/Mathlib.Topology.Piecewise]

   utility: none

   digest: A coordinate collar retracts the entire bottom-or-subcomplex cylinder and gives arbitrary-target homotopy extension. -/

The paired Lean module supplies these definitions and proofs.

The authored context is variable {V : Type*} [Fintype V] [DecidableEq V]. The section NonemptyFaces uses P : SubcomplexPair V, whose nonempty face collection is genuinely required for its minimum. Outside that section K and L are arbitrary complexes; Extension adds only {Y : Type*} [TopologicalSpace Y], f and g of the displayed types. No global nonempty label, full-subcomplex, cone, supplied collar, cofibration or extension assumption is inserted.

The dependency FiniteConeCollapse.SubcomplexPair supplies the actual original-coordinate deformation. FiniteConeUnionWedge.realization_closed supplies closedness for the boundary pasting. These are reused definitions and theorems, not additional hypotheses of the final extension theorem.

Actual consumer: D5.S3.Geometry.FiniteComponentClosure.contractible_cover_equivalence, defined in FiniteComponentClosure/ConeSplits.lean, constructs R and hR directly with retraction (X ⊔ Y) C hC and retraction_fixed, then supplies them to FiniteConeUnionWedge.contractibleCollapse. Its contractibility and basepoint assumptions belong to that consumer. The cylinder and arbitrary-target extension here require none of those assumptions. The import alone is not the evidence of use.

**Definition 1.1 (The existing coordinate realization as a space).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.Space`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.Space` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Space K is the subtype of FiniteConeCollapse.realization K in V → ℝ with its inherited topology. The finite label type may be empty; no Nonempty V or chosen vertex is imposed by this abbreviation.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.Space

Exact authored Lean header:abbrev Space (K : PreAbstractSimplicialComplex V)

**Definition 1.2 (The original realized subcomplex inside K).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.Subspace`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.Subspace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Subspace K L consists of x : Space K whose unchanged coordinate vector belongs to realization L. This definition itself is meaningful without L ≤ K; the retraction and extension theorems supply that inclusion explicitly.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.Subspace

Exact authored Lean header:def Subspace (K L : PreAbstractSimplicialComplex V) : Set (Space K)

**Definition 1.3 (The whole bottom-or-subcomplex cylinder).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.Cylinder`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.Cylinder` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Cylinder K L is the set of pairs in Space K × I satisfying t=0 or x.val ∈ realization L; its coerced subtype is the retraction target. It contains the entire ambient bottom and the entire vertical cylinder over the realized subcomplex, rather than a selected-point cylinder or a collar-only subset.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.Cylinder

Exact authored Lean header:def Cylinder (K L : PreAbstractSimplicialComplex V) : Set (Space K × I)

**Theorem 1.4 (Face nonemptiness exactly detects points).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

A realization point has a face witness. Conversely a face witness is a nonempty Mathlib face, so choose a vertex of that face and use its coordinate unit vector in the convex hull. No inhabitant of V is assumed in advance; this equivalence also handles an empty label type.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty

### Source text

Exact authored Lean header:theorem realization_nonempty_iff_faces_nonempty (L : PreAbstractSimplicialComplex V) :

    (realization L).Nonempty ↔ (L : Set (Finset V)).Nonempty

**Theorem 1.5 (No faces gives the empty realization).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If L has no faces, any supposed realization point would yield a face by the previous equivalence, a contradiction. This empty-subcomplex branch needs neither a face minimum nor a point of L.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces

### Source text

Exact authored Lean header:theorem realization_eq_empty_of_no_faces (L : PreAbstractSimplicialComplex V)

    (hL : ¬ (L : Set (Finset V)).Nonempty) : realization L = ∅

**Definition 1.6 (The bounded original collar control).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.control`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.control` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For P : FiniteConeCollapse.SubcomplexPair V, control(x) is min(delta(x) / epsilon, 1) in I. Here outsideMass(s,x) is the sum of x(v) over the original labels v outside s; delta is its minimum over all actual subcomplex faces, and epsilon = 1 / (2 * (card V + 1)). The dependency proves delta ≥ 0, epsilon > 0, continuity, and delta=0 exactly on the realized subcomplex. At parameter s its deformation coordinate is max(x(v) - s * min(delta, epsilon), 0) divided by the sum of those truncated coordinates over V, a denominator at least 1/2. This preserves every original face and every zero ghost coordinate. Thus deform 1 enters the subcomplex when delta ≤ epsilon; control < 1 supplies this bound without assuming a collar.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.control

Exact authored Lean header:def control (x : P.Space) : I

**Definition 1.7 (The original collar retracts the full cylinder).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For a SubcomplexPair with an inhabited face collection, put u=control(x), choose time=min(t/u,1), and return (deform time x, max(t - control(x), 0)). Lean division at u=0 is defined as zero; the selector need not be continuous there. At u>0 the ratio and clamping are continuous. At u=0 the base point lies in the subcomplex and deform fixes it for every parameter. The compact interval and the generalized tube lemma give uniform neighborhood control for every selected time, so the horizontal composite is continuous at each zero-control point without any continuity of the selector there. Away from that locus, the particular ratio selector is continuous. Positive height forces t>u and hence either the fixed u=0 case or deform 1 with u<1; therefore the output lies in the whole bottom-or-subcomplex cylinder. This includes the u=1,t=1 corner without division by 1-u.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction

Exact authored Lean header:def nonemptyRetraction : C(P.Space × I, Cylinder P.ambient P.subcomplex)

**Theorem 1.8 (The lower branch including its seam).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_lower`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_lower` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0 < control(x) and t ≤ control(x). The clamped time is exactly t/control(x) in I and the height is zero. At equality t=control(x), the bounded ratio is one and both branch expressions agree as (deform 1 x, 0). The theorem keeps its positive-control hypothesis; it does not divide at zero.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_lower

### Source text

Exact authored Lean header:theorem nonemptyRetraction_lower (x : P.Space) (t : I)

    (hx : 0 < (control P x : ℝ)) (ht : (t : ℝ) ≤ (control P x : ℝ)) :

    (nonemptyRetraction P (x, t)).val =

      (P.deform ⟨(t : ℝ) / (control P x : ℝ),

        div_nonneg t.property.1 hx.le, (div_le_one hx).mpr ht⟩ x, 0)

**Theorem 1.9 (The upper branch has no height rescaling).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_upper`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_upper` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume 0 < control(x) and control(x) < t. The clamped time equals one, and the new height is the unnormalized difference t-control(x). Since t≤1, this strict inequality also gives control(x)<1, so deform 1 x lies in the subcomplex. No division by 1-control(x) or rational surrogate height is introduced.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_upper

### Source text

Exact authored Lean header:theorem nonemptyRetraction_upper (x : P.Space) (t : I)

    (hx : 0 < (control P x : ℝ)) (ht : (control P x : ℝ) < (t : ℝ)) :

    (nonemptyRetraction P (x, t)).val =

      (P.deform 1 x, ⟨(t : ℝ) - (control P x : ℝ), sub_nonneg.mpr ht.le,

        (sub_le_self _ hx.le).trans t.property.2⟩)

**Theorem 1.10 (Every point of both cylinder pieces is fixed).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

If the input is on the bottom, time at t=0 is zero and the deformation starts at x, while max(0-u,0)=0. If the base belongs to the subcomplex, u=0, every deformation time fixes x and max(t,0)=t. The disjunction proves exact fixedness on the entire target, including their intersection.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.nonemptyRetraction_fixed

### Source text

Exact authored Lean header:theorem nonemptyRetraction_fixed (z : P.Space × I)

    (hz : z.2 = 0 ∨ z.1.val ∈ realization P.subcomplex) :

    (nonemptyRetraction P z).val = z

**Definition 1.11 (A retraction for every finite inclusion).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction`

*Formalization.* `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Given hLK : L ≤ K, split on whether L has an actual face. The inhabited-face branch uses the displayed lower and upper formulas at positive control and nonemptyRetraction at zero control, for the exact pair (K,L,hLK,hL). Their proved equalities transport the joint continuity of nonemptyRetraction to this same map. When L has no faces, send (x,t) directly to (x,0). This formula uses no minimum or chosen point of L. Empty labels, empty K, empty L and ghost labels are allowed. If L=K, the target is all of Space K × I and the fixedness theorem makes the retraction identity.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.retraction

Exact authored Lean header:def retraction (hLK : L ≤ K) : C(Space K × I, Cylinder K L)

**Theorem 1.12 (The unrestricted retraction fixes its whole target).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction_fixed`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction_fixed` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

In the inhabited-face branch use branchRetraction_eq and nonemptyRetraction_fixed. In the no-faces branch, the side alternative is impossible because realization L is empty, and the bottom alternative is fixed by the bottom map. The exact equality is of the output value with the original pair, for every point satisfying either target condition.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.retraction_fixed

### Source text

Exact authored Lean header:theorem retraction_fixed (hLK : L ≤ K) (z : Space K × I)

    (hz : z.2 = 0 ∨ z.1.val ∈ realization L) : (retraction K L hLK z).val = z

**Theorem 1.13 (Arbitrary-target homotopy extension).**

Lean statement: `D5/S3/Geometry/FiniteSubcomplexCylinder.homotopy_extension`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteSubcomplexCylinder.homotopy_extension` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For an arbitrary topological target Y, continuous f : Space K → Y and g : I × Subspace K L → Y, assume only g(0,a)=f(a.val) and L ≤ K. Define the boundary map on Cylinder by g on the side and f otherwise. The closed bottom and side cover the target: finite-coordinate realization_closed makes the side closed, and the time-zero condition makes the bottom closed. The two restrictions agree at the intersection by hzero, so closed pasting proves continuity with no separation axiom on Y. Compose this map with retraction and swap the time/base factors to obtain F : C(I × Space K,Y). Whole-target fixedness gives both the initial equality and the equality with g at every time on the subspace. HEP is a conclusion of the construction, not an input.

Lean name:D5.S3.Geometry.FiniteSubcomplexCylinder.homotopy_extension

### Source text

Exact authored Lean header:theorem homotopy_extension (hLK : L ≤ K)

    (hzero : ∀ a : Subspace K L, g (0, a) = f a.val) :

    ∃ F : C(I × Space K, Y), (∀ x, F (0, x) = f x) ∧

      ∀ (t : I) (a : Subspace K L), F (t, a.val) = g (t, a)

## References

- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.Cylinder`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.Space`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.Subspace`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.control`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.homotopy_extension`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_fixed`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_lower`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.nonemptyRetraction_upper`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_eq_empty_of_no_faces`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.realization_nonempty_iff_faces_nonempty`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction`
- Truth anchor: `D5/S3/Geometry/FiniteSubcomplexCylinder.retraction_fixed`
- Dependency: [D5/S3/Geometry/FiniteConeUnionWedge](FiniteConeUnionWedge.md)
