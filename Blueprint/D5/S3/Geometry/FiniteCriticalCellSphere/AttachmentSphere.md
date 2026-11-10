# The barycentric collar and the unchanged quotient

## Abstract

The literal finite attachment collar, core quotient and both nonempty-face Euclidean sphere branches.

The standalone based contraction of P is the sole homotopy input. The full boundary, both based inverse homotopies, original labels and attached singleton S0 branch are preserved. An unrestricted arbitrary-plane certificate supplier is not assumed.

**Definition 1.1 (Actual-coordinate attachment input).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The input consists of native X and P on the unchanged finite ambient type, a nonempty face, the exact union X=P union simplex(face), exact intersection P intersect simplex(face)=boundary(face), an actual point p of P, and a HomotopyRel contraction of P to p fixing p. The sole allowed homotopy input is this standalone based contraction of P to p fixing p. No contraction of X, desired sphere equivalence, collar or freeness across X is assumed.

**Definition 1.2 (A point of the face label type).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Nonempty face data supplies a Nonempty instance for its original-label subtype. This orders no labels and deletes no ambient ghosts.

**Definition 1.3 (The existing L2 simplex).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Disk is the frozen rational owner Simplex on the subtype of original face labels, with nonnegative coordinates and mass one.

**Definition 1.4 (The full boundary subspace).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

BDisk is the subtype of disk points having a zero coordinate at some face label. It is empty for a singleton face.

**Definition 1.5 (The literal realized core in X).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of the original realization of X lies in coreSet exactly when its same coordinate vector lies in the realization of P.

**Definition 1.6 (The literal realized attached disk).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A point of X lies in diskSet exactly when its original coordinate vector lies in faceSimplex(face), including support zero at every ambient label outside face.

**Definition 1.7 (The unchanged core inclusion).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The existing realizationInclusion is used for P into X, with containment derived from the exact union.

**Definition 1.8 (The actual included basepoint).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The basepoint of X is the literal core inclusion of the supplied point of P.

**Definition 1.9 (Zero extension into the original X).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The disk map uses the existing faceCoordinateHomeomorph, extending the L2 face coordinates by zero in all original ambient coordinates, then includes that actual face in X.

**Definition 1.10 (The original attaching map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A boundary disk point is sent into P by its unchanged ambient coordinate vector. The proof uses the exact native intersection and the full-boundary coordinate characterization.

**Definition 1.11 (The face-only radial gauge).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

rho(x)=1-card(face)*min_i(x_i), with the min ranging only over the original face labels. The source proves zero-to-one bounds, continuity, and value one on the full boundary.

**Definition 1.12 (Radial expansion with an actual range proof).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For u>0 and rho(x)<=u, expansion is b+u inverse times (x-b) in the actual L2 simplex. Its proof supplies coordinate nonnegativity and mass one. Existing zero extension preserves original ambient support.

**Definition 1.13 (The moving radial seam).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

At time s the seam is c_s=1-s/2. It is continuous and lies between one half and one.

**Theorem 1.14 (A positive seam denominator).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every attachment and unit-interval time the seam denominator is positive, from its lower bound one half.

**Definition 1.15 (The closed outer radial region).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the subset of I times the literal simplex where c_s<=rho(x). The inner region is rho(x)<=c_s; both are closed and cover.

**Definition 1.16 (The actual boundary projection).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On the outer region rho is at least one half. The map sends x to b+(x-b)/rho in the full boundary, with an attained face-coordinate minimum supplying an actual zero coordinate.

**Definition 1.17 (The bounded outer contraction time).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The time is 2*rho(x)-2+s in the unit interval. It is zero on the moving seam and equals s on the disk boundary.

**Definition 1.18 (Closed pasting on the simplex cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

On rho<=c_s use disk inclusion after expansion by c_s; on rho>=c_s use the standalone core contraction of the boundary projection at outerTime. Equality at the seam follows from contraction time zero.

**Definition 1.19 (Closed pasting on the actual attachment cylinder).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The core piece is the supplied contraction followed by inclusion, and the disk piece is diskCollar. The exact intersection is the full boundary, where both pieces equal the same core contraction at time s. Closed-cover pasting proves continuity on I times the actual realization of X.

**Definition 1.20 (The literal core collapse).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Q is the existing subset collapse of coreSet in the actual realization of X, with its native quotient topology.

**Definition 1.21 (The unchanged quotient map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

q is exactly the existing canonical collapseMap of coreSet. It is not changed by a basepoint-adjustment construction.

**Definition 1.22 (The endpoint collar descends).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The inverse Q to X is Quotient.lift of x mapped to collar(1,x). The endpoint sends every core point to the same included p, and quotient-lift continuity follows from the actual continuous collar.

**Definition 1.23 (Both based quotient homotopies).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The forward map is exactly q and the backward map is quotientInverse. On X use the collar from identity to inverse after q. On Q descend q after the full collar; it respects the quotient at every time because the collar preserves P. Continuity uses the existing locally-compact-time quotient-lift API. Reversing both homotopies gives the BasedEquivalence fields.

**Theorem 1.24 (The whole core restriction).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every time s and actual x in P, collar(s,coreIn(x)) is coreIn(contraction(s,x)). This retains all core points and the supplied original contraction.

**Theorem 1.25 (Central representative equation).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s and x with rho(x)<=c_s, collar(s,diskIn(x)) equals diskIn(b+(x-b)/c_s), with the actual simplex range proofs in expand.

**Theorem 1.26 (Outer representative equation).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_outer`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_outer` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every s and x with c_s<=rho(x), collar(s,diskIn(x)) equals the included standalone core contraction of b+(x-b)/rho(x) at time 2*rho(x)-2+s. No collapse pair of P is asserted free in X.

**Theorem 1.27 (Time zero and the fixed actual point).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_laws`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_laws` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The collar is identity on all of X at time zero and fixes the actual included p at every time.

**Theorem 1.28 (Exact quotient and inverse on representatives).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every actual X point, quotientEquivalence.forward is the literal setoid class of that point, and backward of q(x) is collar(1,x).

**Theorem 1.29 (Inner radial doubling).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_inner`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_inner` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every disk point with rho<=one half, quotientInverse of its q-class is diskIn(b+2*(x-b)). The public equation uses expand with the exact positive denominator one half.

**Theorem 1.30 (The inverse center equation).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_barycenter`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_barycenter` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The endpoint inverse sends the q-class of the actual included barycenter to that same original barycenter point.

**Definition 1.31 (A genuine boundary-quotient map).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The continuous lift sends the full-boundary class of x to q(diskIn(x)). It is defined for all nonempty faces; no equivalence claim is made for this map when the face has one label.

**Definition 1.32 (The full-boundary quotient comparison for at least two labels).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For card(face)>=2, a genuine boundary vertex exists. Paste its boundary class on P with the original disk class on the disk, descend through q, and use simplexQuotientToQ as inverse. Both inverse identities and both continuities are proved by actual representatives and closed pasting.

**Definition 1.33 (The exact rational sphere representative).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.spherePsi`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.spherePsi` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the frozen rational psi map followed by its norm-preserving L2 reindexSphere and stdIndex. Only Fintype.card of the original face subtype is rewritten to the corresponding finset cardinality.

**Definition 1.34 (The actual reindexed north pole).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereNorth`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereNorth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the rational owner north point under the same L2 isometric reindexing; it lies in StdSphere(card(face)-1).

**Definition 1.35 (The actual reindexed south pole).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereSouth`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereSouth` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

This is the rational owner south point under the same L2 isometric reindexing; it is the collapsed core point for the nonsingleton branch.

**Definition 1.36 (The actual Euclidean comparison for at least two labels).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose quotientSimplexHomeomorph with the existing rational simplexBoundaryStdSphere, retaining the literal Q domain and actual StdSphere(card(face)-1) codomain.

**Theorem 1.37 (Exact rational representative equation).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_representative`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_representative` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every disk x and card(face)>=2, the actual Q-to-sphere map sends q(diskIn(x)) to spherePsi(x), with the existing rational formula and coordinate ordering.

**Theorem 1.38 (Every core point maps to south).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_core`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_core` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For card(face)>=2 and every actual point x of P, the Q-to-sphere map sends q(coreIn(x)) to the actual reindexed south pole.

**Theorem 1.39 (Barycenter and full-boundary poles).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_poles`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_poles` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For card(face)>=2, the included barycenter maps to the actual north pole and every full-boundary disk point maps to the actual south pole.

**Definition 1.40 (Two actual classes in the singleton case).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

When card(face)=1, the native intersection has empty ordinary realization. The actual core and disk pieces are disjoint closed pieces, hence clopen. Paste false on the core and true on the isolated original vertex, descend through q, and invert by q(p) and q(the unique disk point). This retains the collapsed nonempty core class.

**Definition 1.41 (Actual positive S0 point).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Positive`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Positive` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate function constantly +1 on Fin 1, explicitly packaged in the L2 Euclidean unit sphere StdSphere(0).

**Definition 1.42 (Actual negative S0 point).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Negative`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Negative` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate function constantly -1 on Fin 1, explicitly packaged in the same actual Euclidean unit sphere.

**Definition 1.43 (Explicit plus-minus Euclidean comparison).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.boolSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.boolSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Map false to the negative sphere point and true to the positive sphere point. The coordinate-square equation proves that these exhaust StdSphere(0); the explicit bijection is continuous and compact-to-Hausdorff inverse continuity finishes the homeomorphism.

**Theorem 1.44 (The actual isolated point stays fixed).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singleton_collar`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singleton_collar` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For card(face)=1, every time and every actual disk representative, collar(s,diskIn(x))=diskIn(x). On the complementary clopen core the collar is the supplied standalone contraction.

**Definition 1.45 (The separate actual S0 comparison).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the actual two-class quotient homeomorphism with the explicit plus-minus homeomorphism to StdSphere(0). The one-point simplex quotient by empty boundary is never used as S0.

**Definition 1.46 (Only the dimension equality is transported).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Rewrite card(face)-1=0 in the separate actual singleton sphere comparison. All original points and coordinates are retained.

**Theorem 1.47 (The singleton pole equations).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere_points`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere_points` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

When card(face)=1, the actual included core point maps to the actual negative point of StdSphere(0), and every representative of the unique disk point maps to the actual positive point.

**Definition 1.48 (All nonempty critical faces).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Branch at card(face)=1 using the separate actual S0 comparison; otherwise positivity of the face cardinality gives the at-least-two branch. Empty faces are excluded by the input, and no negative-dimensional sphere is invented.

**Definition 1.49 (The actual chosen sphere point).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Apply the actual sphereHomeomorph to q of the actual included p. The pole equations identify this point in each cardinality branch.

**Definition 1.50 (Both based sphere inverse homotopies).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence`

*Formalization.* `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Compose the actual q based equivalence with the actual Q-to-Euclidean-sphere homeomorphism. Both homotopies and their fixed-point equations are transported explicitly; no sphere equivalence is an input.

**Theorem 1.51 (The exact sphere maps).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphere_maps`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphere_maps` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The forward is sphereHomeomorph after the unchanged q; the backward is the endpoint quotientInverse after sphereHomeomorph inverse.

**Theorem 1.52 (Original labels and zero extension).**

Lean statement: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.diskIn_coordinates`

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.diskIn_coordinates` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

For every disk point, coordinate i in the original face is exactly its input L2 coordinate, and every original ambient coordinate outside face is zero. This is a support statement, never a false identification of the plain-function norm with the L2 norm.

## References

- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Attachment`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.BDisk`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Disk`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.Q`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.basepoint`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.boundaryToCore`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_core`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_inner`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_laws`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.collar_outer`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreIn`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.coreSet`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.cut_pos`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskCollar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskIn`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.diskSet`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.expand`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.faceInhabited`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerRegion`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.outerTime`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.projection`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.q`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_barycenter`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotientInverse_inner`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.quotient_representative`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar.rho`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.boolSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.diskIn_coordinates`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_core`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_poles`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.multiSphere_representative`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.quotientSimplexHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Negative`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.s0Positive`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.simplexQuotientToQ`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonQuotientHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere0Homeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singletonSphere_points`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.singleton_collar`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereBasepoint`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereEquivalence`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereHomeomorph`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereNorth`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.spherePsi`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphereSouth`
- Truth anchor: `D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentSphere.sphere_maps`
- Dependency: [D5/S3/Geometry/FiniteAlexanderDualCollapse](../FiniteAlexanderDualCollapse.md)
- Dependency: [D5/S3/Geometry/FiniteCriticalCellSphere/AttachmentCollar](AttachmentCollar.md)
- Dependency: [D5/S3/Geometry/FiniteSimplexBoundarySphere](../FiniteSimplexBoundarySphere.md)
