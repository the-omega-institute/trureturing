# Normal coordinates at an original regular anchor

## Abstract

Original regular confirmation yields the full signed normal restriction isomorphism and bounded three-dimensional coordinates.

Let V be a finite dimensional real normed space, C its original closed generating cone, and u a linear functional strictly positive on every nonzero vector in C. Keep the entire normalized base K, all its extreme points P, and the entire original effect interval zero <= f <= u. Every original exclusion D(p) is the image of the entire closed Euclidean three-ball under an injective affine map. Assume that equality of exclusion sets implies equality of their original pure labels. No closedness of P, pair properness, least-confirmation law, matrix representation or dimension reduction is assumed.

**Definition 1.1 (Original coordinate space).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.ThreeSpace`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.ThreeSpace` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The coordinate space is EuclideanSpace over the reals indexed by Fin 3, with its Euclidean inner product and norm.

**Definition 1.2 (Entire exclusion chart).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.FullBall3Chart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.FullBall3Chart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

A chart consists of an injective affine map a from the three-dimensional coordinate space to V whose image of the whole closed unit ball equals the original exclusion. Its center is c=a(0), and its linear part B is injective. The native chart conversion preserves the map and the exact whole-image equality.

**Definition 1.3 (All original exclusions are three-balls).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.EB3`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.EB3` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

For every pure point of the entire original base there exists a full three-ball chart. This quantifies every original label and every mixed state in its exclusion.

**Definition 1.4 (Existing native chart carrier).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.nativeChart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.nativeChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The same affine map, injection and whole exclusion equality form an ExclusionChart with dimension exactly three.

**Definition 1.5 (Original regularity).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.Regular`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.Regular` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Regularity at p says that there exists exactly one original linear effect e confirming p and vanishing on every state of D(p). It is uniqueness in the entire common-confirmation family, rather than uniqueness of an exclusion label.

**Definition 1.6 (Signed original normal space).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NormalSpan`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NormalSpan` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

N(p) is the existing zeroPositive set of all original linear functionals nonnegative on the whole cone and zero at p. NormalSpan is its real linear span. Neither positivity nor a choice of effects replaces this signed span.

**Definition 1.7 (Actual constant and slope restriction).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.coordinates`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.coordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Restriction coordinates of f are its value at the chart center and the existing Euclidean Riesz slope of f composed with B. The exact native slope formula gives f(a(w))=f(c)+inner(slope(f),w) for every coordinate vector, including vectors outside the unit ball.

**Definition 1.8 (All affine coordinate functions).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.affineCoordinates`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.affineCoordinates` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The standard constant-plus-linear equivalence for affine maps and the finite dimensional Riesz equivalence identify all affine real functions on the coordinate space with a real constant and a coordinate vector.

**Definition 1.9 (Derived native chart laws).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NativeChart`

*Formalization.* `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NativeChart` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

The data include a linear equivalence from span N(p) onto all affine functions on the actual three-ball, with its forward map proved equal to original restriction. They include an original linear H:V->R^3 satisfying H(a(w))=w for all w, every coordinate functional of H in span N(p), and H(p)=0. For g=u-e they include g in N(p), g(a(w))=1, strict positivity of g on all K except p, and a finite positive M with norm(H(x))<=M*g(x) on the whole original cone. They also identify original comparison zero with the entire exclusion on K, prove source salience from the strict unit, prove u(Bw)=0 for all w, and give dim(span N(p))=4.

**Theorem 1.10 (Original regular-anchor restriction and uniform bound).**

Lean statement: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.regular_anchor_native`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.regular_anchor_native` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Assume the original closed cone, strict unit, generation, full EB3, injective exclusion labels, an original pure p, its common confirmer e, actual regularity at p, and any full chart a of D(p). Then NativeChart data exist with exactly these original parameters. No restriction isomorphism, extension, positivity bound, support representation or shadow geometry is an input.

The existing normal-body inradius theorem supplies actual positive annihilator slopes in a whole neighborhood of zero. A positive annihilator with zero slope is constant on D(p); its global maximum is attained there. After normalization, its complement is an element of the full family A(p). Regularity therefore makes the annihilator a scalar multiple of g. For two positive annihilators with identical constant and slope, add the same actual opposite-slope annihilator. The sums have zero slope and coincide, so the original functionals coincide. The existing positive-span difference theorem extends injectivity to the signed normal span. The inradius and g supply every constant and slope, giving surjectivity onto all affine functions.

Pull back the three unit coordinate slopes to obtain H. Positive annihilators with slopes plus and minus r times each coordinate vector equal g plus and minus r times the corresponding coordinate functional of H. Whole-cone positivity gives absolute value of each H coordinate at most g/r; the Euclidean triangle inequality gives the finite bound M=3/r. Thus the bound includes every mixed original state and extends homogeneously to all cone vectors. For strict positivity of g on K except p, the exposed maximum face of e has only the pure point p: any other pure maximizer would make D(p) a nontrivial subface of its exclusion, so ball-face rigidity and exclusion injectivity force the same label. Compact convex reconstruction then makes the entire maximum face the singleton p.

The full confirming-effect interval is compact, so the original comparison infimum is attained. Consequently comparison(p,x)=0 is equivalent to an actual original confirmer vanishing at x, exactly the native exclusion definition. The construction establishes the original-domain input for normalized shadow ratios; width, directional support minima and boundary-distance conclusions require their additional arguments. These are consequences within the specified mathematical model; no physical realization or literature priority is asserted.

## References

- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.EB3`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.FullBall3Chart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NativeChart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.NormalSpan`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.Regular`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.ThreeSpace`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.affineCoordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.coordinates`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.nativeChart`
- Truth anchor: `D5/S3/Quantum/Foundation/RegularAnchorNormalChart.regular_anchor_native`
- Dependency: [D5/S3/Quantum/Foundation/CommonPositiveExtension](CommonPositiveExtension.md)
- Dependency: [D5/S3/Quantum/Foundation/SingleLabelNormalBody](SingleLabelNormalBody.md)
