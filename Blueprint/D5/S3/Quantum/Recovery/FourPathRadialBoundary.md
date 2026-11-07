# Four-path radial boundary

## Abstract

Exact ambient geometry of the literal four-path inequality domain and its explicit positive homogeneous radial functional.

**Definition 1.1 (Ambient space).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.Point`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.Point` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

Point is the complex coordinate space Fin 4 to Complex, with its ambient product topology and real scalar multiplication.

**Definition 1.2 (Minimum modulus).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.minMod`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.minMod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

minMod(w) is min(min(|w0|,|w1|),min(|w2|,|w3|)). Repeated minima are retained without selecting an index.

**Definition 1.3 (Maximum modulus).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.maxMod`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.maxMod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

maxMod(w) is max(max(|w0|,|w1|),max(|w2|,|w3|)). Repeated maxima are retained without selecting an index.

**Definition 1.4 (Total modulus).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.totalMod`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.totalMod` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

totalMod(w) is |w0|+|w1|+|w2|+|w3|.

**Definition 1.5 (Literal inequality domain).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.W`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.W` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

W is defined independently by all four inequalities |wj| <= 1 and totalMod(w)-2 minMod(w) <= 2. It is not defined as a sublevel set of m.

**Definition 1.6 (Explicit radial functional).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.m`

*Formalization.* `D5/S3/Quantum/Recovery/FourPathRadialBoundary.m` (`✓ std3`).

*Source.* Repository-derived.

*Commentary.*

m(w) is max(maxMod(w),(totalMod(w)-2 minMod(w))/2). No triangle inequality, norm law or convexity is part of the definition.

**Theorem 1.7 (Complete radial geometry).**

Lean statement: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.exact_radial_boundary`

*Proof.* Machine-checked in Lean as `D5/S3/Quantum/Recovery/FourPathRadialBoundary.exact_radial_boundary` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The weak sublevel {w : m(w) <= 1} equals W. Its ambient interior is {w : m(w) < 1}, and its ambient frontier is {w : m(w) = 1}. Equivalently the frontier consists of points in W satisfying maxMod(w)=1 or totalMod(w)-2 minMod(w)=2. The disjunction is inclusive: tied extrema and simultaneous saturation are preserved.

For every nonzero w in W there exist t and z with 0<t<=1, t=m(w), m(z)=1 and w=t z. For every real s>0 and every y with m(y)=1 and w=s y, the theorem proves both s=t and y=z; the competing representation need not be supplied with s<=1. The proof divides by m(w) only after proving positivity from w nonzero. Zero remains in W and its interior, and no radial division is performed there.

Continuity and positive homogeneity follow from the displayed finite modulus formula. At every z with m(z)=1 the proof constructs u(n)=(1+1/(n+1))z. These points converge to z and all lie outside W, since m(u(n))=1+1/(n+1)>1. This construction excludes such z from the interior and supplies the reverse boundary inclusion; it does not assume that inclusion.

This is the literal geometric content of Definition 23.1, Definition 27.1 and Lemma 27.2 of the four-path recovery theory. It does not identify W with diagonals of actual unitary matrices, establish a producer realization or comparison, or prove the full recovery endpoint. Those require their separate bridges. The finite minimum and maximum formulas include all zero coordinates, boundary parameter t=1, and overlaps of the two saturation types.

## References

- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.Point`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.W`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.exact_radial_boundary`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.m`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.maxMod`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.minMod`
- Truth anchor: `D5/S3/Quantum/Recovery/FourPathRadialBoundary.totalMod`
