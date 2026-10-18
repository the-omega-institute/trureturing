# Positive generalized lengths and flat sectors

## Abstract

The entire positive six-coordinate domain has precisely the native genuine or closed flat angle patterns.

The six coordinates vary independently over the open interval (1,infinity), in the original order (12,13,14,34,24,23). Write phi(x,q)=TwoLengthAngleSum.rawCos(x,q) and alpha(x,q)=TwoLengthAngleSum.extendedAngle(x,q). The latter is arccos(max(-1,min(phi(x,q),1))). Both functions use FourCycleCurvature.frame and FourCycleEnvelopes.cosine. No upper coordinate bound, paired transverse lengths, coloring or symmetry is assumed.

Genuine(x) means -1<phi(x,q)<1 at all six positions. For k in Fin(3), first(k)=k and second(k)=k+3 in Fin(6). Sector(x,k) means phi(x,first(k))<=-1. These are the three opposite pairs. The equality fibers phi=-1 and phi=1 are included in the flat patterns.

**Theorem 1.1 (Complete native classification).**

$$\forall x \in Function\left(Fin\left(6\right), Real\right),\; \left(\forall q \in Fin\left(6\right),\; 1 < value\left(x, q\right)\right) \Rightarrow \left(\left(\left(Genuine\left(x\right) \Leftrightarrow \left(\forall q \in Fin\left(6\right),\; 0 < alpha\left(x, q\right) \land alpha\left(x, q\right) < pi\right)\right) \land \left(Genuine\left(x\right) \lor \left(\exists k \in Fin\left(3\right),\; Sector\left(x, k\right) \land \left(\forall j \in Fin\left(3\right),\; Sector\left(x, j\right) \Rightarrow j = k\right)\right)\right)\right) \land \left(\forall k \in Fin\left(3\right),\; \left(Sector\left(x, k\right) \Leftrightarrow phi\left(x, second\left(k\right)\right) \le 0 - 1\right) \land \left(Sector\left(x, k\right) \Leftrightarrow \left(\forall q \in Fin\left(6\right),\; \left(\left(q = first\left(k\right) \lor q = second\left(k\right)\right) \Rightarrow alpha\left(x, q\right) = pi\right) \land \left(\left(q \ne first\left(k\right) \land q \ne second\left(k\right)\right) \Rightarrow alpha\left(x, q\right) = 0\right)\right)\right)\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/PositiveFlatClassification.positive_classification` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

The common polynomial delta satisfies rawNum(x,q)^2-leftRad(x,q)rightRad(x,q)=(x(q)^2-1)delta(x) for every original frame. Positive radicands fix the square-root branches. Negative delta puts all raw values strictly inside (-1,1). For nonnegative delta, the cofactor triangle identity forces a negative numerator. Such a numerator forces its opposite coordinate product to dominate the other two opposite products, making the four adjacent numerators positive. A second cofactor triangle identity then makes the opposite numerator negative. The common square-gap identity places exactly that opposite pair at or below -1 and the other four values at or above 1. Clipping and the principal arccos endpoint laws give the stated complete angle pattern. The selected sector is unique.

The classification is an analytic statement about the original formula. It does not construct a hyperideal polyhedron or assert existence of a common zero-curvature global length. The positive-domain and closed-sector conclusions are those required from the length theory attributed in CFMP_GEOMETRIC_REALIZATION.md Sections 50 and 64 to Luo-Yang, arXiv:1404.5365v2, Propositions 4.4-4.5 and Lemma 4.6. The Lean proof establishes the formula statement directly; the attribution is not an imported proof.

**Theorem 1.2 (Strict local logarithmic budget).**

$$\forall r \in Real, a \in Real, b \in Real, o \in Real, c \in Real, d \in Real,\; \left(\left(\left(\left(\left(\left(1 < r \land 1 < a\right) \land 1 < b\right) \land 1 < o\right) \land 1 < c\right) \land 1 < d\right) \land cosine\left(r, a, b, o, c, d\right) \le 0 - 1\right) \Rightarrow \left(log\left(16\right) + 2 \cdot log\left(\frac{r}{r - 1}\right) + 2 \cdot log\left(\frac{o}{o - 1}\right) \le 2 \cdot log\left(r\right) + 2 \cdot log\left(o\right) - log\left(a\right) - log\left(b\right) - log\left(c\right) - log\left(d\right) \land log\left(16\right) < log\left(16\right) + 2 \cdot log\left(\frac{r}{r - 1}\right) + 2 \cdot log\left(\frac{o}{o - 1}\right)\right)$$

*Proof.* Machine-checked in Lean as `D5/S3/Geometry/Hyperideal/PositiveFlatClassification.native_flat_budget` (`✓ std3`). ∎

*Source.* Repository-derived.

*Commentary.*

Let R=r^2-1, A=rad(r,a,d), B=rad(r,b,c). Apply finite Cauchy-Schwarz to U=(sqrt(R),a-d,sqrt(2(r+1)ad)) and V=(sqrt(R),c-b,sqrt(2(r+1)bc)). Their squared norms are A and B, and their inner product is R+(a-d)(c-b)+2(r+1)sqrt(abcd). Thus this inner product is at most sqrt(A)sqrt(B). Combining this bound with the original negative-cosine inequality gives (r-1)(o-1)>=ac+bd+2sqrt(abcd)>=4sqrt(abcd). Squaring nonnegative sides gives (r-1)^2(o-1)^2>=16abcd. Positive logarithm arguments and the exact product, quotient and power laws give the displayed budget. Both correction logarithms are strictly positive. The inclusive flat boundary remains in scope. No sharpness-at-infinity or equality characterization is asserted.

## References

- Truth anchor: `D5/S3/Geometry/Hyperideal/PositiveFlatClassification.native_flat_budget`
- Truth anchor: `D5/S3/Geometry/Hyperideal/PositiveFlatClassification.positive_classification`
- Dependency: [D5/S3/Geometry/Hyperideal/TwoLengthAngleSum](TwoLengthAngleSum.md)
