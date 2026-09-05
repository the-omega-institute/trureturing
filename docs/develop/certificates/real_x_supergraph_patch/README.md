# Uniform strict-X supergraph certificate near the real counterexample seed

This is a certificate instance for Section 36 of the single theory volume
`docs/develop/theory/MUB_SIX_FOURTH_BASIS_THEORY.md`, not a second theory volume.
It preserves the real-seed and quarter-seed work of the other agents.

## Certified statement

For every parameter alpha=a+i*b in the closed two-real-dimensional rectangle

```
|a+1/5| <= 2^-32,   |b| <= 2^-32,
```

the checker proves existence and uniqueness of one projective common-unbiased
ray in each of 60 fixed signed-Cayley boxes. All 60 rays are distinct. Their
orthogonality graph is a SUBGRAPH of the supplied 114-edge graph: all 1,656
forbidden pairs have squared normalized inner product greater than 10^-8,
uniformly over the rectangle.

The allowed graph has a distinguished complete six-vertex set, no edges from
that set to the remaining vertices, and a bipartite induced graph on the other
54 vertices. Therefore any six-clique among these 60 continuing rays consists
of the distinguished six. The checker also proves those six rays are fixed
projectively by the cyclic shift, using uniqueness boxes. Consequently every
completion formed entirely from this known collection has exact mode affinity
2. This is not a lower bound for completions containing unknown rays.

The parameter rectangle is deliberately small. It is a verified local patch,
not a macroscopic cover of the two-circulant family.

## Why a supergraph is the right stable object

The center has extra S3 symmetry. An exact orthogonality edge at the center
need not remain an edge when the imaginary parameter changes. A root remaining
simple does not prove an inner product remains zero. This certificate never
uses that inference: old edges may disappear freely. Only forbidden edges are
certified, and their positive interval margins prevent new edges from appearing
between the 60 labeled continuations. Removing edges cannot create a clique.

Thus the noncanonical clique obstruction persists without classifying all
orthogonality strata or proving persistence of any accidental zero edge.

## Exact parameter family

Let c(t)=(1+i*t)/(1-i*t), alpha=a+i*b, and

```
p_alpha(t)=(1+a)t^3+b*t^2+(a-3)t+b.
```

The checker verifies the coefficient identity

```
(1-i*t)^3 [c(t)^3-alpha*c(t)^2+conj(alpha)*c(t)-1]
 = -2*i*p_alpha(t).
```

Uniform endpoint sign changes and nonzero derivative intervals isolate three
real roots of p_alpha near -2,+2,0, and three roots of p_minus_alpha near
-sqrt(21)/3,+sqrt(21)/3,0. Their Cayley images r0,r1,r2 and s0,s1,s2 have unit
modulus. Vieta gives product(r)=product(s)=1 and sum(r)=alpha, sum(s)=-alpha.

Define

```
A=circ(r0*r1,r1,1), B=circ(s0*s1,s1,1),
H=[A B; B* -A*].
```

The cyclic row-ratio sums cancel, and circulant blocks commute, so HH*=6I.
The six-phase Hadamard construction is the one consumed by the existing
`TwoCirculantXSeed.lean`; its analytic root adapters are not claimed as Lean
admitted here. The constant row permutation (2,0,1,4,5,3) puts the center at the
symmetric-block representative used by the preceding real-seed certificate.
It commutes with the simultaneous three-cycle for all parameters.

Thirty interval minor witnesses also show that no two squared rows and no two
squared columns are proportional anywhere in the rectangle. These are the
hypotheses consumed by `HadamardSquaredMinorSeparation.lean`. Since a standard
Fourier-family representative has a proportional squared-row or squared-column
pair, this separation survives full Hadamard monomial equivalence and keeps the
patch outside both Fourier equivalence families. The family identification is
a mathematical adapter, not a root-count assertion.

## Uniform root inclusion

The raw vector has u0=1 and uj=i^qj*(1+i*xj)/(1-i*xj). The first five equations
are |H* u|^2-6=0; the sixth follows from the exact Gram identity. Each chart box
has radius 2^-16. The checker obtains a rational preconditioner by exact
Gaussian elimination of a dyadic midpoint Jacobian, then verifies

```
||I-C J(parameter_box, root_box)||_infinity < 1/4
x0-C f(parameter_box,x0)+(I-C J)(root_box-x0) lies strictly inside root_box.
```

For each exact parameter, the preconditioned Newton map is a contraction from
the complete box to itself. Its unique fixed point is a genuine root. These
inequalities hold uniformly; no sampling of parameter points is used for
acceptance. Interval images then certify all forbidden inner products and
projective distinctness. Root labels use fixed, nonoverlapping enclosures.

## Replay

From the repository root:

```
python3 scripts/research/check_real_x_supergraph_patch.py \
  docs/develop/certificates/real_x_supergraph_patch/input.json \
  --report /tmp/real_x_supergraph_patch_report.json
```

The acceptance path uses only the Python standard library and reuses
`check_strict_x_counterexample.py`. Floating-point discovery only proposed the
centers and allowed graph. Wrong centers, removal of an exact edge from the
allowed graph, and an unsupported enlarged parameter rectangle were rejected.
Source and input hashes are in `verification.json`.

## Remaining proof obligation

No global coverage of all common-unbiased roots is proved. There may be roots
outside the 60 boxes, and those could have edges to this collection. The result
cannot be promoted to unique completion or four-MUB exclusion without an
additional root-cover or triangle-bearing-locus certificate. In particular,
neither the context-affinity bound for every actual completion nor the global
six-dimensional MUB conjecture is claimed.

The Python interval verifier, intermediate-value and contraction adapters have
not been formalized in Lean in this commit. The already submitted Lean sources
retain their separate admission obligations. No passing CI is asserted here.
