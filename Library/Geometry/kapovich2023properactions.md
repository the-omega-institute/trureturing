---
bibkey: kapovich2023properactions
authors: M. Kapovich
year: 2023
title: A note on properly discontinuous actions
doi: 10.1007/s40863-023-00353-z
url: https://www.math.ucdavis.edu/~kapovich/EPR/prop-disc.pdf
claim: Lemma 21(2) proves properness of an isometric orbit quotient of a proper metric space by projection of closed balls; the preceding discussion identifies proper and metrically proper discrete actions in a proper ambient space.
strata_touched:
  - D5/S3/Geometry/IsometricOrbitMetric
license: citation-only
triage: anchor
---

<!-- GID: D5/L/Geometry/kapovich2023properactions -->
# Compatible isometric orbit metrics and quotient properness

## Source and scope

Kapovich, *A note on properly discontinuous actions*, published in 2023.
The author's revised manuscript at the URL above is dated 18 June 2024.
The locators here refer to that manuscript: page 9, the quotient metric
formula (20) and Lemma 21(2); page 10, its closed-ball projection proof.
The author's introduction reports a correction to Section 7 concerning
fundamental domains. This note uses the Section 6 quotient metric argument.
The journal also lists a correction, DOI 10.1007/s40863-024-00457-0;
no claim about the contents of that separate correction is made here.

For an isometric discrete action on a proper metric space, the manuscript
identifies properness of the action with metric properness. It then gives
a quotient metric inducing the quotient topology and proves that the
quotient is proper: each closed quotient ball is the projection of the
closed ambient ball about a representative. Neither freeness nor geodesicity
is required for Lemma 21(2). No cocompactness hypothesis is needed.

## Representation convention and formal construction

Let G be a group, X a metric space, and rho a homomorphism from G to the
self-isometries of X. Write pi:X -> X/rho for the orbit projection. The
formal construction uses the infimum distance to an orbit rather than
asserting a minimum without ambient properness. It proves metric and
quotient-topology compatibility for compact-set proper discontinuity even
when X is not proper. The properness conclusion additionally assumes that
X is proper. The general nonproper-ambient clause is not attributed to
Kapovich's metrically proper-action statement alone.

These are classical quotient-metric constructions and their formal bridges;
this note makes no mathematical novelty or rigidity claim. The representation
quotient convention agrees with the standard orbit quotient. Mathlib's
proper-action Hausdorff theorem, closed-set zero-distance criterion and
nearest-point attainment supply the corresponding ingredients.

## Infimum metric and its proof

For the representation orbit relation, put
\(O_y=\{\rho(g)y:g\in G\}\) and define

\[
 d_\rho([x],[y])=\operatorname{infDist}(x,O_y)
 =\inf_{g\in G}d_X(x,\rho(g)y).
\]

The orbit contains \(y\), so this infimum is finite and nonnegative.
Distance to a nonempty set, its invariance under an isometry, and attainment
on a nonempty closed subset of a proper metric space are the standard
point-to-set distance results.

For the representation
quotient, the displayed function is independent
of representatives. If the representation is properly discontinuous in the compact-set sense, this function is a metric inducing the existing quotient
topology. If in addition \(X\) is proper, then \((X/\rho,d_\rho)\) is
proper. Freeness and compactness of the quotient are not hypotheses.

**Proof.** Replacing \(x\) by \(\rho(a)x\) and \(y\) by \(\rho(b)y\)
reindexes the orbit: \(\rho(a)O_y=O_{\rho(b)y}\). Isometry invariance of
point-to-set distance proves independence. Inversion in \(G\) and distance
symmetry give symmetry of \(d_\rho\). For all \(g,h\in G\),

\[
 d_\rho([x],[z])\leq d_X(x,\rho(gh)z)
 \leq d_X(x,\rho(g)y)+d_X(y,\rho(h)z).
\]

Taking the two infima proves the triangle inequality. The distance from
an orbit to itself is zero. Proper discontinuity on a metric space gives
a proper action when the group is given the discrete topology, and a
proper action has a Hausdorff orbit quotient. These standard proper-action
results apply through the standard orbit quotient comparison. Thus each fiber
\(O_y=\pi^{-1}\{[y]\}\) is closed. The standard zero-distance criterion
for a nonempty closed set gives \(d_\rho([x],[y])=0\) exactly when
\(x\in O_y\), proving separation.

If \(U\) is quotient-open and \([x]\in U\), some ambient ball about \(x\)
lies in \(\pi^{-1}U\). Any class sufficiently close to \([x]\) has a
translate of a representative in that ball, so belongs to \(U\).
Conversely, the inequality \(d_\rho([x],[y])\leq d_X(x,y)\) shows that
the preimage of an orbit-distance neighborhood contains an ambient ball.
These two implications identify the metric topology with the
existing quotient topology.

Suppose now that \(X\) is proper. Distance from \(x\) to the closed
nonempty orbit \(O_y\) is attained at a point \(z\in O_y\). If
\(d_\rho([x],[y])\leq r\), then \(d_X(x,z)\leq r\) and \([z]=[y]\),
which gives one inclusion in the ball identity. The opposite inclusion
follows from \(d_\rho([x],[z])\leq d_X(x,z)\). The ambient closed ball
is compact and \(\pi\) is continuous in the agreed topology, so the
quotient closed ball is compact. This bridge concerns the representation
quotient; it imposes no finite-volume or smooth-curvature conclusion.
