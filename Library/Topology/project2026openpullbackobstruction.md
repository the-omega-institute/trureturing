---
bibkey: project2026openpullbackobstruction
authors: trureturing contributors
year: 2026
title: Universal obstruction to preselected full-pullback openness
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/8b0633be3583a50d905517bf0d5e9503a9cd26e6/D5/S3/Topology/Resolution/OpenPullbackObstruction.lean
claim: Every preselected compact Hausdorff zero-dimensional resolution of Cantor space times the unit interval admits a later binary extension whose full pullback fails openness over Cantor.
strata_touched:
  - D5/S3/Topology/Resolution/OpenPullbackObstruction
license: citation-only
triage: anchor
---

# Preselection and the complete pullback

This is a self-contained repository construction, suggested by an Oracle
advisory answer and checked in Lean. It is not attributed to an external
paper, and worldwide novelty is not established. The kernel-checked mathematical
source, rather than this note or the advisory answer, carries the proof.

Let B be the actual binary Cantor space and I the closed real unit interval.
For every continuous surjection a:E -> B x I from an arbitrary-weight
compact Hausdorff zero-dimensional E, the construction gives a continuous
s:B -> I. No metrizability of E or initial openness of fst after a is assumed.
Put T=(B x I) disjoint-sum B. The forgetting map f is the identity on the
first summand and the graph of s on the second; p is the first projection
on the first summand and identity on the second. Thus T is compact
metrizable, p is continuous open onto, f is continuous onto, and fst after
f equals p. Every f fiber has at most two points. The continuous binary
label makes (f,label) a closed embedding into (B x I) x Bool.

The literal full pullback P={(t,e):f(t)=a(e)}, with its product-subtype
topology, is compact Hausdorff zero-dimensional. Both standard projections
are onto. Its common map rho to B is not open. For every topological Y and
every continuous surjection h:Y -> the entire P, rho after h is not open.
The last implication uses the upstream openness-descent theorem directly.

The construction separates the two complete endpoint fibers over the
all-false Cantor point by a clopen H. The closed K=a(H) has a greatest
vertical value c<1 there. A continuous section, built on shrinking clopen
Cantor cylinders, takes values x_n=c+(1-c)/(n+2) on annuli containing
points b_n converging to the all-false point while (b_n,x_n) is outside K.
Its incidence set D is closed, contains the limit point, and excludes all
b_n, so D is not open. The right-labeled points of P whose E coordinate
lies in H form a genuine relative clopen G, and rho(G)=D with a common
compatible witness in both directions.

Writing Fs={e:a(e)=((a(e)).first,s((a(e)).first))}, an explicit
homeomorphism E disjoint-sum Fs -> P supplies the topological assertions.
The E projection is onto using the left representative of a(e), and the
T projection is onto using surjectivity of a at f(t); these are distinct
witness arguments.

The order of quantifiers is: for every preselected a, there exists a later
f. This does not exclude an adaptive resolution depending on f, nor a
proper subspace of P still mapping onto T. It does not resolve unrestricted
Res(B) or Peng Question 5.1. The existing relative metric-kernel resolution
is compatible with this obstruction; see
[project2026relativeopenresolution](project2026relativeopenresolution.md).
The selection literature context is recorded separately in
[valov2008milyutinmaps](valov2008milyutinmaps.md), without attributing this
construction to any uninspected source body.
