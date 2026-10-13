---
bibkey: project2026relativeopenresolution
authors: Project mathematical synthesis
year: 2026
title: Relative open-preserving resolution with a compact metrizable kernel
doi: null
url: https://github.com/the-omega-institute/trureturing/blob/a0be6ac2033b56ca11be346ec6b4593b68fbdc27/D5/S3/Topology/Selection/CompactZeroDimensional.lean
claim: The relative resolution construction preserves openness over an arbitrary compact Hausdorff totally disconnected base when a compact metric coordinate embeds the fibers.
strata_touched:
  - D5/S3/Topology/Resolution
license: project-original
triage: anchor
---

# Relative metrizable-kernel resolution

Let B be compact Hausdorff and totally disconnected, T compact Hausdorff,
and K compact metric. Suppose p:T→B is continuous, open and onto, u:T→K
is continuous, and t↦(p(t),u(t)) is a topological embedding. The theorem
exists_relative_open_resolution constructs compact Hausdorff totally
disconnected Z and continuous onto r:Z→T, with p after r open and onto.
The same constructed Z is metrizable if B is metrizable. The carrier
universes are independent, and compatible empty carriers are included.

This is a relative hypothesis. B need not be metrizable, first countable
or second countable, and T is not replaced by a metric space. The closed
image in B×K has literal closed fibers; their open hitting sets follow
from openness of p. The prescribed-point selection theorem in
CompactZeroDimensional provides the global fiber selectors. Its classical
Michael attribution and inspected Valov source are recorded in
valov2008milyutinmaps.md. No original theorem number beyond that inspected
source, and no new mathematical-priority claim, is made here.
The anchor URL locates that unchanged selection supplier at an immutable
source revision; it does not identify a published relative-resolution article.

Finite distance-open covers of all T produce global fiber nets at every
scale. Clopen interpolation between two distance bands gives serial
base-dependent transitions and paths approximating every prescribed
fiber point. Their actual closed path subtype in B×∏n Fin(N(n)) supports
a uniform limit of continuous evaluation maps. The inverse embedding-range
homeomorphism returns that limit to the original T. The tail bound is
5(1/2)^n; together with the target net error it proves surjectivity.

The exact image of an open-base finite-prefix cylinder is the base-open
set intersected with its finitely many transition sets. Seriality extends
the specified final vertex at the same base. The product and subtype
cylinder bases convert this equality to openness of arbitrary open
images. Ambient product-projection openness alone would not justify
the projection restricted to a closed subtype.

Only the optional metrizability clause installs PiNat.metricSpace on the
dependent countable discrete product. The finite-index product instances
of Topology/Metrizable/Basic do not apply to this Nat product. Empty finite
covers and empty function carriers remain valid throughout the construction.

The ordinary relative construction is a project synthesis, formalized
using the selection result and pinned Mathlib APIs. This note is source
scope and mathematical exposition, not a literature-exhaustiveness claim.
The theorem does not settle unrestricted nonmetric open-map resolution
or Peng Questions 5.1 and 5.2.
