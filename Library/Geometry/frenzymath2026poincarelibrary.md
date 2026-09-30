---
bibkey: frenzymath2026poincarelibrary
authors: FrenzyMath and upstream contributors
year: 2026
title: Poincare-Conjecture library prerequisites for hyperbolic rigidity
doi: null
url: https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a
claim: Generic smooth gluing, metric pullback, covering completeness and curvature transport provide prerequisites for a Mostow-Prasad formalization; the Poincare endpoints do not supply hyperbolic rigidity.
strata_touched:
  - D5/S3/Geometry/MostowPrasadCovering
  - D5/S3/Geometry/IsometricOrbitMetric
license: citation-only; upstream code is Apache-2.0 with NOTICE attribution
triage: anchor
---

<!-- GID: D5/L/Geometry/frenzymath2026poincarelibrary -->
# Reusable geometry from the Poincare library

All source locators below are relative to `PoincareConjecture/` at the
revision in the stable URL. The repository imports work from multiple
upstream authors; `IMPORT.md`, `MODIFICATIONS.md`, the root `LICENSE` and
`NOTICE` provide provenance and licensing. This note cites the sources and
does not vendor code or assert mathematical novelty.

## Endpoint and verification boundary

`PoincareLib/Topology/Manifold/Poincare/Statement.lean` defines two endpoints.
The smooth endpoint is quantified over compact, Hausdorff, second-countable,
simply connected smooth three-manifolds and concludes a diffeomorphism to
`ThreeSphere`. The topological endpoint omits the smooth manifold premise
and concludes a homeomorphism. Both use Mathlib's three-dimensional charted
space and simple connectedness predicates.

`PoincareLib/Topology/Manifold/Poincare.lean` supplies the two endpoint proof
terms, without a predecessor-package argument. `scripts/check_poincare_endpoints.lean`
checks their full recursive axiom closures against `propext`,
`Classical.choice` and `Quot.sound` at every carrier universe. The source's
`verification.md` records endpoint build checks at `516badd1` and comparator
checks at `1876d7dc2c85325a3f62ce9776af98f910c5db04`.
Those are upstream-reported checks; the full endpoint build and comparator
verification have not been independently reproduced in this project.

Poincare classifies the simply connected closed three-manifold. The active
Mostow-Prasad target concerns homotopy equivalences of connected, complete,
finite-volume hyperbolic three-manifolds, including noncompact cusped ones,
and concludes a unique isometry in each homotopy class. The endpoint above
does not supply that existence or uniqueness theorem.

## Generic prerequisites and their direction

| Source module | Declaration | Scope and remaining input |
| --- | --- | --- |
| `Geometry/Manifold/Gluing/Smooth.lean` | `Poincare.Gluing.quotient_isManifold` | Builds a smooth quotient from open pieces and a supplied smooth overlap system; the orbit-specific overlap system must still be constructed. |
| `Geometry/Manifold/Gluing/Smooth.lean` | `Poincare.Gluing.include_isLocalDiffeomorph` | Piece inclusion is a local diffeomorphism for that gluing; it does not identify the gluing quotient with our orbit quotient. |
| `Geometry/Riemannian/Metric/LocalDiffeomorph.lean` | `PoincareMT.RiemannianMetric.pullbackOfLocalDiffeomorph` | Pulls a smooth positive-definite metric from the target to the source, using the invertible differential; no spatial bijectivity or compactness is required. |
| `Geometry/Riemannian/Covering/Completeness.lean` | `PoincareMT.RiemannianMetric.metricComplete_of_isCoveringMap` | A smooth covering preserving tangent inner products pulls completeness from the base to the covering space, with arbitrary sheet count; it does not prove completeness downstairs from completeness upstairs. |
| `Geometry/Riemannian/Covering/Completeness.lean` | `PoincareMT.RiemannianMetric.metricComplete_pullbackOfLocalDiffeomorph` | The same upward completeness transfer for the actual local-diffeomorphism pullback metric. |
| `Geometry/Riemannian/Curvature/LocalIsometry.lean` | `PoincareMT.LeviCivitaData.curvatureTensor_eq_of_local_isometry` | A smooth map preserving tangent inner products on an open set transports the four-covariant curvature tensor; it needs the two metrics and Levi-Civita data. |
| `Geometry/Riemannian/Curvature/LocalIsometry.lean` | `PoincareMT.LeviCivitaData.curvatureTensorNorm_eq_of_local_isometry` | Transports the retained Hilbert-Schmidt curvature norm under the same hypotheses. |
| `Geometry/Riemannian/Metric/Induced/Immersion.lean` | `PoincareMT.RiemannianMetric.Induced.pullbackMetric` | Constructs a smooth positive-definite metric by pulling back through a smooth immersion; injectivity of each differential is required. |
| `Geometry/RicciFlow/Surgery/Metric/Construction/MetricCombination.lean` | `PoincareMT.MetricSurgery.positiveScaling` | Multiplies a smooth metric by a supplied smooth, strictly positive function. |
| `Geometry/Riemannian/Metric/Induced/Complete.lean` | `PoincareMT.RiemannianMetric.edist_map_le_of_metric_pullback` | A smooth map preserving tangent inner products contracts the induced path distance; an inverse with the same properties gives distance equality. |
| `Geometry/Riemannian/Metric/Gluing/Descent.lean` | `Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms` | Descends metrics through a family of local diffeomorphisms covering the target, provided equal projected tangent vectors have equal source inner products; the target smooth structure is input. |

The `Geometry/` paths in this table have the prefix `PoincareLib/`.
`MetricComplete` means completeness of the emetric obtained from the specified
Riemannian metric by the infimum of path lengths. It is defined in
`Geometry/RicciFlow/Harnack/Basic.lean`; its location explains why that
module appears in the small completeness dependency closure.

## Compatibility result

The external project pins Lean 4.33.1 and Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. Our compatibility experiment uses
Lean 4.33.0 and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
The covering-completeness closure comprises 14 external source modules,
65,144 bytes excluding Mathlib. All compiled unchanged under our pins.
The union with the curvature-local-isometry and smooth-gluing closures
comprises 47 external source modules, 280,402 bytes excluding Mathlib.
All compiled unchanged under the same pins. The seven smooth-gluing, covering-completeness and curvature-transport
declarations in the table have recursive axiom closures consisting only of
`propext`, `Classical.choice` and `Quot.sound`.
The additional immersion, positive-scaling, metric-contraction and metric-descent
APIs were checked in separate unchanged-source compatibility closures. Their
modules are not included in the 47-module count above. This establishes source
compatibility for the checked closures, not installation of an external
dependency or independent verification of the complete Poincare proof.

## Connection to the hyperbolic model and orbit quotient

The project supplies an isometric representation's orbit covering under
freeness, compact-set proper discontinuity and local compactness, and an
orbit metric inducing the quotient topology under compact-set proper
discontinuity. Proper ambient spaces additionally give proper orbit
quotients. These prerequisites do not assert finite covolume or curvature.

For a locally compact metric ambient space, freeness and compact-set proper
discontinuity give a radius at every point on which the orbit projection
preserves distance. This application was checked transiently. A disjoint
neighborhood contains a ball of radius epsilon, so every nonidentity
translate moves its center by at least epsilon. On the ball of radius
epsilon/4, the triangle inequality makes each nonidentity translate at least
as distant as the identity. The orbit infimum therefore gives the original
distance. Ambient properness is unnecessary for this estimate. Kapovich's
classical Lemma 21(3), cited in `kapovich2023properactions.md`, instead assumes
metric properness and freeness. Its metric-proper-action hypothesis is
distinct from the compact-set condition used here.

Pinned Mathlib's `Geometry/Manifold/Instances/Quotient.lean` supplies a
charted space for a free properly discontinuous action and leaves smooth
manifold structure and smoothness of the projection as TODOs. A transient
construction using covering branches and smooth deck transformations
supplies a smooth structure on the actual project orbit quotient in its
existing quotient topology, with a locally diffeomorphic projection. Given
a smooth source metric and deck transformations preserving its tangent
inner products, the external metric descent theorem then supplies the
unique quotient metric preserving projection differentials. The concrete
hyperbolic source construction below supplies the required smoothness
and tangent-metric invariance for its isometric deck maps.

A separate transient check connects the source metrics. On the existing
`HyperbolicThreeSpace`, choose an orthonormal identification of its ambient
coordinates with `EuclideanSpace` on `Fin 3`, use the positive-height open
coordinate chart, pull back the Euclidean metric, and scale it by the inverse
square of height. In this same chart the resulting smooth metric has inner
product equal to the Euclidean inner product divided by height squared.
Horizontal translations and the project's inversion are smooth and preserve
these tangent inner products. For every globally continuously differentiable
curve its length on an ordered closed parameter interval is the nonnegative
integral of Euclidean coordinate speed divided by height.

For arbitrary source endpoints, the induced Riemannian extended distance
equals `ENNReal.ofReal` of the project's existing `hyperbolicDist`. Equal
horizontal coordinates reduce to exponential vertical curves and the
log-height lower bound. For unequal horizontal coordinates, a real quadratic
root chooses a horizontal translation after which inversion makes the two
horizontal coordinates equal. Applying the metric contraction theorem to
these maps and their inverses transports the vertical distance equality.
This derives the distance identity without assuming it. Existing
hyperbolic completeness consequently gives `MetricComplete` for this
same constructed source metric.

Every isometric self-equivalence of the model's original hyperbolic distance
is smooth in this same chart and preserves this metric on tangent vectors.
Four fixed target anchors recover reciprocal height and the two horizontal
coordinates from cosh distances. Pulling the anchors back by the inverse
isometry expresses those coordinates using smooth squared coordinate
norms divided by positive heights, including at coincident anchor points.
This proves smoothness without a regularity premise. The cosh-distance
identity then gives an equality between squared coordinate differences
and endpoint heights. Along short coordinate lines, the punctured slope
limit yields the differential norm identity; polarization gives preservation
of the metric's tangent inner products. This check uses the same source
chart and metric as the distance and completeness checks above.

For every group acting by isometries of that original hyperbolic distance,
freeness and compact-set proper discontinuity now give a smooth structure
on the actual project `OrbitQuotient` with its existing quotient topology.
The canonical orbit projection is a smooth local diffeomorphism. In that
constructed smooth structure there is a unique Riemannian metric whose
inner products pull back to the same concrete source metric through the
projection differential. The check applies the smooth covering-branch and
metric-descent constructions above, using the verified arbitrary-isometry
smoothness and invariance rather than assuming them. No finite group,
cocompactness or finite-volume premise is used for this construction.

These checks compiled under the project pins using the unchanged cited
external sources and only `propext`, `Classical.choice` and `Quot.sound`.
They are temporary applications of existing results; no new named project
declaration or external dependency is installed by this note.

The remaining bridge needs equality of the descended Riemannian path
distance with the actual orbit metric and completeness downstairs. The model's curvature of minus one and its Levi-Civita data must
also be supplied before applying curvature transport. Finite covolume,
noncompact cusp analysis, and the global Mostow-Prasad existence and
uniqueness argument remain separate obligations. Compact positive-curvature
sphere covering results cannot replace them.

## Verified locator

- Stable source: https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a
- Endpoint statements: `PoincareConjecture/PoincareLib/Topology/Manifold/Poincare/Statement.lean`, definitions `SmoothPoincare` and `TopologicalPoincare`.
- Endpoint supplier and audit: `PoincareConjecture/PoincareLib/Topology/Manifold/Poincare.lean` and `PoincareConjecture/scripts/check_poincare_endpoints.lean`.
- Generic prerequisites: the exact module paths and declaration names in the table above.
- Verification claims: `PoincareConjecture/verification.md`; complete upstream proof checks are reported there and were not reproduced here.
