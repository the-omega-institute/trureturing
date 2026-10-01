---
bibkey: frenzymath2026poincarelibrary
authors: FrenzyMath and upstream contributors
year: 2026
title: Poincare-Conjecture library prerequisites for hyperbolic rigidity
doi: null
url: https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a
claim: Generic smooth gluing, metric pullback, covering completeness, curvature transport and coordinate volume provide prerequisites for a Mostow-Prasad formalization; the Poincare endpoints do not supply hyperbolic rigidity.
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
| `Geometry/RicciFlow/Local/Connection/Existence.lean` | `PoincareMT.exists_leviCivitaData` | Constructs Levi-Civita data for a supplied smooth metric on a Hausdorff, second-countable manifold. |
| `Geometry/RicciFlow/Curvature/Calculus/Fields/CurvaturePointwise.lean` | `PoincareMT.RicciFlowAnalysis.curvatureOnFields_eq_curvature` | Identifies the connection commutator on smooth vector fields with retained pointwise curvature on an open neighborhood; it supplies extension independence, not the value of curvature. |
| `Geometry/Riemannian/Curvature/LocalIsometrySectional.lean` | `PoincareMT.LeviCivitaData.sectionalCurvature_eq_of_local_isometry` | Transports sectional curvature on an open set for a smooth map preserving tangent inner products, given both Levi-Civita data; no separate invertible-differential premise is required, and it does not compute the source curvature. |
| `Geometry/Riemannian/Curvature/LocalIsometry.lean` | `PoincareMT.LeviCivitaData.curvatureTensor_eq_of_local_isometry` | A smooth map preserving tangent inner products on an open set transports the four-covariant curvature tensor; it needs the two metrics and Levi-Civita data. |
| `Geometry/Riemannian/Curvature/LocalIsometry.lean` | `PoincareMT.LeviCivitaData.curvatureTensorNorm_eq_of_local_isometry` | Transports the retained Hilbert-Schmidt curvature norm under the same hypotheses. |
| `Geometry/Riemannian/Metric/Induced/Immersion.lean` | `PoincareMT.RiemannianMetric.Induced.pullbackMetric` | Constructs a smooth positive-definite metric by pulling back through a smooth immersion; injectivity of each differential is required. |
| `Geometry/RicciFlow/Surgery/Metric/Construction/MetricCombination.lean` | `PoincareMT.MetricSurgery.positiveScaling` | Multiplies a smooth metric by a supplied smooth, strictly positive function. |
| `Geometry/Riemannian/Metric/Induced/Complete.lean` | `PoincareMT.RiemannianMetric.pathELength_map_of_metric_pullback` | Preserves the length of a continuously differentiable curve under a smooth map preserving tangent inner products. |
| `Geometry/Riemannian/Metric/Induced/Complete.lean` | `PoincareMT.RiemannianMetric.edist_map_le_of_metric_pullback` | A smooth map preserving tangent inner products contracts the induced path distance; an inverse with the same properties gives distance equality. |
| `Geometry/Riemannian/Metric/Gluing/Descent.lean` | `Poincare.Gluing.exists_unique_metric_of_covering_local_diffeomorphisms` | Descends metrics through a family of local diffeomorphisms covering the target, provided equal projected tangent vectors have equal source inner products; the target smooth structure is input. |
| `Geometry/Riemannian/Measure/Basic.lean` | `PoincareMT.RiemannianMetric.volumeMeasure` | Defines intrinsic volume as normalized Hausdorff measure for the specified metric's induced Riemannian distance. |
| `Geometry/Riemannian/Measure/Density.lean` | `PoincareMT.RiemannianMetric.pullbackVolumeDensity` | Defines coordinate density as the square root of the Gram determinant of the parametrization differential in the same metric. |
| `Geometry/Riemannian/Measure/HausdorffDensity.lean` | `PoincareMT.RiemannianMetric.volumeMeasure_image_eq_lintegral_pullbackVolumeDensity` | Computes the volume of a smooth coordinate image as the Lebesgue integral of this density, for a measurable subset of the parametrization source and a smooth inverse. |
| `Geometry/Riemannian/Measure/LocalFinite.lean` | `PoincareMT.RiemannianMetric.volumeMeasure_lt_top_of_isCompact` | Compact subsets have finite intrinsic volume for a smooth Riemannian manifold with Borel measurable structure and `T3Space`; completeness and curvature are not required. |

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
modules are not included in the 47-module count above. The Levi-Civita existence and sectional-curvature transport closures were
also checked separately. Five additional external modules compiled unchanged:
`RicciFlow/Local/Connection/{Koszul,Coordinates,Construction,Existence}` and
`Riemannian/Curvature/LocalIsometrySectional`. Both cited declarations have
recursive axiom closures consisting only of the same three standard axioms.
These modules are outside the 47-module count. The extension-independence
closure was checked separately: 13 external modules, 76,771 bytes excluding
Mathlib, with unchanged sources; ten required new compilation and three reused
source-identical cached modules. Its cited declaration has the same three
standard axioms. This separate closure count is not added to the union above.
The volume definition closure was checked separately: two external modules,
3,780 bytes, with one newly compiled and one source-identical cached module.
The coordinate-volume closure comprises 14 external modules, 76,343 bytes;
eleven newly compiled and three reused source-identical cached modules.
All copied sources are unchanged, and the cited coordinate image integral
theorem has the same three standard axioms. These separate counts are not
added to the 47-module union above.
This establishes source
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

For that same descended metric, its Riemannian extended distance equals
`ENNReal.ofReal` of the actual orbit distance for every pair of quotient
points. Metric contraction bounds it above by the source distance to every
translate of an endpoint, hence by their infimum. For the reverse bound,
Mathlib supplies a globally continuously differentiable curve of length
arbitrarily close to the quotient path distance. The orbit covering lifts
it continuously from the real line; smooth local inverse germs make that
lift continuously differentiable. Preservation of tangent inner products
preserves its length, and the source distance identity bounds the orbit
infimum by that lifted length.

The canonical orbit metric retains the existing quotient topology and is
proper because the hyperbolic source is proper. The distance identity makes
its uniform structure equal to the one induced by this same descended
Riemannian metric, giving `MetricComplete` downstairs. These conclusions
hold under the same freeness and compact-set proper-discontinuity
hypotheses, without compactness or finite-volume assumptions on the quotient.

Levi-Civita data exist for this same constructed source metric and each
same descended quotient metric. The source is second-countable in its
original topology through the coordinate homeomorphism. The quotient is
second-countable because its actual orbit covering is open and surjective;
the canonical orbit metric supplies the Hausdorff property while retaining
the existing quotient topology. The existence theorem above therefore
applies without a countability assumption on the acting group.

For every Levi-Civita datum of this source metric, the connection on constant
coordinate vector fields has also been checked explicitly. Write h for
positive height and e for the image under the same orthonormal coordinate
map of the vertical unit vector. With Euclidean inner products in these
coordinates, the formula is
`nabla_u v = h^(-1) (inner(u,v) e - inner(e,u) v - inner(e,v) u)`.
The constant fields are smooth pullbacks of Euclidean constant fields and
have zero Lie bracket. Differentiating the metric pairing
`h^(-2) inner(v,w)` and applying Koszul gives this formula for the actual
connection; the formula is derived, rather than supplied as a premise.
The check retains all earlier source and quotient distance and completeness
clauses in the same construction.

For every Levi-Civita datum of that same source metric, the retained pointwise
curvature has now been computed as
`R(u,v)w = g(u,w) v - g(v,w) u`.
The calculation differentiates inverse height, applies the scalar Leibniz
rule to the connection formula, and uses the zero brackets of the constant
fields. The extension-independence theorem above identifies this field
calculation with the retained pointwise curvature. In the upstream tensor
convention, the sectional numerator is the negative Gram determinant, so
sectional curvature is minus one whenever that determinant is nonzero.
At zero Gram determinant the totalized sectional curvature is zero.

Every Levi-Civita datum of each same descended quotient metric also has
sectional curvature minus one on nondegenerate planes. Surjectivity of the
actual orbit covering selects a source point, and the invertible projection
differential lifts any two target tangent vectors. Preservation of tangent
inner products preserves their Gram determinant; sectional-curvature
transport then gives the quotient value. The combined check constructs the
source and quotient metrics and Levi-Civita data while retaining all earlier
distance, completeness, local-diffeomorphism and metric-uniqueness clauses.
It assumes neither source curvature nor a supplied quotient metric, and
metric uniqueness remains within the chosen smooth quotient structure.

Canonical Borel measurable structures are chosen for the source and each
actual orbit quotient. For the same constructed source metric, its intrinsic
volume equals normalized three-dimensional Hausdorff measure for the
original hyperbolic distance, and every isometry of that distance preserves
volume on every set. For the same descended quotient metric, its intrinsic
volume equals normalized Hausdorff measure for the canonical orbit distance.
The already established all-pair distance identities identify the metrics
used by these volume definitions; neither volume identity is assumed.

At every source point there is a positive-radius ball on which the actual
orbit projection is isometric and preserves the volume of every subset.
No measurability premise is needed for this local image equality: it uses
the measure's outer evaluation on arbitrary sets. This does not assert that
the projection preserves volumes of sets extending beyond such a ball.

In the same chosen source chart, the inverse parametrization has identity
differential on the chart target. The forward differential is identity,
and the chart inverse chain rule gives the inverse differential. Thus the
pullback Gram matrix of this same metric is $h^{-2}I_3$, its determinant is
$h^{-6}$, and its positive square root is $h^{-3}$, where $h$ is the positive
height of the parametrized point. For every measurable coordinate subset
$S$ contained in that chart target, the same source metric's volume of the
inverse-chart image is the Lebesgue integral over $S$ of this density.
The coordinate-volume theorem above supplies the integral identity after
smoothness of the chart and its inverse is checked. This relates hyperbolic
Hausdorff volume to Euclidean coordinate volume with the derived weight;
it supplies no finite total volume conclusion. All earlier source and
quotient distance, completeness, curvature and chosen-structure metric
uniqueness clauses remain in the combined construction.

For the same source and quotient metrics, a further checked application
shows that the global orbit projection contracts outer volume:
$\operatorname{vol}_{g_Q}(q(A)) \le \operatorname{vol}_{g}(A)$ for every
source subset $A$. Its canonical orbit distance is bounded by source distance
using the identity group element in the orbit infimum, so the projection is
1-Lipschitz. The Hausdorff image inequality and the previously established
volume identities give the result. No measurability or injectivity premise
on $A$ is required for this outer evaluation.

Consequently, if a source region $A$ has finite volume and $q(A)$ is the
whole quotient, then this same descended metric has finite total volume.
This is a conditional criterion: a finite-volume covering region is still
to be constructed for the actions relevant to rigidity. Freeness and
compact-set proper discontinuity alone do not supply such a region.
The criterion retains the previous construction, local volume equality,
coordinate-density, completeness and curvature clauses, with metric
uniqueness confined to the chosen quotient smooth structure.

For this same constructed source metric, let $K$ be a measurable horizontal
subset of $\mathbb{C}$ and let $H>0$. The source region with horizontal
coordinate in $K$ and height greater than $H$ has volume
$\operatorname{area}(K)/(2H^2)$, with the equality interpreted in the
extended nonnegative reals. The argument identifies the inverse-chart image
with this actual coordinate region, uses the same orthonormal map and the
measure-preserving `WithLp` product coordinates, and integrates the derived
height density $h^{-3}$. Finite horizontal area therefore gives finite source
tail volume. This does not identify a cusp quotient or provide a region
covering an entire quotient; cusp geometry and core coverage remain open.

For the same constructed source and descended quotient metrics, suppose a
compact quotient subset $C$ together with finitely many projected source
tails $q(T(K_i,H_i))$ covers the whole quotient, where every $K_i$ is
measurable with finite horizontal area and every $H_i>0$. Then
$\operatorname{vol}_{g_Q}(Q)\le
\operatorname{vol}_{g_Q}(C)+\sum_i\operatorname{area}(K_i)/(2H_i^2)<\infty$.
The cited compact-volume theorem makes the core contribution finite;
projection contraction, the same-source tail formula and finite
subadditivity bound the remaining contributions. Neither disjointness,
projection injectivity nor measurability of the projected tails is needed.
The empty tail family includes the compact case. The check supplies this
conditional estimate within the same metric construction and chosen smooth
quotient structure; it does not construct the core, classify cusps or prove
the covering condition. No orientability premise is introduced; the
noncompact and nonorientable rigidity cases remain in scope.

These checks compiled under the project pins using the unchanged cited
external sources and only `propext`, `Classical.choice` and `Quot.sound`.
They are temporary applications of existing results; no new named project
declaration or external dependency is installed by this note.

Finite covolume,
noncompact cusp analysis, and the global Mostow-Prasad existence and
uniqueness argument remain separate obligations. Compact positive-curvature
sphere covering results cannot replace them.

## Verified locator

- Stable source: https://github.com/frenzymath/Poincare-Conjecture/tree/432c38f2aa5a30efb13871292d17b4a3309a496a
- Endpoint statements: `PoincareConjecture/PoincareLib/Topology/Manifold/Poincare/Statement.lean`, definitions `SmoothPoincare` and `TopologicalPoincare`.
- Endpoint supplier and audit: `PoincareConjecture/PoincareLib/Topology/Manifold/Poincare.lean` and `PoincareConjecture/scripts/check_poincare_endpoints.lean`.
- Generic prerequisites: the exact module paths and declaration names in the table above.
- Verification claims: `PoincareConjecture/verification.md`; complete upstream proof checks are reported there and were not reproduced here.

## Negative curvature and finite-radius exponential geometry

The unchanged `SpaceForm/Curvature.lean` radial curvature formula supports
arbitrary constant sectional curvature, and
`Connection/AlongCurve/Manifold.lean` constructs isometric parallel transport
from the smooth metric. `SpaceForm/ParallelJacobi.lean`,
`SpaceForm/GeodesicJacobi.lean` and `SpaceForm/ExponentialMetric.lean` give
positive-curvature sine formulas; their conclusions are not negative-curvature
formulas. `Analysis/ODE/Jacobi/Basic.lean` and `Analysis/ODE/Linear.lean`
supply the Jacobi predicate and linear ODE uniqueness used for the adaptation.

A transient negative-curvature application checks the following for any
complete smooth Riemannian manifold with a `T3Space` topology and supplied
Levi-Civita data of constant sectional curvature `-1`. For each point `p` and
each finite `R > 0`, the precompact-ball exponential constructor selects an
actual smooth normalized radial geodesic map `e` on the Euclidean ball of
radius `R`, with `e(0) = p`. Writing `De` for its manifold differential, for
`inner(θ,θ) = 1` and `0 ≤ t < R` the same selected map satisfies

```text
t² g[e(tθ)](De[tθ]w, De[tθ]z)
  = sinh(t)² inner(w,z)
    + (t² - sinh(t)²) inner(w,θ) inner(z,θ).
```

The application constructs parallel transport and derives the normal Jacobi
`sinh/cosh` formulas by linear ODE uniqueness; it supplies the compact intrinsic
ball input from metric completeness. These scoped applications compile with
only `propext`, `Classical.choice` and `Quot.sound`. They require no global
compactness, orientability or finite-volume hypothesis. The selected `e` may
depend on `R`: compatibility between radii, global injectivity or surjectivity,
abstract hyperbolic-manifold realization, cusp classification and full
Mostow-Prasad rigidity have not been established. The same finite-radius
exponential conclusion is also checked for the previously constructed
upper-half-space metric `g` and for its unique descended metric `gQ`, under the
same free, compact-set proper isometric-action hypotheses. Their already
constructed Levi-Civita data, completeness and curvature `-1` discharge the
application inputs; no replacement metric or supplied exponential is used.
All prior source, volume and quotient clauses are retained, with metric
uniqueness still within the chosen smooth quotient structure. These are
classical prerequisite applications, with no novelty claim.
