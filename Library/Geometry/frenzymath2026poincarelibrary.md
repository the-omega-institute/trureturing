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
compactness, orientability or finite-volume hypothesis. This finite-radius constructor selects `e` separately for each `R`. The
global construction below uses one initial frame and one map over all radii.
These finite-radius clauses alone do not establish global injectivity or
abstract hyperbolic-manifold realization. The following sections supply the
global covering, H3 inverse and isometric target realization. Cusp
classification and full Mostow-Prasad rigidity remain separate obligations. The same finite-radius
exponential conclusion is also checked for the previously constructed
upper-half-space metric `g` and for its unique descended metric `gQ`, under the
same free, compact-set proper isometric-action hypotheses. Their already
constructed Levi-Civita data, completeness and curvature `-1` discharge the
application inputs; no replacement metric or supplied exponential is used.
All prior source, volume and quotient clauses are retained, with metric
uniqueness still within the chosen smooth quotient structure. These are
classical prerequisite applications, with no novelty claim.

## Global normalized exponentials and surjectivity

`Geodesic/Complete.lean` supplies global geodesics for every initial coordinate
velocity. `Coordinates/Exponential/SmoothExtension.lean` supplies smooth
endpoint dependence without requiring smoothness of a chosen geodesic family;
`EndpointAgreement.lean` identifies the zero endpoint and its derivative.
Together with one orthonormal coordinate frame and `RadialCurve.lean`, these
results construct one globally smooth normalized map `e` at each base point of
any complete smooth Riemannian manifold with `T3Space` topology. Every radial
curve is a geodesic on all of `ℝ`. The map is fixed over the whole tangent
space; it is not selected again when a radius changes.

When the manifold is also preconnected, the same selected `e` is surjective.
`Comparison/Laplacian/Branch/Complete.lean` supplies a minimizing geodesic
from the base point to any target point. The inverse initial frame specifies
a velocity for `e`, and `Coordinates/Exponential/Uniqueness.lean` identifies
the radial curve with that geodesic by their initial position and coordinate
velocity. This surjectivity application requires no curvature hypothesis.

With supplied Levi-Civita data of constant sectional curvature `-1`, the
same global `e` has a bijective manifold differential at every tangent-space
point and satisfies the negative polar metric formula above for every unit
`θ` and every `t ≥ 0`. The finite-radius formula is applied with `R = t + 1`
and differential nonsingularity with `R = ‖x‖ + 1`; neither application changes
`e`. The estimate `sinh(t) ≥ t` and Cauchy-Schwarz give the positivity used for
nonsingularity. These constructions require no global compactness,
orientability or finite-volume premise.

The combined global surjectivity, nonsingularity and metric formula are also
checked for the same constructed upper-half-space metric `g` and its unique
descended metric `gQ` under the original free, compact-set proper isometric
group-action hypotheses. Source connectedness follows from the coordinate
homeomorphism to the convex positive-height region, and quotient connectedness
from the existing quotient topology. All earlier source, curvature,
completeness, volume, conditional core/tail bound and quotient clauses remain
in the application; metric uniqueness is still within the chosen smooth
quotient structure. Smooth local tangent-metric isometries through arbitrary
prescribed source and quotient points are checked in the same construction.

These scoped classical applications compile under the unchanged project pins
and cited external revision with only `propext`, `Classical.choice` and
`Quot.sound`. They are temporary applications, with no retained named project
Lean declaration, new dependency or novelty claim. Surjectivity and a
bijective differential alone do not establish covering-map structure; the
checked covering construction is given below. The following sections also
supply arbitrary-target realization as a hyperbolic isometric quotient.
Cusp classification and full Mostow-Prasad existence and uniqueness remain
unfinished. The noncompact and
nonorientable cases remain part of the rigidity target.


## Complete pullback of the same global negative exponential

The everywhere bijective differential and global smoothness of the same `e`
provide local smooth inverse branches through
`Comparison/Injectivity/LocalInverse.lean`. Packaging those branches gives
`IsLocalDiffeomorph e`. `Metric/LocalDiffeomorph.lean` then supplies the actual
smooth differential pullback `gE = g.pullbackOfLocalDiffeomorph e hlocal`;
its tangent inner product is exactly the target inner product of the two
images under `mfderiv e`.

For every tangent-space point `x` and vector `w`, the negative polar identity
implies `inner w w ≤ gE.inner x w w`. At `x = 0` this is the normalized
initial-frame identity. Away from zero, write `x = ‖x‖ • θ` with `θ` unit;
`sinh(‖x‖) ≥ ‖x‖` and Cauchy-Schwarz show that the angular correction is
nonnegative. This estimate applies over the entire tangent space.

`Distance/TangentBound.lean`, specifically
`RiemannianMetric.edist_le_mul_of_inner_mfderiv_le`, applied to the identity
map and the Euclidean metric from
`Comparison/Injectivity/PullbackGeodesics.lean`, gives Euclidean extended
distance at most `gE.edist`. A sequence Cauchy for the intrinsic pullback
distance is therefore Euclidean Cauchy and has a Euclidean limit. The smooth
intrinsic metric has the original topology, so that same limit establishes
`MetricComplete gE`. The check keeps the source and target uniform-space
instances explicit during the Cauchy transfer.

The combined application retains the same selected `e`, its surjectivity,
normalization, radial geodesics at every real time, everywhere bijective
differential and negative polar identity for all `t ≥ 0`. Its actual
pullback completeness and Euclidean inner lower bound are checked for the
same constructed `g` and descended `gQ`; all preceding source, volume,
curvature, conditional core/tail and quotient clauses remain. The original
free, compact-set proper isometric-action hypotheses and uniqueness within
the chosen smooth quotient structure are retained. No compactness,
orientability or finite-volume premise is added.

These are scoped transient classical applications under the unchanged pins,
with only `propext`, `Classical.choice` and `Quot.sound`. This increment does
not by itself establish that `e` is a covering map or injective. The next
section supplies the covering construction; the later target-distance
comparison supplies arbitrary-manifold isometric quotient realization.
Full Mostow-Prasad rigidity, including cusps and nonorientable manifolds,
remains unfinished.


## Covering structure of the same global negative exponential

The next checked composition establishes `IsCoveringMap e` for the same
selected global exponential and its complete actual pullback metric. The
source map is retained throughout; its normalization, radial geodesics at
all real times, surjectivity, everywhere bijective differential, full
negative polar identity and Euclidean inner lower bound remain.

The generic covering check uses a complete smooth Riemannian metric on
Euclidean space and a smooth map preserving its actual tangent inner
products into a complete, preconnected smooth manifold of sectional
curvature `-1`. No covering, source compactness, finite fiber count,
orientability or finite-volume hypothesis is assumed.

`SpaceForm/LocalIsometry/Geodesic.lean` transports affine geodesics through
local metric isometries. Global source geodesics and initial-data uniqueness
lift target geodesics. Smooth endpoint dependence supplies, for every target
point `y`, one fixed global target exponential `eY` and smooth maps `Sx` for
every source fiber point `x`, with `Sx 0 = x` and `F ∘ Sx = eY`. The same `eY`
is used for all points in the fiber. Differentiating that identity shows
that each `Sx` is a local diffeomorphism and hence an open map.

Choose one inverse branch of `eY` near zero. Its open source `U` maps to one
open target neighborhood `V`, shared by all the source sheets `Sx '' U`.
Injectivity of `eY` on `U` and uniqueness of continuous lifts through a
locally injective separated map make those sheets pairwise disjoint. To
cover the entire preimage of `V`, lift a reversed target radial geodesic
from any source point over `V` back to a point over `y`; lift uniqueness
identifies the original point with its sheet endpoint. Each sheet maps
homeomorphically onto `V`. Mathlib's `IsOpen.trivializationDiscrete` and
`IsEvenlyCovered.of_trivialization` then provide the actual covering
structure, including fibers with infinitely many points.

The complete construction is checked for the same actually constructed
upper-half-space metric `g` and descended quotient metric `gQ`, retaining
all earlier source, curvature, completeness, volume, conditional core/tail,
quotient and local tangent-isometry clauses. The original free, compact-set
proper isometric-action conditions are retained; quotient metric uniqueness
is within the chosen smooth structure. These scoped transient classical
applications compile with only `propext`, `Classical.choice` and `Quot.sound`.

This covering increment alone does not establish global injectivity or an
inverse on hyperbolic three-space; the next section supplies the H3 inverse.
The later target-distance comparison supplies isometric quotient
realization under its explicit target metric and topology conditions.
Cusp classification and full Mostow-Prasad rigidity remain unfinished.
The full rigidity target still includes noncompact cusps and nonorientable
manifolds. No new project Lean declaration or novelty claim is retained.


## Global smooth inverse of the same H3 exponential

The project's `HyperbolicTopology.coordinatesHomeomorph` identifies the
hyperbolic topology of H3 with the usual topology of the positive-height
half-space in `Ambient ℂ`. The positive-height half-space is convex and
nonempty, so Mathlib's `Convex.contractibleSpace` and transport through that
homeomorphism give contractibility of the actual H3 type. Its simple
connectedness follows from `SimplyConnectedSpace.ofContractible`. The
selected Euclidean manifold atlas supplies local path connectedness through
`ChartedSpace.locallyPathConnectedSpace`.

The pinned upstream `PoincareLib/Topology/Covering/SimplyConnected.lean`, specifically
`Poincare.Topology.bijective_of_isCoveringMap_of_simplyConnected`, makes the
same previously checked covering exponential from Euclidean three-space
to H3 bijective. Mathlib's `IsLocalDiffeomorph.diffeomorphOfBijective` then
provides a global smooth diffeomorphism whose forward function is exactly
that chosen exponential. Its inverse is smooth everywhere. No compactness,
proper-map condition, finite-fiber condition or new simple-connectedness
premise is supplied by the user.

This is checked for the same actually constructed upper-half-space metric
`g`, retaining the chosen exponential's normalization, radial geodesics at
all real times, smoothness, surjectivity, bijective differential, complete
actual pullback, Euclidean inner lower bound and full negative polar
identity. Deleting the single added H3 diffeomorphism clause and reversing
the import and theorem names restores the preceding combined constructor
byte-for-byte. All earlier source, volume, curvature, conditional core/tail
and quotient clauses and original free, compact-set proper action
conditions are retained; quotient metric uniqueness remains within the
chosen smooth structure.

The quotient exponential retains its covering structure. Its target is
not assumed to be simply connected, and no global inverse on an arbitrary
quotient is asserted. The later target-distance comparison supplies
arbitrary-manifold isometric quotient realization. Cusp classification and
full Mostow-Prasad existence, homotopy and uniqueness remain unfinished,
including noncompact and nonorientable manifolds. These are scoped transient classical applications under
unchanged pins, with only `propext`, `Classical.choice` and `Quot.sound`;
no new project Lean declaration or novelty claim is retained.


## Global metric-preserving covering of an arbitrary negative target

For any complete, preconnected smooth three-manifold with a smooth
Riemannian metric of sectional curvature `-1` and the stated Levi-Civita
data, the next composition constructs a smooth covering from the actually
constructed H3 metric to that target. Any prescribed source and target
points can be matched. No compactness, orientability or finite-volume
hypothesis is added.

Within this covering construction, choose one normalized global H3
exponential and its global diffeomorphism witness, and one normalized global
target covering exponential. Their differential pullback inner products
agree at every Euclidean parameter. At zero this is their common initial
normalization; at a nonzero parameter, write it as its norm times a unit
vector and apply both full negative polar identities. The positive squared
norm cancels. This establishes the equality over the entire parameter
space, without a finite-radius restriction.

Compose the target exponential with the smooth inverse of the chosen H3
diffeomorphism. The derivative chain rule and the inverse differential
identity convert the pullback equality into preservation of the actual
tangent metrics at every H3 point. Covering structure follows from the
target exponential's `IsCoveringMap` by Mathlib's
`IsCoveringMap.comp_homeomorph`. The value at the chosen basepoint follows
from the two exponential normalizations. The target need not be simply
connected.

The combined check binds this statement to the same constructed H3 metric
`g` and retains all prior source, exponential, volume, curvature,
completeness, conditional core/tail and quotient clauses and the original
free, compact-set proper action conditions. Quotient metric uniqueness
remains within its selected smooth structure. Removing the one new
arbitrary-target covering clause and its application and reversing names
restores the preceding combined constructor byte-for-byte. The exponentials
used within this new covering construction are selected there; no identity
with existential exponential witnesses in separate earlier clauses is
asserted.

These scoped transient classical applications use unchanged pins and only
`propext`, `Classical.choice` and `Quot.sound`, with no new tracked project
Lean declaration or novelty claim. The preceding covering clause alone does
not include the deck-action conclusions. The following composition supplies
the faithful isometric deck action and topological quotient identification,
then the global isometric quotient-to-target realization. Finite-volume cusp
classification and covolume, and full Mostow-Prasad existence, homotopy and
uniqueness remain unfinished. Noncompact cusps and nonorientable manifolds
remain within the full rigidity target.


## Isometric deck action and topological realization of a negative target

For the same constructed H3 metric and any preconnected smooth
three-manifold with `T3Space` topology, a smooth Riemannian metric that is
`MetricComplete` and has sectional curvature `-1`, and the supplied
Levi-Civita data, a new composition supplies a surjective, smooth,
tangent-metric-preserving covering through any prescribed pair of basepoints. Its full deck group
acts freely and properly discontinuously, is represented faithfully by
isometries of the original H3 metric, and has an orbit quotient homeomorphic
to the target. The homeomorphism composed with the orbit projection is
exactly this selected covering. No target simple connectedness,
compactness, orientability or finite-volume premise is added.

For the topological part, the H3 source is simply connected and locally
path connected. Mathlib's covering lift existence and uniqueness construct
a deck homeomorphism between any two points of a fiber. Uniqueness makes
the deck action free. Path lifting over the connected target supplies
surjectivity; fibers are precisely deck orbits, giving a quotient covering.
The unchanged pinned `PoincareLib/Topology/Covering/Quotient/Properness.lean`
gives, over the Hausdorff target, finiteness of the group elements that move
one compact set to meet another. This argument has no finite-group or compact-source premise.

Positive definiteness and equal tangent dimensions make the covering's
differential bijective. Its covering branches and the pinned smooth inverse
theorem make it a local diffeomorphism. Any continuous projection-preserving
map agrees locally with a smooth inverse branch composed with the
projection, so it is smooth. Differentiating the projection identity gives
preservation of the actual source tangent metric. Applying the pinned
`edist_le_mul_of_inner_mfderiv_le` with factor one to a deck homeomorphism
and its inverse gives equality of intrinsic distances. The already checked
identity between that same H3 intrinsic distance and the original
hyperbolic distance turns each deck homeomorphism into an actual
`IsometryEquiv`; the underlying maps respect identity and composition,
giving a faithful group homomorphism. Freeness and compact-set properness
transfer along its pointwise equality with the deck action.

The orbit relation equals the covering's fiber relation. Mathlib's quotient
homeomorphism constructions therefore identify the orbit quotient with the
target and retain the projection identity. This clause is a topological
identification; the following distance comparison supplies global distance
preservation by a quotient-to-target homeomorphism selected within that
construction.

The combined check adds one arbitrary-target isometric-deck clause for the
same actual H3 metric `g`. Removing that clause and its application and
reversing names restores the preceding combined constructor byte-for-byte.
All preceding source, exponential, volume, curvature, completeness,
conditional core/tail and quotient clauses and original free, compact-set
proper action conditions are retained. The new covering is selected within
this construction; it is not identified with the witness of a separately
quantified earlier covering clause. Quotient metric uniqueness remains
within its selected smooth structure.

These are scoped transient classical applications under unchanged pins,
with only `propext`, `Classical.choice` and `Quot.sound`. No new tracked
project Lean declaration or novelty claim is retained. The following section
supplies isometric realization of an arbitrary target. Finite-volume cusp
classification and covolume, and full Mostow-Prasad existence, homotopy and
uniqueness remain unfinished,
including noncompact cusps and nonorientable manifolds. The existing escape
audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these recorded compilation checks nor prior CI closes that audit.


## Isometric quotient realization of an arbitrary negative target

For the same constructed H3 metric and a preconnected smooth
three-manifold with `T3Space` topology, a smooth Riemannian metric that is
`MetricComplete` and has sectional curvature `-1`, and supplied Levi-Civita
data, the selected deck-orbit-to-target homeomorphism now preserves the
actual target intrinsic distance. For every two quotient points, that
distance equals `ENNReal.ofReal` of the existing H3 orbit distance. The
covering, full deck group, faithful free and compact-set proper isometric
representation, homeomorphism and projection identity are chosen together
within this construction. No target simple connectedness, compactness,
orientability or finite-volume premise is added.

The distance comparison uses the existing metric pullback contraction,
Mathlib's covering lifts, the previously checked smoothness of continuous
curve lifts and the pinned path-length pullback equality. For one bound,
project a source curve and compare against every deck translate of the
second endpoint; taking the orbit-distance infimum gives the target
intrinsic-distance upper bound. For the other, choose a global `C¹` target
curve whose length is arbitrarily close to its intrinsic distance, lift it
through the actual covering from the first endpoint, and use its smoothness
and unchanged length. The lifted last point is in the second endpoint's
fiber, hence in its full deck orbit. Its source distance bounds the orbit
infimum and is bounded by the lifted length. The two inequalities give the
exact distance identity. No shortest target curve or distance equality is
assumed.

The prior quotient-to-target homeomorphism respects the selected
projection, so the pointwise fiber-distance identity descends to all
quotient points. The target intrinsic extended distance is finite for all
point pairs by this identity and surjectivity of the homeomorphism. Mathlib's
`EMetricSpace.ofRiemannianMetric` constructs this actual target intrinsic
metric with the original topology; `EMetricSpace.toMetricSpace` converts
its proved finite distances to real distances while retaining its
uniformity and topology. Together with the existing `orbitMetricSpace`,
the same homeomorphism is the underlying function of an actual
`IsometryEquiv` from the H3 orbit quotient to the target. This construction
uses the metric arising from the supplied target Riemannian metric, with
no substituted target-distance definition or supplied isometry premise.

The combined check binds the realization to the same actual H3 metric `g`
and adds one universal arbitrary-target clause. Removing that clause and
its application and reversing names restores the preceding entire
constructor byte-for-byte. All preceding source, exponential, volume,
curvature, completeness, conditional core/tail and quotient clauses and
original free, compact-set proper action conditions are retained. The new
covering and deck representation are selected within this new clause;
identity with separate earlier existential witnesses is not asserted.
Quotient metric uniqueness remains within the selected smooth structure.

These are scoped transient classical applications under unchanged pins,
with only `propext`, `Classical.choice` and `Quot.sound`, with no retained
new project Lean declaration or novelty claim. An isometric quotient
realization does not establish that a homotopy equivalence induces a lattice
isomorphism realized by an ambient conjugator. Finite-volume cusp
classification and covolume, lattice rigidity, and full Mostow-Prasad
existence, homotopy and uniqueness remain unfinished, including noncompact
cusps and nonorientable manifolds. The existing escape audit remains
unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these compilation checks nor CI closes that audit.


## Fundamental groups and the actual deck and holonomy groups

For the actual H3 quotient covering selected in the preceding realization,
Mathlib's `IsQuotientCoveringMap.fundamentalGroupEquiv` identifies the target
fundamental group at the selected basepoint with the opposite of the full
covering deck group. The source uses its already established simple
connectedness in the original H3 topology. The lifted basepoint is in the
actual fiber because the same selected covering sends it to the prescribed
target basepoint. No new simple-connectedness premise is imposed on the
target. Opposite multiplication is retained explicitly; the plain `op` or
`unop` function is not treated as a group homomorphism.

The target realization check includes this fundamental-group equivalence
for that very covering, along with its faithful free and compact-set proper
original-H3 isometric representation, projection-compatible homeomorphism
and intrinsic isometric realization. One universal target clause is added
to the constructor for the same actual H3 metric `g`. Removing that clause
and its application and reversing names/import restores the preceding whole
constructor byte-for-byte. All its earlier clauses remain. Witnesses in the
new clause are selected together; no equality with separately quantified
older covering witnesses is asserted.

For a homotopy equivalence between two target spaces, Mathlib's
`FundamentalGroupoidFunctor.equivOfHomotopyEquiv` supplies an equivalence of
fundamental groupoids. Its fully faithful functor's `mulEquivEnd` gives an
isomorphism of fundamental groups whose underlying homomorphism is exactly
`FundamentalGroup.map` for the given continuous map. Basepoint transport by
`eqToIso.conj` retains exactly `FundamentalGroup.mapOfEq` when the image
basepoint is identified with the target basepoint.

Composing this induced isomorphism with the two actual covering
fundamental-group equivalences gives an isomorphism of opposite deck
groups. Mathlib's `MulEquiv.unop` converts the whole isomorphism to one
between the actual deck groups. Its opposite commutes with the given
map's induced fundamental-group homomorphism and the two selected covering
equivalences, pointwise on every loop class. Thus the constructed group
isomorphism has the required relation to the original homotopy equivalence.
For the faithful original-H3 deck representations, `MonoidHom.ofInjective`
then transports a deck-group isomorphism to an abstract isomorphism of their
image subgroups, taking each represented deck element to the representation
of its corresponding element.

These are six scoped transient classical applications under unchanged pins,
with only `propext`, `Classical.choice` and `Quot.sound`; no new project Lean
declaration or novelty claim is retained. The image subgroup isomorphism
does not establish discreteness in the ambient isometry-group topology,
finite covolume or realization by an ambient conjugator. Finite-volume
cusp classification and covolume, lattice rigidity, and full Mostow-Prasad
existence, homotopy and uniqueness remain unfinished, including noncompact
cusps and nonorientable manifolds. The existing escape audit remains
unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these compilation checks nor CI closes that audit.


## Intrinsic volume transfer for the selected target realization

For a preconnected smooth three-manifold with `T3Space` topology, a smooth
Riemannian metric that is `MetricComplete` and has sectional curvature `-1`,
and supplied Levi-Civita data, the same actual H3 construction now also
transfers intrinsic volume through its selected isometric orbit realization.
Here `gM.volumeMeasure` and a supplied quotient metric's `gQ.volumeMeasure`
mean the pinned library's normalized three-dimensional Hausdorff measures of
their respective intrinsic extended metrics. This increment does not check
identification with coordinate volume density for the arbitrary target.

The original target and orbit topologies supply their Borel structures.
For the selected full deck representation, the existing `orbitMetricSpace`
supplies the source metric. The intrinsic-isometry clause supplies finite
pairwise target distances and an `IsometryEquiv` whose underlying function
is exactly the selected quotient-to-target homeomorphism `j`. Mathlib's
`IsometryEquiv.measurePreserving_euclideanHausdorffMeasure` then proves that
`j` preserves the normalized orbit Hausdorff measure into the target's
actual `gM.volumeMeasure`. The target Riemannian bundle and intrinsic metric
are installed from that same `gM`; the finite-distance conversion retains
its extended distance, uniformity and original topology.

Applying this measure-preservation identity to the whole target gives
exact equality of extended-valued total measures. The normalized orbit
Hausdorff total measure is finite if and only if the target intrinsic total
volume is finite. This is an equivalence; no unconditional finite-volume
conclusion or finite-volume premise is introduced. The finite pairwise
distance proof used to construct the target metric is a separate fact from
finiteness of its total volume.

A separate scoped check takes a supplied quotient Riemannian metric `gQ`
whose intrinsic distance equals `ENNReal.ofReal` of the same orbit distance,
under its smooth-manifold, `T3Space` and Borel conditions. The previously
checked intrinsic-metric/Hausdorff-volume identification derives that
`gQ.volumeMeasure` equals the normalized orbit Hausdorff measure. Thus the
same `j` preserves `gQ.volumeMeasure` into `gM.volumeMeasure`, their total
measures are equal, and their finiteness is equivalent. Volume equality is
derived, not assumed. This supplied-metric check does not identify `gQ`
with separately quantified older quotient-metric witnesses.

The universal target clause selects the covering, full deck representation,
basepoint fundamental-group equivalence, homeomorphism, intrinsic isometry
and intrinsic-volume preservation together. It is bound to the same actual
H3 metric `g`. Removing the one added clause and application and reversing
names/import restores the preceding entire constructor byte-for-byte. All
previous source, exponential, volume, curvature, completeness, conditional
core/tail and quotient clauses remain. The new clause adds no compactness,
orientability, finite-volume or target-simple-connectedness premise.

These are six scoped transient classical applications under unchanged pins,
with only `propext`, `Classical.choice` and `Quot.sound`, with no new tracked
project Lean declaration or novelty claim. Transfer of intrinsic quotient
volume does not identify Haar covolume in an ambient isometry group or
establish a lattice-conjugacy theorem. Finite-volume
cusp classification, Haar covolume and full Mostow-Prasad existence, homotopy
and uniqueness remain unfinished, including noncompact cusps and
nonorientable manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these compilation checks nor CI closes that audit.


## Discrete actual deck image in the compact-open topology

Give the original-H3 isometry group the topology induced by sending each
isometry to its bundled continuous map in `C(HyperbolicThreeSpace,
HyperbolicThreeSpace)`, equipped with Mathlib's compact-open topology.
This explicitly specified topology is used throughout this increment.
Evaluation at every fixed H3 point is continuous, by
`continuous_eval_const` and continuity of the induced map.

For an actual quotient covering `F` by its full covering deck group and an
isometric representation whose evaluation equals that deck action,
evaluation of the image subgroup at a fixed point lands in the actual
fiber of `F`. The covering's evenly covered neighborhood gives that fiber
its discrete subtype topology. Freeness from
`IsQuotientCoveringMap.isCancelSMul` makes evaluation on the image subgroup
injective. Applying `DiscreteTopology.of_continuous_injective` proves that
the actual image subgroup has discrete subtype topology in the specified
compact-open topology. No discreteness premise or replacement discrete
ambient topology is used.

For each preconnected smooth three-manifold with `T3Space` topology, a
smooth `MetricComplete` Riemannian metric of sectional curvature `-1`, and
supplied Levi-Civita data, this discreteness conclusion is attached to the
same jointly selected covering, faithful full deck representation,
basepoint fundamental-group equivalence, intrinsic isometric orbit
realization and intrinsic-volume transfer. The volume measures retain the
preceding pinned intrinsic normalized Hausdorff3 definition and original
Borel structures. No compactness, orientability or finite-volume premise
is added. A shortened source-contract check chooses the actual H3 chart and metric from the
preceding complete source constructor and retains its actual distance,
completeness and curvature data while supplying the new target contract.
The previous entire constructor remains available unchanged. Extending
its large statement with the new clause did not compile within the default
heartbeat limit; no successful extension of that entire statement is
claimed here.

These are four scoped transient classical composition checks under the
unchanged pins, with only `propext`, `Classical.choice` and `Quot.sound`.
No new tracked project Lean declaration or mathematical novelty is claimed.
The four discreteness checks alone do not supply continuity of group
multiplication or inversion, local compactness of the ambient group, Haar
covolume, cusp classification or an ambient conjugator. Full Mostow-Prasad existence,
homotopy and uniqueness remain unfinished, including noncompact cusps and
nonorientable manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these compilation checks nor CI closes that audit.


## Hausdorff topological group and closed actual deck image

The same explicitly induced compact-open topology makes the actual
original-H3 isometry group a Hausdorff topological group. The original-H3
proper-space instance supplies local compactness of H3 for the existing
continuous-map joint-evaluation interface; this does not assert local
compactness of the isometry group.

Joint evaluation is continuous by Mathlib's `continuous_eval` through the
induced bundling map. Joint inverse evaluation is continuous by the exact
identity
`dist (e.symm x) (e0.symm x0) = dist x (e (e0.symm x0))`:
the right side tends to zero by fixed-point evaluation continuity and
continuity of distance. `ContinuousMap.continuous_of_continuous_uncurry`
and the inducing-map continuity equivalence then give continuity of
isometry-group multiplication and inversion in that same topology.

Bundling an actual isometry as a continuous map is injective. Applying
`T2Space.of_injective_continuous` to this map into the Hausdorff
continuous-map space proves Hausdorffness of the isometry-group topology.
For an actual quotient covering and its full deck representation with the
exact deck-action evaluation identity, the previously checked discrete
image conclusion and this group structure meet the hypotheses of pinned
`Subgroup.isClosed_of_discrete`. Hence the same actual image subgroup is
closed in the specified compact-open topology. Closedness of an arbitrary
discrete subset is not inferred.

These three additional scoped transient classical checks retain the same
pins and standard three axioms. They add no tracked project Lean
mathematical declaration, volume premise or novelty claim. Haar covolume, finite-volume cusp classification,
lattice conjugacy and full Mostow-Prasad existence, homotopy and uniqueness
remain unfinished, including noncompact cusps and nonorientable manifolds.
The preceding intrinsic normalized Hausdorff3 volume definition and the
unfinished escape-audit disclosure remain in force.


## Locally compact isometry group and existence of Haar measure

For an actual original-H3 basepoint `p`, the same explicitly induced
compact-open isometry-group topology is locally compact. For every real
`R`, the set of actual isometries satisfying `dist (e p) p ≤ R` is compact.
With positive `R` this is a neighborhood of the identity. This establishes
local compactness of the isometry group itself.

The forward and inverse continuous maps form a closed embedding into a
product of continuous-map spaces. Its range is characterized by distance
preservation and both inverse identities. Joint continuous-map evaluation
and continuity of distance make these constraints closed. The product
pairing homeomorphism and the existing compact-convergence embedding put
this same pair into the function space used by pinned Arzela-Ascoli.

The paired functions `x ↦ (e x, e.symm x)` preserve distances for the product
metric, so they form a uniformly equicontinuous family. When the image of
`p` moves by at most `R`, both coordinates of the image of any `x` lie in
an actual proper-H3 product closed ball of radius `dist x p + R` centered
at `(p,p)`. These balls are compact. Applying
`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding` to all compact H3
subsets proves compactness of the closure of the bounded-basepoint set.
Continuous evaluation and distance make that set closed, so it equals its
compact closure. The positive-radius identity neighborhood and
`IsCompact.locallyCompactSpace_of_mem_nhds_of_group` give local compactness
in the original specified group topology.

The original coordinate homeomorphism gives second countability of H3.
The existing second-countability result for `C(H3,H3)` and the induced
bundling topology give second countability of the same isometry group.
With its Borel measurable structure, pinned `Measure.haar` supplies a
regular, sigma-finite left Haar measure. It is finite on compact sets and
positive on nonempty open sets; finite total mass is not asserted.

This Haar measure is on the isometry group. These four checks alone do
not identify its evaluation pushforward with normalized intrinsic
Hausdorff3 on H3 or establish quotient-target Haar covolume. No finite Haar covolume or lattice realization is derived
from target finite volume in this increment. These are four scoped
transient classical composition checks under unchanged pins and standard
three axioms, with no new tracked project Lean declaration or novelty
claim. Finite-volume cusp classification, Haar covolume identification,
lattice conjugacy and full Mostow-Prasad existence, homotopy and uniqueness
remain unfinished, including noncompact cusps and nonorientable manifolds.
The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these compilation checks nor CI closes that audit.

## Proper evaluation, transitivity and pushed Haar measure on H3

For every supplied actual original-H3 point `p`, evaluation `e ↦ e p` from
the same compact-open isometry group to original H3 is proper. A compact
H3 set is bounded inside some closed ball centered at `p`; its evaluation
preimage is a closed subset of the previously checked compact displacement
sublevel. The existing Hausdorff compact-coherence criterion gives
`IsProperMap`. In particular, the actual stabilizer set `{e | e p = p}` is
compact as the preimage of the singleton `{p}`.

The actual isometry group acts transitively on original H3. For supplied
points `p,q`, compose the project's positive dilation by the ratio of
their positive coordinate heights with a horizontal translation correcting
the horizontal coordinate. This is an actual `IsometryEquiv` carrying `p`
to `q`, using the existing dilation and translation constructions. Proper
evaluation is therefore a continuous closed surjection and, by the existing
closed-surjection theorem, a quotient map to the original H3 topology.

For any supplied left Haar measure `μ` on the same group's Borel structure,
its pushforward by evaluation at `p` is a measure on the original H3 Borel
structure. It is finite on compact sets by properness, positive on nonempty
open sets by continuous surjectivity, sigma-finite and regular by the
existing original-H3 topology and measure instances. It is invariant under
each actual H3 isometry: composition with such an isometry corresponds to
left multiplication on the group, and measure-map composition and left Haar
invariance give the equality. This is a pushed measure on H3, not a Haar
measure on a group structure imposed on H3.

These are three scoped transient classical composition checks under the
same pins and standard three axioms. They establish properties of the
actual evaluation pushforward. These three checks alone do not prove
uniqueness of invariant measures on H3, equality or proportionality to
normalized intrinsic Hausdorff3, a normalization scalar, unimodularity, a fundamental domain,
finite Haar covolume or lattice realization. Cusp classification, lattice
conjugacy and full Mostow-Prasad existence, homotopy and uniqueness remain
unfinished, including noncompact cusps and nonorientable manifolds. No new
tracked Lean declaration or mathematical novelty is claimed. The existing
escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Invariant H3 measure uniqueness and normalized Haar evaluation volume

An auxiliary affine group supplies the invariant-measure comparison. It is
Mathlib's semidirect product of additive complex translations and additive
real log-height, expressed with `Multiplicative`, with action
`z ↦ exp(t) • z`. Its topology is induced by its exact coordinate equivalence
to `ℂ × ℝ`; the explicit multiplication and inverse formulas prove that
it is a topological group. The horizontal coordinate and log of positive
height give a homeomorphism from original H3 to `ℂ × ℝ`, whose inverse has
height `exp(t)`. Combining these gives an actual homeomorphism between the
auxiliary group and original H3. Left multiplication corresponds exactly
to an existing positive dilation followed by an existing horizontal
translation, hence to an actual original-H3 isometry. This auxiliary group
is distinct from the full H3 isometry group with its compact-open topology.

For any two nonzero original-H3 Borel measures that are finite on compact
sets and invariant under every actual H3 isometry, there is a positive
finite real scalar relating them. To prove this, push each measure back
through the affine homeomorphism. The explicit left-multiplication identity
makes these measures left invariant on the auxiliary group. Its coordinate
homeomorphism supplies Hausdorffness, local compactness and second
countability. Existing regularity and positivity results make each lifted
measure a left Haar measure. Pinned `Measure.isMulLeftInvariant_eq_smul`
and positivity of `haarScalarFactor` give proportionality there;
injectivity of mapping by a measurable equivalence returns it to original
H3. Proportionality is a conclusion, with nonzero, compact-finite and
isometry-invariant measures as its hypotheses.

The original-H3 normalized three-dimensional Hausdorff measure is a valid
reference measure. Its nonzero and compact-finite properties are obtained
by selecting the actual chart and smooth metric from the existing complete
H3 source constructor, retaining its intrinsic distance and volume
identities, and using the pinned local-finiteness result. The source's
exact cylinder formula gives positive volume to the cylinder over the
horizontal unit ball at heights above one. Invariance under every actual
H3 isometry follows from existing
`IsometryEquiv.measurePreserving_euclideanHausdorffMeasure`.

For each supplied actual H3 point `p` and any supplied left Haar measure
`μ` on the same full compact-open isometry group's Borel structure, the
preceding evaluation-pushforward properties and this uniqueness result give
`μ.map (fun e => e p) = c • Measure.euclideanHausdorffMeasure 3`
for a positive `c : ℝ≥0`. Choosing an existing full-group Haar measure and
scaling it by `c⁻¹` therefore gives a left Haar measure whose evaluation
pushforward at this supplied `p` equals the original-H3 normalized
Hausdorff3 measure exactly. The checked quantifiers choose a normalized
measure for each supplied point; they do not assert that one chosen measure
works simultaneously at every point or prove ambient unimodularity.

For a supplied actual H3 smooth chart and manifold structure and a supplied
smooth source metric `g` whose intrinsic extended distance agrees with the
original H3 extended distance at every pair of points, the existing
intrinsic-volume identification gives `g.volumeMeasure` as that same
normalized Hausdorff3 measure. Thus a normalized full-group left Haar
measure exists for which evaluation at the supplied `p` is measure
preserving to this actual `g.volumeMeasure`. For every original-H3 Borel
measurable set `S`, its evaluation preimage has Haar measure exactly
`g.volumeMeasure S`, and these measures are finite if and only if each
other is finite. This statement does not require an assumed target
coordinate-density identity or a fundamental domain.

These are five scoped transient classical composition checks under the
same pins, with only `propext`, `Classical.choice` and `Quot.sound` in the
successful printed closures. They add no tracked project Lean declaration
or mathematical novelty claim. These five checks alone do not establish an actual deck fundamental
domain, its measure restriction or finite Haar covolume;
unrestricted pushforward through an infinite-sheet orbit projection does
not supply that volume comparison. Finite-volume cusp classification,
lattice conjugacy and full Mostow-Prasad existence, homotopy and uniqueness
remain unfinished, including noncompact cusps and nonorientable manifolds.
The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Actual Borel deck domains and normalized Haar covolume as source-domain volume

For a supplied actual original-H3 point `p`, every supplied surjective
local homeomorphism `F` from original H3 to a space with its Borel measurable
structure admits an original-H3 Borel set `D` on which `F` is injective and
whose image is the whole target. The construction uses local injectivity
to choose open source sheets. Original-H3 second countability gives a
countable subcover, enumerated by natural numbers. Their open target
images cover the target. Disjointizing these images with existing
`disjointed` gives a Borel partition. Intersect each source sheet with the
preimage of its target piece and take their countable union. The resulting
set is Borel, covers every fiber, and is injective over the target by
disjointness of the pieces and injectivity within each sheet.

For any supplied actual quotient covering `F` by a group `G` acting on
original H3, that construction supplies a Borel transversal. The quotient
covering's orbit/fiber identity and freeness imply that exactly one group
element moves any original-H3 point into the transversal. Existing
`IsFundamentalDomain.mk'` therefore makes it a fundamental domain for any
supplied measure on original-H3 Borel. Its pointwise selection implies
the required almost-everywhere coverage and disjointness; a fundamental
domain is not assumed as a premise.

For a supplied original-H3 smooth chart/manifold and smooth source metric
`g` with its pairwise intrinsic extended distance equal to original H3
extended distance, a supplied actual point `p`, and a faithful group
homomorphism `ρ` into the same full compact-open H3 isometry group whose
evaluation agrees with the actual `G` action at every point, any such
Borel `G` fundamental domain for `g.volumeMeasure` lifts through evaluation
to a fundamental domain for the actual image subgroup `ρ.range` acting
on the full isometry group by left multiplication. Use the preceding
normalized evaluation measure-preserving map and existing
`IsFundamentalDomain.preimage_of_equiv`; `ρ.rangeRestrict` is bijective by
faithfulness and range surjectivity, and the exact representation identity
supplies the required evaluation equivariance. The lifted domain's Haar
measure equals `g.volumeMeasure D` exactly, with finiteness equivalent.

The actual quotient-covering group is countable. Its fiber above `F p` is
discrete by the actual covering map and second countable as an original-H3
subspace, hence countable by existing separability/discreteness results.
The covering's actual `fiberEquivGroup` transfers countability to `G`, and
the range restriction transfers it to the actual image subgroup.

Combining these checks chooses the same Borel domain `D` and normalized
left Haar measure `μ` together. The source domain is injective and
surjective over the actual target, and its evaluation preimage is an
actual image-subgroup fundamental domain. Existing
`IsFundamentalDomain.covolume_eq_volume`, with the derived countability and
left Haar invariance, identifies `covolume ρ.range (H3 ≃ᵢ H3) μ` with
`g.volumeMeasure D`. Thus this covolume is finite if and only if this
actual source-domain volume is finite. Both the domain and its lifted
fundamental-domain property are established before using the covolume
definition; no inference is made from its default value when a domain is
absent.

These are five further scoped transient classical composition checks
under the same pins and standard three axioms, with no tracked project
Lean declaration or mathematical novelty claim. These five checks alone do not identify
the restricted source-volume pushforward on `D` with the actual target's
intrinsic volume or derive finite Haar covolume from actual target finite
volume. Ambient unimodularity, finite-volume
cusp classification, lattice conjugacy and full Mostow-Prasad existence,
homotopy and uniqueness remain unfinished, including noncompact cusps and
nonorientable manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Actual target Riemannian volume and finite normalized Haar covolume

For an actual quotient covering of original H3, a disjoint covering
neighborhood contains a ball of positive radius `R`. If two points lie in
the concentric ball of radius `R/4`, every nonidentity deck translate of
the second point lies outside the larger ball. The triangle inequalities
show that its distance from the first point is at least their original
distance. The infimum over the actual deck orbit therefore equals the
original distance between the two points. Combining this with the existing
actual metric-covering fiber-distance formula proves local distance
preservation. This step retains the actual source smooth chart and metric,
its pairwise intrinsic-distance identity with original H3, the actual
quotient covering, local diffeomorphism, tangent-metric pullback identity,
and exact evaluation identity of the full deck representation. Local
isometry is a conclusion here.

On each such locally isometric ball, existing
`Isometry.euclideanHausdorffMeasure_image`, applied to the ball subtype and
its source inclusion, identifies normalized Hausdorff3 measures of a
subset and its image. Original-H3 second countability gives a countable
cover by these balls. Disjointizing the source balls partitions any Borel
set `D` on which `F` is injective. The restriction of `F` to each ball is
an open embedding, so its Borel piece images are Borel. Injectivity on `D`
makes these images disjoint, and countable additivity proves that the
normalized Hausdorff3 measure of `F '' D` equals that of `D`. Apply the
same argument to `D ∩ F ⁻¹' S` for each Borel target set `S`. When `F '' D`
is the whole target, this proves that restriction of source Hausdorff3 to
`D` pushes forward to target Hausdorff3. This intermediate comparison uses
a target extended metric space and its Borel structure.

For the actual supplied smooth target metric `gM`, install its existing
Riemannian bundle and intrinsic extended metric. Their topology and Borel
structure are the supplied target topology and Borel structure. Bind the
local distance result above to this metric, and use the existing source
volume identity and target volume definition. For an original-H3 Borel
transversal of the actual covering, the result is
`MeasurePreserving F (gH.volumeMeasure.restrict D) gM.volumeMeasure`.
In particular, `gH.volumeMeasure D = gM.volumeMeasure univ`, with finiteness
equivalent. There is no assumed coordinate-density comparison or assumed
restricted-volume identity, and no unrestricted covering pushforward.

Choose the same `D` and normalized left Haar measure `μ` from the preceding
actual deck-domain construction. For a faithful representation of the
full deck group whose evaluation is the actual action at every point,
its actual image subgroup then satisfies
`covolume ρ.range (H3 ≃ᵢ H3) μ = gM.volumeMeasure univ`.
This is an equality for that jointly selected domain and measure. Thus
actual target finite volume implies finite covolume under that measure,
without an extra finiteness premise on the source domain. The fundamental
domains are constructed before applying the covolume formula.

A shortened composition also binds this result to the existing actual
complete curvature-minus-one target constructor. Given the actual
complete original-H3 smooth source metric with curvature minus one and its
original pairwise distance formula, an actual preconnected complete
smooth target of curvature minus one with finite intrinsic volume, and
actual source and target basepoints, choose the constructor's covering
`F` and its same faithful full deck representation `ρ`. The exact action
identity, actual quotient covering, tangent-metric pullback identity,
fundamental-group/deck-group correspondence, and compact-open discreteness
of `ρ.range` are retained. There exists a normalized full-group left Haar
measure whose actual image-subgroup covolume equals that target's volume
and is finite. This uses the already checked source constructor contract;
it does not claim compilation of the earlier entire 455-line extension.

These are five further scoped transient classical composition checks,
with nine printed closures using only `propext`, `Classical.choice` and
`Quot.sound` under the same pins. No tracked project Lean declaration or
mathematical novelty is claimed. Neither compactness nor orientability is
assumed in these checks; they do not classify noncompact ends. These five checks alone do not establish ambient unimodularity. Any
additional library lattice predicate, finite-volume
cusp classification, lattice conjugacy and full Mostow-Prasad existence,
homotopy and uniqueness remain unfinished, including noncompact cusps and
nonorientable manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Right invariance from the same finite-volume deck domain

For a supplied locally compact, second-countable topological group with
its Borel structure and supplied left Haar measure `μ`, let `Γ` be a
countable subgroup with a supplied Borel fundamental domain `D` of finite
`μ` measure. Existing `IsFundamentalDomain.measure_ne_zero`, using Haar
nonzero and subgroup left invariance, makes the domain's mass nonzero.
For each ambient element `g`, existing
`quasiMeasurePreserving_mul_right` and `IsFundamentalDomain.preimage_of_equiv`
show that the right-translation preimage of `D` is another fundamental
domain for the same subgroup and measure. Associativity gives the exact
equivariance with the subgroup's left action; right invariance is not
assumed for this step. Existing fundamental-domain measure equality
therefore gives the translated domain the same mass.

The existing right-translation Haar instance and
`Measure.isMulLeftInvariant_eq_smul` express the right-pushed measure as a
scalar multiple of the same left Haar measure. Evaluate that equality on
`D`. Its finite nonzero mass forces the scalar to equal one by existing
ENNReal cancellation. Hence every right pushforward equals `μ`, proving
`μ.IsMulRightInvariant`. This is a classical finite-domain argument using
existing APIs, with countability and the Borel fundamental domain explicit.
It does not require compactness of the group or the domain.

Apply this to the same original-H3 full compact-open isometry group, the
same actual full-deck image `ρ.range`, and the same normalized left Haar
measure selected by the preceding actual target-volume construction.
The actual covering derives countability of the deck group and its image.
The evaluation preimage of the same Borel source domain is Borel by
continuous evaluation and is already a fundamental domain for that image.
Its mass equals the already identified covolume, hence the actual target
total volume. If that target volume is finite, the finite-domain argument
makes this same `μ` right invariant. It remains a left Haar measure, and
its actual image-subgroup covolume still equals the actual target volume.
The supplied original-H3 smooth source geometry and original pairwise
distance identity, actual target geometry/Borel structure, actual full-deck
quotient covering/local diffeomorphism/tangent-metric pullback, and faithful
representation implementing the actual action at every point remain
explicit premises.

A shortened composition retains these conditions in the existing
complete curvature-minus-one target constructor. For the same chosen
covering and faithful compact-open discrete full-deck image, with the
fundamental-group/deck-group correspondence retained, a left and right
invariant normalized Haar measure gives covolume equal to actual finite
target volume. The actual complete source metric, original pairwise
distance formula, source and target curvature-minus-one data, and actual
basepoints remain explicit. No compactness or orientability premise is
added, and the old whole 455-line extension is not claimed to compile.

These are three further scoped transient classical composition checks
with three standard-axiom closures and no tracked project Lean declaration
or novelty claim. The right-invariance conclusion is tied to the actual
finite-volume construction above. Any additional library lattice predicate,
finite-volume cusp classification, lattice conjugacy and full
Mostow-Prasad existence, homotopy and uniqueness remain unfinished,
including noncompact cusps and nonorientable manifolds. The existing escape
audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Finite invariant actual group quotient measure and recurrence

Starting with the same Borel left-subgroup fundamental domain `D` and
same left and right Haar measure `μ`, inversion is measure preserving
from `μ.inv` to `μ`. Existing `IsFundamentalDomain.preimage_of_equiv`,
with the subgroup bijection given by inversion followed by `equivOp`,
therefore makes `D⁻¹` a Borel right-subgroup fundamental domain for
`Γ.op` and `μ.inv`. Its mass is exactly `μ D`, hence finite.
The inverse measure is itself left Haar and right invariant. This step
keeps the inverse measure explicit; it does not assert `μ.inv = μ`.

For a supplied Polish topological group with its Borel structure, a
countable subgroup `Γ`, and the actual Hausdorff Borel coset space
`K ⧸ Γ`, define
`ν = (μ.inv.restrict D⁻¹).map QuotientGroup.mk`.
Existing fundamental-domain quotient-measure results give
`QuotientMeasureEqMeasurePreimage μ.inv ν` and ambient left-action
invariance `SMulInvariantMeasure K (K ⧸ Γ) ν`.
The measurable quotient map gives `ν univ = μ D`. Thus `ν` is finite
and nonzero, with nonzero domain mass obtained from the existing
fundamental-domain theorem and Haar nonzero. No normality of `Γ` is
assumed: this is the actual coset space, without a quotient-group
multiplication requirement. The left/right action directions and
inverse measure are part of the construction.

For the same full original-H3 compact-open isometry group, existing
coordinate second countability, source completeness and properness,
complete metrizability of continuous maps, and the already checked
closed embedding of isometries as map/inverse pairs give complete
metrizability. Together with the group's already checked second
countability this gives a Polish space for that same topology.
The actual covering's closed image theorem then makes the actual
coset space by `ρ.range` Hausdorff; `CosetSpace.borelSpace` supplies its
Borel compatibility without assuming subgroup normality.

Under the supplied compatible original-H3 smooth source geometry and
original pairwise distance identity, actual target geometry and Borel
structure, actual full-deck quotient covering/local diffeomorphism/
tangent-metric pullback, faithful representation implementing the actual
action at every point, and finite actual target volume, use the same
jointly selected source domain, lifted group domain and normalized Haar
measure from the actual target-volume construction. The already checked
finite-domain argument makes that same `μ` right invariant.
The actual deck/image countability and closedness, and the same lifted
Borel fundamental domain, now supply a measure `ν` on the actual space
`(H3 ≃ᵢ H3) ⧸ ρ.range`. It is finite, nonzero and invariant under the
ambient group's left action. Its total mass equals the actual target
Riemannian total volume, while that same `μ` still has actual image
covolume equal to that volume. The quotient-measure relation is with
`μ.inv`, as above.

For any supplied finite nonzero ambient-invariant Borel coset measure on
a second-countable topological coset space, each fixed ambient element
acts measure preservingly by existing `measurePreserving_smul`.
Existing `MeasurePreserving.conservative` and
`Conservative.ae_frequently_mem_of_mem_nhds` imply that almost every coset
returns to every neighborhood infinitely often under iteration of that
fixed element. Nonzero total mass supplies at least one such coset.
Bind this to the same `ν` on the actual original-H3 coset space above,
retaining its inverse-Haar relation and actual-volume normalization.
The quantifiers are: for every ambient element separately, almost every
coset is recurrent and some recurrent coset exists. These checks do not
supply one coset recurrent for all ambient elements, recurrence of every
coset, boundary density, centralizer triviality or lattice conjugacy.

These are six further scoped transient classical composition checks,
with six printed closures using only `propext`, `Classical.choice` and
`Quot.sound` under the same pins. No tracked project Lean declaration or
mathematical novelty is claimed. No compactness or orientability premise
is added to the actual finite-volume construction. Any additional library
lattice predicate, finite-volume cusp classification, lattice conjugacy
and full Mostow-Prasad existence, homotopy and uniqueness remain
unfinished, including noncompact cusps and nonorientable manifolds.
The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Open positivity and dense recurrence on the same actual coset space

For a supplied locally compact, second-countable topological group and
actual Hausdorff Borel coset space by a subgroup, let `ν` be a finite,
nonzero measure invariant under the ambient group's left action.
The actual coset space is locally compact and second countable; its
Hausdorff locally compact topology gives the regularity and metrizability
needed by the existing finite-measure regularity instance. The ambient
coset action is transitive, hence minimal. Existing
`measure_isOpen_pos_of_smulInvariant_of_ne_zero` makes every nonempty
open subset have positive `ν` measure. This gives `ν.IsOpenPosMeasure`.
For each fixed ambient element, apply the preceding almost-everywhere
neighborhood recurrence and existing `Measure.dense_of_ae` to obtain a
dense subset of recurrent cosets for that element.

Under the same supplied compatible original-H3 smooth source geometry,
original pairwise distance identity, actual target geometry/Borel,
actual full-deck quotient covering/local diffeomorphism/tangent-metric
pullback, faithful representation implementing the actual action at every
point, and finite actual target volume, bind this to the same actual
normalized Haar `μ` and actual coset measure `ν` above. The existing
compact-open ambient-group local compactness and second countability,
actual closed deck image, and actual coset Hausdorff/Borel compatibility
supply the required hypotheses without normality or compactness of the
subgroup or quotient. Retain the same left/right Haar invariance,
actual covolume and `ν` mass equal to actual target total volume, explicit
`μ.inv` quotient-measure relation, and finite nonzero ambient-left-invariant
`ν`. That same `ν` is positive on every nonempty open coset subset, and
for every ambient element separately its recurrent cosets are dense.

These are two further scoped transient classical composition checks,
with two printed closures using only `propext`, `Classical.choice` and
`Quot.sound` under the same pins, with no tracked project Lean declaration
or mathematical novelty claim. Dense recurrence here concerns the actual
group coset space. It supplies no dense interior deck orbit, no boundary
or attracting-pole density, no common recurrent coset for all ambient
elements, and no recurrence of every coset. Lattice conjugacy, finite-volume
cusp classification and full Mostow-Prasad homotopic isometry existence
and uniqueness remain unfinished, including noncompact cusps and
nonorientable manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.
