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

## Continuous centralizer conjugation and recurrence constraints

For a supplied topological group `K`, subgroup `Γ`, and element `z`
commuting with every element of `Γ`, the actual function
`x ↦ x * z * x⁻¹` descends to a continuous map `Φ : (K ⧸ Γ) → K`.
The defining left-coset relation gives `x⁻¹ * y ∈ Γ`; the supplied
commutation makes the conjugation values agree on that relation.
Existing quotient lifting and continuity then give the map with exact
value `Φ (QuotientGroup.mk x) = x * z * x⁻¹` and exact equivariance
`Φ (g • q) = g * Φ q * g⁻¹`. Subgroup normality is not assumed.

For continuous `Φ` semiconjugating two supplied self-maps, neighborhood
recurrence of a point transfers to neighborhood recurrence of its image.
The preimage of an image-point neighborhood is a neighborhood of the
original point, and existing semiconjugacy iteration identifies the
iterates. Only continuity of `Φ` is assumed for this transfer.
Apply it to the actual continuous centralizer map above, for a locally
compact, second-countable ambient topological group with actual Hausdorff
Borel coset space and supplied finite nonzero ambient-left-invariant
coset measure `ν`. For each fixed ambient `g`, almost every coset has
`Φ q` recurrent under conjugation `y ↦ g * y * g⁻¹`. The already checked
open positivity and existing `Measure.dense_of_ae` make these cosets
a dense subset of the actual coset space. This asserts density of the
specified cosets, not density of their images or of a conjugacy orbit in
`K`.

Under the supplied compatible original-H3 smooth source geometry,
original pairwise distance identity, actual target geometry/Borel,
actual full-deck quotient covering/local diffeomorphism/tangent-metric
pullback, faithful representation implementing the actual action at every
point, and finite actual target volume, bind this to the same original-H3
full compact-open isometry group, actual image `ρ.range`, normalized Haar
`μ` and actual coset measure `ν` from the preceding construction.
The same ambient topology/Borel/Polish/local compactness/second countability,
actual closed deck image and actual coset Hausdorff/Borel compatibility
supply the hypotheses. Retain left/right Haar invariance, actual covolume
and `ν` total mass equal to actual target volume, explicit `μ.inv`
quotient-measure relation, and finite nonzero ambient-left-invariant,
open-positive `ν`. For each supplied `z` centralizing that actual image,
the exact continuous `Φ` above has, for each ambient `g` separately,
almost-everywhere and dense cosets with conjugation-recurrent `Φ q`.
This does not prove `z = 1`.

A further generic conditional check isolates a remaining geometric
obligation. With the same supplied ambient-group, coset-measure and
centralizer hypotheses, fix `g` and supply a closed subset `S ⊆ K`
containing every neighborhood-recurrent point of conjugation by `g`.
The preimage `Φ⁻¹(S)` is closed and contains the dense set of
conjugation-recurrent cosets. It therefore contains every coset; the
exact value formula gives `x * z * x⁻¹ ∈ S` for every `x : K`.
The closed set and its coverage of all recurrent conjugation points are
explicitly supplied premises. No such concrete classification or closed
constraint for actual H3 is established by this generic check.

These are five further scoped transient classical composition checks,
with five printed closures using only `propext`, `Classical.choice` and
`Quot.sound` under the same pins; the semiconjugacy-transfer closure uses
only `propext` and `Quot.sound`. No tracked project Lean declaration or
mathematical novelty is claimed. No compactness or orientability premise
is added to the actual finite-volume construction. An actual H3
recurrent-conjugation constraint, centralizer triviality, lattice
conjugacy, finite-volume cusp classification and full Mostow-Prasad
homotopic isometry existence and uniqueness remain unfinished, including
noncompact cusps and nonorientable manifolds. The existing escape audit
remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Lorentz coordinates and linear extension of actual H3 isometries

A further transient classical composition starts from the same original
upper-half-space metric, without replacing its distance. Existing
half-distance and hyperbolic-function identities give, for original
upper-half-space points `p,q`,
`cosh(hyperbolicDist p q) = 1 + distAmbient(p,q)^2/(2*height p*height q)`.
For the original H3 point with horizontal coordinate `x + i*y` and
positive height `t`, define the real four-coordinate map
`C(p) = ((x^2+y^2+t^2+1)/(2*t), x/t, y/t,
(x^2+y^2+t^2-1)/(2*t))` and Lorentz bilinear form
`B(u,v) = u0*v0-u1*v1-u2*v2-u3*v3`.
The exact original-distance identity is `B(C(p),C(q)) = cosh(dist p q)`.
It gives `B(C(p),C(p)) = 1`, injectivity of `C`, and preservation of this
kernel by every actual H3 isometry.

The four actual upper-half-space points `(0,1)`, `(0,2)`, `(1,1)` and
`(i,1)` have Lorentz vectors `(1,0,0,0)`, `(5/4,0,0,3/4)`,
`(3/2,1,0,1/2)` and `(3/2,0,1,1/2)`. Exact coefficient expansion spans
the real four-dimensional vector space, and their Lorentz probes detect
the zero vector. Distances to these four points determine every actual H3
point. The values of an actual H3 isometry at these four points determine
the entire isometry.

For every actual H3 isometry `e`, preservation of the frame Gram matrix
makes the four vectors `C(e(frame_i))` linearly independent. Existing
Mathlib finite-dimensional basis construction and basis equivalence give
a real linear equivalence `L(e)` sending each `C(frame_i)` to
`C(e(frame_i))`. Pairing the exact frame expansion with the image basis
proves `L(e)(C(p)) = C(e(p))` for every actual H3 point `p`, rather than
only for the four frame points. Bilinearity and kernel preservation on
the frame then give `B(L(e)u,L(e)v) = B(u,v)` for all real four-vectors.
Agreement on the frame proves `L(1) = 1` and
`L(e*f) = L(e)*L(f)`, with composition in the same order as the original
isometry group. Coordinate injectivity and determination by the four
frame values prove that this group homomorphism is injective. These
arguments cover the full original H3 isometry group; they do not assume
orientation preservation.

The six scoped transient checks reuse the existing original
upper-half-space metric, real hyperbolic-function identities, finite sums,
finite-dimensional basis construction and basis equivalence. Their
23 printed closures use only `propext`, `Classical.choice` and `Quot.sound`
under the same pins. No tracked Lean declaration or mathematical novelty
is claimed. Continuity of this representation, any assertion that its
image is the full Lorentz group, and an actual H3 recurrent-conjugation
constraint are not established by these checks. Centralizer triviality,
lattice conjugacy, finite-volume cusp classification and full
Mostow-Prasad homotopic-isometry existence and uniqueness remain
unfinished, including noncompact cusps and nonorientable manifolds.
The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Continuous actual matrix coefficients and diagonal positive dilation

Five further transient classical composition checks supply additional
ingredients for the still missing actual recurrent-conjugation constraint.
The same original H3 coordinate homeomorphism makes its Lorentz-coordinate
map continuous. In the same actual compact-open isometry-group topology,
existing point evaluation and the exact frame expansion make
`e ↦ L(e)u` continuous for each fixed real four-vector `u`.
The coefficient matrix `A(e)ij = (L(e)(single j 1))i` is therefore
continuous in the finite real product topology. Existing Mathlib
`LinearMap.toMatrix'` identifies these exact coefficients and gives
`A(1)=1` and `A(e*f)=A(e)*A(f)`. The already proved faithful linear
representation makes `A` injective. The matrices of `e` and `e⁻¹` are
two-sided inverses. This does not assert a topological embedding or
surjectivity onto a matrix group.

A separate generic real dynamical check assumes `a>0`, `a≠1`, and
neighborhood recurrence of `x` under `y ↦ a*y`; it proves `x=0`.
Exact scalar iteration is `a^n*x`. Existing geometric-power convergence
handles `0<a<1`; divergence of the absolute-value orbit handles `a>1`.
The recurrence is expressed by arbitrarily late visits to every
neighborhood, not by assuming a fixed point. This generic check alone
classifies no actual H3 isometry.

The real linear coordinate change
`P(u)=(u0+u3,u1,u2,u0-u3)` has inverse
`P⁻¹(v)=((v0+v3)/2,v1,v2,(v0-v3)/2)`.
Conjugating the same actual isometry representation through `P` preserves
its group multiplication and its action on every actual H3 point.
For the actual positive upper-half-space dilation with scale `a>0`,
the transformed coordinates have weights `(a,1,1,a⁻¹)`. Exact frame
expansion proves that its transformed linear map acts with these weights
on every real four-vector, not only on the coordinate-image points.
This diagonalization is derived for the actual existing dilation and
original metric; it is not supplied as a premise.

The five scoped checks print 15 closures using only `propext`,
`Classical.choice` and `Quot.sound` under the same pins. No tracked Lean
declaration or mathematical novelty is claimed. Combining the actual
continuous matrix coefficients, dilation diagonalization and generic
scalar recurrence into an actual H3 recurrent-conjugation classification
remains unfinished. Centralizer triviality, lattice conjugacy, cusp
classification and full Mostow-Prasad homotopic-isometry existence and
uniqueness remain unfinished, including noncompact cusps and nonorientable
manifolds. The existing escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.

## Actual recurrent-conjugation constraint for positive H3 dilation

Three further transient classical composition checks bind the preceding
scalar recurrence result to the actual full original H3 isometry group.
The light-coordinate coefficient matrices of `P*L(e)*P⁻¹` are continuous
in the same actual compact-open topology, preserve multiplication and
are injective. For the actual positive dilation `d` of scale `a>0`,
its matrix is diagonal with weights `w=(a,1,1,a⁻¹)`; the matrix of its
actual inverse has the reciprocal weights. Thus the actual coefficient
formula is `A(d*e*d⁻¹)ij = (wi/wj)*A(e)ij`.

Suppose an actual H3 isometry `e` is neighborhood-recurrent under
conjugation by this actual `d`. Each continuous matrix coefficient
transports that recurrence through its exact scalar semiconjugacy.
All weights are positive. If `wi≠wj`, the positive multiplier `wi/wj`
is unequal to one, so the generic scalar check forces `A(e)ij=0`.
The resulting coefficient constraints make `A(e)` commute with the
actual diagonal matrix of `d`. Matrix injectivity gives `e*d=d*e` in
the actual original H3 isometry group. The constraint set
`S={e | e*d=d*e}` is closed by actual compact-open group continuity
and Hausdorff equality. This proves the previously supplied geometric
premise for this concrete closed constraint and positive dilation.
It does not assert an arbitrary-conjugating-isometry classifier.

Under the supplied compatible original-H3 smooth source geometry and
original pairwise distance identity, actual target geometry/Borel,
full-deck quotient covering/local diffeomorphism/tangent-metric pullback,
faithful representation implementing the actual deck action at every
point, and finite actual target volume, select the same normalized Haar
`μ` and finite nonzero invariant actual coset measure `ν` as before.
Retain actual covolume and `ν` mass equal to actual target volume,
Haar right invariance, explicit `μ.inv` quotient relation and `ν` open
positivity. For every `z` centralizing the actual deck image, for every
positive scale and every ambient actual isometry `x`, the same accepted
closed-constraint argument now gives
`(x*z*x⁻¹)*d = d*(x*z*x⁻¹)` for the actual dilation at that scale.
The geometric recurrence-coverage premise is proved here rather than
supplied. No subgroup normality, compactness or orientation-preserving
restriction is introduced. The conclusion concerns all actual conjugates
of the supplied centralizer element; it still does not prove `z=1`.

These three scoped checks print 11 closures using only `propext`,
`Classical.choice` and `Quot.sound` under the same pins. No tracked Lean
or mathematical novelty is claimed. Centralizer triviality, lattice
conjugacy, finite-volume cusp classification and full Mostow-Prasad
homotopic-isometry existence and uniqueness remain unfinished, including
noncompact cusps and nonorientable manifolds. The existing escape audit
remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549 .
Neither these checks nor CI closes that audit or the remaining mathematics.


## Actual H3 centralizer identity from translations and dilation

The same original H3 horizontal translations satisfy
`dₐ Tᵤ dₐ⁻¹ = Tₐᵤ` for every positive real scale. In particular,
`Tᵤ d₂ Tᵤ⁻¹ d₂⁻¹ = T₋ᵤ`. The group conjugation identity and
these actual action formulas show that if every ambient conjugate of `z`
commutes with `d₂`, then `z` commutes with every horizontal translation.
No supplied translation relation or classification is used.

For an actual full H3 isometry commuting with `d₂`, `T₁` and `Tᵢ`, write
its image of `(0,1)` as `(u,t)` with `t>0`. Commutation identifies the
images of the other three accepted frame points as `(2u,2t)`, `(u+1,t)`
and `(u+i,t)`. The original rational cosh-distance identity for the first
horizontal pair gives `t=1`; the doubled-height pair then gives `u=0`.
The four actual frame values and the previously checked determination
lemma imply that the isometry is the identity. This uses the original
metric and full isometry group, with no orientation restriction.

Under the same supplied compatible smooth original-H3 geometry and exact
original-distance identity, actual target smooth geometry and Borel
structure, full-deck quotient covering, local diffeomorphism and tangent
metric pullback, faithful all-point actual deck action and finite actual
target volume, the selected Haar and coset measures from the preceding
construction now give `z=1` for every element centralizing the actual deck
image. The same witnesses retain right Haar invariance, covolume and coset
mass equal to actual target volume, the inverse-Haar quotient relation,
and a finite nonzero ambient-left-invariant open-positive coset measure.
The all-conjugates dilation constraint and centralizer identity are derived;
centralizer triviality is no longer an extra premise of this conditional
finite-target result. Compactness, orientability and subgroup normality
are not added.

The three scoped checks contain ten accepted axiom closures using only
`propext`, `Classical.choice` and `Quot.sound`. Two rejected frame-identity
source/log pairs are excluded from the accepted evidence. This is transient
classical reuse and composition; no tracked Lean declaration or mathematical
novelty is claimed. The existing escape audit remains unfinished at the
linked issue. The compatible original-H3 smooth geometry and the full
covering/action/metric inputs remain supplied. Lattice conjugacy, general
homotopic-isometry existence and the full Mostow–Prasad endpoint, including
cusps and nonorientable manifolds, remain unproved by these checks.


## Centralizer and conjugator uniqueness for a selected complete target

For a preconnected smooth three-dimensional target with `T3Space` topology,
Borel structure, complete Riemannian metric of sectional curvature `-1`,
Levi-Civita data and finite intrinsic volume, and a supplied compatible
smooth original-H3 metric with the exact original distance, completeness,
sectional curvature `-1` and Levi-Civita data, the existing complete-target
constructor now selects a covering and full deck representation with trivial
range centralizer. The covering, local diffeomorphism and all-point deck
metric action needed by the preceding finite-target result are obtained from
that constructor rather than supplied independently in this extension.
The compatible original-H3 geometric inputs remain explicit.

The same selected covering retains its prescribed basepoint, smoothness,
surjectivity, tangent metric pullback, full-deck quotient-covering property,
fundamental-group equivalence with the opposite deck group, free action and
compact-set properness. Its same faithful actual H3 representation retains
discreteness in the original compact-open topology, freeness, proper
discontinuity, smooth inverse actions and tangent metric preservation.
The same orbit homeomorphism retains its projection identity, actual target
intrinsic-distance comparison, intrinsic isometric realization and the
existing conditional quotient-volume contract. No independently chosen
covering, representation or quotient witness is substituted.

For any second representation of this selected deck group, if two actual
ambient H3 isometries implement the same pointwise conjugation relation,
they are equal. The existing generic conjugator-uniqueness theorem supplies
this implication from the newly obtained range centralizer. This is a
uniqueness implication; existence of an ambient conjugator remains missing.
No compactness or orientation restriction is imposed.

One scoped transient cache-guarded check exited zero and printed one axiom
closure using only `propext`, `Classical.choice` and `Quot.sound`. It directly
reuses the preceding complete-target constructor and conditional actual
centralizer result; it does not recompile or claim a fresh whole check of
the older long H3 constructor. This is classical composition with no tracked
Lean or novelty claim. General lattice conjugacy, homotopic-isometry
existence, global target uniqueness and the full Mostow–Prasad endpoint,
including cusps and nonorientable manifolds, remain unproved by this check.
The existing escape audit remains unfinished at the linked issue.


## Continuous interpolation equivariant under the full original H3 group

The original H3 Lorentz coordinates have light difference
`v₀-v₃=1/height>0`. Every real four-vector with Lorentz self-kernel `1`
and positive light difference has an explicit original-H3 inverse: its
horizontal real and imaginary coordinates are `v₁/(v₀-v₃)` and
`v₂/(v₀-v₃)`, and its height is `1/(v₀-v₃)`. This recovers every actual
original H3 point. It is a point-coordinate inverse; no surjectivity claim
for the matrix representation of the isometry group is made.

For `r∈[0,1]` and actual points `p,q`, form the Lorentz vector
`v=(1-r)L(p)+rL(q)`. Its self-kernel is
`(1-r)²+r²+2r(1-r)cosh(dist(p,q))`, hence at least `1`; its light difference
is positive. Dividing by the square root of that self-kernel and applying
the explicit future-unit-vector inverse gives an actual original H3 point.
The resulting interpolation has endpoints `p,q`. Every actual full H3
isometry preserves this interpolation: the existing exact linear extension
preserves the Lorentz kernel and agrees on every actual H3 point. No affine
shape, orientation restriction or substituted metric is used.

The interpolation is jointly continuous in the closed-interval parameter
and both points, using the same original H3 coordinate homeomorphism and
continuous Lorentz coordinate map. The proof keeps every reciprocal away
from zero through the proved positive-light and positive-kernel bounds.
For any topological source space and two continuous maps into original H3,
the construction supplies an actual continuous homotopy with the stated
endpoints. If both maps are equivariant for the same group action on the
source and the same representation into the actual full H3 isometry group,
that very homotopy is equivariant for every group element and every time.
Continuity here is joint in time and the source point; no joint continuity
in the group variable is asserted or required.

Three scoped transient cache-guarded checks exited zero and printed nineteen
axiom closures using only `propext`, `Classical.choice` and `Quot.sound`.
One rejected algebra source/log pair and two rejected continuity/homotopy
pairs are excluded. The repaired composition uses explicitly typed maps
and a local irreducibility annotation for the already proved interpolation
operator; the original statements, metric, actions and resource limits are
retained. These are classical compositions, with no new tracked Lean or
novelty claim. The existing escape audit remains unfinished at the linked
issue.

This check constructs the original-H3 equivariant homotopy. It does not yet
descend that homotopy through the actual target coverings, construct an
equivariant lift of an arbitrary prescribed homotopy equivalence, or obtain
an ambient conjugator from an abstract lattice isomorphism. General
homotopic-isometry existence, global target uniqueness and the full
Mostow–Prasad endpoint remain unfinished, including cusps and nonorientable
manifolds.


### Homotopy descent and continuous equivariant covering lifts

For the same original H3 equivariant homotopy, a supplied quotient covering
`F:X→M`, a continuous map `P:H3→N` invariant under the same representation,
and continuous lifts `f,g:X→H3` equivariant under that representation now
supply a homotopy between continuous maps `φ,ψ:M→N`, provided the all-point
identities `P(f(x))=φ(F(x))` and `P(g(x))=ψ(F(x))` hold. Fiber equality gives
an actual group orbit; equivariance and invariance make the projected
homotopy independent of a chosen representative. The chosen section is
not assumed continuous. The product of the identity on the time interval
with the same open quotient covering is an open quotient map, which proves
continuity of the descended homotopy and preserves both endpoints.

Separately, for quotient coverings `F:X→M` and `P:Y→N` by groups `G,H`, a
simply connected, locally path connected source `X`, a continuous base map
`φ:M→N` and compatible supplied basepoints, the same coverings now select
a continuous lift `L:X→Y` and a group homomorphism `τ:G→H`. The lift has the
specified basepoint and the all-point projection identity, and satisfies
`L(a•x)=τ(a)•L(x)` for every group element and source point. The construction
uses the existing unique continuous covering lift. It selects the unique
target group element matching each source action at the lift basepoint;
covering lift uniqueness proves equivariance at every point, and the free
target action proves both homomorphism laws. No equivariance of the lift
or homomorphism laws are assumed.

An exact application uses the original H3 on both covering spaces and their
same full deck groups. Original-H3 simple connectivity is reused; a supplied
compatible H3 chart supplies local path connectivity. Thus any continuous
map between those actual bases with compatible chosen basepoints admits
the stated continuous lift and actual deck-group homomorphism. No metric,
orientation, compactness or group-variable continuity premise is added to
this topological conclusion.

Two serial scoped transient cache-guarded checks exited zero and printed
three axiom closures using only `propext`, `Classical.choice` and
`Quot.sound`. Two rejected descent source/log pairs are excluded. Five
`haveILetI` style warnings in the successful lift check are recorded; they
are not errors or proof exceptions. These are classical compositions with
no tracked Lean or novelty claim. The linked escape audit remains unfinished.

This closes conditional quotient homotopy descent and continuous equivariant
lift construction. It does not yet prove that the constructed deck-group
homomorphism is bijective for a homotopy equivalence or equals the previously
bound fundamental-group deck isomorphism. An ambient lattice conjugator,
general homotopic-isometry existence, global target uniqueness and the full
Mostow–Prasad endpoint remain unfinished, including cusps and nonorientable
manifolds. All supplied compatible original-H3 geometric inputs of the
complete-target constructor remain explicit in that earlier result.


### The lift-induced deck homomorphism is the fundamental-group isomorphism

For the same coverings `F:X→M`, `P:Y→N`, continuous maps `φ:M→N`,
`L:X→Y` and all-point identity `P(L(x))=φ(F(x))`, mapping the actual lifted
path by `L` proves monodromy naturality. For the same quotient-covering
actions and a homomorphism `τ:G→H` satisfying `L(a•x)=τ(a)•L(x)`, this
identifies the opposite-group map of `τ` with the map on fundamental groups
through the two covering correspondences. When both covering spaces are
simply connected and `φ` is the forward map of an actual homotopy
equivalence, the existing induced fundamental-group equivalence and those
same covering equivalences prove that this same `τ` is bijective. Neither
bijectivity nor replacement by another deck homomorphism is assumed.

For the same actual original-H3 full-deck quotient coverings `FM,FN`, an
actual homotopy equivalence `h:M≃ₕN`, a supplied compatible H3 chart and any
source point `pHM`, target-cover surjectivity selects `pHN` with
`FN(pHN)=h(FM(pHM))`. The existing continuous lift constructor supplies
`L,τ`; the proved bijectivity promotes that very `τ` to a deck-group
isomorphism `d`, with `d.toMonoidHom=τ`. The same chosen lift retains its
basepoint, all-point projection and equivariance identities. The same `d`
implements `FundamentalGroup.map h.toFun (FM pHM)` through the two actual
covering fundamental-group equivalences. It is unique among deck-group
isomorphisms implementing that binding with those same chosen points.

A separate exact check compares this with the earlier binding written using
`FundamentalGroup.mapOfEq h.toFun rfl`: the reflexive endpoint cast equals
the ordinary induced map. For the same actual covers, compatible basepoints,
continuous lift, projection and equivariance, any deck isomorphism satisfying
that earlier binding has underlying homomorphism exactly `τ`. This closes
the previously recorded lift-induced deck-isomorphism binding gap; it does
not assert uniqueness of isometries on the target manifold.

Three serial scoped transient cache-guarded checks exited zero and printed
six axiom closures using only `propext`, `Classical.choice` and `Quot.sound`.
One rejected monodromy source/log pair and one rejected exact-binding pair
are preserved and excluded. Typed heterogeneous path equalities and the
existing reflexive-cast identity repair endpoint elaboration; explicit
homomorphism extensionality compares deck elements. Statements, endpoints,
actions and resource limits are retained. Two `haveILetI` style warnings
are recorded, one in each actual-H3 check; they are not proof exceptions.
These are classical compositions with no tracked Lean or novelty claim.
The linked escape audit remains unfinished.

An ambient lattice conjugator, general homotopic-isometry existence, global
target uniqueness and the full Mostow–Prasad endpoint remain unfinished,
including cusps and nonorientable manifolds. The supplied compatible
original-H3 geometric inputs of the complete-target constructor remain
explicit. The present result supplies the actual lift/deck-isomorphism
connection; it does not obtain an ambient isometry from an abstract lattice
isomorphism.


### A supplied conjugator yields the prescribed homotopic isometry

For an actual group isomorphism and isometric representations, the existing
conjugator-induced orbit map is continuous in the quotient topologies:
its composition with the source quotient projection is the target
projection composed with the same ambient isometry. Transporting that map
through the same supplied quotient homeomorphisms gives a continuous base
map `ψ`, with the all-point identity `FN(a(x))=ψ(FM(x))`.

For the same actual original-H3 full-deck quotient coverings, prescribed
homotopy equivalence `h`, continuous lift `L`, equivariant homomorphism `τ`
and deck isomorphism `d` with `d.toMonoidHom=τ`, suppose the actual
representations evaluate to those same deck actions and the supplied ambient
isometry `a` implements their conjugacy through that same `d`. The maps `L`
and `a` are then equivariant for the same source action and representation
`ρN∘d`. The target covering is invariant under that representation. The
already proved original-H3 interpolation descent therefore constructs a
homotopy from `h.toFun` to this same projected `ψ`. No desired base-map
homotopy is assumed, and no different deck isomorphism is substituted.

With properly discontinuous representations, the same ambient conjugator
maps each whole source orbit onto the corresponding target orbit; reverse
inclusion uses surjectivity of the same group isomorphism. Preservation of
point-to-set distance proves the existing orbit equivalence is an isometry
for the same orbit metrics. For metric bases with supplied quotient
isometries `eM,eN` satisfying `eM(qM(x))=FM(x)` and
`eN(qN(x))=FN(x)` at every actual H3 point, composition transports that very
orbit isometry to `e:M≃ᵢN`. Its all-point projection is
`FN(a(x))=e(FM(x))`, and its continuous map is homotopic to the prescribed
`h.toFun`. These quotient-to-base isometries remain supplied; no new target
metric or automatic geometric compatibility is asserted.

An exact application first selects the original-H3 lift, target fiber
point and fundamental-group-bound deck isomorphism from the previously
proved same-cover constructor, retaining its basepoint, all-point
projection, equivariance and fundamental-group binding. For those same
selected objects, every supplied pair of actual deck representations,
proper-action witnesses, compatible quotient isometries and ambient
conjugator has the stated homotopic isometry representative. A compatible
H3 chart remains supplied to the lift constructor.

Three serial scoped transient cache-guarded checks exited zero and printed
five axiom closures using only `propext`, `Classical.choice` and `Quot.sound`.
Two rejected orbit-isometry source/log pairs are preserved and excluded.
Repairs restore the existing metric/covering namespaces and explicitly
normalize the reverse orbit-image application before applying conjugacy;
statements, original-H3 metric, actions and resource limits are retained.
Five `haveILetI` style warnings and one unused-variable-name warning remain;
they are not proof exceptions. The latter names a conjugacy premise that
is used in the proof; the proposition does not explicitly reference the
name of that proof. These are classical compositions with no tracked Lean
or novelty claim. The linked escape audit remains unfinished.

This closes the conditional connection from the actual lift-induced deck
isomorphism and a supplied ambient conjugator to the prescribed homotopic
isometry. Ambient lattice conjugator existence and global target uniqueness
remain unfinished, as does the full Mostow–Prasad endpoint including cusps
and nonorientable manifolds. Compatible original-H3 geometric inputs of
the complete-target constructor remain explicit supplied premises. The
conditional construction does not prove the ambient conjugator exists.


### The same lift of a base map preserving distance is locally isometric

For metric covering spaces `X,Y`, extended metric bases `M,N`, maps
`F:X→M`, `P:Y→N`, a continuous lift `L:X→Y` and a base map `φ:M→N`
preserving distance, the all-point identity `P(L(x))=φ(F(x))` now proves
that `L` preserves every pairwise distance on a ball at each source point,
provided `F` and `P` themselves preserve all pairwise distances on a ball
at each of their points. Choose the source projection's ball and the
target projection's ball at `L(a)`; continuity of the same `L` provides a
source ball mapping into the latter. On the intersection radius, the same
projection identity and distance preservation of `φ,F,P` compare every
pair of lifted points. No global distance preservation of `L` is assumed.

An exact application uses the same actual original H3 on both covering
spaces, the same full-deck quotient coverings and their actual
representations evaluating to the deck actions. With supplied compatible
H3 and base manifold structures, base `T3Space` hypotheses, the same
Riemannian metrics, compatibility of the H3 intrinsic distance with the
original metric, local diffeomorphism of both coverings and preservation
of their tangent inner products, the existing covering distance theorem
supplies both local projection properties. A supplied continuous lift of
a base map preserving the actual intrinsic distances therefore has the
stated local distance property in the original H3 metric. No smoothness
of the base map or of the lift is assumed for this implication.

A further exact application takes a prescribed actual homotopy equivalence
whose forward map preserves those intrinsic distances. The earlier
same-cover constructor selects the target fiber point, continuous lift,
equivariant deck homomorphism and its deck isomorphism. Their same
basepoint, projection, all-point equivariance and fundamental-group binding
are retained, and that very selected lift now satisfies the local pairwise
distance conclusion. This covers the isometry case of the prescribed map;
it does not yet identify that lift as a full ambient H3 isometry.

Three serial scoped transient cache-guarded checks exited zero and printed
three axiom closures using only `propext`, `Classical.choice` and
`Quot.sound`. One rejected actual-H3 source/log pair is preserved and
excluded. Its first proposed telescope lacked the base `T3Space` instances
required to form the existing intrinsic extended metrics; those explicit
premises, already required in the earlier complete-target constructor,
were added in the accepted exact application. This telescope change is
recorded, and the earlier proposal is not accepted. Seven `haveILetI`
style warnings are recorded; they are not proof exceptions. The original
H3 metric, covering identities, actions and resource limits are retained.
These are classical compositions with no tracked Lean or novelty claim.
The linked escape audit remains unfinished.

The new result is local preservation of distance by the same actual lift.
Promoting such a lift to a full ambient isometry, proving general target
uniqueness, constructing the ambient lattice conjugator and completing the
full Mostow–Prasad endpoint remain unfinished, including cusps and
nonorientable manifolds. The compatible original-H3 geometric inputs
remain explicit supplied premises.


### A Lorentz linear equivalence induces an actual H3 isometry

A real linear equivalence of the same four-dimensional Lorentz coordinates
that preserves the bilinear kernel and maps one supplied actual H3 point
to another now yields a full isometric bijection of the original H3, with
that same linear equivalence agreeing with its coordinates at every point.
Neither an ambient isometry nor positivity at every point is assumed.

The original H3 contractibility supplies connectedness. For every H3
point the transformed coordinate vector has self-kernel one; its light
difference cannot vanish, since vanishing would make that self-kernel the
negative sum of two squares. Continuity of the same linear equivalence
and the established coordinate map, together with the intermediate value
theorem and positivity at the supplied mapped point, forces positive
light difference everywhere. Kernel preservation by the inverse and the
same mapped-point identity give the inverse positivity statement. The
established future-unit inverse therefore constructs both maps. Their
coordinate identities and the existing coordinate injectivity prove both
inverse laws. The same Lorentz kernel/cosh-distance identity and cosh
injectivity on nonnegative distances prove preservation of the original
H3 metric.

One serial scoped transient cache-guarded check exited zero with two axiom
closures containing only propext, Classical.choice and Quot.sound. One
haveILetI style warning is recorded, with no rejected converse source.
Default resources and the original metric are retained. This is classical
reuse/composition; no tracked Lean or novelty claim.

This is a converse model interface. It does not yet construct a Lorentz
linear equivalence extending an arbitrary locally distance-preserving
lift; small spanning frames inside arbitrary neighborhoods and their
local extensions remain to be proved. Global lift identification, general
target uniqueness, ambient lattice conjugator existence and the full
finite-volume cusped/nonorientable Mostow–Prasad endpoint remain open.
The linked escape audit remains unfinished; new registrations are paused
by the synchronized repository instructions.


### From local distance preservation to the same full ambient H3 isometry

The local-to-global metric obligation is now discharged in the original
H3: any map that preserves every pairwise distance on some positive ball
at every point equals a unique full original-H3 isometric bijection at
all points. No smoothness, global distance preservation, injectivity,
surjectivity, orientation or supplied linear extension is assumed. The
map need not be supplied as continuous for this implication. Uniqueness
here concerns the full ambient isometry agreeing with this same map.

The small-frame gap identified above is now closed. At the reference
point, the four coordinate points (0,1), (0,1+d²), (d,1) and (di,1) vary
continuously with the real parameter d and coincide at d=0. For d>0,
their Lorentz vectors are independent: the two horizontal coordinates
detect two coefficients, the nonzero vertical coordinate detects the
third, and the time coordinate detects the fourth. A sufficiently small
positive parameter places all four in any reference ball. The existing
actual H3 transitivity and its Lorentz representation transport this
frame into any positive-radius ball without changing the metric.

For a map preserving all pairwise distances on such a ball, the image
frame has the same Lorentz Gram matrix. Basis expansion and the same
nondegenerate kernel prove its independence. The resulting real linear
basis equivalence preserves the kernel everywhere, and distances to the
frame prove its coordinate agreement with the map at every point of the
same ball. The preceding Lorentz converse supplies a full ambient
isometry agreeing there. Two actual ambient isometries agreeing on any
positive ball agree everywhere, by the contained spanning frame and the
existing coordinate representation. Choose one local extension; the
points where it agrees with the map on a neighborhood form a nonempty
open and closed set. At a closure point, another local extension overlaps
one of those neighborhoods; ball agreement forces the two extensions
equal. Original H3 contractibility supplies connectedness, giving the
same full isometry at every point. This propagates neighborhood agreement
rather than only equality at one point.

The exact application retains the previously constructed target fiber
point, continuous lift L, homomorphism tau and deck isomorphism d for the
prescribed intrinsic-distance-preserving homotopy equivalence. It keeps
d.toMonoidHom=tau, the basepoint equality, projection, equivariance,
fundamental-group binding and local extended-distance identities. The
latter are converted to distances in the original metric. The new full
ambient isometry equals that same L at every point, and its exact
conjugacy of the supplied actual full-deck representations follows from
that same equivariance. Uniqueness is only among ambient isometries
pointwise equal to this selected L; it is not general uniqueness of
isometric representatives in a homotopy class. Compatible original-H3/base
structures, T3Spaces, intrinsic metric compatibility, local covering
diffeomorphisms, tangent inner preservation and forward intrinsic
distance preservation remain supplied in this application.

Five serial scoped transient cache-guarded checks, including the earlier
reviewed Lorentz converse, exited zero and printed twelve axiom closures
using only propext, Classical.choice and Quot.sound. 3 style warnings
are recorded. Two rejected small-frame source/log pairs are preserved
and excluded; normalized zero equations produced disjunctions, and a
local parameter-continuity helper needed explicit real-domain types. The
repairs keep the theorem telescopes and original metric unchanged. No
resource increase, suppression, tracked Lean or novelty claim is made.

This closes the metric local-to-global lift step, including its exact
same-lift/deck-isomorphism application for an already distance-preserving
prescribed map. It does not prove an arbitrary homotopy equivalence has
an isometric representative, ambient lattice conjugator existence,
general target uniqueness or the full finite-volume cusped/nonorientable
Mostow–Prasad endpoint. The compatible original geometric inputs remain
explicit. The linked escape audit is unfinished; new registration work
remains paused by the repository instructions.


### Homotopic actual isometries are unique for the same compatible covers

The homotopy-class uniqueness step is now proved under the same explicit
compatible original-H3/base geometric and full-deck-cover hypotheses.
For ordinary metric bases whose distances agree with the supplied
intrinsic metrics, and finite intrinsic volume of the source, every
prescribed homotopy equivalence has at most one actual isometric
bijection homotopic to it. The prescribed homotopy equivalence need not
itself preserve distance in this final statement. The theorem is exactly
the existing UniqueIsometryRepresentative predicate. It does not assert
that an isometric representative exists. No compactness, orientation,
dense-orbit, separately supplied centralizer or separately supplied
faithfulness premise is added to that final statement.

A generic covering-homotopy composition starts with the same supplied
continuous lift and equivariant deck homomorphism. The actual base
homotopy pulls back along the source projection and lifts continuously
through the target covering. At every source point, uniqueness of lifted
paths on the unit interval compares source deck action with target action
through that same homomorphism; their initial equality is precisely the
original equivariance. Consequently the lifted homotopy retains that same
homomorphism at every time and point, and its endpoint projects to the
other base map. No based or relative homotopy condition is assumed.

The exact H3 composition first treats a prescribed intrinsic-distance-
preserving homotopy equivalence and another continuous intrinsic-distance-
preserving map homotopic to it. The earlier constructor supplies the same
lift/tau/d and its full ambient isometry. The lifted base homotopy starts
from that lift and keeps tau, so its endpoint becomes another full H3
isometry through the established local metric and global extension
theorems. Both ambient isometries realize the same d and actual deck
representations. The existing actual finite-volume centralizer theorem
and existing conjugator-uniqueness theorem make them equal; source-cover
surjectivity then makes the two base maps equal. The finite-volume
centralizer is proved by the earlier library result, not supplied as a
new hypothesis.

For two ordinary base isometries homotopic to an arbitrary prescribed
homotopy equivalence, compose their actual homotopies, use the first
isometry's homotopy equivalence, and obtain intrinsic distance preservation
from the explicit metric compatibility. The faithful source representation
is derived from the same full-deck-cover evaluation injectivity and its
all-point evaluation identity. The resulting base-map equality is the
required actual isometry equality. Compatible H3/base smooth structures,
original/intrinsic distance compatibility, metric covering local
diffeomorphisms, tangent inner preservation, base measurability/Borel
structure and source finite intrinsic volume remain explicit.

Two accepted serial scoped transient cache-guarded checks exited zero
with three axiom closures using only propext, Classical.choice and
Quot.sound. 7 warning headers are recorded, including one unused-
tactic warning and the remaining haveILetI style warnings. Two exact
failed source/log pairs are preserved and excluded; direct evaluation
and composition expressions required explicit beta-normalization before
rewriting. The prior accepted final statement with separately supplied
source faithfulness is preserved, while the stronger accepted final
statement discharges that premise from the same cover rather than
supplying it. Its validity delta and the unchanged first implication's
scope are recorded. Default resources and all original metrics are
retained; no suppression, tracked Lean or novelty claim.

This closes homotopy-class isometry uniqueness for the supplied compatible
actual covers. Existence of an isometric representative for an arbitrary
homotopy equivalence, existence of its ambient lattice conjugator and
discharge of canonical original-H3 geometry remain open. The full
finite-volume cusped/nonorientable Mostow–Prasad endpoint remains active
and incomplete. The linked escape audit is unfinished, and new
registration work remains paused.


### Complete negative-curvature bases: uniqueness with constructed H3 covers

The canonical original-H3 geometry and actual target covers constructed
earlier are now integrated into the homotopy-class uniqueness statement.
For connected smooth three-dimensional Riemannian metric bases M and N,
with actual Levi-Civita data, complete intrinsic metrics, sectional
curvature -1 on every nondegenerate tangent two-plane, finite intrinsic
volume of M, and ordinary distances agreeing with both intrinsic metrics,
every prescribed homotopy equivalence has at most one actual isometric
bijection homotopic to it. M also carries a measurable/Borel structure.
This proves the existing UniqueIsometryRepresentative predicate and
asserts no existence of an isometric representative. No compactness,
orientation, target finite-volume, dense-orbit, separately supplied
centralizer or separately supplied faithfulness premise is used.

The final statement supplies no H3 chart or Riemannian metric, original-H3
distance identity, covering maps, full-deck quotient structure, covering
local diffeomorphisms, tangent inner-preservation identities, actual deck
representations or all-point evaluation identities. Those objects and
facts are obtained together from the earlier
hyperbolicRiemannianSourceAndCompleteOrbitIsometricDeckBridge. Choose the
constructed H3 smooth structure and metric, and apply that same
constructor's actual full-deck-cover clause to M and N, using connected
nonemptiness and an actual H3 point. Its intrinsic-distance identity is
the original hyperbolic distance; the original metric's edist_dist gives
the required ordinary/intrinsic equality on H3. Apply the previously
accepted same-cover uniqueness theorem to these exact constructed
objects. The prescribed homotopy equivalence need not preserve distance.
This is classical reuse and exact composition of existing results, not
a new rigidity theorem or a tracked Lean declaration.

Actual LeviCivitaData for both base metrics remains an explicit geometric
input, together with its sectional-curvature hypotheses. The upstream
global exists_leviCivitaData API requires T2Space and
SecondCountableTopology; MetricSpace alone does not supply second
countability. This composition neither silently adds that hypothesis nor
claims global connection existence without it. The stated completeness,
curvature, source volume, measurable/Borel and metric-compatibility
conditions remain in the exact theorem telescope.

One accepted serial scoped transient cache-guarded Lean check exited zero.
The exact complete_negative_three_manifold_isometry_homotopy_class_unique
declaration has a single axiom closure using only propext,
Classical.choice and Quot.sound. Four haveILetI style warnings are
retained. An earlier exact source/log pair exited one because an unused
finite-tail index universe in the old constructor was unresolved; that
attempt is preserved and excluded. The repair explicitly instantiates
the constructor at universes u and 0, keeping geometric target types in
Type u. The theorem telescope and consequent are byte-identical before
and after this repair. Default resources and original metrics are
retained, with no suppression or compiler replay claim. All new Lean
remains transient under ignored .lake; only this research note is tracked.

The preceding appendix's reference to an open canonical-H3 geometry
obligation described integration into its then-current supplied-cover
statement. It did not mean the earlier source geometry and actual target
covers were absent. This composition closes that integration for the
uniqueness half under the base geometric conditions above. Existence of
an isometric representative for an arbitrary homotopy equivalence and
existence of its ambient lattice conjugator remain open. The full
finite-volume Mostow-Prasad endpoint, including cusps and nonorientable
manifolds, remains active and incomplete. The linked escape audit is
unfinished, and new registration work remains paused.


### Constructing an ambient conjugator from scaled future-null-cone data

An independent conditional existence bridge now constructs an actual
original-H3 ambient isometry from concrete Lorentz cone data. On the
existing signature-(1,3) kernel B on Fin 4 -> R, use the future null cone
{v | v(0) > 0 and B(v,v) = 0}. Suppose a map F preserves B(u,v) for every
pair of cone vectors and has positive time coordinate on every cone
image. Then there is an actual H3 isometry whose full Lorentz action
agrees with F on every cone vector. F is presented as a total vector
function for convenience; only its restriction to the cone is constrained
or identified with a linear action. No linearity, continuity, surjectivity,
ambient linear equivalence, interior isometry, local distance preservation
or ambient conjugator is supplied.

The four explicit future null vectors (1,1,0,0), (1,-1,0,0), (1,0,1,0)
and (1,0,0,1) span the Lorentz vector space. Their images have the same
Gram matrix. Using the existing basis kernel-detection theorem, derive
image linear independence and obtain a full linear equivalence by
transporting the two bases. Expand both arguments in that basis to prove
kernel preservation on the entire vector space. Pairing with the image
basis then shows that this same equivalence agrees with F at every cone
vector, not just the four frame vectors. These are scaled null vectors,
not merely projective ideal-boundary points.

The actual reference hyperboloid point is half the sum of the first two
null vectors. The positive time coordinates of their images put the
constructed image of this point on the future unit sheet. The existing
explicit Lorentz future-point inverse and Lorentz converse then construct
an isometry of the original upper-half-space metric. Its faithful actual
Lorentz representation is exactly the constructed linear equivalence.
No supplied frame-image basis or supplied future-sheet interior point is
used.

For arbitrary abstract groups G,H, an isomorphism d:G ~=* H and actual
H3 isometric representations rho and sigma, add the exact all-cone-point
equivariance F(R(rho(g))v)=R(sigma(d(g)))F(v), where R is the existing
actual full Lorentz representation. The same constructed ambient isometry
a then satisfies sigma(d(g))=a*rho(g)*a^-1 for every g, and its cone action
still agrees with the same F at every cone vector. Actual H3 isometries'
future-null-cone preservation is proved from kernel preservation and the
positive time of actual hyperboloid coordinates, not supplied as an
extra action hypothesis. Equivariance on the spanning null frame makes
the two linear compositions equal; faithfulness of the actual Lorentz
representation yields the required original-H3 isometry equality.

Future preservation is material. The accepted countermodel F(v)=-v
preserves every Lorentz pairing, yet its future-cone restriction cannot
be the Lorentz action of any actual original-H3 isometry. This exhibits
why preserving the kernel alone does not select the required time sheet.
The construction imposes no compactness, orientation, dense-orbit,
faithfulness of the supplied group representations or finite-volume
hypothesis: its stronger geometric cone data are explicit input.

Two accepted serial scoped transient cache-guarded Lean checks exited
zero, with ten axiom closures using only propext, Classical.choice and
Quot.sound and no warning headers. Three exact failed source/log pairs
are preserved and excluded, including their failed sorryAx closures.
Default resources and
original metrics are retained; no suppression, compiler replay, novelty
or tracked Lean claim. These are classical finite-dimensional Gram and
hyperboloid constructions checked under ignored .lake. The standard
hyperbolic-model framework is discussed in Foundations of Hyperbolic
Manifolds (Springer; DOI 10.1007/978-0-387-47322-2); public bibliography
metadata identifies that reference but is not evidence for an exact
theorem page or a completed formalization.

This closes a sufficient cone-data-to-ambient-conjugator construction,
not ambient conjugator existence for arbitrary lattice isomorphisms.
Existence of the required future-cone map, its exact pairing preservation
and equivariance for the SAME arbitrary-h induced deck isomorphism remain
open. Projective boundary-map construction, cross-ratio lifting and the
rigidity argument forcing the necessary boundary geometry are separate
obligations. Finite volume has not been shown to supply these cone inputs.
The full finite-volume Mostow-Prasad endpoint, including cusps and
nonorientable manifolds, remains active and incomplete; arbitrary-h
isometric representative existence remains unproved. The linked escape
audit is unfinished and registration remains paused. Only this research
note is intended tracked delivery.


### Actual H3 horizontal contraction and the Mautner mechanism

For a jointly continuous isometric action of a group on a metric space,
let a_i act asymptotically trivially on x along a nonempty filter. If
a_i*g*a_i^-1 tends to the identity along the same filter, then g fixes x.
The pseudometric version gives dist(g*x,x)=0; metric separation yields
point equality. This local Mautner argument needs neither a Hilbert
space nor compactness, properness or finite volume. The nonempty-filter
condition is essential: for the actual continuous isometric translation
action of the additive real line, the bottom filter satisfies both
convergence conditions, while translation by 1 moves 0.

This mechanism applies to the SAME actual original-H3 isometry group
with its previously constructed compact-open topology. Horizontal
translation T(u), u in C, is jointly continuous in u and the H3 point,
using the original coordinate homeomorphism. Consequently u -> T(u) is
continuous into that compact-open isometry group. For positive r_i
with r_i -> 0, the actual identity

    D(r_i)*T(u)*D(r_i)^-1 = T(r_i*u)

and this continuity derive convergence to the identity. Conjugation
convergence is proved for the original H3 translations and dilations;
it is not an extra premise supplied to the H3 application. Any jointly
continuous isometric action of this SAME group on a metric space
therefore satisfies: if D(r_i)*x -> x along a nonempty filter, every
horizontal translation fixes x. In particular, invariance under all
positive dilations implies invariance under all horizontal translations,
using r_n=(1/2)^n.

There is also an exact finite-p Lp application of the continuous
isometric domain-pullback action. Its domain action must be continuous
and measure preserving, the measure locally finite and inner regular
on compact sets below infinite mass, and the domain must carry the
stated Borel and R1 structures. The target is a normed additive group,
and 1 <= p < infinity. These hypotheses remain explicit. Pullback uses
DomMulAct, whose multiplication reverses the original group product.
Accordingly choose a_i=mk(D(r_i)^-1). Its conjugation of mk(T(u)) is
mk(D(r_i)*T(u)*D(r_i)^-1), so the actual H3 contraction proves contraction
in this opposite group too. Asymptotic inverse-dilation pullback
invariance of f then implies every horizontal pullback fixes f.
Invariance under every positive dilation supplies the required inverse
invariance by the actual dilation inverse formula. No contraction
hypothesis is supplied to these H3 Lp conclusions.

The original-H3 isometry-group topology, joint evaluation, topological
group structure and finite nonzero invariant group-quotient measures
were already constructed. They are available inputs, rather than
missing constructions. The new Lp application is checked for domain
actions satisfying its explicit hypotheses; it has not yet been
instantiated with the previously constructed actual quotient measure
and its required regularity. Neither finite quotient mass alone nor
horizontal invariance alone proves the needed ergodicity.

Five accepted serial scoped cache-guarded transient Lean checks exited
zero, with eleven axiom closures using only propext, Classical.choice
and Quot.sound and no warning headers. Failed checks are excluded from
these accepted readings. All new Lean remains under ignored .lake;
these are classical reuse and construction, with original metrics and
default resources, no novelty or tracked-Lean claim.

Subgroup generation, the actual quotient Lp specialization, flow
ergodicity and the boundary rigidity argument remain separate
obligations. Unipotent generation concerns the identity component:
for an orientation-preserving lattice, the full disconnected isometry
group quotient has two components. Full-group ergodicity cannot be
inferred from the geodesic flow on that quotient; an orientation
component or orientation-cover argument is still required. The boundary
map and its geometric preservation for the SAME arbitrary-h induced
deck isomorphism remain unconstructed. Full finite-volume
Mostow-Prasad, including cusps and nonorientable manifolds, remains
active and incomplete. The linked escape audit is unfinished and
registration remains paused. Only this research note is tracked.


### The actual finite quotient measure and its L2 domain action

On the SAME original-H3 compact-open isometry group G, let Gamma be a
closed subgroup. Every finite measure on the coset space G/Gamma with
its ORIGINAL quotient measurable structure is regular. The existing
locally compact, Hausdorff and second-countable quotient topology gives
sigma compactness and a compatible metrizable topology; the existing
Polish group structure identifies the quotient measurable structure
with its Borel structure. The finite-measure regularity theorem then
supplies compact inner regularity and local finiteness. The original
H3 metric and isometry-group topology are preserved. No normality of
Gamma is required, and no new quotient measurable structure replaces
the one used by the existing quotient-measure constructor.

For a finite G-invariant measure nu on this actual coset domain, a
normed additive target and 1 <= q < infinity, the existing jointly
continuous isometric domain-pullback action therefore applies to
Lp(nu). Regularity and continuous action are derived from this actual
quotient, rather than supplied as separate hypotheses. If every
positive actual dilation pullback fixes f, every actual horizontal
translation pullback fixes f. The reverse multiplication of DomMulAct
and the inverse-dilation contraction proved in the preceding appendix
remain the mechanism. Invariance under ALL positive dilations is a
material premise, not a conclusion obtained from finite volume.

The geometric specialization selects the SAME nu already produced by
the actual finite-target quotient-measure construction. Its data are
Riemannian metrics on original H3 and a base M, compatibility of the H3
metric with its original distance, a quotient covering by the FULL deck
group, a local diffeomorphism preserving the tangent inner products,
and an injective actual-H3 isometric deck representation whose point
evaluation agrees with the original deck action. Base intrinsic volume
is finite. The existing construction supplies nu on G/rho.range,
G-invariance, finite nonzero mass and total mass equal to that intrinsic
base volume. The closedness of the ACTUAL deck image is derived from
the same covering and representation data. With its original measurable
carrier, this same nu now supports the exact real L2 application:
for every f in L2(nu), if all positive dilation pullbacks fix f, all
horizontal-translation pullbacks fix f. Neither nu, its regularity nor
a continuous quotient action is supplied to this geometric statement.
The stated geometric hypotheses remain explicit; this is not a theorem
from finite base volume alone.

One accepted serial scoped cache-guarded transient Lean check exited
zero, with three axiom closures using only propext, Classical.choice
and Quot.sound. Four haveILetI style warnings are retained without
suppression. Failed checks are excluded from the accepted readings.
All new Lean remains under ignored .lake; these are classical reuse and
construction with default resources and the original metric/topology,
not a novelty or tracked-Lean claim.

This supplies the actual quotient regularity/action integration left
open in the preceding appendix. It proves a consequence of all-positive-
dilation fixing; it does not establish the required invariant-function
constancy or flow ergodicity. Actual H3 subgroup generation, opposite
unipotent invariance, boundary-map construction and geometric
preservation for the SAME arbitrary-h induced deck isomorphism remain
separate obligations. Orientation components and covers still need
explicit treatment: the full disconnected isometry-group quotient has
two components for an orientation-preserving lattice. Cusps and the
nonorientable endpoint remain in the full target. Arbitrary-h ambient
conjugator and isometric representative existence are still unproved,
and full finite-volume Mostow-Prasad remains active and incomplete.
The linked escape audit is unfinished and registration remains paused.
Only this research note is intended tracked delivery.


### Actual inversion-conjugate horizontal contraction and light-null charts

Let J be the existing boundary-centered inversion of ORIGINAL H3,
T(v) its actual horizontal translation, and D(a) its actual positive
dilation. The actual coordinate inversion and norm scaling give
J inverse = J and J D(a) = D(a) inverse J for a > 0. Thus
J D(a) J inverse = D(a) inverse. Define Uminus(v) = J T(v) J inverse.
The derived identity

D(r) inverse Uminus(v) D(r) = J (D(r) T(v) D(r) inverse) J inverse

and the existing horizontal contraction imply convergence to identity
as positive r tends to zero, in the SAME compact-open group topology.
The original H3 metric and group topology are preserved. Neither the
inversion/dilation relation nor the opposite contraction is supplied
as a hypothesis. Here the opposite family means this actual
inversion-conjugate family; a matrix-unipotent identification and
its generation of the orientation component remain unproved.

For a jointly continuous isometric action of this actual group on a
metric space, if ALL positive D(a) fix x, every Uminus(v) fixes x.
The finite-p domain-pullback version retains a Borel R1 domain with a
continuous group action, an invariant measure that is locally finite
and compact inner regular, a normed additive target, and
1 <= q < infinity. If ALL positive dilation pullbacks fix f in Lp,
every Uminus(v) pullback fixes f. DomMulAct reverses multiplication:
this opposite contraction uses the sequence mk(D(r)), whereas the
preceding horizontal-family argument uses mk(D(r) inverse).

On the SAME actual closed coset quotient G/Gamma with its ORIGINAL
quotient measurable structure and a finite G-invariant measure nu,
regularity and the continuous domain action are derived by the
preceding construction. For a normed additive target and
1 <= q < infinity, every f in Lp(nu) fixed by ALL positive dilation
pullbacks is fixed by BOTH T(v) and Uminus(v) pullbacks. The geometric
real-L2 specialization selects the SAME finite nonzero nu from the
preceding actual finite-target constructor and preserves total mass
equal to base intrinsic volume. Its full hypotheses remain: original
H3 and base Riemannian metrics with original-H3 distance compatibility;
the base T3/Borel/manifold and H3 manifold structures; a quotient
covering by the FULL deck group; a local diffeomorphism preserving
tangent inner products; an injective actual-H3 isometric deck
representation whose evaluation agrees with the original deck action
at EVERY point; and finite intrinsic base volume. Closedness of the
actual deck image is derived from those same data. The selected nu,
its regularity and its quotient action are not supplied as placeholders.
For every real L2 f on this SAME nu, ALL-positive-dilation fixing
implies BOTH horizontal-family invariances. The dilation-fixing
premise is not obtained from finite volume.

The existing Lorentz light coordinates also now give an explicit
scaled chart of every future Lorentz-null vector w. Its light
coordinates are c times either (1,0,0,0) or
(re(z)^2+im(z)^2,re(z),im(z),1), for c > 0 and z in the complex plane.
The null equation and positive time coordinate yield a nonnegative
last light coordinate. If it is zero, the two middle coordinates
vanish and the first is positive. Otherwise c is the last coordinate
and z is obtained by dividing the middle coordinates by c. The SAME
existing infinity frame (1,0,0,1) has light coordinates twice
(1,0,0,0). Existing actual-isometry future-null-cone preservation
therefore gives this scaled chart for EVERY actual isometry's image
of that frame, without supplying null, future or chart data for the
isometry. Positive scaling is retained; no projective boundary
topology, boundary action or boundary map between lattices is claimed.

Three serial scoped cache-guarded transient Lean checks exited zero,
with twelve axiom closures using only propext, Classical.choice and
Quot.sound. Four haveILetI style warnings in the actual quotient
application remain unsuppressed; the other two checks have no warnings.
These are classical reuse and construction under ignored .lake with
default resources, not a novelty or tracked-Lean claim.

Actual orientation-component identification/generation, invariant-
function constancy and flow ergodicity remain separate obligations.
The full disconnected group quotient has two components when the
lattice preserves orientation; component and orientation-cover
arguments remain necessary for the nonorientable endpoint. Boundary
map construction and geometric preservation for the SAME arbitrary-h
induced deck isomorphism, cusp handling and arbitrary-h ambient
conjugator/isometric representative existence remain unproved.
Full finite-volume Mostow-Prasad remains active and incomplete.
The linked escape audit is unfinished and registration remains paused.
Only this research note is intended tracked delivery.


### Actual two-family words normalize the infinity ray and height

The original horizontal translation and boundary-centered inversion
now have coordinate-derived linear actions in the SAME Lorentz light
coordinates. For an arbitrary real four-vector v and complex z,
T(z) acts by

(v0 + 2 re(z) v1 + 2 im(z) v2 + (re(z)^2+im(z)^2) v3,
 v1+re(z) v3, v2+im(z) v3, v3).

The original inversion J acts by (v3,v1,v2,v0). These actions are
derived first on every actual H3 point from the original coordinates,
height and inversion radius formula, then extended to every vector
using the SAME spanning Lorentz frame. Neither action is supplied
as a boundary or matrix hypothesis.

Let H be the algebraic subgroup generated by the two actual families
T(z) and Uminus(z)=J T(z) J inverse. The concrete actual word
W=T(1) Uminus(-1) T(1) belongs to H. Its light action is
(v3,-v1,v2,v0). For every complex z, W T(-z) sends the finite
light-null chart (re(z)^2+im(z)^2,re(z),im(z),1) to
(1,0,0,0). The preceding positive scaled-chart constructor therefore
normalizes the infinity-frame image of EVERY actual original-H3
isometry e: there are an actual g in this SAME H and c > 0 such that
the light coordinates of L(g e)(1,0,0,1) are c(1,0,0,0).
Here H is algebraically generated, and g is an actual word chosen
from the actual image chart; no density or full-group equality is
asserted. Positive scale is retained.

For every actual original-H3 isometry k, if its Lorentz action sends
the SAME original infinity frame (1,0,0,1) to a times that frame for
a real scalar a, the existing actual future-cone preservation implies
a > 0. Actual Lorentz pairing preservation and the original identity
v0-v3=1/height then imply height(k p)=a height(p) at EVERY actual
point p. Positivity and the height law are derived; neither is an
additional premise. Applying this to the normalized g e above gives
a=c/2 > 0, L(g e)(1,0,0,1)=a(1,0,0,1), and uniform positive height
scaling at every point. This reduces the next classification task
to the actual infinity-ray stabilizer with a proved height law.
It does not yet classify the remaining horizontal action.

Two accepted serial scoped cache-guarded transient Lean checks exited
zero, with eleven axiom closures using only propext, Classical.choice
and Quot.sound. Two unnecessarySeqFocus style warnings remain
unsuppressed in the light-action check; the height check has none.
Failed checks are excluded in full. The original H3 metric/topology
and default resources are retained. All new Lean remains under
ignored .lake as classical reuse and construction, without novelty
or tracked-Lean claims. Only this research note is intended delivery.

The full actual stabilizer classification, orientation-component
identification/generation, invariant-function constancy and flow
ergodicity remain unproved. The normalization constructs no boundary
topology/action or lattice boundary map. The SAME arbitrary-h induced
deck isomorphism still needs its boundary-map/geometric-preservation
and ambient-conjugator/isometric-representative existence arguments.
Cusps, orientation components and covers, and the nonorientable
endpoint remain in scope. Full finite-volume Mostow-Prasad remains
active and incomplete; the linked escape audit is unfinished and
registration remains paused.


### Actual infinity-ray stabilizer: Euclidean horizontal normal form

For an actual isometry k of the ORIGINAL H3 and a real scalar a,
assume its actual Lorentz action sends the SAME original infinity
frame (1,0,0,1) to a times that frame. The previously checked result
derives a > 0 and height(k p)=a height(p) at every point. Under this
same frame-fixing hypothesis, the remaining horizontal action is now
classified: there are a single complex b and a single unit complex u
such that ONE of the following alternatives holds at EVERY point
p=(z,t):

horizontal(k p) = b + a u z,

or

horizontal(k p) = b + a u conjugate(z).

Together with the height law, these are the actual coordinate normal
forms (b+a u z,a t) and (b+a u conjugate(z),a t). The branch is global;
it is not selected separately at each point. No horizontal similarity,
linearity, surjectivity, positivity or height law is supplied as an
additional premise.

The argument uses the original Lorentz-kernel/cosh-distance formula
for arbitrary actual points. Compare the points (z,t) and (z,1):
the known image heights force the squared horizontal displacement
between their images to vanish. Thus the horizontal map q(z), defined
at height 1, is independent of input height. Comparing (z,1) and
(w,1) gives dist(q(z),q(w))=a dist(z,w). Actual surjectivity of k,
applied to (w,a), and the height law yield surjectivity of q.
Consequently a inverse times q is an actual surjective Euclidean
isometry of the complex plane. Existing Mathlib Mazur-Ulam constructs
its real linear isometry after subtracting its value at zero;
Mathlib's linear_isometry_complex and rotation_apply give the global
rotation or rotation-after-conjugation alternative. This is classical
reuse and construction, without a novelty claim.

The exact application to an arbitrary actual H3 isometry e is also
checked: the preceding actual two-family word constructor supplies
g in the SAME algebraically generated subgroup H and a > 0 with
L(g e)(1,0,0,1)=a(1,0,0,1). The SAME g e then has both the every-point
height law and one of the two global horizontal formulas above, with
one b and one u. This gives a coordinate normal form after an actual
generated word; it does not identify H with the whole isometry group
or its orientation-preserving component.

Two serial scoped cache-guarded transient Lean checks exited zero:
the horizontal-classification module has five printed axiom closures
and its exact universal word application has one. All six use only
propext, Classical.choice and Quot.sound. Five unusedSimpArgs style
warnings remain unsuppressed in the classification check; the exact
application has none. Failed checks are excluded in full. The
original carrier, metric, topology, Lorentz frame and default compiler
resources are retained. All new Lean remains under ignored .lake;
only this research note is intended tracked delivery.

This appendix advances the earlier unfinished horizontal-action
classification. A converse stabilizer/group identification,
orientation-component identification and generation, invariant-function
constancy and flow ergodicity remain unproved. No lattice boundary map
or ambient conjugator for the SAME arbitrary-h induced deck isomorphism
has been constructed. Its geometric preservation and the prescribed
homotopy equivalence's isometric representative still need proof.
Cusps, orientation components and covers, and the nonorientable
finite-volume endpoint remain in scope. Full Mostow-Prasad remains
active and incomplete. The escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549
Registration remains paused under CLAUDE section 3.9.


### Actual generated subgroup and the two determinant cosets

Let H remain the SAME algebraic subgroup generated by the actual
original-H3 horizontal translations T(z) and Uminus(z)=J T(z) J
inverse, with J the SAME original inversion. The preceding actual
infinity-ray normal form now leads to an algebraic classification
of the full actual isometry group: H is exactly the kernel of the
actual light-representation determinant homomorphism, and EVERY
actual isometry belongs to exactly one of H and the right coset H J.
The determinant takes values 1 and -1, respectively. This identifies
the determinant subgroup; identification with manifold orientation
or the topological connected component is not yet claimed.

The generated similarities are constructed as actual finite words.
For nonzero complex v, put n=normSq(v)>0 and

W(v)=T(v) Uminus(-n inverse times v) T(v),

D(v)=W(v) W0, where W0=T(1) Uminus(-1) T(1).

Both words lie in the SAME H. Using the already checked actual T/J
light actions, the derived light action of D(v) on EVERY real
four-vector x is

(n x0,
 (re(v^2) x1-im(v^2) x2)/n,
 (im(v^2) x1+re(v^2) x2)/n,
 x3/n).

Apply this to each actual original-H3 point and use the original
light-coordinate formula and positive heights. At EVERY point
p=(z,t), D(v) has horizontal coordinate v^2 z and height n t.
No coordinate similarity or linear action is supplied as a premise.
For any complex translation b and nonzero complex coefficient c,
Mathlib Complex.isSquare supplies v with c=v^2. Nonzero c implies
v is nonzero; norm multiplicativity gives normSq(v)=norm(c).
Thus the actual T(b) D(v) in H realizes

(z,t) -> (b+c z, norm(c) t)

at EVERY actual point. Any actual isometry with these every-point
coordinate formulas equals the constructed member of H, using
extensionality of the original horizontal and height coordinates.
This is classical reuse and construction, not a novelty claim.

To handle the global reflection alternative, construct the actual
Q=W0 J. Its derived light action is (x0,-x1,x2,x3); the original
point coordinates then give height(Q p)=height(p) and
horizontal(Q p)=-conjugate(horizontal(p)) at EVERY point. Applying
these formulas twice and using original point extensionality gives
Q Q=1. Neither its reflection law nor its involution is assumed.

For arbitrary actual e, the previous normalization gives the SAME
g in H and k=g e with positive a, original infinity-frame scaling,
every-point height multiplication by a, and one global horizontal
rotation or reflection formula with a single b and unit complex u.
In the rotation case, c=a u is nonzero with norm(c)=a, so k belongs
to H by the actual similarity construction. Hence e belongs to H.
In the reflection case, k Q has the global horizontal formula
b-a u z and the same height multiplier a, so k Q belongs to H.
Since Q=W0 J and Q Q=1, the actual member
s=g inverse (k Q) W0 of H satisfies e=s J. This proves covering by
at most two actual algebraic cosets before any determinant argument.
The SAME e, g, a, original frame and generated subgroup are retained
throughout; no abstract component or group-generation premise is
substituted.

The actual light representation is a group homomorphism, and its
linear-equivalence determinant gives a homomorphism delta into the
nonzero real units. Its real value equals the determinant of the
SAME actual light matrix. The actual T(z) matrix is upper triangular
with diagonal entries all 1, so delta(T(z))=1. Multiplicativity and
inversion imply delta(Uminus(z))=1. Algebraic subgroup closure then
places H inside the kernel of delta. Q has diagonal light matrix
(1,-1,1,1), so delta(Q)=-1. Since W0 belongs to H and Q=W0 J,
delta(J)=-1. The actual two-coset covering therefore gives, for
EVERY actual e,

e belongs to H if and only if delta(e)=1.

The exact application also checks that the covering alternatives
cannot both hold and that delta(e) is always 1 or -1. Thus the two
cosets are distinct, not merely an upper bound on their number.
No determinant value, disjointness, kernel identity or full actual
coset cover is supplied as a premise.

Seven accepted serial scoped cache-guarded transient Lean checks
exited zero, with twenty-one printed axiom closures using only
propext, Classical.choice and Quot.sound. Four unusedSimpArgs style
warnings remain unsuppressed: three in the square-word light check
and one in the determinant check. The other five checks have none.
Six failed modules are preserved and excluded in full, including
partial good closures and the failed kernel-timeout attempt. No
resource, transparency or suppression option was increased. The
original H3 carrier, metric, topology, Lorentz/light frame and actual
transformations remain intact. All new Lean is under ignored .lake;
only this research note is intended tracked delivery. The final
disjointness/sign application is transient bind-only evidence.

This appendix advances the earlier unfinished actual generation
step to the determinant-kernel and exact two-coset classification.
Topological connected-component and manifold-orientation
identification, invariant-function constancy and flow ergodicity
remain unproved. The inherited disconnected-quotient caveat remains:
H-invariance alone is not a full-group ergodicity claim. The SAME
arbitrary-h induced lattice/deck isomorphism still needs its boundary
map, geometric preservation, ambient conjugator and prescribed
homotopy equivalence's isometric representative existence proof.
Cusps, orientation covers and nonorientable finite-volume manifolds
remain in scope. Full Mostow-Prasad remains active and incomplete.
The escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549
Registration remains paused under CLAUDE section 3.9.


### The actual identity component and the same finite quotient measure

Let G be the isometry group of the ORIGINAL hyperbolic three-space with
its existing compact-open topology, and let H be the SAME algebraic
subgroup generated by the two actual horizontal families. The real
coercion of the existing light-determinant homomorphism is continuous:
this follows from the actual light-matrix continuity and the pinned
matrix determinant continuity theorem. The already derived determinant
kernel and sign classification identify H with the inverse image of 1
and its complement with the inverse image of -1. Hence H is both open
and closed in this ORIGINAL topology.

Both original horizontal families are continuous images of the connected
complex parameter space and pass through the identity at parameter 0.
They therefore lie in the original identity component. The existing
identity-component subgroup and algebraic closure property give H as a
subset of that component. Conversely, the clopen set H contains the
identity, so the identity component is a subset of H. Thus H equals
connectedComponent(1) in the ORIGINAL compact-open isometry group. This
identifies a topological group component; no manifold-orientation
identification is claimed here.

On the ORIGINAL quotient G/Gamma, for closed Gamma and a finite
G-invariant measure nu, consider Lp(nu) with an arbitrary normed additive
target and 1 <= q < infinity. If EVERY positive actual dilation pullback
fixes f, EVERY element of this SAME H fixes f. The existing exact
both-horizontal invariance result is extended through algebraic
subgroup closure. The fixing subgroup is constructed using the actual
DomMulAct action; mk(a*b)=mk(b)*mk(a), so multiplication acts in the
reversed order. Inversion and multiplication preserve fixedness with
this order retained. This is an all-H conclusion, not a constancy or
flow-ergodicity conclusion.

There is also a checked regular-action quotient application. Let K be
a second-countable topological group with its stated Borel structures,
mu an SFinite measure invariant under both left and right multiplication,
Gamma a countable subgroup, and D an actual RIGHT fundamental domain
for Gamma. Let nu satisfy the original quotient-measure/preimage relation
with mu and be K-invariant. Then the FULL K action on K/Gamma is ergodic.
Gamma need not be normal. The pinned fundamental-domain absolute-
continuity theorem makes the full quotient map quasi-measure-preserving.
Measurable a.e.-invariant sets lift to mu; the existing left regular-action
ergodicity theorem makes their lifts null or conull. Restricting to D and
using its measure-preserving quotient map transfers that conclusion to
nu. The quotient measurable structure is preserved.

For a locally compact Polish group K with Borel structure, a Haar measure
mu invariant under right multiplication, countable Gamma, the stated
Hausdorff/Borel quotient, and a measurable LEFT fundamental domain D of
finite mu-mass, the existing inverse-Haar construction therefore gives
ONE nu with ALL of: the original mu.inv quotient/preimage relation,
K-invariance, finite nonzero mass, nu(univ)=mu(D), and ergodicity of the
FULL K action. The right domain is D inverse for this SAME mu.inv; it is
not a separately chosen measure or supplied ergodicity witness.

The exact actual finite-target application retains the original gH/gM,
metric-distance compatibility, map F, native quotient covering, local
diffeomorphism, local metric preservation, injective deck holonomy rho,
its every-point evaluation law, and finite target-volume premises. It
reuses the actual target-volume-normalized Haar domain and constructs
ONE actual nu on G/rho.range. This SAME nu has its mu.inv quotient relation,
G-invariance, finite nonzero mass equal to the actual target volume, and
FULL-G regular-action ergodicity. For EVERY f in L2 of this SAME nu,
invariance under EVERY positive actual dilation implies invariance under
EVERY e in the SAME H. The explicit invariant-measure witness supplies
the original DomMulAct instance, and the original closed holonomy image
and quotient Borel structure are retained. No new normality premise,
replacement H3 metric, replacement group topology or replacement quotient
measurable structure is used.

Five accepted serial scoped cache-guarded transient Lean checks exited
zero, with seven standard-three axiom closures. Twenty-four unsuppressed
warnings remain: one deprecated set-membership lemma and twenty-three
letI style suggestions. Four failed whole modules are excluded, including
partial successful declarations. New Lean remains under ignored .lake;
this note is the only tracked delivery. These are classical reuse and
construction, without a novelty, tracked-Lean, admission or freeze claim.

The FULL-G regular action just proved ergodic is different from the
H/dilation/geodesic-flow action. In particular, H-fixedness cannot supply
full-quotient constancy when separate H-orbits remain. The correct H
quotient or finite-index/orientation-cover treatment, invariant-function
constancy and flow ergodicity remain unfinished. Manifold orientation,
the boundary map and geometric preservation for the SAME arbitrary
prescribed-h induced lattice/deck isomorphism, the ambient conjugator and
its isometric representative existence remain unfinished. Full finite-
volume Mostow-Prasad, including cusps and nonorientable manifolds, stays
active and incomplete. The linked escape audit is unfinished and
registration remains paused.


### The finite intersection lattice and the same native-target H quotient

Let K be the stated topological Borel group, mu a right-invariant Haar
measure, H an open subgroup, and Gamma a subgroup contained in H. For
the SAME measurable finite left Gamma-domain D, the inclusion H -> K
is quasi-measure-preserving for mu.comap, which is Haar and right
invariant on H. The SAME preimage of D is a left domain for
Gamma.subgroupOf H. Its mass is exactly mu(D intersect H), hence finite.
If K is locally compact Polish, H is also closed, and Gamma is closed
and countable, the natural H quotient therefore carries ONE nu with
ALL of: the inverse of mu.comap quotient/preimage relation, H invariance,
finite nonzero mass exactly mu(D intersect H), and ergodicity of the
FULL H regular action. These are the original subgroup topology and
quotient measurable structure.

For a measurable group K with left-invariant mu, suppose an actual
r in Gamma lies outside H and EVERY g in Gamma satisfies g in H or
r*g in H. Then E=D union r*D is a left domain for Gamma intersect H.
The original domain supplies its four a.e.-disjoint translated pairs;
its coverage uses g or r*g acting on the SAME point. Its mass is at most
mu(D)+mu(D), and is finite when mu(D) is finite. No normality premise
is needed for this two-coset construction.

Now take the ORIGINAL compact-open hyperbolic-three-space isometry
group G and the SAME subgroup H generated by the two horizontal
families, already identified with the identity component. For EVERY
subgroup Gamma of G, H.subgroupOf Gamma has finite index: the restricted
actual light-determinant homomorphism has kernel exactly this subgroup
and finite range contained in {1,-1}. The original sign classification
also supplies the two-coset condition when Gamma is not contained in H.
Thus the SAME Haar mu and finite left Gamma-domain D yield a finite
left domain E for Gamma intersect H, with mu(E) <= mu(D)+mu(D).
If Gamma is closed and countable and mu is right invariant, ONE nu on
the natural H/(Gamma.subgroupOf H) satisfies the inverse-comap relation,
H invariance, finite nonzero mass exactly mu(E intersect H), the same
upper bound, and FULL H regular-action ergodicity. There is no
Gamma <= H premise in this actual arbitrary-Gamma conclusion.

The native-target application retains EVERY original gH/gM/hd/F/rho
premise: gH distance equals the original hyperbolic distance; F is the
native deck-group quotient covering and a local diffeomorphism; F
preserves the stated Riemannian metric; rho is injective and at EVERY
point implements the SAME deck action; and the target volume is finite.
It reuses the SAME actual target-volume-normalized Haar mu and the
actual evaluation-lifted left domain. Its ORIGINAL rho.range covolume
equals the target volume. H.subgroupOf rho.range has finite index, and
the SAME intersection domain E and ONE natural H quotient measure nu
carry the inverse(mu.comap) relation, H invariance, finite nonzero mass
exactly mu(E intersect H), and FULL H regular-action ergodicity.
Both mu(E) and nu(univ) are at most target-volume + target-volume.
Equality of this H quotient mass to the whole target volume is NOT
asserted. This constructor does not itself discharge the native inputs
from arbitrary complete endpoint manifolds.

Five accepted serial scoped cache-guarded transient Lean checks exited
zero, with seven standard-three axiom closures and twenty-four
unsuppressed letI style suggestions. Seven failed whole modules are
excluded, including partial declarations and diagnostic no-axioms output.
New Lean remains under ignored .lake, and this note is the sole tracked
delivery. These are classical reuse and construction without a novelty,
tracked-Lean, admission or freeze claim.

This advances the finite-intersection and correct H-quotient construction
identified as unfinished above. The FULL H regular action is still
different from the dilation or geodesic-flow action. The actual typed
H-quotient Lp/Mautner application, invariant-function constancy, and
dilation/geodesic-flow ergodicity remain unfinished. Manifold orientation
and the prescribed-h finite-cover compatibility, the boundary map and
geometric preservation for the SAME arbitrary prescribed-h induced
lattice/deck isomorphism, the actual ambient conjugator and prescribed
isometric representative existence remain unfinished. Full finite-volume
Mostow-Prasad, including cusps and nonorientable manifolds, remains
active and incomplete. The linked escape audit remains unfinished;
registration remains paused under CLAUDE section 3.9.


### The actual H action, Lp constancy and homogeneous log-time dilation flow

Every original positive hyperbolic-three-space dilation belongs to the
SAME subgroup H generated by the horizontal and opposite-horizontal
families. The typed elements D_H(a), T_H(v), and U_H(v) are the original
isometries with derived membership. In the ORIGINAL induced compact-open
topology of H, D_H(a) T_H(v) D_H(a)^-1 tends to the identity as a tends
to zero through positive values, as does D_H(a)^-1 U_H(v) D_H(a).

For ANY continuous action of THIS H on a Borel R1 space Y, with a
locally finite compact-inner-regular H-invariant measure nu, ANY normed
additive target V and 1 <= q < infinity, suppose the original positive
dilation pullbacks fix the SAME f in Lp(V,q,nu). The original H-subtype
Mautner argument then proves that EVERY H pullback fixes f. Both
contraction families are used; the fixed subgroup is mapped through
the original H inclusion to apply the original algebraic generation
statement. The multiplication reversal of DomMulAct is retained.
This statement needs an H action and H-invariant nu, so it applies to
the natural H quotient without demanding a G action or G-invariant nu.

If this SAME H action is ergodic, f is a.e. equal to a constant V-valued
function. A.e. strong measurability supplies a separable a.e. range;
the pinned countable-separating criterion and the null/conull alternative
for invariant preimages give constancy. No global separability or
completeness of V is assumed. When nu is finite, the real-valued L2
indicator of a measurable set supplies the corresponding set criterion:
invariance a.e. under EVERY original positive H dilation implies that
the set is null or conull. Full-H ergodicity is a premise at this
generic action stage; dilation-family ergodicity is derived from it.

For EVERY closed subgroup Gamma of the ORIGINAL G, the SAME natural
H/(Gamma.subgroupOf H) retains the original subgroup/coset topology
and quotient measurable structure. Closedness of H derives its Polish
and local-compact structures; closedness of Gamma derives closedness
of Gamma.subgroupOf H and the quotient Hausdorff property. Local
compactness and second countability give quotient metrizability and
sigma compactness. Its Borel structure and finite nu therefore supply
the compact inner regularity needed by the Lp argument. Quotient
regularity is derived rather than supplied as a new hypothesis.

For closed COUNTABLE Gamma, right-invariant Haar mu, and the original
measurable finite left Gamma-domain D, the preceding intersection
construction now yields ONE E and ONE nu carrying ALL prior properties:
the inverse(mu.comap H.subtype) quotient/preimage relation, H invariance,
finite nonzero mass exactly mu(E intersect H), the bound nu(univ) <=
mu(D)+mu(D), and full-H regular-action ergodicity. On THIS SAME nu,
the typed H-subgroup Lp statement gives a.e. constancy for every
1 <= q < infinity and every normed additive target, conditional on
EVERY original positive-dilation pullback fixing the same function;
the dilation-invariant measurable-set criterion also holds. Gamma
need not be contained in H or be normal.

The homomorphism from Multiplicative Real to the ORIGINAL H sends t
to D_H(exp(t)). Its group laws use the original coordinate scaling,
and its continuity is proved in the ORIGINAL induced compact-open
topology by the joint scaling map. Composing the original H action
with this homomorphism gives the actual continuous log-time action.
For a finite compact-inner-regular full-H ergodic nu, this action is
ergodic: exp(log(a))=a transfers the invariant-set criterion for every
positive a. The exact natural H quotient specialization derives all
topological and measure-regularity inputs on the SAME finite nu.
This is homogeneous log-time dilation-flow ergodicity; a geometric
unit-tangent-bundle or geodesic-flow identification is not asserted.

The native-target applications retain ALL original gH/gM/hd/F/rho
premises: gH distance equals the original hyperbolic distance; F is
the native deck-group quotient covering and a local diffeomorphism;
F preserves the stated tangent Riemannian metric; rho is injective
and at EVERY point implements the SAME deck action; and the target
volume is finite. The SAME actual target-volume-normalized Haar mu
and original evaluation-lifted domain give the ORIGINAL rho.range
covolume equality to target volume and finite intersection index.
The SAME intersection domain E and ONE natural H quotient nu retain
the inverse-comap relation, H invariance, finite nonzero mass exactly
mu(E intersect H), and full-H ergodicity. Both mu(E) and nu(univ) are
at most target-volume + target-volume. This finite nu supports the
Lp constancy and dilation-set criteria above, and its actual log-time
action is continuous and ergodic. No equality of H quotient mass with
whole target volume is asserted. These constructors still do not
discharge the native inputs from arbitrary endpoint manifold data.

Eight accepted serial scoped cache-guarded transient Lean checks exited
zero with sixteen axiom closures using only propext, Classical.choice
and Quot.sound. All warnings remain visible. Five failed whole modules
are excluded, including every partial declaration and diagnostic
standard-axiom closure. New Lean remains under ignored .lake, and
this research note is the sole tracked delivery. These are classical
reuse and construction, with no novelty, tracked-Lean, admission or
freeze claim.

The typed natural-H-quotient Lp/Mautner application, invariant-function
constancy and homogeneous positive-dilation/log-time-flow ergodicity
have advanced beyond the earlier pending statements. The geometric
flow identification, native input discharge for arbitrary endpoint
manifolds, manifold orientation and prescribed-h finite-cover
compatibility, the boundary map and geometric preservation for the
SAME arbitrary prescribed-h lattice/deck isomorphism, the actual
ambient conjugator, and prescribed isometric representative existence
remain unfinished. Full finite-volume Mostow-Prasad, including cusps
and nonorientable manifolds, remains active and incomplete. The escape
audit remains unfinished; registration remains paused under CLAUDE
section 3.9 and the linked issue.


### Complete negative-curvature target inputs for the homogeneous H flow

For ANY connected smooth three-dimensional T3 manifold M with its
measurable/Borel structure, an actual Riemannian metric gM and actual
LeviCivitaData DM, suppose the intrinsic metric is complete, DM has
sectional curvature -1 on every nondegenerate tangent two-plane, and
the intrinsic volume of M is finite. The preceding canonical original
H3 source and complete full-deck-cover bridge now supply the native
inputs of the homogeneous log-time flow application. No H3 chart,
H3 metric or distance-compatibility identity, covering F, local
diffeomorphism, tangent metric-preservation identity, holonomy rho,
faithfulness or every-point deck evaluation is a final supplied premise.

The SAME canonical H3 chart and Riemannian metric give the original
hyperbolic distance identity. Applying that SAME constructor's complete
full-deck clause to this M gives a covering F and an injective original
isometric rho implementing the full deck action at EVERY point. The
accepted native-target theorem applies to those exact selected objects.
ONE target-normalized Haar mu has original rho.range covolume equal
to gM.volumeMeasure(univ), and H.subgroupOf rho.range has finite index.
ONE intersection domain E and ONE nu on the ORIGINAL natural
H/(rho.range.subgroupOf H) retain the inverse(mu.comap H.subtype)
quotient/preimage relation, H invariance, finite nonzero mass exactly
mu(E intersect H), and full-H regular-action ergodicity. Both mu(E)
and nu(univ) are at most twice the target volume. For this SAME nu,
the actual action defined by t -> D_H(exp t) is continuous and ergodic.
The previously checked natural-quotient Lp constancy and invariant-set
criteria also apply to this SAME finite full-H-ergodic nu. No equality
of H quotient mass with the whole target volume is asserted.

This exact composition integrates the formerly supplied native-target
inputs for the homogeneous-flow application under the stated base
conditions. It does not require compactness, orientability or an
ordinary metric on M separately identified with its intrinsic metric.
Actual LeviCivitaData, its curvature condition, intrinsic completeness,
finite volume and the measurable/Borel structure remain explicit inputs;
global connection existence without the upstream second-countability
condition is not asserted. The same original compact-open group,
induced H topology, natural coset structure and exp-time action are used.

One accepted serial scoped cache-guarded transient Lean check exited
zero. The exact complete_negative_three_manifold_native_log_time_ergodic_quotient
statement has one axiom closure using only propext, Classical.choice
and Quot.sound; its style warnings remain visible. This is classical
reuse of the constructed canonical source/full-deck-cover bridge and
the actual native-target flow result. New Lean remains under ignored
.lake; the research note is the sole tracked delivery, without a
novelty, tracked-Lean, admission or freeze claim.

The earlier native-input obligation is advanced for this homogeneous
flow theorem with the explicit base geometric conditions above.
Geometric unit-tangent/geodesic-flow identification, orientation and
the prescribed-h finite-cover compatibility, the boundary map and
geometric preservation for the SAME arbitrary prescribed-h lattice/deck
isomorphism, the actual ambient conjugator and prescribed isometric
representative existence remain unfinished. Full finite-volume
Mostow-Prasad, including cusps and nonorientable manifolds, stays
active and incomplete. The linked escape audit remains unfinished;
registration remains paused under CLAUDE section 3.9.


### Levi-Civita existence from complete intrinsic geometry

For ANY finite dimension n and preconnected smooth T3 Riemannian
manifold M with a specified metric g, intrinsic MetricComplete g now
supplies SecondCountableTopology M and Nonempty (LeviCivitaData g).
No ordinary MetricSpace, second-countability, connection, curvature,
volume, compactness or orientation data is supplied to this application.
The original topology and the specified intrinsic metric are retained.

The accepted finite-distance theorem supplies g.edist(x,y) != infinity
from preconnectedness. Install the specified metric's intrinsic
EMetricSpace, and convert it to a MetricSpace using that finite-distance
fact; the topology and extended distance are definitionally the original
ones. The accepted complete-ball theorem makes
{y | g.edist(x,y) <= ofReal(r)} compact. Each actual metric closed ball is
a closed subset of this set, for EVERY real r. This containment handles
negative r without incorrectly identifying a negative-radius closed
ball with an ofReal-radius zero ball. Thus the intrinsic metric space
is proper. Mathlib derives second countability from properness, and
the accepted upstream exists_leviCivitaData supplies actual compatible
torsion-free connection data using T2 from the original T3 assumption.

For every real k, under these same completeness assumptions, requiring
sectional curvature k on every nondegenerate tangent two-plane for ALL
actual LeviCivitaData is equivalent to the existence of ONE such datum.
Derived connection nonemptiness makes the universal condition nonvacuous;
the accepted curvatureTensor_eq for two connections of the SAME metric
makes their sectional curvatures equal. Degenerate tangent pairs are
not added to the curvature hypothesis.

The complete negative-curvature native-flow application now constructs
its LeviCivitaData internally. Its final inputs are the original
connected smooth three-dimensional T3 Borel manifold, gM, intrinsic
completeness, connection-independent sectional curvature -1 on all
nondegenerate planes, and finite intrinsic volume. No connection witness
or second-countability instance is supplied. The SAME previous canonical
H3/full-deck construction gives actual F and rho, ONE target-normalized
Haar mu, SAME intersection E and ONE nu on the ORIGINAL natural H
quotient. Its inverse-comap relation, H invariance, finite nonzero exact
mass mu(E intersect H), bound twice the target volume and continuous
ergodic exp-time dilation action are retained. No separate ordinary
MetricSpace M or compactness/orientation premise is added.

The complete negative-curvature uniqueness application likewise
constructs both DM and DN internally for the SAME original gM and gN.
It retains the original connected smooth three-dimensional metric bases,
Borel structure on M, completeness and connection-independent curvature
-1 on both bases, finite intrinsic source volume, and BOTH ordinary/
intrinsic extended-distance compatibility identities. For EVERY original
prescribed homotopy equivalence h, any two isometries homotopic to h are
equal. This is exactly the uniqueness half; it constructs no isometry.

Three complete first-attempt serial default-resource scoped transient
Lean checks exited zero. The general module has three standard-three
axiom closures and six unsuppressed haveILetI style warnings. The flow
and uniqueness applications each have one standard-three closure and
zero warnings. There are no failed whole modules in these three checks.
All new Lean stays ignored under .lake; this is classical reuse and exact
application, without a novelty, tracked-Lean, admission or freeze claim.
Only the research note is the intended tracked mathematical delivery.

Connection existence and second-countability premises are discharged
for these complete intrinsic geometric applications. Their stated
smooth/T3/Borel/completeness/curvature/volume and, for uniqueness,
ordinary-distance compatibility conditions remain explicit. Geometric
unit-tangent/geodesic-flow identification, orientation and prescribed-h
finite-cover compatibility, the boundary map and geometric preservation
for the SAME arbitrary prescribed-h induced deck/lattice isomorphism,
the ambient conjugator and prescribed isometric representative existence
remain unfinished. Full finite-volume Mostow-Prasad, including cusps
and nonorientable manifolds, remains active and incomplete. The linked
escape audit remains unfinished; registration stays paused under
CLAUDE section 3.9.


### Corresponding finite-index subgroups for the prescribed homotopy equivalence

The two original determinant characters need not be preserved by an
arbitrary prescribed group isomorphism. For arbitrary groups A and B,
homomorphisms rhoA and rhoB into the SAME actual H3 isometry group G,
and an arbitrary isomorphism d : A equiv B, define

    KM = preimage(rhoA,H) intersect preimage(rhoB composed with d,H)
    KN = preimage(rhoB,H) intersect preimage(rhoA composed with inverse(d),H).

Here H is the ORIGINAL generated subgroup, already identified with the
kernel of the original Lorentz/light determinant homomorphism. No premise
asserts that d preserves either individual determinant character.

KM is exactly the kernel of the homomorphism sending a to the PAIR
of original determinants det(rhoA(a)) and det(rhoB(d(a))). Each coordinate
is 1 or -1. Thus this pair has finite range, and its kernel is normal
and has index at most four. The same construction proves the corresponding
facts for KN. The restriction of the SAME original d is an actual
isomorphism KM equiv KN: its underlying value is d(a), and its inverse
has underlying value inverse(d)(b). The image of KM under d is exactly
KN, so their indices in the two original groups are equal. The bound
does not require either original representation to be injective.

For any two ORIGINAL quotient covering maps FM and FN from H3, with
the charted H3 instance used by the existing lift theorem, any original
prescribed homotopy equivalence h, original source basepoint and explicitly
supplied homomorphisms rhoM/rhoN from their full deck groups into G,
the accepted lift theorem constructs pHN, L and d. The checked application
retains L's basepoint value, its every-point projection to h, every-point
FULL deck equivariance, naturality with the actual fundamental-group
map of h and uniqueness of that same induced d. The corresponding KM
and KN are then constructed from THIS d, with normality, finite index,
equal indices and the bound four on each side. The restricted isomorphism
retains d and inverse(d) pointwise, both represented deck elements lie
in the SAME H, and the ORIGINAL L is equivariant for this restriction
at every point. No unrelated isomorphism or lift is substituted.

The general algebraic check and the prescribed-h application each passed
a complete serial default-resource scoped transient Lean check, with
seven printed standard-three axiom closures in total and two unsuppressed
haveILetI warnings. Each module's first whole attempt failed on elaboration
(product projections and implicit restricted-subgroup binders respectively);
both whole failed modules are preserved and excluded, and each revised
whole module passed. This is classical reuse and exact application under
.lake, with no tracked-Lean, novelty, admission or freeze claim.

This discharges an algebraic correspondence needed for a prescribed-h
finite-cover reduction. The application keeps rhoM/rhoN explicitly
supplied; it does not establish their geometric holonomy identities
from these topological covering inputs. Membership in H is the proved
original determinant/generated-subgroup condition, without asserting
smooth orientation identification. Geometric finite-cover realization,
lifted homotopy equivalence and quotient-volume transfer are not supplied
by this algebraic construction. Geometric unit-tangent/geodesic-flow
identification, the boundary map and forced geometric preservation for
the SAME arbitrary prescribed-h induced deck/lattice isomorphism,
actual ambient conjugator existence, prescribed isometric representative
existence and full endpoint assembly remain unfinished. Full finite-volume
Mostow-Prasad, including cusps and nonorientable manifolds, remains active
and incomplete. The linked escape audit remains unfinished; registration
stays paused under CLAUDE section 3.9.


### Finite domains, native recurrence and full-group extension for the same isomorphism

For an arbitrary measurable ambient group R, ONE left-invariant measure
mu, a subgroup Gamma, an original measurable finite-mass Gamma fundamental
domain D, and ANY homomorphism chi : Gamma -> real-units whose values are
1 or -1, construct a measurable fundamental domain E for the ACTUAL image
of kernel(chi) under the subgroup inclusion. Its mass satisfies

    mu(E) = index(kernel(chi) in Gamma) * mu(D)
    mu(E) <= mu(D) + mu(D), and mu(E) < infinity.

The trivial character uses D and index one; the nontrivial character uses
D union r.D and index two. Actual almost-everywhere disjointness of the
two original Gamma translates proves the equality. No replacement of mu
or assumption of compactness is used.

For a faithful representation rho : A -> R and Gamma <= range(rho),
transport any original sign character psi on A to Gamma through the
inverse of rho's actual range equivalence. The image of the transported
kernel is EXACTLY (preimage(rho,Gamma) intersect kernel(psi)).map(rho).
Applying this construction to Gamma = range(rhoA) intersect original H
and psi = original determinant composed with rhoB composed with SAME d
produces an actual finite fundamental domain for represented KM. The
symmetric application produces one for represented KN. These applications
retain the original d, its inverse and mu, with at most twice the mass
of the corresponding original Gamma domain.

For any discrete subgroup of the ACTUAL H3 isometry group with an actual
measurable finite-mass fundamental domain for a Haar and right-invariant
mu, derive closedness and countability, construct a finite nonzero full
group quotient measure, and apply the accepted centralizer conjugation
recurrence and closed dilation constraint. The accepted actual H3 identity
for all conjugates then forces its ambient centralizer to be trivial.
Discreteness of a represented subgroup follows from discreteness of the
original representation range by the actual continuous injective inclusion.

For arbitrary homomorphisms alpha,beta : A -> Q, agreement on a NORMAL
subgroup K and trivial centralizer of beta(K) force alpha = beta:
beta(a)^(-1) alpha(a) centralizes beta(K) for each original a. Consequently,
if a supplied c conjugates rhoA to rhoB composed with SAME d on KM, and
the target representation is faithful and discrete with an actual finite
domain for range(rhoB) intersect H, the constructed KN domain supplies
the required trivial centralizer and SAME c conjugates on ALL original A.
The restricted conjugator remains a premise; this reduction creates none.

For an original connected T3 smooth three-manifold M, with its Borel
measure structure, intrinsic complete Riemannian metric gM, curvature -1
on every nondegenerate plane for every Levi-Civita realization, and finite
original volume V, consume the earlier complete native flow construction.
It supplies an actual H3 quotient covering F, faithful deck representation
rho with EVERY-POINT original deck evaluation, and ONE original Haar,
right-invariant mu with covolume(range(rho)) = V. For ANY explicitly
supplied other group A, representation rhoA and SAME isomorphism
d : A equiv deck(F), construct E for EXACT represented KN, with

    mu(E) <= (V + V) + (V + V), and mu(E) < infinity.

The original cover/evaluation derive discreteness. The SAME mu/E derive
trivial ambient centralizer and extend a supplied KM conjugator c to ALL
A without changing c or d. No connection, holonomy, fundamental domain,
closedness, countability or centralizer premise is supplied on this native
target; the other rhoA, d and existence of restricted c remain explicit.

For ANY discrete Gamma <= original H with an actual finite domain E,
derive ONE natural H/Gamma quotient measure nu from SAME mu/E. Its mass
is exactly mu(E intersect H), is nonzero and at most mu(E); it is finite
and invariant/ergodic under H. The original log-time dilation action on
this SAME quotient and SAME nu is continuous and ergodic. The checked
complete native application retains F/rho/mu, represented KN, E, the
derived centralizer and SAME-c extension together with this natural
H/KN measure, whose total mass is at most (V+V)+(V+V).

Six complete serial default-resource transient Lean checks passed, with
twelve printed closures containing only propext, Classical.choice and
Quot.sound, and nineteen unsuppressed haveILetI style warnings. The first
whole sign-kernel and faithful-intersection attempts failed on elaboration;
both are preserved and wholly excluded, with a two-failure reassessment,
and their repaired whole modules passed. All new Lean remains ignored
under .lake. This is classical reuse and exact application, with no
novelty, tracked-Lean, admission or freeze claim; only this note is the
intended tracked mathematical delivery.

The new native applications leave other rhoA and d explicitly supplied.
They do not assemble the original arbitrary prescribed-h lift with both
derived native holonomies. Smooth orientation identification, geometric
finite covers and their lifted homotopy/volume transfer, and geometric
unit-tangent/geodesic-flow identification are not established here. The
boundary map and forced geometric preservation for SAME prescribed-h d,
actual restricted ambient conjugator existence, prescribed isometric
representative existence and full endpoint assembly remain unfinished.
Full finite-volume Mostow-Prasad, including cusps and nonorientable cases,
remains active and incomplete. The escape audit remains unfinished:
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549
Registration stays paused under CLAUDE section 3.9.


### 两侧原几何、给定同伦等价与度量绑定

`h3_intrinsic_topological_homotopy_equiv_lift_deck_isomorphism` 现在从原
H³ 上半空间的凸坐标域，经已有 `Convex.locallyPathConnectedSpace` 及
坐标同胚导出局部道路连通性，不要求另给 H³ 的 `ChartedSpace`。
对原实际商覆盖 `FM/FN`、任意给定同伦等价 `h` 和原源基点 `pHM`，
使用已有一般覆盖提升构造同一个 `pHN/h₀/L/τ/d`，保留
`d.toMonoidHom=τ`、`L pHM=pHN`、逐点投影
`FN(L x)=h(FM x)`、完整 deck 等变性以及实际基本群自然性。
`d` 在该同一基点与基本群识别下唯一；这不声称提升无条件唯一，
也不要求原提升是等距映射。

`h3SameDMeasuredCompatibleFlowData` 是已经验证的对应子群测度、中心化子、
同一共轭元延拓和自然 H 商遍历性结论的显式合取，不是新的刚性假设。
对表示 `ρA/ρB`、同一个 `d:A≃B`、原 `μ` 和体积 `V`，它的目标群始终为
`KN=h3SameIsomorphismGeneratedSource ρB ρA d.symm`，实际环境子群为
`Γ=KN.map ρB`。数据包含同一可测基本域 `E`、
`μ(E)≤(V+V)+(V+V)<∞`、Γ 的环境中心化子平凡、同一自然商
`H ⧸ Γ.subgroupOf H` 的闭性证明和测度 ν、原 comapped inverse-Haar
商前像恒等式，以及 `ν(univ)=μ(E∩H)≠0`、`ν(univ)≤4V`、H 不变遍历性
和同一对数时间膨胀的连续遍历性。延拓结论仍为条件命题：
对任意已给定 c，若它在对应源子群上实现该 d 的共轭关系，
则同一个 c 在完整原源群上实现同一个 d。

`complete_negative_three_manifolds_prescribed_h_two_native_compatible_flows`
从两侧原连通、T3、Borel、光滑三维流形的 Riemannian 度量、各自内蕴完备性、
每个 Levi-Civita 实现在每个非退化平面上曲率为 −1，以及各自原体积有限出发，
对任意原给定 `h:M≃ₕN`，构造两侧实际 `FM/FN`、原商覆盖、忠实表示
`ρM/ρN` 及其逐点原 deck 作用绑定，并各给一个 Haar 且右不变的 `μM/μN`，
满足各自 `covolume(ρ.range)=g.volumeMeasure(univ)`。从这两个同一覆盖导出
原 h 的同一个 L/d 及全部基点、投影、完整等变、基本群自然性和 d 的唯一性。
目标数据以实际 `ρM/d` 调用，源数据以实际 `ρN/d.symm` 调用，
各保留本侧原测度和原体积；没有用一个另外给定的表示或同构代替它们。
同一个 d 给出的 `KM/KN` 正规、有限指标相等且各至多四，
原限制同构及其逆逐点等于 d/d.symm，同一个 L 在限制作用下继续等变。
该结论没有保留轨道商到原流形的度量识别，不能单凭它进行等距下降。

`complete_negative_three_manifold_metric_bound_same_d_native_compatible_flow`
处理该度量接口。这里原 M 带 `MetricSpace`；除上述原连通、Borel、光滑三维、
内蕴完备、每个 Levi-Civita 实现的非退化平面曲率 −1 及有限原体积条件外，
显式要求 `∀x y, gM.edist x y=edist x y`，将原 Riemannian 内蕴距离
绑定到当前度量。已有完备连接构造给出实际 Levi-Civita 实现，
原 H³ bridge 给出实际图册、度量和同一个原 deck 覆盖 F/ρ。
已有覆盖纤维距离与轨道商距离识别导出一个实际轨道商等距同构 e，
保留 `e(orbitQuotientMk ρ x)=F x`。同一个 F/ρ 的作用适当不连续；
在它的轨道商度量下，e 对当前原 M 度量等距。该同一覆盖、表示和原度量
再导出原 Haar/右不变 μ 及余体积等于原体积，并对任意另给 ρA 和同一个 d
产生上述完整对应子群数据。这里没有另给覆盖、holonomy、图册、连接、
有限基本域、中心化子、遍历性或轨道商等距同构的前提。

`complete_negative_three_manifolds_prescribed_h_native_metric_restricted_endpoint`
将两侧上述度量绑定构造与原任意给定 h 合并。M/N 位于同一 Lean 宇宙，
各带原 `MetricSpace`、连通性、Borel 结构、光滑三维结构、内蕴完备原度量、
每个 Levi-Civita 实现的非退化平面曲率 −1、有限原体积，以及各自显式
`g.edist=edist`。它构造并保留两侧同一个覆盖、忠实且逐点绑定的表示、
适当不连续性、实际轨道商等距同构、原 Haar/右不变测度及精确余体积，
并从这些同一覆盖构造原 h 的同一个 L/d、全部基本群自然性、d 的唯一性、
两侧对应子群测度/遍历性数据和同一个有限指标限制同构。

在上述两侧原几何、度量识别以及原 h 所确定的同一个 d 条件下，
若另给 c 并证明
`∀a:KM, c*ρM(a)*c⁻¹=ρN(d(a))`，则目标子群的原数据延拓该同一个 c，
在完整源 deck 群上实现该同一个 d。已有同一提升的共轭下降、等距轨道商下降
和连接无关的原几何同伦类唯一性给出实际 `e:M≃ᵢN`，满足
`∀x, FN(c x)=e(FM x)`、e 的连续映射同伦于原 h，并且任意另一个
同伦于该原 h 的等距同构 e' 均等于 e。源代码只在 c 及其限制共轭关系
已经给定的同一条件作用域内断言这一存在和唯一性；没有证明 ∃c。
该条件链保留原给定同构、提升和覆盖，没有以另一个可实现同构替代原 d。

完整有限体积 Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**。
当前真实缺口是对上述原 h 诱导的同一个 d 构造对应子群上的实际环境共轭元。
原 d 的边界映射、被迫的几何/配对保持及其存在性仍未证明，
自然 H 商的代数对数时间作用也尚未识别为几何单位切丛/测地流。
没有建立几何定向识别、对应有限覆盖和其提升同伦/体积识别。
本轮没有加入紧性或可定向假设，目标仍包含非紧尖点及非可定向情形；
条件等距存在性不等于完整刚性已证。上述都是已有构造的经典应用和接口组装，
无新颖性、跟踪 Lean、准入或冻结声明；Lean 源仍位于忽略目录 `.lake`，
本笔记是唯一跟踪交付。逃逸审计仍未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 原等距群的紧光锥截面作用与边界交比

`h3NormalizedNullSection` 是原 Lorentz 坐标中的实际截面
`{v:Fin 4→ℝ | v 0=1 ∧ h3LorentzKernel v v=0}`。
`h3_normalized_null_section_isCompact` 从连续二次型的闭性与各坐标的
`[-1,1]` 界证明其紧性，并给出截面类型的 `CompactSpace`。
这里的紧性属于该截面；原有限体积流形仍允许非紧、带尖点。

`h3NullRayNormalize v=(v 0)⁻¹•v` 对非零标量缩放不变。
原实际 H³ 等距变换 e 的已有 Lorentz 线性表示保持未来零光锥，
其正时间坐标 `t(e,b)` 因而给出实际归一化作用
`h3NullBoundaryAction e b=normalize(Ae b)`。该作用满足单位和乘法律，
在原等距群的已有 compact-open 拓扑与截面拓扑下联合连续，
每个 e 均产生以 e⁻¹ 作用为逆的实际截面同胚。原线性作用可精确重构为
`Ae b=t(e,b)•action(e,b)`，且 t 为正并满足
`t(e*f,b)=t(e,action(f,b))*t(f,b)`。

`h3_null_boundary_pairing_transform` 保留原二次型的精确变换关系：
作用后两点的 Lorentz 配对等于原配对除以两点各自的正时间因子之积。
`h3_null_boundary_pairing_spatial_difference` 进一步证明，原截面两点
后三个坐标之差的平方和精确等于其 Lorentz 配对的两倍。
因此配对非负、为零当且仅当两截面点相等、为正当且仅当两点不同。

`h3NullBoundaryCrossRatio(a,b,c,d)` 定义为
`K(a,c)*K(b,d)/(K(a,d)*K(b,c))`。在 a≠d、b≠c 两个分母点对
不同的条件下，已有配对正性确保分母非零，原实际 H³ 等距变换的
归一化作用精确保持这个交比。该定理没有断言尚未构造的、由原 h
诱导的同一个 d 的边界映射存在，更没有断言该未知映射保持交比。

两个完整模块串行编译通过，共十一项已检查公理闭包只含
`propext`、`Classical.choice`、`Quot.sound`，没有风格警告抑制。
第一个模块的整次失败尝试保留并整体排除，只有修正后的完整编译被接受。
这些是原光锥截面与原等距作用的经典构造和几何事实；没有新增紧性或
可定向流形前提，也没有构造对应原 h/d 的边界映射、迫使该映射保持几何，
或给出对应子群上的实际共轭元。完整有限体积 Mostow–Prasad 仍为
**ACTIVE/INCOMPLETE**，继续包含非紧尖点与非可定向情形。
Lean 源仍在忽略目录 `.lake`，笔记是唯一跟踪交付；没有新颖性、跟踪 Lean、
准入或冻结声明。逃逸审计仍未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 从保持交比的边界映射构造实际等距映射与同一个群同构的共轭

本轮把原归一化未来零光锥截面上的配对几何接到实际等距存在性，
没有假设已经给定的配对权重、光锥延伸或环境共轭元。
`positive_symmetric_four_point_kernel_constructs_weights` 对任意类型上的
对称核 R，在不同点间严格为正、满足明确非退化四点乘积恒等式且有
三个不同锚点的条件下，以锚点三角比值的正平方根构造处处正的 w，
并证明所有不同点对满足 `R(x,y)=w(x)*w(y)`。

对于原截面的单射 φ，若 φ 在 a≠d、b≠c 两个分母点对不同的条件下
保持已有的 `h3NullBoundaryCrossRatio`，则原配对比值
`R(x,y)=K(x,y)/K(φ(x),φ(y))` 满足上述恒等式和正性。
`h3_injective_crossRatio_boundary_map_constructs_positive_pairing_weights`
从已有原 null frame 内部取得三个实际不同锚点，构造正权重，证明
`w(x)*w(y)*K(φ(x),φ(y))=K(x,y)` 对所有点对成立，包括相等点的零配对。
公共结论没有再要求调用者提供锚点或权重。

在同一单射与交比保持条件下，
`h3_injective_crossRatio_boundary_map_induces_actual_isometry`
对原未来零光锥向量 v 定义径向延伸
`F(v)=v(0)*w(normalize(v))*φ(normalize(v))`，并在光锥外取零。
证明对任意两个原未来零光锥向量，F 保持它们的原 Lorentz 配对，
且每个原未来零光锥向量的像的时间坐标严格为正，
再调用此前实际光锥延伸定理构造原 H³ 的实际等距映射 c，
使其归一化边界作用精确等于原 φ。φ 单射与交比保持是前提；
没有预先要求 φ 为满射、同胚或提供 c。

`h3_actual_isometry_eq_one_of_boundary_fixed` 以原四向量 null basis 证明
边界作用恒等的实际等距映射就是单位元：配对保持使不同基向量上的
正时间因子满足乘积为 1，三个因子的关系迫使首个因子平方为 1，
正性排除负号，其余因子也等于 1。原线性表示的单射性完成结论。
`h3_null_boundary_action_faithful` 因而证明相同边界作用确定同一个实际
等距映射。在上述单射与交比保持条件下，φ 可由唯一实际等距映射实现。

`h3_prescribed_group_isomorphism_boundary_map_constructs_conjugator`
进一步证明：对于原表示 ρ、σ 和给定群同构 d，若上述 φ 满足
`φ(action(ρ(g),b))=action(σ(d(g)),φ(b))`，则构造出的同一个 c 满足
`σ(d(g))=c*ρ(g)*c⁻¹` 对所有 g 成立。边界作用的忠实性直接把边界
等变关系提升为实际等距映射等式，没有换成另一个可实现的群同构。

在已有 `h3SameDMeasuredCompatibleFlowData` 与上述单射、交比保持
条件下，`h3_same_d_compatible_boundary_map_constructs_unique_full_conjugator`
只要求 φ 对原兼容子群 KM 等变，使用原 KM、KN 与 d 的实际限制 r
先构造限制共轭，再复用原延拓关系得到完整原 d 的共轭。唯一性针对
同时实现 φ 的共轭元；没有把它冒充一般格子共轭元唯一性的新证明。
原生数据在本定理中仍显式给定；此前原流形构造供应它，当前定理
没有凭空构造数据。原给定 h 的同一个 d 与同一个 c 可继续进入此前
条件下降链；当前仍缺把上述 φ 的前提真正证明出来。

五个完整模块串行编译通过，共十项已检查公理闭包只含
`propext`、`Classical.choice`、`Quot.sound`，未抑制警告。四个模块的
初次失败均保留并整次排除，只有各自最终完整成功编译被接受。
这是经典正核因子分解、原光锥径向延伸、忠实作用及已有原生数据的组合；
没有新增紧性或可定向流形前提。完整有限体积 Mostow–Prasad 仍为
**ACTIVE/INCOMPLETE**，包含非紧尖点与非可定向情形。尚未构造原给定
h 所诱导的同一个 d（或其实际兼容限制 r）的单射等变边界映射，也尚未
迫使那个未知映射保持交比，因此没有无条件证明对应环境共轭元存在
或每个原 h 的唯一等距代表存在。
Lean 源仍在忽略目录 `.lake`，笔记是唯一跟踪交付；没有新颖性、
跟踪 Lean、准入或冻结声明。逃逸审计仍未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 实际测地线、归一化理想端点与有界距离端点唯一性

本轮在原 H³ 的原距离上构造几何边界工具。
对原归一化零光锥截面中的 b，定义
`h3BoundaryGeodesicVector(b,t)=(cosh(t),sinh(t)*b₁,sinh(t)*b₂,sinh(t)*b₃)`。
原空间方向平方和为 1，故该向量的 Lorentz 自配对为 1，时间坐标
严格为正。已有原未来单位向量逆构造给出实际点
`h3BoundaryGeodesicLine b t`，并证明其原 Lorentz 坐标正是上述向量。
同一条线上的配对为 `cosh(s-t)`；原配对与原距离的恒等式及 cosh
在非负半轴的单射性给出 `Isometry (h3BoundaryGeodesicLine b)`，因此
实际距离精确等于 `|s-t|`。时间零的点是原上半空间坐标 `(0,1)`。
没有要求调用者提供另一条测地线或替代距离。

`real_sinh_div_cosh_tendsto_atTop_one` 以 `exp(-t)` 趋于零和恒等式
`sinh(t)/cosh(t)=(1-exp(-t)^2)/(1+exp(-t)^2)` 证明该比值趋于 1。
`h3_boundary_geodesic_normalized_endpoint` 随后证明实际点的原 Lorentz
坐标经 `h3NullRayNormalize` 归一化后，在 t 趋于正无穷时趋于原 b。
这里收敛发生在原四维实向量空间；有限时间的归一化内部点并未被
宣称属于零光锥截面，也没有把归一化坐标收敛冒充一般紧化等价性。

对任意原实际等距映射 e，
`h3_actual_isometry_normalized_lorentz_equivariance` 证明实际点 e(p)
的归一化坐标，等于把 p 的归一化坐标送入原 Lorentz 线性表示后
再次归一化。`h3_actual_isometry_preserves_normalized_boundary_convergence`
对任意滤子及任意实际点族 P 证明：若 P 的归一化坐标趋于原 b，
则 e(P) 的归一化坐标趋于原 `h3NullBoundaryAction e b`。
证明使用原有限维线性表示的连续性和像的严格正时间坐标。
这个结论描述实际等距映射；没有证明原同伦提升的边界延拓。

`h3_boundary_convergence_forces_inverse_time_to_zero` 由原归一化坐标
的自配对等于时间坐标倒数的平方、原零光锥极限的零自配对以及
正时间分支，推出时间坐标的倒数趋于零。
`h3_bounded_distance_normalized_boundary_endpoints_equal` 则证明：
对同一个非底滤子 l，若实际点族 P、Q 的归一化坐标分别趋于原
边界点 b、c，且存在非负实数 C 使每个参数处的原距离都不超过 C，
则 b=c。原归一化配对非负，并被两条路径时间倒数的乘积乘
`cosh(C)` 控制，因而趋于零；原配对联合连续性和零配对分离性质
给出端点相等。`NeBot l` 与两条路径各自的收敛都是明确前提；
结论没有供应另一条路径的收敛、射线追踪或原提升的几何控制。

四个完整模块串行编译通过，共十二项公理闭包只含
`propext`、`Classical.choice`、`Quot.sound`，零警告。三个模块初次
完整失败均保留并整次排除，只有最终完整成功编译被接受。
这些结论复用原 Lorentz 模型、实际等距作用与经典双曲函数分析，
没有新增紧性或可定向前提。完整有限体积 Mostow–Prasad 仍为
**ACTIVE/INCOMPLETE**，范围包含非紧尖点与非可定向情形。
尚未从原给定同伦等价构造其同一个诱导群同构 d 的单射等变边界
映射，也尚未迫使那个映射保持原交比。上述端点唯一性是构造该
映射所需的几何工具，不是该映射存在或完整刚性的证明。
Lean 源仍在忽略目录 `.lake`，研究笔记是唯一跟踪交付；没有
新颖性、跟踪 Lean、准入或冻结声明。逃逸审计仍未完成，登记按
CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 实际射线比较、有界扰动收敛与径向逃逸端点存在

对任意原实际等距映射 e 和原归一化零光锥点 b，
`h3_boundary_geodesic_vector_exp_null_decomposition` 把原测地线向量
分解为 `(exp(t)/2)*b+(exp(-t)/2)*opposite(b)`，其中原反向点的
时间坐标仍为 1，三个空间坐标取负。
`h3_actual_isometry_boundary_geodesic_kernel_defect` 计算原实际点
`e(ray(b,t))` 与 `ray(action(e,b),t)` 的原配对相对时间零的差：
它等于 `(exp(-t)^2-1)/4` 乘原线性表示送出的反向零向量与另一
反向零向量的配对。原零光锥配对非负，而 t 非负时该指数系数
非正，故 `h3_actual_isometry_boundary_geodesic_distance_bound`
给出原距离上界 `dist(e(o),o)`，其中 o 是原上半空间点 `(0,1)`。
这个射线比较界由原等距几何推出，没有作为前提输入。它描述
实际等距映射，并不供应原给定同伦提升的几何控制。

`h3_lorentz_coordinates_time_ge_one` 从原单位未来向量的自配对
和正时间分支推出时间坐标至少为 1。
`h3_normalized_coordinate_difference_sq_le_pairing` 利用归一化后
时间坐标等于 1、两个原自配对非负，证明任一原四维坐标的差
平方至多为两倍原归一化配对。结合原配对与距离的 cosh 恒等式，
`h3_bounded_distance_normalized_coordinate_difference_sq` 在非负 C
和原距离 `dist(p,q)≤C` 下给出上界 `2*cosh(C)/time(p)`。
由此，`h3_bounded_distance_preserves_normalized_boundary_convergence`
对任意滤子和实际点族 P、Q 证明：若 P 的原归一化坐标趋于原
边界点 b，且每个参数处 `dist(P,Q)≤C`，则 Q 的原归一化坐标
也趋于同一个 b。这里 C 非负；没有要求 Q 已有极限，也没有
要求滤子非底。这比此前“两条路径都已有极限”的端点唯一性
多供应了一条路径的收敛。任意滤子的收敛传递不冒充任意滤子
下的极限唯一性；此前唯一性定理的非底条件仍保留。

`h3_lorentz_time_eq_cosh_basepoint_distance` 证明原时间坐标等于
到同一个原点 o 的原距离的 cosh。
`h3_radial_escape_inverse_time_bound` 因而对任意实数 R 和实际点 p，
在 `R≤dist(p,o)` 时推出 `1/time(p)≤2*exp(-R)`；R 不必非负。
证明使用正时间、指数单调性和原 cosh 公式。

`h3_geometric_inverse_time_sequence_has_boundary_endpoint` 对实际
H³ 序列 P 构造原归一化零光锥边界点 b。明确条件是非负 C、A，
`0≤r<1`，每步原距离 `dist(P(n),P(n+1))≤C`，以及
`1/time(P(n))≤A*(r^n)^2`。上述坐标差平方界使每个归一化坐标
的相邻差被 `sqrt(2*cosh(C)*A)*r^n` 控制；经典几何级数 Cauchy
判据和实数完备性供应各坐标极限，而非预设其存在。
这些坐标组成原四维极限 v。时间坐标恒为 1；时间倒数被几何
序列控制并趋于零，因此归一化自配对趋于零。原配对联合连续性
给出 `K(v,v)=0`，于是 v 确实定义原边界点 b，并且原归一化
坐标沿自然数正无穷趋于 b。

`h3_linearly_escaping_bounded_step_sequence_has_boundary_endpoint`
直接以原距离的条件得到同一存在结论：C 非负，a 严格为正，
B 是任意实数，每步距离至多 C，且每个自然数 n 满足
`a*n-B≤dist(P(n),o)`。径向倒数界给出
`1/time(P(n))≤2*exp(B)*(exp(-a/2)^n)^2`，其中指数比严格小于 1，
从而应用上述实际端点构造。没有要求调用者供应边界映射、
端点或端点极限，也没有只假设序列逃向无穷而省略增长速率。
这次存在结论的参数是自然数序列；尚未由此证明任意连续参数
射线像的收敛、边界映射的单射性或连续性。

三个完整模块串行编译通过，共十一项公理闭包只含
`propext`、`Classical.choice`、`Quot.sound`，零警告；成功编译中
未抑制的 ring 技巧建议不计作错误或警告。四次完整失败尝试
均保留并整次排除，只有完整成功编译被接受。
这些原 H³ 几何工具没有添加紧性或可定向前提。完整有限体积
Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**，目标包含非紧尖点和
非可定向情形。尚未证明原给定同伦等价能供应保持同一个诱导
群同构 d 的受控提升，因而也尚未构造该 d 的单射等变边界映射
或迫使其保持原交比。离散端点存在定理不关闭这些缺口；尖点
情形不能由紧流形的粗等距论证自动涵盖。
Lean 源仍位于忽略目录 `.lake`，研究笔记是唯一跟踪交付；没有
新颖性、跟踪 Lean、准入或冻结声明。逃逸审计仍未完成，登记按
CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 从原距离控制构造连续等变边界映射

本轮输入是一个实际原 H³ 映射 F，以及原距离上的全局双边控制：
对所有原点 p、q，`dist(F(p),F(q))≤L*dist(p,q)+K`，且
`a*dist(p,q)-B≤dist(F(p),F(q))`，其中 L、K 非负，a 严格为正，
B 是实数。这里没有假设 F 连续，也没有输入一个边界映射。

`h3_coarse_map_ray_step_and_escape` 对每个原归一化零光锥点 b，
在同一原实际测地线的整数时刻证明：像序列的相邻原距离至多
`L+K`，到原点 o 的原径向距离至少为
`a*n-(B+dist(F(o),o))`；o 始终是原上半空间点 `(0,1)`。
此前已证明的径向逃逸端点存在定理因而供应每条像序列的实际
原边界极限。`h3_coarse_map_constructs_equivariant_discrete_boundary_map`
选择这些极限，构造同一个原边界映射 φ。它进一步对任意一对
原实际等距映射 e、e′ 证明：若同一个 F 在每个原点处满足
`F(e(p))=e′(F(p))`，则同一个 φ 在每个原边界点处满足
`φ(action(e,b))=action(e′,φ(b))`。
证明把原实际等距射线比较界送入 F 的同一个距离上界，并由
一条已知端点的收敛推导另一条路径的同端点收敛，最后使用
自然数正无穷滤子的非底性与原四维 Hausdorff 极限唯一性。
φ 及其极限均由原距离控制构造，没有作为这条存在结论的前提。

`h3_coarse_upper_control_extends_discrete_ray_endpoint_to_real_times`
利用 `floor(max(t,0))` 采样。采样自然数随 t 趋于正无穷；原
单位速度测地线上的采样点与 `max(t,0)` 时刻的点相距至多 1，
故其 F 像的原距离至多 `L+K`。有界扰动收敛定理把整数极限
传到整条实参数射线，且 t 最终非负，夹零参数与原参数最终
相同。`h3_coarse_map_constructs_equivariant_real_ray_boundary_map`
将这一步应用于同一个实际构造的 φ，保留上述所有逐点等变
关系。F 连续性和另一个实参数极限都不是额外前提。

为了证明边界映射连续，另构造定量坐标误差界。若实际原点
p、q 的原距离至多非负 C，且 `1/time(p)≤A*(r^n)^2`，其中
A、r 非负，则每个原归一化坐标差的绝对值至多
`sqrt(2*cosh(C)*A)*r^n`。若这个几何时间倒数界在序列每一步
都成立、每步距离至多 C、`r<1`，且该序列的原归一化极限为 b，
经典几何级数尾项界进一步给出任一坐标误差上界
`sqrt(2*cosh(C)*A)*r^n/(1-r)`。
该定量中间定理使用已知极限；最终构造中的极限仍由此前的
存在定理供应，不把它重新变成外部假设。

对同一个受控 F，设
`A=2*exp(B+dist(F(o),o))`、`r=exp(-a/2)`、`C=L+K`，并令
`D=sqrt(2*cosh(C)*A)`、`T=D/(1-r)`。
`h3_coarse_map_ray_inverse_time_geometric_bound` 从原距离下界
推导每条整数射线像的时间倒数界 `A*(r^n)^2`。
`h3_coarse_map_ray_endpoint_uniform_coordinate_tail` 因而将同一
映射 φ 的每个坐标误差统一控制在 `T*r^n`；常数与 b、坐标 i
无关，且 `0<r<1`。

`h3_boundary_geodesic_vector_continuous_at_time` 证明固定任意实数
t 时原测地线向量随原边界点连续。原配对联合连续性、自配对
等于 1 及原 cosh 距离恒等式进一步说明：对于固定 c、t，b 在
c 的某个邻域中时，原射线点 `ray(b,t)` 与 `ray(c,t)` 距离至多 1。
这一步没有借助 F 的连续性。
在 n 时刻满足这个原距离条件时，F 像的归一化坐标差至多
`D*r^n`；两个像序列各自的端点尾项至多 `T*r^n`，故
`h3_coarse_map_boundary_coordinate_pair_bound` 给出
`abs(φ(b)_i-φ(c)_i)≤(2*T+D)*r^n`。
先令 n 足够大，再取上述原边界邻域，这个统一界使每个 φ
坐标连续；有限乘积和原零光锥截面的子空间拓扑给出
`h3_coarse_map_ray_endpoint_map_continuous`。
最后，`h3_coarse_map_constructs_continuous_equivariant_boundary_map`
实际供应同一个连续 φ、整条实参数射线像的原归一化收敛和
所有由同一个 F 逐点实现的原等距作用等变关系。没有要求
调用者供应连续 φ、射线追踪界或 Morse 引理。

四个完整模块串行编译通过，共十三项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。
三次完整失败尝试均保留并整次排除；成功编译中未抑制的 ring
技巧建议不计作错误或警告。这些结果复用经典原 H³ 几何与
实数、滤子、几何级数分析，没有新增紧性或可定向前提。
完整有限体积 Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**，范围
包含非紧尖点与非可定向流形。尚未从原给定同伦等价供应保持
其同一个诱导群同构 d 的受控 F；当前逐点等变构造只在这样的
F 及其原距离控制已给定时应用。也尚未证明同一个 φ 的单射性
或迫使其保持原交比；这里的连续映射不是已证明的边界同胚。
Lean 源仍在忽略目录 `.lake`，研究笔记是唯一跟踪交付；没有
新颖性、跟踪 Lean、准入或冻结声明。逃逸审计仍未完成，登记按
CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 一般点族的边界扩展与受控逆映射

`h3PolarBoundaryDirection` 从实际原 H³ 点 p 的原 Lorentz 空间
坐标除以 `sinh(dist(p,o))` 构造原归一化零光锥方向；原点仍为
`o=(0,1)`。当 p=o 时使用实际零光锥点 `(1,1,0,0)`。
原自配对为 1、时间坐标等于 `cosh(dist(p,o))` 及原双曲恒等式
证明这确是原边界点，而非输入一个方向。
`h3_polar_ray_reconstruction` 对每个实际原点 p 证明
`ray(direction(p),dist(p,o))=p`；射线表示是结论。

对于任意同一个滤子 l 和实际原点族 P，若 P 的原归一化坐标
趋近实际原边界点 b，已有的时间倒数趋零结论和原 cosh 距离
恒等式给出 `dist(P(z),o)` 趋于正无穷。
`h3_polar_direction_spatial_coordinates_away` 将实际极坐标方向
的空间坐标写成 `cosh(radius)/sinh(radius)` 乘原归一化坐标。
原 sinh/cosh 的无穷远极限供应系数趋于 1，最终
`h3_boundary_convergence_polar_direction_tendsto` 证明实际构造的
方向在原边界子空间拓扑中趋于同一个 b。
没有输入径向逃逸或极坐标方向极限，也不要求 l 非底；这一段
是收敛推导，不是任意滤子上的极限唯一性。

设实际原映射 F 在所有原点对上满足距离上界 `L*dist+K` 和
下界 `a*dist-B`，其中 L、K 非负，a 严格为正，B 任意实数。
极坐标射线在 `floor(radius)` 的采样点与 p 的原距离至多 1，
故 F 像间距离至多 `L+K`。保留此前同一个实际构造的 φ，以及
`A=2*exp(B+dist(F(o),o))`、`r=exp(-a/2)`、`C=L+K`、
`D=sqrt(2*cosh(C)*A)`、`T=D/(1-r)`。
整数射线的统一端点尾界和采样像的归一化坐标差界共同给出
`h3_coarse_map_point_uniform_coordinate_tail`：任意实际原点 p
的 F 像归一化坐标与 `φ(direction(p))` 的各坐标误差至多
`(T+D)*r^floor(radius)`。
径向逃逸使这个界趋零，实际极坐标方向趋近 b，已证明的同一
φ 连续性使 `φ(direction(P(z)))` 趋近 `φ(b)`。
`h3_coarse_map_extends_any_normalized_boundary_convergence` 因而
供应任意原边界趋近点族的 F 像归一化极限，不再局限于固定
射线。最终构造定理供应同一个连续 φ、所有这些一般点族极限
和由同一个 F 在每个原点处实现的所有原等距作用等变关系。
中间尾界定理使用整数端点极限；实际构造仍由此前的存在定理
供应这些极限，没有重新把它们变成构造的外部假设。

进一步设另一个实际原映射 G 也具有它自己的全局原距离双边
控制 `LG*dist+KG`、`aG*dist-BG`，其中 LG、KG 非负，aG 严格
为正，BG 任意实数；F 的控制仍保持上述全部条件。
若存在非负 C 使所有原点 p 都满足 `dist(G(F(p)),p)≤C`，一般
点族扩展可应用于 F 的原射线像。有界扰动又把同一复合像的
端点供应为原 b；自然数正无穷滤子的非底性与原坐标空间极限
唯一性证明实际构造的两个边界映射满足 `ψ(φ(b))=b`。
`h3_controlled_left_inverse_constructs_injective_boundary_map`
据此实际构造同一个连续单射 φ、F 的整条实参数射线端点极限
和所有原逐点作用等变关系。这里只需这一侧的复合距离界。

若还存在非负 D0，使所有原点 q 满足
`dist(F(G(q)),q)≤D0`，对称论证供应 `φ(ψ(b))=b`。
`h3_controlled_inverse_constructs_equivariant_boundary_homeomorphism`
从这两个实际构造的连续映射及双向逆关系构造原边界同胚 E。
它保留同一个 F、G 的整条实参数射线极限；对每一对由同一个
F 在每个原点处联系的原实际等距作用，E 保留对应等变关系，
而 E 的逆对由同一个 G 逐点联系的作用也保留对应等变关系。
最终单射和同胚构造均没有输入边界映射、端点极限、单射性、
同胚或 Morse/射线追踪前提；实际原 F、G 的各自全局控制及
所使用的一侧或两侧原复合距离界始终是明确的输入条件。

四个完整模块串行编译成功，共十五项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。
三次完整失败尝试均保留并整次排除，没有接受失败尝试中的
部分闭包。完整有限体积 Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**，
包含非紧尖点、非可定向流形、两侧原度量及原给定同伦等价
诱导的同一个群同构 d。本轮没有从该原 h/d 供应满足上述条件
的 F、G 和原一致有界复合，也没有迫使同一个边界映射保持
原交比；条件下的实际边界同胚构造不等于原目标实例已构造。
Lean 源仍在忽略目录 `.lake`，研究笔记是唯一跟踪交付；没有
跟踪 Lean、准入、冻结或新颖性声明。逃逸审计仍未完成，登记
按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 从粗稠密性构造逆映射与一般边界同胚

设实际原 H³ 映射 F 在所有原点对上满足原距离上界
`L*dist+K` 和下界 `a*dist-B`，其中 L、K 非负，a 严格为正，
B 任意实数。再设 R 非负，且每个实际原目标点 q 都有原点 p
使 `dist(F(p),q)≤R`。`h3_coarse_density_constructs_controlled_inverse`
从这个实际粗稠密性逐点选择 G(q)，不再输入另一个受控 G。
同一个实际选择的 G 满足 `dist(F(G(q)),q)≤R`，并由原 F 的
距离下界导出 `dist(G(F(p)),p)≤max(0,(B+R)/a)`。
原三角不等式与同一个 F 的距离双边控制还供应 G 自己的全局
原距离上界 `(1/a)*dist+max(0,(B+2R)/a)`，以及下界
`(1/(L+1))*dist-(K+2R)/(L+1)`；前者的系数和常数非负，
后者的系数严格为正。两侧一致有界逆复合和 G 的控制均为
构造结论，没有成为新的外部输入。

这个选择的 G 不保证逐点等变。对每一对实际原等距映射
e、e′，若同一个 F 在每个原点上满足 `F(e(p))=e′(F(p))`，
`h3_coarse_inverse_approximate_intertwining` 则给出所有原点 q
上的一致原距离界
`dist(G(e′(q)),e(G(q)))≤max(0,(B+2R)/a)`。
证明比较两个 F 像：它们与同一个 `e′(q)` 的原距离各至多 R，
再应用同一个原 F 的距离下界。
`h3_coarse_density_constructs_approximately_equivariant_inverse`
保留实际构造的同一个 G、它自己的全局控制、双向逆复合界
以及对所有上述原等距映射对的这一近似等变界。

在上述同一个实际原 F 的全部条件和 R 粗稠密性下，
`h3_coarse_density_constructs_general_equivariant_boundary_homeomorphism`
实际构造同一个 G 与原归一化零光锥边界上的同胚 E。
它使用已导出的 G 控制及双向逆复合界，而非输入 G 或 E。
F 和 G 的整条实参数原射线像分别趋于 `E(b)` 与 `E.symm(b)`。
从这些实际构造的整条实射线极限导出整数射线极限，再复用
一般点族扩展，得到任意滤子 l、实际原点族 P 的双向结论：
若 P 的原归一化坐标趋于原边界 b，则 F(P) 的原归一化坐标
趋于 `E(b)`，G(P) 的原归一化坐标趋于 `E.symm(b)`。
同一个 G、E 同时实现这些射线及一般点族极限；没有额外的
F 连续性、G 连续性、Morse/射线追踪或滤子非底前提。
任意滤子上的这段推导仍是收敛传递，不是极限唯一性断言。

对每一对由同一个 F 在所有原点处联系的原实际等距映射
e、e′，同一个 E 满足
`E(action(e,b))=action(e′,E(b))`。
`h3_boundary_homeomorphism_inverse_intertwining` 从这个同一个
E 的逆关系代数地推出
`E.symm(action(e′,c))=action(e,E.symm(c))`。
逆边界映射的精确等变性由同一个 F 的原逐点关系和边界逆
关系供应，没有假称实际选择的 G 具有原逐点精确等变性。
对原给定群同构 d 的应用仍须由所构造的 F 在所有原点处
联系同一个 d 对应的两侧原表示；本轮没有供应该原 h/d 的 F。

三个完整模块串行本地 Lean 成功，共六项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。
一次完整失败尝试保留并整次排除，包括其中的部分标准闭包
和后续 `sorryAx` 诊断；没有接受失败尝试的任何闭包。
完整有限体积 Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**，范围
保留非紧尖点、非可定向情形、两侧原度量和原给定同伦等价
诱导的同一个群同构 d。尚未从该原 h/d 构造具有上述距离
控制和粗稠密性的 F，也没有迫使同一个边界映射保持原交比。
条件下的实际 G 和边界同胚不等于原目标实例已构造。
Lean 源仍在忽略目录 `.lake`，研究笔记是唯一跟踪交付；没有
跟踪 Lean、准入、冻结或新颖性声明。逃逸审计仍未完成，登记
按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 从水平数据构造原 H³ 高度保持映射

`h3HorizontalHeightExtension T` 将实际水平映射 `T : ℂ → ℂ`
延伸到实际原 H³：水平坐标变为 T 的像，严格正的原高度保持。
若 C、D 都至少为 1，且所有水平点对 z、w 满足欧氏距离上界
`dist(T(z),T(w))≤C*dist(z,w)` 与反向界
`dist(z,w)≤D*dist(T(z),T(w))`，
`h3_horizontal_height_extension_native_distance_controls` 就在所有
原 H³ 点对 p、q 上推导原双曲距离双边界：
`dist(p,q)-arcosh(D²)≤dist(F(p),F(q))≤dist(p,q)+arcosh(C²)`。
F 是上述同一个实际高度保持延伸；双曲距离控制是推导结论，
没有作为水平输入条件。证明用原坐标的精确 cosh 距离式、
复数欧氏距离平方、严格正的高度分母及 cosh 加法公式。
`h3_horizontal_height_extension_surjective` 还从 T 的实际满射性
构造同一个 F 的实际原 H³ 满射性；目标高度保持为原正高度。
这个满射结论本身不需要 C、D 或水平距离控制。

对每一对实际原等距映射 e、e′，若它们在原 Lorentz 表示中
都将原无穷远零光锥标架射线按同一个 a 缩放，且所有水平点 z
满足 `T(h3InfinityHorizontalMap(e,z))=h3InfinityHorizontalMap(e′,T(z))`，
`h3_horizontal_height_extension_intertwines_original_isometries`
就在每个实际原 H³ 点 p 上推导
`F(e(p))=e′(F(p))`。它用实际原等距作用的水平坐标与高度律，
推导原逐点关系，没有再输入 F 的逐点等变性；没有加入定向
保持条件。同一个缩放 a 的正性由实际原射线固定关系供应。
这段等变推导自身不需要 T 的双边距离控制或满射性。

`h3PeriodBasisHorizontalEquiv b b′` 从两组实际实基
`b,b′ : Module.Basis (Fin 2) ℝ ℂ` 构造同一个实际连续实线性
等价 T；`h3PeriodBasisHeightExtension b b′` 是它的原 H³ 高度
保持延伸 F。`h3_period_bases_construct_controlled_surjective_translation_map`
不再输入 T、F 或水平距离控制，而是从这两组有同一索引配对
的基实际构造它们。T 与 T.symm 的算子范数给出各自的常数
`C=max(1,‖T‖)`、`D=max(1,‖T.symm‖)`，推导同一个 F 的上述
所有原 H³ 距离双边界和实际满射性。对每个整数系数族
`m : Fin 2 → ℤ` 及每个原 H³ 点 p，同一个 F 精确联系实际
水平平移：源平移向量是 `∑j (m(j):ℝ)•b(j)`，目标平移向量
是使用同一个 m 的 `∑j (m(j):ℝ)•b′(j)`。这些平移的逐点关系
来自所构造的同一个基等价的线性性，没有输入该原 F 的
平移等变性。两组实基及同一索引的配对仍是明示的周期输入，
本轮没有从原 h/d 构造尖点上的这两组周期基。

三个完整模块串行本地 Lean 成功，四项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。
四次完整失败尝试全部排除；其中的部分标准闭包、`sorryAx`
诊断及警告均未接收。仅修正距离平方规范化、实基类型的
命名空间、反向算子范数界的常数推断及原正高度证明的显式参数，不改变数学条件和
目标陈述，不压制诊断。

前两个模块以实际水平 T 及明示的水平控制、满射或等变条件
为相应输入；第三个模块从明示的两组实基构造 T、F 及全部
距离控制、满射性和上述全部整数周期关系。尚未为原给定同伦等价诱导的同一个全甲板群
同构 d 构造尖点水平映射 T，也没有完成尖点与紧核心的原
全局等变拼接或迫使原交比保持。完整有限体积 Mostow–Prasad
仍为 **ACTIVE/INCOMPLETE**，保留非紧尖点、非可定向情形、
两侧原度量及原 h 所诱导的同一个 d。Lean 源仍在忽略目录
`.lake`，仅交付研究笔记，没有跟踪 Lean、准入、冻结或新颖性
声明。逃逸审计仍未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 正规平移周期、有限轨道平均与尖点仿射修正

`h3_affine_finite_index_zero_stabilizer_constructs_fixed_shift` 对实际
实仿射表示 `ψ : G →* (ℂ ≃ᵃ[ℝ] ℂ)` 和给定的有限指数子群 H，
若每个 h∈H 都满足 `ψ(h)(0)=0`，便构造整个 G 的固定点 c。
证明先建立实际求值作用，由 H 包含于零点稳定子推导实际零点
轨道有限，再取这个非空有限轨道的重心。仿射组合保持重心且
每个群元素置换同一个轨道，故每个 `ψ(g)` 都固定 c。
这里不要求整个 G 有限、H 正规或作用保持定向，也没有输入
固定点。有限指数和所有 H 元素固定零点仍是明示条件。

`h3_affine_period_linear_compatibility_constructs_full_conjugacy`
对同一个 G 的两个实际实仿射表示 r、s，给定可逆连续实线性
A 和有限指数 H，若每个 g、z 满足
`A(r(g).linear(z))=s(g).linear(A(z))`，且每个 h∈H 满足
`A(r(h)(0))=s(h)(0)`，则构造实际 c 和同一个
`T(z)=A(z)+c`，证明 T 双射及每个 g、z 的精确关系
`T(r(g)(z))=s(g)(T(z))`。它实际构造平移缺陷仿射表示：
`δ(g)=s(g)(0)-A(r(g)(0))`，`ψ(g)(c)=δ(g)+s(g).linear(c)`，
从原 r、s 的乘法及上述线性兼容性证明该表示的乘法，再用
前一重心构造修正 c。没有输入 c、T 或完整仿射共轭关系；
T 的线性部分保持为上述同一个可逆 A，没有通过平均任意
映射来假定可逆性。这个阶段仍输入每个 g 的线性兼容性。

`h3_normal_translation_periods_construct_full_affine_conjugacy`
进一步从周期数据推导该线性兼容性。条件是同一个 G 的实际
仿射表示 r、s，有正规有限指数 H，在两侧每个 h∈H 都按
`z↦z+r(h)(0)`、`z↦z+s(h)(0)` 平移；给定两组实际实基
`b,b′ : Module.Basis (Fin 2) ℝ ℂ`，每个 h∈H 的两侧平移
向量使用同一个整数系数族分别展开在 b、b′ 中，且 b 的每个
基向量实际出现为某个源 H 元素的平移向量。由两组基构造
同一个连续实线性 A，H 的正规性将每个周期的共轭仍留在 H；
比较实际共轭平移的两侧向量，然后用基的外延性，导出每个
g 的线性兼容性。随后构造同一个 c 及双射 T，对所有 G 元素
和所有水平点实现上述仿射关系。没有输入线性兼容性、T、c
或仿射共轭；H 的正规性、有限指数和全部匹配周期仍是输入。
没有增加定向保持条件，因此条件允许外围作用含反射。

`h3_prescribed_period_data_construct_original_controlled_equivariant_map`
将此构造接回原 H³。输入是两个给定无穷远稳定子群 G、G′ 的
群同构 d，两侧实际原 H³ 等距表示在每个群元素处都按单位
实比例固定原无穷远零光锥标架射线，以及在所有水平点处与
原水平映射相等的实际仿射表示 r、s。再输入源 G 中上述正规
有限指数 H、两组实基、所有同系数周期与源基向量的实现；
目标仿射表示使用同一个 `s.comp d.toMonoidHom`。
由这些数据构造同一个 c、T(z)=A(z)+c 及原高度保持延伸
`h3PeriodAffineHeightExtension b b′ c`。A 与 A 的逆的算子范数
实际给出 C、D≥1，在每个原 H³ 点对上导出
`dist(p,q)-arcosh(D²)≤dist(F(p),F(q))≤dist(p,q)+arcosh(C²)`，
证明同一个 F 满射，且对每个 g∈G、每个原点 p 精确满足
`F(ρ(g)(p))=ρ′(d(g))(F(p))`。没有输入 F、距离控制、满射性、
水平或原逐点等变性，也没有定向保持条件。

这最后一段是无穷远稳定子群的条件桥接，不能把“所有 G
元素”理解成有限体积流形的整个甲板群。两侧尖点稳定子群的
识别、单位缩放、实际水平仿射表示、正规有限指数平移子群及
周期数据仍未从原给定 h/d 构造；这里的 d 也尚未被实现为原
同伦等价诱导的同一个全甲板群同构在尖点上的限制。全局尖点
与紧核心的受控粗稠密等变拼接和原交比保持仍缺，完整非紧、
含尖点、非可定向、两侧原度量及原 h 所诱导同一个全甲板群 d
的 Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**。

四个完整模块串行本地 Lean 成功，四项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。四次完整
失败尝试全部排除，未接受其 `sorryAx` 诊断或警告；修正仅为
实例/仿射强制转换、同一个原逆像的显式化、已有正规性证明
参数和单位实标量类型，不压制诊断。Lean 仍在忽略目录
`.lake`，仅交付研究笔记，没有跟踪 Lean、准入、冻结或新颖性
声明。逃逸审计仍未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


### 原甲板群限制、自由作用与构造的公共平移子群

`h3_original_unit_infinity_action_constructs_affine_representation`
对给定原 H³ 等距表示，若每个群元素以单位实比例固定原
无穷远零光锥射线，实际构造水平仿射群表示。水平距离保持和
满射性给出实际水平等距映射，Mazur–Ulam 给出其实仿射结构；
原表示的乘法和原水平图与高度无关的性质证明群表示乘法。
仿射表示及其与原水平图的逐点相等关系都成为结论，没有输入
这些关系，也没有定向保持条件；单位缩放仍是输入。

`h3_original_full_deck_d_period_restriction_constructs_cusp_map`
保持同一个给定全群同构 `d : Γ ≃* Γ′`、两侧原 H³ 表示及
源子群 `P : Subgroup Γ`。若每个 P 元素及其同一个 d 的像都
以单位实比例固定原无穷远射线，实际构造两侧在同一个 P 上的
仿射表示，目标表示直接沿 `d` 和原包含映射拉回。给定
`H : Subgroup P` 的正规性、有限指数、两侧实际原水平平移、
两组实基、所有 H 元素的同整数系数周期匹配及每个源基向量
的实现后，构造原高度延伸 F，推导全部原双曲距离双边加性界、
满射性和每个 g∈P、每个原点 p 的关系
`F(ρ(g)(p))=ρ′(d(g))(F(p))`。这里不再输入局部 d、仿射
表示或水平图相等关系；P、单位缩放和周期子群数据仍是输入。

`h3_free_unit_infinity_horizontal_fixedpoint_forces_identity`
在原单位无穷远作用及原 `FreeRepresentation` 条件下，将
水平固定点实际提升为高度 1 的原 H³ 固定点，推出原群元素
为单位元。`h3_free_unit_infinity_excludes_nontrivial_horizontal_rotation`
继而对原水平公式 `z↦b+u*z`，在 u≠1 时构造
`b/(1-u)`，由原自由性和单位元原水平作用推出矛盾，因此
u=1。没有输入水平自由性或排除旋转的结论。

`h3_free_unit_infinity_constructs_normal_translation_subgroup`
对同一原单位无穷远自由表示，构造实际水平仿射表示 r，并取
其实际线性群表示的核 H。原旋转/反射分类和前述旋转排除
说明线性像至多含恒等及一种反射：任意两种反射的乘积是
旋转，原自由性迫使该乘积的线性部分为恒等，故反射线性
部分相同。实际线性像落在一个至多两元素集合中，从而推导
H 正规、有限指数且 `H.index≤2`，并证明每个 H 元素的原
水平作用都是平移。H、正规性、有限指数、平移结构及定向
保持条件均非输入；原自由性与单位缩放仍是条件。

`h3_same_full_deck_d_constructs_common_peripheral_translation_subgroup`
对同一个原全群同构 d、两侧原自由表示和给定 P，若 P 及其
同一个 d 的像满足上述单位无穷远条件，则沿原包含映射与 d
证明两侧在同一个 P 上的自由性，构造两侧实际仿射表示和
各自指数至多 2 的正规平移核。取它们在 P 内的交 H，推导
H 正规、有限指数且 `H.index≤4`，两侧每个 H 元素都按实际
原水平平移作用。不输入公共 H、正规性、指数或两侧平移
结构，也不选择新的目标同构；允许原作用含反射。

`h3_free_same_full_deck_d_constructs_period_cusp_extension`
将这个公共 H 直接接入原尖点映射构造。量词顺序是：从上述
两侧原自由性、同一个 d、P 和单位无穷远条件实际构造
正规有限指数 H，随后对任意两组实际实基，在每个 H 元素的
同整数系数原周期匹配及每个源基向量实际实现的条件下，
构造同一个 c 和原高度 F，由两组基线性等价及其逆的算子
范数给出 C、D≥1，对所有原点对证明
`dist(p,q)-arcosh(D²)≤dist(F(p),F(q))≤dist(p,q)+arcosh(C²)`，
并证明 F 满射及所有 g∈P、原点 p 的上述同一个 d 的作用
关系。没有输入 H、两侧平移、仿射表示、F、控制常数或满射性。
两组基、秩二周期存在性及同系数匹配仍未构造，不能把这个
条件结论理解为已证明这些周期条件一定成立。

P 仍是给定子群，尚未从原有限体积流形识别为实际尖点稳定子；
两侧单位无穷远规范化及原同伦等价诱导的 d 与这些数据的
绑定仍缺。所有 P 元素的等变性不等于整个原甲板群的等变性。
全局尖点/紧核心拼接、粗稠密性与原交比保持尚未完成；完整
含尖点、非可定向、两侧原度量及原给定同伦等价的
Mostow–Prasad 仍为 **ACTIVE/INCOMPLETE**。

六个完整模块串行本地 Lean 成功，七项公理闭包仅含
`propext`、`Classical.choice`、`Quot.sound`，零警告。三次完整
诊断尝试全部排除，其中一次编译退出 0 但含一项风格警告；
另两次退出 1 的 `sorryAx` 诊断均未接受。修正限于既有
强制转换、原坐标展开、隐式参数和推荐的策略语法，不改
数学条件或压制诊断。Lean 仍在忽略目录 `.lake`，跟踪交付
仅为研究笔记，无跟踪 Lean、准入、冻结或新颖性声明。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 原等距共轭、单位缩放及实际整数周期格

完整终点仍是连通、完备、曲率 −1、有限体积的双曲三维流形上的
Mostow–Prasad 刚性，包含非紧尖点和非可定向情形、两侧原度量、
同一个给定同伦等价及其诱导的全甲板群同构。本批不完成该终点。

### 任意原无穷远比例的共轭及离散群中的单位比例

对实际原 H³ 等距变换 e，若其原 Lorentz 作用以实比例 a 固定原无穷远射线，
构造 a>0 及实际实线性等距 R。对于每个原水平平移向量 u，证明实际群内
e·translation(u)·e⁻¹=translation(a·R(u))，以及向量长度为 a‖u‖。
R 可以包含反射；没有以纯膨胀代替原 e，也没有定向保持或单位比例前提。

对这个原 e，在其比例 a<1 的条件下，构造原共轭序列的实际平移向量
aⁿ·Rⁿ(u)，证明它趋于零，以及 eⁿ·translation(u)·e⁻ⁿ 在原等距群的
compact-open 拓扑中趋于恒等。保留原 e 的线性部分和原作用。

若同一个原等距子群 K 在上述诱导拓扑下离散、包含非零原水平平移
translation(u)，且 e∈K 以实比例 a 固定该原射线，则排除 a<1：
同一个 K 中的共轭序列趋于恒等，离散性迫使它最终恒等，与 u≠0 矛盾。
再对原 e⁻¹ 应用同一论证排除 a>1，从而推出 a=1。
离散性与实际非零平移的存在在此群论结论中仍是前提。

对实际原商覆盖 F:H³→M、其原甲板等距表示 ρ 及每点的原作用等式，
从覆盖本身推出同一个 ρ.range 的离散性。因此，当该实际原表示像中
存在给定非零水平平移时，对于任意给定原甲板元素 g 及其给定原射线比例 a，
推出 a=1。此处不输入离散性或单位比例；非零原平移的存在仍需提供。

### 从原自由平移作用构造整数格对应

对同一个原群 G 的两侧实际 H³ 表示，若两侧均满足原 FreeRepresentation，
且每个原元素确实是给定原偏移 u(g)、v(g) 的完整水平平移，
构造实际加性偏移同态和其像的整数子模 L、L′，并构造整数线性等价 e:L≃L′，
匹配每个同一个原 g 的偏移。偏移的加法律及单射性从原表示乘法和原自由性推出；
不输入原 G 的交换性、偏移同态、格或格等价。这里不推出离散性、秩二或全水平张成。

对同一个给定全甲板群同构 d、两侧原自由 H³ 表示及给定 P，
在每个 P 元素及其同一个 d 的像均满足原单位无穷远条件下，
先构造 P 内公共正规有限指数 H、指数至多 4，再构造两侧的完整原平移作用、
实际整数偏移子模及整数线性等价，匹配每个原 H 元素。
原水平公式连同原单位高度公式用于重建完整原等距平移，
没有把仅水平图的相等当成整个 H³ 等距映射相等。
全群同构始终是原同一个 d；不输入局部替代 d、H、格等价或定向条件。

对实际原商覆盖及其甲板表示、原作用等式，如果整数子模 L 的每个元素
对应的完整原水平平移属于同一个原表示像，则从实际甲板像的离散性、
原平移映射的连续性及单射性，推出 L 在原水平平面的诱导拓扑下离散。
这里不输入 L 的离散性；每个平移的原表示像成员关系仍是前提。

### 原覆盖数据下的匹配秩二基：全张成条件仍开放

对两侧实际原商覆盖、两侧甲板表示及原每点作用关系、同一个给定全群同构 d、
给定 P 和每个 P/d 像的原单位无穷远条件，先从原覆盖取消律推出两侧原自由性，
构造公共 H、两侧完整原平移、实际整数偏移子模 L、L′及其整数线性等价，
并从两侧原覆盖分别推出两个实际偏移子模的离散性。

**在这些 H、L、L′构造之后**，若两个实际偏移子模各自的实线性张成均为整个 ℂ，
则通过 Mathlib 的整数格秩定理构造两组 Fin 2 索引的实际实基。
输送同一个实际整数基，得到每个原 H 元素在两侧偏移的同整数系数匹配，
并推出每个源基向量由实际 H 元素实现。
这些基、整数系数匹配和实现关系均为构造结果；不输入实基、周期匹配、
自由性、离散性、公共 H 或格等价。两个原实线性全张成等式仍是条件，
本批没有从原有限体积几何证明它们。

上述整合不等于已识别实际尖点子群，也不等于已为每个原尖点构造非零平移。
给定 P 的原单位射线条件、实际尖点识别、原格全水平张成及这些数据与
原给定同伦等价诱导的 d 的具体绑定仍缺。每个 P 元素的作用关系不等于
全甲板群等变性；全局受控且粗稠密的同一个 d 等变映射、原交比保持及完整刚性
仍未完成。任意原 h 的提升无需与受控映射一致；后续仍应构造同一个 d 的映射
并使用既有同伦桥接。

本地串行核验为九个完整成功模块、十一项标准公理闭包、零警告。
四次完整诊断尝试全部排除：两次退出 1，另两次退出 0但有未抑制警告；
这些尝试中的标准闭包和 sorryAx 诊断均不计入成功结果。
独立源码/笔记/摘要审查及远端发布在本稿准备时仍待完成。
跟踪交付仅为本研究笔记；Lean 源和证据仍在忽略目录 .lake，
不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 从实际水平商测度构造受控尖点映射

对两侧实际原商覆盖 F、F′、两侧原甲板等距表示及每点的原作用等式，
同一个给定全甲板群同构 d、给定子群 P，以及每个 P 元素及其同一个 d 的像
均以单位实比例固定原无穷远射线的条件，先构造 P 内公共正规有限指数 H，
指数至多 4、两侧完整原水平平移、实际整数偏移子模 L、L′及两侧诱导离散拓扑。
在这些对象构造之后，若两个实际子模都实线性张成整个 ℂ，
则构造两组实际实基、偏移 c 和常数 C、D≥1，使实际原仿射高度延拓 F₀ 满射，
并对任意原 H³ 点 p、q 满足

dist(p,q) − arcosh(D²) ≤ dist(F₀p,F₀q) ≤ dist(p,q) + arcosh(C²)。

该映射还满足每个原 P 元素及每个原点的精确关系
F₀(ρ(g)p)=ρ′(d(g))F₀(p)。
实基、周期匹配、源基实现、映射、控制常数及满射性均由证明构造，
不作为该结论的输入；两个原全张成等式在这个版本中仍是条件。
每个 P 元素的关系不等于全甲板群等变性。

### 原加性商的紧性与全张成

对任意有限维实赋范空间 E 中的实际整数子模 L，若原加性商 E/L 紧，
则证明 L 实线性张成整个 E。若该实张成是真子空间，
构造在它上恒为零的非零实线性泛函；这个同一个泛函连续且满射到 ℝ，
并下降到原商。原紧商的连续像于是会是整个 ℝ，与 ℝ 无界矛盾。
该结论不输入离散性、整数秩或实基。

因此，在前述两侧原覆盖、同一个 d、给定 P 和每个 P/d 像的原单位射线条件下，
先构造同一个 H 和原偏移子模 L、L′之后，若两个实际原加性商 ℂ/L、ℂ/L′均紧，
即可推出两个原全张成等式，并构造上述原受控满射映射及其每个 P 元素的精确关系。
这里不输入全张成、周期基、匹配、映射或控制；两个实际水平商的紧性仍需提供。
这不是原三维流形紧性的假设，也不是非均匀双曲格子环境群商紧性的结论。

### 用实际有限不变测度替代商紧性前提

对有限维实赋范空间 E、实际整数子模 L、原加性商 E/L 的原拓扑与 Borel 结构，
若该原商上有有限、非零、正则且平移不变的测度 ν，
则从正则性、非零性及不变性推出非空开集正测度。
若原商不紧，Mathlib 的局部紧加性群不变测度定理将使 ν 的总质量无穷，
与其有限性矛盾。因此构造原商紧性，并推出 L 的实全张成；
紧性、全张成和离散性均不是这个测度论结论的输入。

最终的尖点整合仍保留两侧实际原覆盖、原每点作用等式、同一个给定全群同构 d、
给定 P 和每个 P/d 像的原单位无穷远条件。
先构造同一个 H、实际原 L、L′和两侧诱导离散拓扑之后，
若两个实际原加性商各自在自己的 Borel 结构下有有限、非零、正则且平移不变的测度，
则构造两侧商紧性和原全张成，再构造原受控满射映射，
满足全部原 H³ 点的上述距离界和每个原 P 元素的同一个 d 精确关系。
这个版本不输入商紧性、全张成、基、周期匹配、源基实现或受控映射。
两侧实际水平商测度的存在和这些性质仍是条件，
没有把环境等距群的非均匀格子商与这里的加性商混同。

原有限体积流形的尖点识别、非零原水平平移与单位射线条件、
从原尖点体积构造上述两个水平商测度，以及与原给定同伦等价诱导 d 的具体绑定，
仍需证明。全甲板群的同一个 d 等变受控粗稠密映射、原交比保持及完整刚性仍未完成。
连通、完备、曲率 −1、有限体积的完整 Mostow–Prasad 终点继续包含非紧尖点、
非可定向情形、两侧原度量和同一个给定同伦等价；任意原 h 的提升无需就是受控映射。

本地串行核验为五个完整成功模块、五项标准公理闭包、零警告。
一次完整失败尝试退出 1，有两个名称诊断、零警告、零闭包输出，整体排除；
仅将测度正则性类限定到它的原命名空间后通过，没有更改数学前提或抑制警告。
独立源码、笔记及摘要审查和远端发布在本稿准备时仍待完成。
跟踪交付仍仅为研究笔记；Lean 源和证据留在忽略目录 .lake，
不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 从原高度柱有限重数构造水平商测度

本批先对原 H³ 的内禀 Hausdorff 三维体积证明：若原水平集合 K⊆ℂ 可测、H>0，
则 K 上高度大于 H 的原柱体积为

volume(K) · ofReal((2H²)⁻¹)。

这里的体积和柱来自既有原黎曼源构造，不输入替代坐标测度或柱体积公式。

### 原覆盖的单射柱与有限重数柱

对实际原商覆盖 F、原源和目标黎曼度量 gH、gM 各自与原 edist 的等式，
原局部微分同胚及切向度量保持、原甲板表示 ρ 与每点原甲板作用的等式，
以及原目标总体积有限的条件，若 K 可测、H>0 且 F 在该原高度柱上单射，
则证明原目标柱像体积等于上述原柱体积，进而证明原水平 Lebesgue 体积 volume(K) 有限。
单射性仍是这一版本的几何条件。

为处理有限重数，对原 H³ 到原 Borel 度量空间的局部同胚 F，若 F 在每点邻域保持原距离，
且原可测集合 D 内每个实际纤维的扩展自然基数至多为有限 k，
则证明原内禀体积 μH(D) ≤ k·μM(univ)。
证明构造可数原等距局部片、两两不交的可测源片及其原 Borel 像；
原纤维基数界给出像的重叠数界，再通过有限指标函数和的积分及无穷和推出体积界。
这里不要求 F 在 D 上单射，不输入源体积与像体积的替代等式。
一般可测族的有限重叠测度和引理用于这个原 H³ 消费者。

在前述实际原 F、gH、gM、原 edist 等式、原局部微分同胚及切向度量保持、
原 ρ 和每点作用、原目标有限体积条件下，若 K 可测、H>0，
且这个同一个 F 在原 K 高度柱中的每个实际纤维至多有有限 k 个点，
则证明

volume(K) · ofReal((2H²)⁻¹) ≤ k·gM.volumeMeasure(univ)，

并推出原 volume(K) 有限。有限 k 仍是几何条件；k>1 时不宣称原柱像与源柱体积相等。

### 自动基本域和原水平商测度

对原 ℂ 中的实际整数子模 L，若 L 的诱导拓扑离散，
则由同一个原加性商映射 q:ℂ→ℂ/L 的覆盖性质自动构造 Borel 集合 K，
使 q 在 K 上单射、q(K)=univ，且 K 为 L 的原平移作用的加性基本域。
构造不输入基本域存在、秩、实全张成、商紧性或有限体积。
使用的第二可数 Borel 源局部同胚截面引理有这个实际水平商消费者；
离散性本身不保证所构造 K 的体积有限。

对同一个原离散 L 的加性基本域 K，若原 Lebesgue 体积 volume(K) 有限，
则构造原 ℂ/L 上的实际测度 ν=(volume.restrict K).map q，
并证明它有限、非零、正则、平移不变，以及 ν(univ)=volume(K)。
非零性来自原基本域和原非零 Lebesgue 测度；不变性来自原加性商测度定理。
由前批的实际有限非零不变测度结论，进一步推出原加性商紧性及 L 的实全张成。
该构造不输入商测度或其这些性质，也没有把原加性商与非均匀格子的环境群商混同。

最终整合保留前述实际原 F、gH、gM、各自原 edist、原局部微分同胚及切向度量保持、
原 ρ 与每点原作用、原目标有限体积，以及给定原离散整数 L。
先自动构造同一个原 Borel 基本域 K；在构造之后，若存在 H>0 和有限 k，
使这个原 F 在这个原 K 高度柱中的每个实际纤维至多有 k 个点，
则得到上述原源柱体积上界及原 volume(K) 有限，构造同一个原商测度 ν，
并推出它的有限、非零、正则、不变性、精确总质量、原商紧性和原 L 实全张成。
另保留柱上单射的整合版本，可额外给出原目标柱像的精确体积。
两个版本都不输入基本域、有限水平体积、商测度及其性质、商紧性或全张成。

本批没有证明上述原高度柱的有限纤维界。原精确不变 horoball、原尖点群识别、
非零平移和单位无穷远条件，以及从 P 内有限指数平移子群 H 推出实际纤维界仍需证明。
有限重数路线保留非可定向尖点可能出现的反射或滑移作用，但未宣称这些几何义务已闭合。
两侧原对象与同一个指定同伦等价诱导的全甲板同构 d 的绑定、
全甲板群同一个 d 的原受控粗稠密映射、原边界交比保持及完整刚性仍未完成。
完整目标继续是连通、完备、曲率 −1、有限体积的 Mostow–Prasad，包含非紧尖点、
非可定向情形、两侧原度量和同一个给定同伦等价；任意原同伦映射的提升无需就是受控映射。

本地串行核验为七个完整成功模块、十项标准公理闭包、零警告。
三个完整失败尝试保留并整体排除：一个名称错误尝试，以及有限重叠模块的两次展开诊断。
其中有限重叠模块首次失败有四个警告，未通过抑制消除；修正类型中的可判定性、
目标展开和局部实例绑定后通过，失败模块内的局部闭包输出均不计入接受结果。
独立源码、笔记及摘要审查和远端发布在本稿准备时仍待完成。
跟踪交付仅为研究笔记，Lean 源和证据留在忽略目录 .lake，
不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 从原 horoball 交叠条件构造两侧测度和受控尖点映射

对原商覆盖 F:X→Y、原甲板群 Γ、实际群同态 i:P→Γ 和有限指数子群 H≤P，
若原集合 D 的每个相交甲板变换均在 i(P) 中，且 D 在每个 i(H) 轨道中至多含一个点，
则证明同一个原 F 在 D 中的每个实际纤维的扩展自然基数至多为 [P:H]。
证明把非空原纤维单射到原陪集空间 P/H；这里不要求 H 正规或 i 单射。

对原 H³ 商覆盖 F、原表示 ρ 与每点原作用的等式、实际 i:P→原全甲板群、
有限指数 H≤P、原完整平移等式 ρ(i h)=horizontalTranslation(u h)、实际整数 L=range(u)，
以及原水平集合 K 上原加性商映射的单射性，若给定高度 T 的原 horoball 的每个相交
甲板变换均属于 i(P)，则证明该原 K 高度柱中每个实际 F 纤维至多有 [P:H] 个点。
H 轨道唯一性由原水平商单射性和原平移坐标及高度不变性推出，不输入纤维界。
这证明了原 horoball 交叠条件到纤维界的蕴含；交叠条件本身仍是输入。

在同一个原 F、原 gH/gM 各自与原 edist 的等式、原局部微分同胚及切向度量保持、
原 ρ 与每点原作用、原目标有限总体积条件下，若上述实际 i/H/u/L 满足完整平移和
range 等式、L 的诱导拓扑离散，且存在 T>0 满足上述原 horoball 交叠条件，
则先自动构造原 Borel 加性基本域 K，再推出原每个高度柱纤维至多有 [P:H] 个点、
原 volume(K)·ofReal((2T²)⁻¹)≤[P:H]·gM.volumeMeasure(univ) 及原水平体积有限。
由这个同一个 K 构造原 ν=(volume.restrict K).map q，证明其有限、非零、正则、
平移不变和精确质量 ν(univ)=volume(K)，并推出原加性商紧性和原 L 实全张成。
这里不输入基本域、水平体积有限、柱单射、纤维界、商测度及其性质、商紧性或全张成。

两侧整合保留同一个 Lean 宇宙中的原 M,N、原 F:H³→M 和 F':H³→N、两侧原商覆盖及每点原甲板表示，
原 gH/gM/gN 各自与原 edist 的等式、两侧原局部微分同胚及切向度量保持、
两侧原目标各自有限总体积，以及同一个原全甲板群同构 d 和实际 P≤原源甲板群。
若 P 及 d(P) 的原 Lorentz 作用均以系数 1 固定原无穷远 null 向量，且两侧分别有
T,T'>0，使原 horoball 的所有相交甲板变换分别属于 P 和这个同一个 d(P)，
则构造同一个 H≤P，H 在 P 内正规、有限指数且 [P:H]≤4，以及两侧实际离散整数
平移子模 L,L' 和原完整平移作用；随后自动构造两侧原 Borel 基本域 K,K'，
在两侧分别由同一个 H 推出原纤维界≤[P:H]、原体积界、原有限水平体积和上述实际
商测度及全部性质、原商紧性及原实全张成。由这两侧全张成构造原匹配周期基，
再构造原满射仿射高度映射，给出原距离的双向加性控制，并对每个 g∈P 严格满足
与原 ρ'(d(g)) 的等变等式。整合不输入两侧秩、全张成、周期基、基本域、水平有限体积、
商测度、纤维界或柱单射；两侧原对象、同一个 H 和同一个 d 从头到尾保持绑定。

本批仍未证明原 horoball 交叠条件的存在，或从原有限体积导出原尖点群识别及单位
无穷远作用；P 和两侧单位条件仍是输入。每个 P 元素的等变性不等于全甲板群等变性。
同一个指定同伦等价诱导这个 d 的绑定、全甲板群受控粗稠密映射、原边界交比保持及
完整连通、完备、曲率 −1、有限体积 Mostow–Prasad 仍未完成；完整目标保留非紧尖点、
非可定向情形、两侧原度量和同一个给定同伦等价。

本地串行核验为三个完整成功模块、四项标准公理闭包、零警告。
两个完整失败尝试保留并整体排除：纤维模块的三个展开诊断和两侧整合的一个括号诊断。
独立源码、笔记及摘要审查和远端发布在本稿准备时仍待完成。
跟踪交付仅为研究笔记，Lean 源和证据留在忽略目录 .lake，
不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 从原平移格子构造原 horoball 交叠条件

对任意原 H³ 等距变换 e，若原逆作用的无穷远 null 向量在原 light 坐标中为
c·finite(z)，c>0，则从原 Lorentz 配对证明精确恒等式
c·(|horizontal(p)-z|²+t(p)²)·t(e p)=2t(p)，因而每个原点满足
原高度乘积 t(p)t(e p)≤2/c。这里使用原等距变换、原高度和原配对，包含反射。
原正向和逆向作用的有限边界系数相等；正系数自动给出该原作用的有限边界坐标。
因此若原群表示在指定 P 外的原系数有统一正下界 c₀，则构造 T>0、T²>2/c₀，
证明原高度大于 T 的 horoball 的每个相交群元素都属于这个同一个 P。
这个中间结论仍以统一正下界为前提。

对原等距变换 e 的原正向无穷远有限 light 坐标 c·finite(z)、c>0，通过原 N=W·translation(-z)·e 的归一化，
证明原 N 以 c/2 缩放无穷远向量，并由原实线性等距变换 R 构造 v，
满足 ‖v‖=(c/2)‖u‖ 及原等式
e·translation(u)·e⁻¹=translation(z)·W⁻¹·translation(v)·W·translation(-z)。
R 可包含反射；没有辅助 PSL₂ 表示或可定向前提。于是当原中心 zₙ 收敛、原正系数
cₙ 趋于 0 时，固定原平移的这些原共轭在原 compact-open 拓扑中趋于恒等元。

对在原 compact-open 诱导拓扑中离散的同一个原 K，若每个原等距变换 eₙ 都属于这个同一个 K、原非零平移 T(u) 属于 K、每个 eₙ 的原正向有限 light 坐标为 cₙ·finite(zₙ) 且 cₙ>0、原中心 zₙ 都属于同一个原紧集 C，则原系数 cₙ 不可能趋于 0：抽取原中心收敛子列后，原共轭仍在这个同一个 K，离散性迫使其最终等于恒等元，与原平移非零矛盾。
对这个同一个诱导离散的原 K 和其中的原非零平移，若给定留在同一个 K 内且保持原系数的紧中心归一化，则构造 K 中所有原正系数的统一正下界；这一中间结论仍输入紧归一化和原非零平移。

若上述原 K 离散，并给定实际整数子模 L≤ℂ，其在原 ℂ 中的诱导拓扑离散、
实张成为整个 ℂ，且每个原 translation(l) 都属于这个同一个 K，则自动构造原
整数基、原有界平移基本域及其紧闭包，并从原基导出一个原非零平移。
原有限边界中心在这个同一个 K 内由原 L 平移归一化，原系数保持不变；由此构造
K 中所有正原系数的统一正下界。这里不输入基、紧集、紧归一化、非零平移或系数下界。
L 的离散性和满实张成仍是输入，没有由原有限体积或尖点存在性证明它们。

对原商覆盖 F:H³→M、原完整甲板群、原表示 ρ 与每个原点上的作用等式，
若给定实际整数 L≤ℂ，在原 ℂ 中诱导离散且满实张成，其每个原 translation(l)
都在这个同一个 ρ.range 中，并给定 P≤原完整甲板群包含所有原系数为 0 的
甲板变换，则从原商覆盖导出 ρ.range 的原 compact-open 诱导离散性，构造
P 外的原统一正系数下界，再构造 T>0 和原 horoball 的每点交叠条件：
若 x 和 g·x 的原高度均大于 T，则 g 属于这个同一个 P。
不输入表示像离散性、系数下界、horoball 高度或交叠条件、紧集、基本域或周期基。
实际 L 的满实张成及原平移包含关系、P 对零系数甲板变换的包含关系仍为前提。

本批不能与上一批“由给定 horoball 条件推出满张成”的结论互相循环，冒充
已从原有限体积构造实际满秩平移格子。原尖点及格子存在性、实际 P 的识别、
两侧 P 与同一个给定同伦等价诱导的全甲板同构 d 的对应、全甲板群受控粗稠密映射、
原边界交比保持及完整 Mostow–Prasad 仍未完成。完整目标保留连通、完备、曲率 −1、
有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定同伦等价。

本地串行核验为六个完整成功模块、十七项标准三公理闭包、零警告。
三个完整失败尝试和三个完整 exit0 含警告尝试整体保留并排除，均无部分闭包获准。
源码、笔记和摘要的独立审查及远端发布在本稿准备时待完成。
跟踪交付仅为研究笔记；Lean 源及证据在忽略目录 .lake，不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 原无穷远稳定子及原覆盖上的 horoball 构造

对任意原 H³ 等距变换 e，原有限边界系数为 0 当且仅当存在 a>0，原 Lorentz 作用把原无穷远 null 向量变成其 a 倍。
对在原 compact-open 诱导拓扑中离散的同一个原 K，若原非零平移 T(u) 属于 K，则对每个 e∈这个同一个 K，上述伸缩 a 必须为 1。因此这些 e 的零系数条件恰好等价于固定原无穷远 null 向量；包含反射。

对原群表示 ρ，构造 Pρ={g | 原 ρ(g) 的 Lorentz 作用固定原无穷远 null 向量}，并证明它是原群的子群。若同一个原 ρ.range 在原 compact-open 诱导拓扑中离散，且含有一个实际原非零平移，则每个原 g 满足 g∈Pρ 当且仅当原 ρ(g) 系数为 0；同一个 Pρ 中每个原元素都保持每个原点的原高度。这里不输入 P、零系数包含关系或单位无穷远作用；表示像离散性和实际非零平移仍是这一中间结论的前提。

对原商覆盖 F:H³→M、原完整甲板群、原表示 ρ 与每个原点上的作用等式，以及原基点 p，若给定实际整数子模 L≤ℂ，其原实张成是整个原 ℂ，且每个原 T(l) 都属于这个同一个 ρ.range，则先从原覆盖导出原 ρ.range 和原 L 的诱导离散性，再由原 L 构造实际原非零平移。由此构造这个同一个原 Pρ，证明它恰好包含全部原零系数甲板变换，并证明其中每个原元素保持每个原点的原高度；再构造 Pρ 外的统一正系数下界 c₀ 和 T>0、T²>2/c₀，使每个原点 x 满足：若 x 和 g·x 的原高度均大于 T，则 g∈这个同一个 Pρ。

本结论不输入 P、零系数包含关系、单位无穷远作用、L 或表示像的离散性、非零平移、系数下界、紧集、基本域、周期基、horoball 高度或交叠条件。实际 L 的满实张成和每个原平移在原表示像内的包含关系仍是前提。源码直接输入原实张成等式；先导出 L 离散性，再内部建立 IsZLattice，避免该类型类在陈述处隐含要求预先给出离散性。

原有限体积下的尖点和实际满秩平移格子存在性仍待证明，不能把此前“给定 horoball 推出满张成”和现在“给定满张成推出 horoball”互相循环。两侧实际尖点及其稳定子与同一个给定同伦等价诱导的全甲板同构 d 的对应、全甲板群受控粗稠密映射、原边界交比保持及完整 Mostow–Prasad 仍未完成；完整目标保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定同伦等价。

本地串行核验为两个完整成功模块、四项标准三公理闭包、零警告；两个完整失败尝试保留并整体排除，零部分闭包获准。源码、笔记和摘要的独立审查及远端发布在本稿准备时待完成。跟踪交付仅为研究笔记；Lean 源及证据在忽略目录 .lake，不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 一个原非零平移给出的原系数下界

对任意原 H³ 等距变换 e 和原水平平移 T(u)，设 C(e) 为原无穷远有限 light 系数，A(e) 为原无穷远 null 向量像的第一 light 坐标，k=e·T(u)·e⁻¹，p 为原坐标点 (0,1)。从同一个原 Lorentz 作用证明
C(k)=‖u‖²C(e)²/2，A(k)≤4+‖u‖²C(e)A(e)，以及 cosh(dist(kp,p))=1+‖u‖²(A(e)+C(e))²/8。
这些量来自原等距变换和原度量；包含反射，不输入递推关系、位移界、满秩格子或 horoball。

对在原 compact-open 诱导拓扑中离散的同一个原等距子群 K，若一个原非零平移 T(u) 属于 K，则每个 e∈这个同一个 K 且 C(e)>0 都满足 1≤‖u‖²C(e)。证明在同一个 K 内构造 eₙ₊₁=eₙ·T(u)·eₙ⁻¹。反设 ‖u‖²C(e₀)<1 时，原系数保持正且严格下降，原第一 light 坐标有统一上界；上述原位移恒等式把全部后继变换放入实际原紧 evaluation ball。这个紧集与原离散 K 的交有限，与迭代单射矛盾。

该下界只需要上述原诱导离散性和一个实际原非零平移，不输入满实张成、周期基、基本域、紧中心归一化、系数下界或 horoball。常数不是最优 Shimizu 常数。它给出既有统一系数下界到原 horoball 引理所需的正下界；本批编译声明是上述量化共轭关系和原系数下界，没有新增绑定包装声明。

从原有限体积几何构造实际尖点和非零平移仍未完成。两侧实际尖点稳定子与同一个给定同伦等价诱导的全甲板同构 d 的对应、全甲板群受控粗稠密映射、原边界交比保持及完整存在唯一性仍待证明。完整目标保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定同伦等价。原系数下界减少了先给满秩格子再构造 horoball 的依赖，不能代替尖点存在性或完整刚性。

本地串行核验为两个完整成功模块、两项标准三公理闭包、零警告。4 个完整失败尝试和 1 个 exit0 含警告尝试整体保留并排除，无部分闭包获准。独立源码、笔记及摘要审查和远端发布在本稿准备时待完成。跟踪交付仅为研究笔记；Lean 源和证据位于忽略目录 .lake，不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 原非平凡单位无穷远稳定子给出的 horoball

对原 H³ 上一个非平凡群的等距表示，若每个元素在同一个原 Lorentz 作用中逐字固定单位无穷远 null 向量，且原表示的点作用自由，则内部构造出实际原非零水平平移 T(u)，并证明它属于这个表示的像。该构造不输入离散性、满实张成、格子、horoball 或方向假设。先复用原平移核的指数至多 2；对选定的非单位原群元素 g，自由作用排除 g²=1，因为此时原水平仿射作用固定 0 与 r(g)0 的中点。由指数至多 2 得到 g² 属于同一个原平移核，自由作用再保证其实际原平移偏移 u 非零；逐点核验完整原等距变换 ρ(g²)=T(u)。反射情形保留。

临时精确应用针对同一个原商覆盖 F、原完整甲板群表示 ρ 及其实际子群 P={g | 原 Lorentz 作用逐字固定单位无穷远 null 向量}。只在这个实际 P 非平凡的条件下，从原商覆盖直接导出限制表示 ρ|P 的自由性，应用上述新构造，并将其实际原非零平移见证送回同一个完整 ρ.range；原完整像的诱导离散性直接来自同一个原商覆盖。原零系数刻画给出 g∈P 当且仅当 C(ρ(g))=0。既有原 Shimizu 型下界再给出每个原 g∉P 都满足 c₀≤C(ρ(g))，其中 c₀=1/‖u‖²>0。因此存在 T>0 且 2/c₀<T²，使每个原 g 和原点 x 若同时满足 height(x)>T 与 height(g·x)>T，则 g∈这个同一个实际 P；P 的每个元素保持全部原点的原高度。C 是同一个原无穷远 null 向量像的有限 light 系数，height 来自原 H³ 坐标，所有动作和位移均绑定原度量与原甲板表示。

这个精确应用没有输入非零平移、格子、满实张成、系数下界或 horoball，也没有替换子群、度量、空间或表示；原商覆盖和实际 P 非平凡性仍是明确前提。精确应用只用临时 example 编译，没有新增绑定包装具名声明或 exact-check olean。真正新增的数学声明是非平凡自由单位无穷远作用构造非零平移。

从原有限体积几何构造实际尖点及其非平凡单位无穷远稳定子仍未完成；本次条件结论不能代替它。实际满实张成、两侧原外围群与同一个给定同伦等价 h 诱导的完整甲板同构 d 的对应、全甲板群受控粗稠密映射、原边界交比保持以及完整存在唯一性仍待证明。完整 Mostow–Prasad 目标继续保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定同伦等价。

本地串行核验为一个真正新增的完整成功模块、一项标准三公理闭包和一个完整成功的临时精确 example，均零警告。example 中显示的三项公理闭包属于已存在的依赖声明，不计为三个新定理；没有对匿名 example 宣称具名公理输出。2 个完整失败尝试和 1 个 exit0 含警告尝试整体保留并排除，无部分接受。新构造的实际编译基线为 bdb5a4a5f839b644541270ffa74778a987a3212a，精确应用的实际编译基线为 b97751e87972ff565e1de8eb24090ac8cc9288c1，没有因随后同步重放编译。独立源码、笔记及摘要审查和远端发布在本稿准备时待完成。跟踪交付仅为研究笔记，Lean 和证据位于忽略目录 .lake，不宣称跟踪 Lean、准入、冻结或新颖性。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 原有限体积下的条件满实张成与原平移共轭

对同一个原 H³ 商覆盖 F 及其完整原甲板表示 ρ，设实际逐字固定单位无穷远 null 向量的原子群 P 非平凡；原 Riemannian 度量 gH、gM 与两侧原 edist 一致，F 是原局部微分同胚并满足原内积相容，且原 gM 总体积有限。在这些原几何条件下，临时精确 example 内部构造 H≤P、实际原偏移 w:H→ℂ 和整数子模 L，使 H 正规且有限指数、指数至多 2，ρ(h)=T(w(h))、L=range(w)，L 在实际原诱导拓扑中离散，原水平商 ℂ/L 紧致，且 L 满实张成。

该应用先从同一个原商覆盖导出 P 上的原自由作用，再内部构造实际原非零平移、原系数下界及原 horoball。原平移核、实际偏移子模和原诱导离散性由既有结果构造；由实际原 horoball 交叠给出原覆盖纤维计数界，原有限总体积据此构造有限非零水平商不变测度，再得到紧商和满实张成。没有输入平移核、格子、满实张成、不变测度、非零平移、系数下界或 horoball。这是条件结论：原实际 P 非平凡性及上述原覆盖和度量相容条件仍是输入，不能把它说成原有限体积尖点存在性。

对任意原 H³ 等距变换 e、实际原 u≠0 和任意原 v，若原 e·T(u)·e⁻¹=T(v)，另一个临时精确 example 内部推出原无穷远有限 light 系数 C(e)=0，从而存在原 a>0 及原水平线性等距 R，使原 Lorentz 作用把单位无穷远 null 向量送到 a 倍自身，v=a·R(u)、‖v‖=a‖u‖、v≠0，且对每个原 w 都有 e·T(w)·e⁻¹=T(a·R(w))。若在上述同一个原共轭条件下 v=u，则 a=1，e 逐字固定原单位无穷远 null 向量。这一应用包含反射，没有输入无穷远固定性、方向、离散性或满实张成。

再对同一个原 compact-open 诱导拓扑中离散的等距子群 K，若实际原 H≤K 的每个元素都是原水平平移、H 含一个实际原非零 T(u)，且原 e∈这个同一个 K 正规化这个同一个 H，则另一临时精确 example 从原平移共轭的零系数推导与同一个 K 的原离散性推出 e 逐字固定原单位无穷远 null 向量，并保持全部原点的原高度；没有输入原固定性、缩放系数或高度保持。这里 H 已经是实际原平移子群，e 是实际原环境等距变换；任意抽象群同构把原外围群送到这样的目标子群仍未证明。

本批只编译三个临时精确 example，没有新增绑定包装具名声明或 exact-check olean。两次完整串行成功编译均零警告；显示的五项标准三公理闭包属于既有依赖声明，既不是五个新定理，也不是匿名 example 的具名公理报告。本批无失败或警告尝试，继承批次的失败排除、真实 COMMENT 及精确修正历史完整保留。原有限体积到满实张成应用的实际编译基线为 3908052551cf8a264c1934a9d00685f18ed2993c，本批平移共轭应用的实际编译基线为 9f573e8c9bc5373c5b219fe1eaf4a56e4153f5e1，没有重放已接受应用。独立源码、笔记及摘要审查和远端发布在本稿准备时待完成。跟踪交付仅为研究笔记；Lean 和证据位于忽略目录 .lake，不宣称新增 canonical Lean、准入、冻结或新颖性。

原有限体积几何中的实际尖点及非平凡单位无穷远稳定子存在性仍未完成。上述条件满实张成与原正规化者结论也未完成两侧实际外围群在同一个给定同伦等价 h 诱导的完整甲板同构 d 下的对应；不能假定目标抽象像已经是原平移子群或原单位无穷远稳定子。全甲板群受控粗稠密映射、原边界交比保持和完整存在唯一性仍待证明。完整 Mostow–Prasad 目标继续包含连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定同伦等价。
逃逸审计未完成，登记按 CLAUDE 3.9 暂缓：
https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 同一原 compact-open 诱导离散 K 中无限阶 e∈K 的边界固定点，以及忠实且原像按原 compact-open 诱导拓扑离散的 ρ:Multiplicative(ℤ×ℤ)→原 H³ 等距群的共同边界点

设 K 是同一个原 H³ 等距群中按原 compact-open 诱导拓扑离散的子群，原 e∈K 且 e 无限阶。一个临时精确 example 内部构造实际原规范化 future-null 边界点 b，使原边界作用满足 e·b=b。没有输入边界点、边界固定性、方向或线性轨道逃逸。原 e 的幂单射与实际原 evaluation 闭球的紧致性、原 K 的诱导离散性共同推出原幂轨道的位移无界；内部选择位移超过每个自然数的原幂轨道点，规范化实际原内部 Lorentz 向量落在四坐标紧立方体中，提取子列。逆时间坐标趋零与原 Lorentz 自配对关系证明极限属于实际原 null 边界，随后原 e 在自身幂轨道上的位移恒定和既有原有界距离端点相等结果推出固定性。规范化内部向量在取极限之前并不属于 null 边界；这里没有把仅适用于线性逃逸的全序列结果用于抛物轨道。

在上述同一个原诱导离散 K、原 e∈K 且 e 无限阶的条件下，另一个临时精确 example 构造同一个实际原边界点 b，使每个与原 e 交换的原环境等距变换 g 都固定这个同一个 b。各个 g 不要求属于 K；原交换关系使 g 在上述同一个原 e 幂轨道上的位移等于原基点 p 与原 g(p) 的距离，原有界距离端点相等据此给出共同固定性。结论是整个原中心化子的同一个共同边界点，而非为不同元素分别选择不同端点。

再对任意忠实的原群同态 ρ:Multiplicative(ℤ×ℤ)→原 H³ 等距群，若同一个原 ρ.range 在原 compact-open 诱导拓扑中离散，第三个临时精确 example 内部构造同一个实际原边界点 b，使每个原 ρ(γ) 都固定 b。原 e=ρ(ofAdd(1,0)) 的无限阶性由同一个原 ρ 的单射性内部推出，全部原交换关系由原域的群运算和同一个原 ρ 的乘法保持内部推出；没有输入无限阶元素、共同边界点、平移子群、方向、自由作用或有限体积。这将实际原抽象二秩群像接到共同边界固定性，仍未证明该像的原 null 射线缩放系数为 1，或该像已经是原水平平移子群及实际尖点群。

三个临时精确 example 的三个完整串行成功编译均零警告，没有新增具名绑定声明或 olean；九项打印的标准三公理闭包仅属于既有依赖声明，不是九个新定理，也不是匿名 example 的具名公理报告。本批两个完整失败尝试均保留并排除，没有从失败编译接纳任何部分证明；全部既有已接受源、回执与历史判词保持不变。前两个应用的实际编译基线为 c035f0fd652bcafb009fbba8f34998ed01ca3e48，抽象二秩像应用的实际编译基线为 0d5969e22734eda89266d63b43915bb66c4ace22，没有重放已接受应用。跟踪交付仅为研究笔记，Lean 与证据保留于忽略目录 .lake，无新增 canonical Lean、准入、冻结或新颖性声明。

实际原有限体积尖点及非平凡单位无穷远稳定子存在性、抽象外围群像的原单位射线缩放与平移/尖点分类、两侧实际外围群在同一个给定同伦等价 h 诱导的完整甲板同构 d 下的对应、全甲板受控粗稠密映射、原边界交比及完整存在唯一性仍未完成。共同边界固定性不能代替这些义务。完整 Mostow–Prasad 目标继续包含连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定 h。逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 实际原规范化 null 边界点的无穷远归一化

对任意实际原规范化 future-null 边界点 b，一个临时精确 example 内部构造原水平平移与 Weyl 字组成的同一个实际原等距变换 g，以及正数 c，使原 Lorentz 作用将同一个原 b 送到 c 倍的原无穷远向量。对于每个固定同一个原 b 的原等距变换 e，同一个原共轭 g·e·g⁻¹ 在原无穷远向量上的缩放系数恰为原 h3NullBoundaryTime(e,b)，且该系数也是其在每个原点上的高度乘子。这里没有输入 g 或单位缩放；所给 b 可接续此前共同边界构造，但本应用本身以实际原 b 为输入。归一化保留原作用、同一个共轭和同一个原缩放系数，不能将正缩放直接改称为系数 1。

## 实际原无穷远射线缩放 a≠1 的等距变换及与其交换的原无穷远射线固定者的共同水平中心

设同一个原等距变换 e 的实际原 Lorentz 作用在原无穷远向量上为 a 倍，且 a≠1。第二个临时精确 example 从原射线作用内部推出 a>0，并构造同一个原水平映射的唯一实际固定中心 z。a<1 时直接使用原水平距离缩放与 Banach 不动点定理；a>1 时由同一个原水平映射的单射性和满射性构造其实际逆映射，证明逆距离缩放为 a⁻¹，再使用 Banach。唯一性由同一个原距离缩放和 a≠1 推出。每个同样固定原无穷远射线且与原 e 交换的原环境等距变换都固定这个同一个水平中心 z；没有要求这些环境变换属于某个离散群，也没有加可定向或无反射条件。此结论仍以某个实际非单位缩放元素存在为条件，不证明忠实离散二秩像中存在这种元素。

## 同一忠实、原像按原 compact-open 诱导拓扑离散的 ρ:Multiplicative(ℤ×ℤ)→原 H³ 等距群中，同时固定原无穷远向量与原水平中心的元素为单位元

对同一个忠实原群同态 ρ，假定同一个原 ρ.range 按原 compact-open 诱导拓扑离散。若同一个原 ρ(γ) 实际固定原无穷远向量，且其同一个原水平映射固定实际中心 z，第三个临时精确 example 推出原抽象元素 γ=1。单位射线作用和水平固定性先使原点 (z,1) 固定，全部原自然数幂因此位于该原点半径 0 的紧 evaluation 闭球。原诱导离散性使该球与同一个原 ρ.range 的交有限；若 γ≠1，同一个原 ρ 的忠实性与原 ℤ² 的无挠性给出原幂单射，与该有限性交矛盾。没有输入自由作用、有限体积或不同表示；也没有把所有外围元素的单位缩放放入前提。

三个完整成功串行编译、三个临时精确 example、零警告、零新增具名声明或 olean。九项打印的标准三公理闭包仅属于既有依赖声明，不是九个新定理或匿名 example 的具名公理报告。两个完整失败尝试均保留并排除，没有从失败编译接纳部分证明。边界归一化的实际编译基线为 139f2ce4c4973649d849ef4a3e1f0e4f86a32cea，共同中心与单位中心核应用的实际编译基线为 7ab11138317ba8ffb82005252199fa014385188b；已接受应用没有重放。跟踪交付仅为研究笔记；Lean 与证据留在忽略目录 .lake，无 canonical Lean、准入、冻结或新颖性声明。

抽象外围群像中所有原射线缩放系数为 1、实际原平移/尖点分类、有限体积中的实际尖点及非平凡单位稳定子存在性、两侧实际外围群在同一个给定同伦等价 h 诱导的完整甲板同构 d 下的对应、全甲板受控粗稠密映射、原边界交比及完整存在唯一性仍未完成。完整 Mostow–Prasad 目标继续包含连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定 h。逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 同一忠实原二秩表示、原诱导离散像与所有像元素固定的同一实际原边界点上的缩放系数全部为 1

设同一个原群同态 ρ:Multiplicative(ℤ×ℤ)→原 H³ 等距群忠实，同一个原 ρ.range 按原 compact-open 诱导拓扑离散，并且每个原 ρ(γ) 都固定同一个实际原规范化 future-null 边界点 b。一个临时精确 example 在这些条件下推出：对每个原 γ，同一个原 h3NullBoundaryTime(ρ(γ),b)=1。这里没有输入单位缩放、归一化共轭、水平中心、自由作用或有限体积；实际原共同边界点 b 是本应用的输入，未在此重新构造。

证明内部构造同一个实际原水平/Weyl 等距变换 g，将原 b 送到正倍的原无穷远向量；同一个原边界时间成为 g·ρ(γ)·g⁻¹ 的实际原无穷远缩放及高度乘子。反设某个原元素具有非单位缩放，内部构造所有这些同一个原共轭元素共享的实际水平中心 z。令 p=(z,1)，并取实际原点 P=g⁻¹p，把所有共轭距离估计拉回同一个原 ρ 在同一个原 P 上的距离。紧 evaluation 闭球始终与同一个原 ρ.range 相交，并始终使用它在原 compact-open 拓扑下的诱导离散性，没有换用另一表示或离散性前提。

同一个原边界时间的对数定义原 ℤ² 上的加性特征。其核中的原元素固定原 P；原自然数幂落在原半径 0 的紧 evaluation 闭球中。原离散像的有限性交、同一个原 ρ 的忠实性和原 ℤ² 的无挠性推出核为零，故该加性特征单射。对原边界时间位于 [1/2,2] 的原元素，原距离不超过 arcosh(2)，因此同一个原紧 evaluation 球和原离散性使特征像在对应非空对数开区间中的交有限。实加性子群的稠密或循环二择一排除稠密分支；循环分支与原 ℤ² 的单射像矛盾，故原非单位缩放反设不成立。

一个完整成功串行编译、一个临时精确 example、零警告、零新增具名声明或 olean。四项打印的标准三公理闭包属于既有依赖声明，不是四个新定理，也不是匿名 example 的具名公理报告。两个完整失败尝试保留并排除，分别因依赖高度改写/API 名称/数值化简及剩余分子零项化简失败；没有部分接纳。成功 attempt3 的真实编译基线为 dad9d222ef27d4491bb20a8625b92c85052d3add，编译分支为 lane/math/mostow-h3-nonunit-common-center-20261003，宿主句柄为 34812；此前已经接受的源和编译证据未修改、未重放。跟踪交付仅为研究笔记，Lean 与证据位于忽略目录 .lake，无 canonical Lean、准入、冻结或新颖性声明。

本批只闭合上述同一忠实原二秩表示、原诱导离散像和给定实际原共同边界点条件下的单位缩放。实际原平移/尖点子群分类、有限体积中的实际尖点及非平凡稳定子存在性、两侧实际外围群在同一个给定同伦等价 h 诱导的完整甲板同构 d 下的对应、全甲板受控粗稠密映射、原边界交比及完整等距代表存在唯一性仍未完成。完整 Mostow–Prasad 目标继续保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定 h。逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 同一忠实原 ℤ² 表示与同一原 compact-open 诱导离散像内部构造共同边界点、单位缩放、同一归一化、自由作用、正规平移核及非零平移

设同一个原群同态 ρ:Multiplicative(ℤ×ℤ)→原 H³ 等距群忠实，且同一个原 ρ.range 按原 compact-open 诱导拓扑离散。一个临时精确 example 仅从这些条件内部构造同一个实际原规范化 future-null 共同边界点 b，并推出每个原 h3NullBoundaryTime(ρ(γ),b)=1。原 b 在本应用中是构造出的对象；没有输入 b、单位缩放、归一化共轭、水平中心、自由作用或有限体积。原无挠域与同一个原离散像的紧 evaluation 球幂论证还推出同一个原 ρ 在每个原点上的自由作用。

同一个应用内部构造实际原水平/Weyl 等距变换 g 和 c>0，使 L(g)b=c 倍原无穷远向量；随后构造实际群同态 Φ(γ)=g·ρ(γ)·g⁻¹，证明它忠实，并把同一个原 ρ 的自由作用通过同一个 g 搬运为 Φ 的自由作用。每个 Φ(γ) 的实际原 Lorentz 作用固定原无穷远向量本身，且保持每个原点的原高度。这里 Φ 由同一个原 ρ 与内部构造的同一个 g 定义，没有输入另一表示，也没有输入或使用额外的 Φ.range 离散性。共同边界、原单位时间和原自由作用的证明始终使用同一个原 ρ.range 在原 compact-open 拓扑下的诱导离散性及原 evaluation 球。

复用已有原单位无穷远自由作用库，同一个应用构造实际水平仿射表示 r，逐点满足 r(γ)(z)=h3InfinityHorizontalMap(Φ(γ),z)，以及原 ℤ² 域中的正规有限指数子群 H，H.index≤2。每个 h∈H 的同一个实际仿射映射为 z↦z+r(h)(0)。同一个应用还构造实际 u≠0，使原水平平移 horizontalTranslation(u) 属于这个同一个内部构造的 Φ.range。没有加可定向前提或排除反射，也没有将“存在正规平移核及非零平移”升级为所有 Φ 元素都是平移、平移核全张成或完整尖点分类。

一个完整成功串行编译、一个临时精确 example、零警告、零新增具名声明或 olean。六项打印的标准三公理闭包属于既有依赖声明，不是六个新定理，也不是匿名 example 的具名公理报告。两个完整 Lean 失败尝试保留排除，分别因新构造的群同态未展开及展开后结构应用未化简；成功 attempt3 用实际 Φ(γ)=g·ρ(γ)·g⁻¹ 的 rfl 等式显式改写后运输原单位时间。成功编译的真实基线为 c77d132ccc1a66d81e1bc6780a3bbdb17b6978f1，分支为 lane/math/mostow-h3-ranktwo-parabolic-20261003，宿主句柄15987。另一个先行一般自由作用准备曾因缓存写入锁 busy 以 exit2 在 Lean 启动和日志创建前退出；该守护拒绝单独保留，不计为此组合应用的 Lean 失败或成功。此前接受的源及编译证据未修改、未重放。唯一跟踪交付仍为研究笔记，Lean 与证据留在忽略目录 .lake，无 canonical Lean、准入、冻结或新颖性声明。

完整外围群的实际原平移/尖点分类及平移核全张成、有限体积中的实际尖点及非平凡稳定子/二秩注入存在性、两侧实际外围群在同一个给定同伦等价 h 诱导的完整甲板同构 d 下的对应、全甲板受控粗稠密映射、原边界交比及完整等距代表存在唯一性仍未完成。完整 Mostow–Prasad 目标继续保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定 h。逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549

## 同一完整群同构、两侧忠实原 H³ 表示及各自原诱导离散像、同一二秩注入下构造共同有限指数平移子群和对应非零平移

给定原群 Γ、Γ′ 及同一个实际完整群同构 d:Γ≃*Γ′，两侧原 H³ 等距群表示 ρ、ρ′ 各自忠实，各自同一个原像按原 compact-open 诱导拓扑离散，以及同一个实际单射群同态 j:Multiplicative(ℤ×ℤ)→*Γ。一个临时精确 example 构造实际限制 σ=ρ∘j、σ′=ρ′∘d∘j，逐侧证明限制像包含于各自同一个原表示像，并从各自原像的诱导离散性推出限制像的诱导离散性。d 和 j 是本应用给定的实际原对象；没有给定另一目标二秩表示或目标外围子群，也没有在本应用中从给定同伦等价 h 构造 d。

对这两个同一个 d、j 关联的实际限制，应用内部逐侧构造实际规范化共同边界 b、b′、全部原边界时间为 1、实际原水平/Weyl 归一化 g、g′，并构造忠实的实际 Φ(δ)=g·ρ(j(δ))·g⁻¹ 和 Φ′(δ)=g′·ρ′(d(j(δ)))·g′⁻¹。原限制的自由作用由各自原离散像与原无挠域推出，再经各自同一个 g、g′ 搬运为 Φ、Φ′ 的自由作用。它们固定原无穷远向量本身，并有实际水平仿射表示 r、r′。没有输入共同边界、单位缩放、归一化、自由作用或共轭像的额外离散性；这里没有把原限制的自由作用升级为完整 Γ、Γ′ 的自由作用。

逐侧构造的原二秩域中正规平移核 H₁、H₂ 各有有限指数至多 2。取同一个原域交子群 H=H₁⊓H₂，证明 H 正规、有限指数且 H.index≤4。对每个 δ∈H，不仅两侧水平仿射映射为平移，还通过同一个原水平与高度桥证明实际 H³ 等距变换 Φ(δ)=horizontalTranslation(r(δ)(0)) 和 Φ′(δ)=horizontalTranslation(r′(δ)(0))。

应用内部选取 0<n≤H.index≤4，使同一个 γ=ofAdd(1,0)ⁿ 属于 H；原第一整数坐标证明 γ≠1，原 j 的单射性和同一个完整 d 证明 j(γ)≠1、d(j(γ))≠1。两侧自由作用推出同一个 γ 的实际偏移 u=r(γ)(0)≠0、u′=r′(γ)(0)≠0。因此 g·ρ(j(γ))·g⁻¹=horizontalTranslation(u)，且 g′·ρ′(d(j(γ)))·g′⁻¹=horizontalTranslation(u′)。这证明的是给定同一个 d、j 下这个共同有限指数子群和这个同一个元素的两侧平移对应，没有证明 g=g′、完整群之间存在环境共轭、两侧平移长度相同或完整外围群对应。

一个完整成功串行编译、一个临时精确 example、零警告、零新增具名声明或 olean。五项打印的标准三公理闭包属于既有依赖声明，不是五个新定理，也不是匿名 example 的具名公理报告。两个整体尝试保留排除：attempt1 宿主50393 exit1，两个钉版 API 用法错误及六处未抑制写法警告；attempt2 宿主19122 exit0，但仍有六处未抑制写法警告，未接纳。成功 attempt3 宿主89339 exit0、零警告，真实基线59006ac3dbf0b3a7f0bc4c76e3225369a437299f，分支lane/math/mostow-h3-full-deck-paired-translations-20261003。修正使用钉版 API 和普通 have，没有关闭警告或改变前提、目标。此前接受的源、收据及编译证据未修改、未重放；本应用内部复用既有匿名单侧应用的证明体。唯一跟踪交付仍为研究笔记，Lean 与证据留在忽略目录 .lake，无 canonical Lean、准入、冻结或新颖性声明。

同一个给定 h 的原生完整甲板同构与本应用的实际 d、j 桥接、实际有限体积尖点及非平凡稳定子/二秩注入存在性、完整原外围群的最大性/平移尖点分类与平移核全张成/格子、全甲板受控粗稠密、原边界交比和完整等距代表存在唯一性仍未完成。本应用没有有限体积或可定向前提，没有排除反射；共同有限指数平移结论没有升级为所有 Φ 或 Φ′ 元素都是平移。完整 Mostow–Prasad 目标继续保留连通、完备、曲率 −1、有限体积、非紧尖点、非可定向情形、两侧原度量和同一个给定 h。逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


## 给定同一完整群同构 d、两侧忠实且原像按原 compact-open 诱导拓扑离散的原 H³ 表示及同一二秩注入 j 时，同一有限指数平移子群的两侧全张成周期基

给定同一个实际抽象完整群同构 d:Γ≃*Γ′、两侧忠实原 H³ 表示 ρ、ρ′ 且各自同一个原像按原 compact-open 诱导拓扑离散，以及同一个实际单射 j:Multiplicative(ℤ×ℤ)→*Γ，在这些相同前提下，临时精确应用保留实际限制 ρ∘j、ρ′∘d∘j 和内部构造的原 g、g′、Φ、Φ′、水平仿射 r、r′。同一个原二秩域交子群 H 正规且有限指数不超过4；每个 δ∈H 的两侧实际原 H³ 等距变换分别是 horizontalTranslation(r(δ)(0))、horizontalTranslation(r′(δ)(0))，同一个非平凡选定幂 γ 保留两侧非零偏移。

在上述同一个 d、忠实且各自原像诱导离散的 ρ、ρ′ 及单射 j 下，对各自实际共轭像构造回到同一个原限制像的连续单射 e↦g⁻¹eg、e′↦g′⁻¹e′g′，内部推出 Φ.range、Φ′.range 的原 compact-open 诱导离散性。对同一个 H，实际偏移加法同态 τ(h)=r(h)(0)、τ′(h)=r′(h)(0) 都是单射；其实际整数线性像 L、L′ 与 Additive H 分别整数线性等价。通过实际水平平移构造 L→Φ.range、L′→Φ′.range 的连续单射，推出两侧偏移子模的离散拓扑，没有输入额外的共轭像或偏移离散性。

仍在上述同一个 d、两侧原表示忠实及原像诱导离散、同一个单射 j 的前提下，两侧原平移核指数各不超过2，故每个原二秩元素 δ 的平方都属于同一个 H。实际倍增映射 ℤ×ℤ→Additive H 再复合到 L、L′，得到两侧实际单射，推出整数秩至少2。对这些同一个实际离散整数子模使用离散实/整数秩比较，结合 ℂ 的实维数为2，内部推出 span ℝ L=⊤、span ℝ L′=⊤；全张成及格子条件没有作为输入。

对上述同一个 d、两侧忠实且各自原像诱导离散的原表示、同一个单射 j 和内部构造的同一个 H，令 e:L≃ₗ[ℤ]L′ 为两侧 Additive H 整数等价的复合。它把每个 δ∈H 的实际偏移 r(δ)(0) 送到 r′(δ)(0)。内部构造两组实基 bp、bp′:Basis(Fin2)ℝℂ，使每个 δ∈H 在两侧使用同一个整数坐标 m:Fin2→ℤ：r(δ)(0)=∑ᵢmᵢbpᵢ、r′(δ)(0)=∑ᵢmᵢbp′ᵢ；每个源基向量 bpᵢ 由一个实际 δ∈H 实现。这是该同一个有限指数 H 的两侧实际格子与匹配周期基，没有证明两组基的长度或夹角相同。

当前成果只涉及给定实际 d、j 的上述条件性应用。d 尚未由同一个给定同伦等价 h 原生构造，j 的有限体积尖点来源尚未证明；同一有限指数 H 的全张成不等于完整外围群最大性或分类，也不说明全部 Φ、Φ′ 元素都是平移。实际有限体积尖点/稳定子/二秩注入存在性、同一个 h 的原生 d/j 桥接、完整外围最大性/分类、全甲板受控粗稠密、原边界交比以及完整等距代表存在唯一性仍未完成。完整目标继续包括非紧尖点、非可定向情形、两侧原度量和同一个给定 h；没有加入有限体积或可定向前提，也没有排除反射。

逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


## 给定同一完整群同构 d、两侧忠实且原像按原 compact-open 诱导拓扑离散的原 H³ 表示及同一二秩注入 j 时，构造对应全部原二秩元素的原距离受控满射

给定同一个实际抽象完整群同构 d:Γ≃*Γ′、两侧忠实原 H³ 表示 ρ、ρ′ 且各自同一个原像按原 compact-open 诱导拓扑离散，以及同一个实际单射 j:Multiplicative(ℤ×ℤ)→*Γ，一个临时精确应用内部构造两侧原共同边界、单位边界时间、原归一化 g、g′ 和实际 Φ(δ)=g·ρ(j(δ))·g⁻¹、Φ′(δ)=g′·ρ′(d(j(δ)))·g′⁻¹。它保留原二秩域 Multiplicative(ℤ×ℤ) 中同一个正规平移交子群 H，在该二秩域中的指数不超过4；两侧实际离散整数偏移子模、实线性全张成及匹配周期基 bp、bp′ 都在内部构造，没有输入额外边界、归一化、自由作用、共轭像离散性、全张成、格子或周期数据。

对上述同一个实际抽象 d、两侧忠实且各自原像诱导离散的原表示 ρ、ρ′ 及单射 j，把同一个原二秩域中的正规有限指数 H 和实际匹配周期基交给既有的原周期数据受控映射结果。内部构造实际 c∈ℂ、C,D∈ℝ，1≤C、1≤D，以及 T=h3PeriodAffineHeightExtension(bp,bp′,c)。T 是满射；它对应全部原二秩元素 δ∈Multiplicative(ℤ×ℤ) 的实际 Φ、Φ′ 作用，不仅是 H 元素。这里的有限指数始终相对于原二秩域，没有升级为 Γ 或 Γ′ 中的有限指数。

仍在上述同一个 d、两侧原表示忠实及原像诱导离散、同一个单射 j 的前提下，用同一个实际原 g、g′ 把 T 搬回原对象，定义 F(p)=g′.symm(T(g(p)))。F:原H³→原H³ 是满射，并且对所有原 H³ 点 p,q，以两侧原 H³ 距离 dist 为准，有

`dist(p,q)−arcosh(D²) ≤ dist(F(p),F(q)) ≤ dist(p,q)+arcosh(C²)`。

对每个原二秩元素 δ∈Multiplicative(ℤ×ℤ) 和每个原 H³ 点 p，同一个实际 F 满足

`F(ρ(j(δ))(p)) = ρ′(d(j(δ)))(F(p))`。

上述实际 F、误差常数、周期基和全张成都由原前提内部构造，没有换用其他度量或另一个目标二秩表示。这一对应覆盖同一个注入 j 的全部二秩域；没有证明它对应全部 Γ 元素，也没有证明 F 等距、与给定流形同伦等价 h 相连，或两侧周期等长等角。

当前成果保留给定实际 d、j 的条件性边界。实际有限体积尖点/稳定子/二秩注入存在性、同一个给定 h 的原生 d/j 桥接、完整原外围最大性/分类、完整甲板群对应的受控映射与粗稠密、原边界交比以及完整等距代表存在唯一性仍未完成。完整目标继续包括非紧尖点、非可定向情形、两侧原度量和同一个给定 h；这批没有加入有限体积或可定向前提，也没有排除反射。

逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


## 给定同一完整群同构 d、两侧忠实且原像按原 compact-open 诱导拓扑离散的原 H³ 表示及同一二秩注入 j 时，全部原二秩元素的两侧实际归一化作用都是水平平移

给定同一个实际抽象完整群同构 d:Γ≃*Γ′、两侧忠实原 H³ 表示 ρ、ρ′ 且各自同一个原像按原 compact-open 诱导拓扑离散，以及同一个实际单射 j:Multiplicative(ℤ×ℤ)→*Γ，一个临时精确应用内部构造原 g、g′、实际 Φ(δ)=g·ρ(j(δ))·g⁻¹、Φ′(δ)=g′·ρ′(d(j(δ)))·g′⁻¹ 和实际水平仿射表示 r、r′。它保留原二秩域 Multiplicative(ℤ×ℤ) 中同一个正规有限指数平移交子群 H（在该二秩域中的指数不超过4）以及内部构造的两侧实际离散整数偏移子模 L、L′、两侧实线性全张成和匹配周期基。

在上述同一个实际抽象 d、两侧忠实且各自原像诱导离散的原表示及同一个单射 j 下，原二秩域的交换性使每个实际 r(δ) 的实线性部分固定所有实际 H 偏移。对每个原二秩 δ，构造实子模 W=ker(r(δ).linear−id)；由实际 L 包含于 W 和内部已推出的 span ℝ L=⊤，得到 W=⊤。因此对每个原二秩 δ 和每个 z∈ℂ，r(δ)(z)=z+r(δ)(0)。对同一个实际目标偏移子模 L′ 和实际 r′ 重复该推导，得到对应的全部目标仿射元素也是平移。这里没有额外输入全张成或纯平移条件，没有把 Γ 本身当作交换群。

仍在上述同一个 d、两侧原表示忠实及原像诱导离散、同一个单射 j 的前提下，用同一个实际原无穷远单位向量固定、实际水平图和原高度保持，把仿射结论提升为每个原二秩元素的实际原 H³ 等距变换等式：

`Φ(δ)=horizontalTranslation(r(δ)(0))`、`Φ′(δ)=horizontalTranslation(r′(δ)(0))`，对所有 `δ∈Multiplicative(ℤ×ℤ)` 成立。

此前同一个实际 F(p)=g′.symm(T(g(p))) 的满射性、两侧原 H³ 距离的统一加性控制，以及 F(ρ(j(δ))(p))=ρ′(d(j(δ)))(F(p)) 的全部原二秩元素对应关系，在同一个完整精确应用中保留。这批没有修改度量或新增具名声明。纯平移结论只涉及同一个注入 j 的整个原二秩域，没有证明全部 Γ 元素或完整外围群都是平移，也没有证明 H=⊤、外围最大性、周期等长等角或 F 等距；完整目标中的非可定向情形及完整群中的反射没有被排除。

完整 Mostow–Prasad 目标仍未完成。实际尖点/稳定子/二秩注入的几何存在性与完整外围分类、同一个给定同伦等价 h 的原生 d/j 桥接、全甲板群对应的受控映射及粗稠密、原边界交比和完整等距代表存在唯一性仍缺失。完整目标包括紧与非紧有限体积情形、带尖点情形、非可定向情形、两侧原度量和同一个给定 h；本批给定 j 的条件性结果没有证明每个紧流形都存在这种二秩注入。

逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


## 给定同一完整群同构 d、两侧忠实且原像按原 compact-open 诱导拓扑离散的原 H³ 表示及同一二秩注入 j 时，构造两侧完整群中的实际单位无穷远稳定子和 horoball 分离阈值

给定同一个实际抽象完整群同构 d:Γ≃*Γ′、两侧忠实原 H³ 表示 ρ、ρ′ 且各自同一个原像按原 compact-open 诱导拓扑离散，以及同一个实际单射 j:Multiplicative(ℤ×ℤ)→*Γ，临时精确应用内部构造原 g、g′ 后，把同一两侧完整表示归一化为 R(η)=g·ρ(η)·g⁻¹、R′(η′)=g′·ρ′(η′)·g′⁻¹。对两侧完整原像分别构造回到同一原 ρ、ρ′ 像的连续单射，推出两侧实际 R、R′ 的完整像各自诱导离散；这里的 R、R′ 定义在整个 Γ、Γ′ 上。

在上述同一个 d、两侧原表示忠实及原像诱导离散、同一个单射 j 的前提下，定义实际 P=h3OriginalUnitInfinitySubgroup(R)、P′=h3OriginalUnitInfinitySubgroup(R′)，即固定同一个原无穷远向量、缩放系数恰为 1 的实际子群。内部证明全部 j(δ)∈P、d(j(δ))∈P′，并把同一个已构造的非平凡二秩元素 γ 所对应的两侧非零水平平移分别放入各自完整原像。原离散非零平移的单位缩放结论给出 η∈P 当且仅当 R(η) 的实际原无穷远有限系数为零；目标侧同样成立。

仍在上述同一个 d、两侧忠实且各自原像诱导离散的原表示及同一个单射 j 下，对两侧完整原像使用原 Shimizu 系数间隔，内部构造实际正阈值 T、T′。对所有原 η∈Γ 和原 H³ 点 p，若 T<height(g(p)) 且 T<height(g(ρ(η)(p)))，则 η∈P；对所有原 η′∈Γ′ 和原点 p，目标侧同样得到 T′ 的分离结论。对 η∈P，height(g(ρ(η)(p)))=height(g(p))；目标侧 P′ 也保持对应的原归一化高度。因而这批分离和高度保持陈述覆盖两侧完整群的全部原元素，而此前实际 F 的对应关系仍只覆盖同一个 j 的二秩域。

本批保留同一二秩域的全部实际水平平移、两侧实际偏移全张成和匹配周期基，以及实际 F 的满射性、两侧原距离加性控制和全部二秩对应关系。没有额外输入尖点、稳定子、非零平移或 horoball 阈值，也没有改变度量或新增具名声明。

这里得到的是给定 j 条件下两侧各自的实际稳定子及 horoball 高度保持/交集排除性质；没有证明 d(P)=P′、完整外围最大性或商空间尖点分类，也没有证明全部外围群或 Γ 元素纯平移。实际有限体积流形中尖点及二秩 j 的几何存在性、同一个给定同伦等价 h 的原生 d/j 桥接、全甲板受控映射及粗稠密、原边界交比和完整等距代表存在唯一性仍未完成。完整 Mostow–Prasad 目标继续保留紧与非紧有限体积情形、非可定向情形、两侧原度量和同一个给定 h；本批没有证明每个紧流形都存在二秩注入。

逃逸审计未完成，登记按 CLAUDE3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549


## 给定同一个抽象完整群同构、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示与同一个单射二秩注入时，其像在各自实际完整单位无穷远稳定子中的有限指数

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ、ρ′`，以及同一个单射二秩同态 `j : Multiplicative (ℤ × ℤ) →* Γ`，新的完整匿名应用在内部构造的 `R η = g * ρ η * g⁻¹`、`R′ η′ = g′ * ρ′ η′ * g′⁻¹` 与实际单位无穷远稳定子 `P、P′` 上，分别推出 `j.range.relIndex P ≠ 0` 和 `(d.toMonoidHom.comp j).range.relIndex P′ ≠ 0`。这两个相对指数非零意味着相应二秩像在各自完整稳定子中的陪集集合有限；两侧指数不要求相等。

推导复用同一个已内部构造的 `H` 所产生的实际整数偏移格子 `L、L′`。各自整数基给出有界基本域，其闭包紧。对完整稳定子中的每个实际元素，使用原 `j` 或 `d ∘ j` 的水平平移在左侧归一化原高度一基点的水平坐标。原坐标距离公式给出统一的原 H³ evaluation 位移界；原紧开等距群中有界 evaluation 集紧，与各自完整诱导离散像相交后有限。原表示的忠实性经原共轭给出 `R、R′` 的单射性，进而得到完整稳定子内有限的归一化代表。这里使用的是高度保持元素的实际点位移，不把正有限系数的边界基本域命题用于系数为零的稳定子。

陪集论证保留左右乘法次序：对陪集代表 `η` 归一化 `η⁻¹`，得到 `ε = j δ * η⁻¹`（目标侧使用 `d (j δ)`）；以 `ε⁻¹` 的左陪集代表原 `η`，因为 `ε * η = j δ`。因此无需假设完整稳定子内二秩像正规。全部既有的同一个 `d/j`、实际格子和匹配周期、每个二秩元素的字面水平平移、原距离受控满射与全部二秩等变性、两侧完整群 horoball 分离与高度保持结论均保留。

这一增量只在上述给定 `d、ρ、ρ′、j` 的条件下证明两个实际相对指数有限。尚未推出 `d(P) = P′`，尚未识别完整稳定子与二秩像的可公度化子，也未从实际有限体积流形构造 `j` 或原生给定同伦等价诱导的 `d`。完整外围群分类、全部甲板群等变受控映射、原边界交比与最终等距存在唯一性仍未完成；紧、非紧尖点和非可定向有限体积范围仍属完整目标。

逃逸审计仍未完成，登记按 CLAUDE §3.9 暂缓：[当前障碍](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定同一个抽象完整群同构、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示与同一个单射二秩注入时，两侧实际稳定子的可公度关系

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ, ρ′`，以及同一个单射 `j : Multiplicative (ℤ × ℤ) →* Γ`，上述完整匿名应用现在同时推出以下结论。这里 `R, R′` 是在各自原表示上实际构造的共轭表示，`P = h3OriginalUnitInfinitySubgroup R`、`P′ = h3OriginalUnitInfinitySubgroup R′`；记 `J = j.range`、`J′ = (d.toMonoidHom.comp j).range`。

- `J` 与 `P` 可公度，`J′` 与 `P′` 可公度。
- `P ≤ Comm(J)`，`P′ ≤ Comm(J′)`，其中 `Comm` 表示可公度化子。
- 同一个原 `d` 下，`P.map d.toMonoidHom` 与 `P′` 可公度，因而它们在原目标群 `Γ′` 中的可公度化子相等。

这些结论在上述同一个给定 `d`、两侧原忠实离散表示与同一个单射 `j` 的条件下，由已有实际有限指数内部推出。`J ≤ P`、`J′ ≤ P′` 使反向相对指数等于一；结合两侧已经推出的有限相对指数，得到可公度性。每个稳定子元素规范化它所属的实际稳定子，可公度子群具有相同的可公度化子，遂得到两侧包含。原 `d` 的单射性运送相对指数，而 `j.range.map d.toMonoidHom = (d.toMonoidHom.comp j).range` 保持同一个二秩像；再用可公度性的对称性与传递性得到目标侧结论。无需假设二秩像在完整稳定子中正规，也没有增加稳定子对应前提。

在上述条件下，该完整应用保留两侧原规范化边界、实际格子与匹配周期、所有原二秩元素的字面水平平移、原距离受控满射及二秩等变性、两侧完整原共轭离散像、实际稳定子、horoball 几何与有限相对指数。新增结论只给出可公度关系及所述可公度化子相等；`d(P) = P′` 和反向几何包含 `Comm(J) ≤ P`、`Comm(J′) ≤ P′` 尚未证明。

完整 Mostow–Prasad 仍未完成：实际有限体积尖点与二秩注入的存在、同一个给定同伦等价 `h` 的原生接入、完整周边分类、完整甲板群等变受控映射与粗稠密性、原边界交比以及完整等距代表存在性与唯一性仍待推进。紧、非紧尖点和非可定向情形继续保留；本段条件性成果不证明每个紧流形存在这样的 `j`。

验证范围为整个新匿名 Lean 应用；未新增具名声明或保留 olean。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定同一个抽象完整群同构、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示与同一个单射二秩注入时，两侧原几何可公度化子及实际稳定子的完整对应

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ, ρ′`，以及同一个单射 `j : Multiplicative (ℤ × ℤ) →* Γ`，完整匿名应用进一步推出 `Comm(j.range) = P`、`Comm((d.toMonoidHom.comp j).range) = P′` 和 `P.map d.toMonoidHom = P′`。这里 `Comm` 是各自原群中的可公度化子，`R, R′` 是在两侧原表示上实际构造的共轭表示，`P = h3OriginalUnitInfinitySubgroup R`、`P′ = h3OriginalUnitInfinitySubgroup R′`；对应使用的就是同一个原 `d`。

在上述给定 `d`、两侧原忠实离散表示与同一个单射二秩 `j` 的条件下，反向包含来自原 H³ 几何。一个可公度化元素 `η` 的共轭二秩像与原二秩像相交为有限指数；因此原生成元有一个正幂属于这个共轭像。原整数第一坐标证明该正幂非平凡，二秩注入与原表示的忠实性将其变为实际非零水平平移。共轭等式说明它固定 `R η` 的原无穷远像。若这个像有有限光锥坐标 `z`，已有原坐标平移公式会把 `z` 移到 `z + w`；固定性将强迫非零偏移 `w` 等于零。因此实际无穷远有限系数为零，再由已有离散非零平移的单位尺度结论得到 `η ∈ P`。目标侧在自身原表示上执行相同推导，得到 `η′ ∈ P′`。

在同样的全部原条件下，结合前批两侧稳定子到可公度化子的包含，得到上述两个子群相等。已证明的同一个 `d(P)` 与 `P′` 可公度，使它们有相同的可公度化子；各自子群的自规范化给出 `d(P) ≤ P′`。用同一个原 `d⁻¹` 运送相对指数，在源群取得对应反向包含，最终得到实际 `P.map d.toMonoidHom = P′`。证明没有预设 `d` 保持稳定子、边界尺度或取向特征。

在上述全部条件下，这一完整应用保留前批两侧规范化边界、实际离散满秩格子及匹配周期、全部原二秩元素的字面水平平移、原距离受控满射及二秩等变性、两侧完整原共轭离散像、实际稳定子、horoball 几何、有限相对指数及可公度关系。当前成果证明的是给定原 `d` 和单射 `j` 时的实际稳定子对应；它不提供有限体积几何中的 `j` 或尖点存在，也未把给定流形同伦等价 `h` 原生接入这些对象。

完整 Mostow–Prasad 仍未完成。完整周边商群与正规平移核分类、受控映射对完整稳定子及完整甲板群的等变性与粗稠密性、原边界交比、完整等距代表存在性与唯一性，以及实际有限体积尖点、二秩注入和原生 `h` 的接入仍待推进。紧、非紧尖点和非可定向情形继续保留，本段不证明每个紧流形存在上述二秩注入。

验证范围为整个新匿名 Lean 应用；未新增具名声明或保留 olean。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定同一个抽象完整群同构、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示与同一个单射二秩注入时，实际完整单位无穷远稳定子的等变受控满射

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ, ρ′`，以及同一个单射 `j : Multiplicative (ℤ × ℤ) →* Γ`，完整匿名应用保留全部前批输出，并进一步构造满射 `fP : H³ → H³`，使每个 `η ∈ P` 和每个原点 `p` 都满足 `fP (ρ η p) = ρ′ (d η) (fP p)`，同时具有双侧原距离加性控制。这里 `R, R′` 仍是前批在两侧原表示上构造的共轭表示，`P = h3OriginalUnitInfinitySubgroup R`、`P′ = h3OriginalUnitInfinitySubgroup R′`，并且使用前批证明的同一个原 `d` 所满足的 `P.map d.toMonoidHom = P′`。

在上述全部原条件下，映射实际为 `fP p = g′.symm (h3PeriodAffineHeightExtension bp bp′ cP (g p))`；它使用原来同一对匹配周期基 `bp, bp′` 和新构造的水平中心 `cP`。前批常数 `C,D` 本身仍可使用：`1 ≤ C`、`1 ≤ D`，并且对每对原点 `p,q` 有 `dist p q - arcosh (D²) ≤ dist (fP p) (fP q) ≤ dist p q + arcosh (C²)`。等变性现在覆盖实际完整 `P` 中的每个元素，而原二秩像上的前批映射和全部几何输出也保留。

在同样全部原条件下，构造先将原单射 `j` 限制到实际 `P`，得到 `jP`，再取 `Q = H.map jP`。前批实际相对指数非零、`jP` 的单射性和原 `H` 的有限指数内部给出 `Q.FiniteIndex`。两侧原表示限制为 `RP = R.comp P.subtype`、`SP = R′.comp (d.toMonoidHom.comp P.subtype)`；实际稳定子对应给出两侧单位无穷远标架固定，从已有原 H³ 结论构造实际仿射表示 `rP,sP`。它们在 `jP` 上的水平坐标就是前批 `r,r′`，所以 `Q` 两侧均为实际平移，偏移由同一个周期线性等价 `AP` 匹配，且原 `bp` 的每个基向量都在实际 `Q` 中实现。这些均为内部推导。

在上述全部原条件下，局部仿射推导使用 `Q` 的有限指数正规核 `K = Q.normalCore`。实现每个原周期的元素有正幂属于 `K`，任意 `P` 元素对它的共轭仍属于 `K ≤ Q`。两侧实际仿射共轭的偏移公式与 `Q` 偏移匹配产生正实标量倍数下的线性兼容性；消去该非零标量，再按原周期基扩展，得到对完整 `P` 的线性兼容性。已有有限仿射轨道平均结论随后构造 `cP` 和完整仿射共轭。原 H³ 水平高度延拓给出等变性与满射性；新延拓等于在前批延拓之后施加实际水平等距平移 `horizontalTranslation (cP - cmap)`，因此直接继承前批双侧原距离估计。

在上述全部原条件下，这一推导未添加完整 `Γ` 的自由作用、稳定子保持、正规性、有限指数、周期匹配或周期实现前提。两侧原群允许处于各自独立的 Lean 宇宙，默认 heartbeat 上限仍为 200000，未提高或重置预算。为降低展开成本，父推导的周期基构造复用已有实际格子等价，原共同边界提取复用同一个实际逃逸轨道的极坐标重构与规范化光锥紧性；父输出的条件和范围保留。

完整 Mostow–Prasad 仍未完成：实际有限体积尖点与二秩注入存在、同一个给定同伦等价 `h` 的原生接入、完整周边商群与正规平移核分类、完整原甲板群 `Γ` 的受控等变性与粗稠密性、原边界交比以及完整等距代表存在性与唯一性仍待推进。紧、非紧尖点、非可定向和两侧原度量范围均保留；当前给定单射二秩 `j` 的结论不证明每个紧流形存在这种注入。

验证范围为整个新匿名 Lean 应用，未新增具名声明或保留 olean。打印的 25 个闭包属于既有依赖，均只使用标准三公理白名单的子集；其中 `LinearMap.ext_on` 使用 `propext, Quot.sound`。这些打印不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定同一个完整群同构、两侧各自忠实且原紧开拓扑诱导离散的 H³ 表示与同一个单射二秩注入时，两侧完整平移核及有限周边商群的对应

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ,ρ′`，以及同一个单射 `j : Multiplicative (ℤ × ℤ) →* Γ`，完整匿名应用保留全部前批对象与输出，并进一步构造两侧实际完整平移核 `K ≤ P`、`K′ ≤ P′`、它们的有限指数及由同一个原 `d` 诱导的有限周边商群同构。这里 `R,R′` 是前批原表示的实际共轭，`P,P′` 是其实际完整单位无穷远稳定子，`eP : P ≃* P′` 是由已证明的 `P.map d.toMonoidHom = P′` 限制得到的同一个原群同构。

在上述全部原条件下，`rP` 是源实际稳定子的原水平仿射表示，`tP` 是目标实际稳定子在原 `R′` 水平坐标中的仿射表示。两个核实际为 `K = (AffineEquiv.linearHom.comp rP).ker`、`K′ = (AffineEquiv.linearHom.comp tP).ker`，并且对每个原稳定子元素都有 `η ∈ K ↔ ∃ z, R η = horizontalTranslation z` 和目标侧的同类等价。因此它们包含各自稳定子中的全部实际水平平移。两个核分别在 `P`、`P′` 内正规；当前结论不声称它们在完整 `Γ`、`Γ′` 内正规。

在同样全部原条件下，完整周边仿射共轭在一个点和零点的等式经加法消去，给出 `AP ((rP η).linear z) = (sP η).linear (AP z)`。同一个原周期线性等价 `AP` 的满射性与单射性使两侧在同一个源 `P` 上的线性核相等；将目标仿射表示沿实际 `eP⁻¹` 写到 `P′`，得到 `K.map eP.toMonoidHom = K′`。运送回两侧完整原群后，仍使用同一个原 `d`：`(K.map P.subtype).map d.toMonoidHom = K′.map P′.subtype`。

在上述全部原条件下，前批实际有限指数周期像 `Q` 的平移公式给出 `Q ≤ K`，因此内部推出 `K.FiniteIndex`。实际核对应和同一个 `eP` 的双射性给出 `K.index = K′.index`，并推出目标核的有限指数。已有 `QuotientGroup.congr` 构造实际 `eQ : P ⧸ K ≃* P′ ⧸ K′`，两个商群均有限，每个商代表满足 `eQ (QuotientGroup.mk η) = QuotientGroup.mk (eP η)`。这不是预设的商群对应；每个代表都沿同一个原 `d` 运送。

在同样全部原条件下，对完整核中的每个元素，其原水平偏移还满足 `AP (rP η 0) = tP (eP η) 0`，使用的就是前批同一对匹配周期基。全部前批规范化边界、二秩实际平移、匹配格子与周期、原距离双侧受控满射及其完整 `P` 等变性、原 horoball 几何、可公度化子等式和实际稳定子对应均保留。未增加完整原群的自由作用、正规性、有限指数或核对应前提；两侧原群保持独立 Lean 宇宙，默认 heartbeat 上限仍为 200000，未提高或重置。

完整 Mostow–Prasad 仍未完成。完整平移核的实际偏移格子、精确 holonomy 阶数以及流形尖点的环面／克莱因瓶分类，实际有限体积尖点与二秩注入存在，同一个给定同伦等价 `h` 的原生接入，完整原甲板群的受控等变性与粗稠密性，原边界交比及完整等距代表存在性与唯一性仍待推进。当前有限商群结论不提供这些分类或几何存在步骤，也不证明每个紧流形存在给定形式的二秩注入；紧、非紧尖点、非可定向和两侧原度量范围继续保留。

验证范围是整个新匿名 Lean 应用，0 错误、0 警告，未新增具名声明或保留 olean。27 个打印闭包属于既有依赖，仅使用标准三公理白名单的子集；`LinearMap.ext_on` 使用 `propext, Quot.sound`，这些打印不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定同一个抽象完整群同构、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示与同一个单射二秩注入时，两侧完整平移核的实际偏移格子与匹配周期

给定同一个抽象完整群同构 `d : Γ ≃* Γ′`、两侧各自忠实且原紧开拓扑诱导离散的实际 H³ 表示 `ρ,ρ′`，以及同一个单射 `j : Multiplicative (ℤ × ℤ) →* Γ`，完整匿名应用保留前批全部对象与输出，并进一步构造两侧完整平移核 `K ≤ P`、`K′ ≤ P′` 的全部实际水平偏移格子。这里 `R,R′` 是两侧原表示的实际共轭，`P,P′` 是其实际完整单位无穷远稳定子；`K,K′` 是已构造的完整平移核，在各自 `P,P′` 内正规且有限指数。同一个 `eP : P ≃* P′` 限制原 `d`，实际 `eK : K ≃* K′` 再限制同一个 `eP`，每个原群元素仍沿同一个 `d` 运送。

在上述全部原条件下，`τ,τ′` 实际为原 `R,R′` 在完整 `K,K′` 上的限制，`uK η = rP η 0`、`uK′ η = tP η 0` 是各自原水平仿射坐标的实际偏移，并且 `τ η = horizontalTranslation (uK η)`、目标侧同类等式对每个完整核元素成立。若这些限制中的某个元素固定实际 H³ 点，已有水平平移固定点判据强制其偏移为零，再由各自原忠实表示推出原核元素为单位。因此内部推出的是两个实际核限制的自由作用，不是完整 `Γ,Γ′` 的自由作用，也未加入这样的前提。

在同样全部原条件下，已有整数偏移对应构造作用于源限制 `τ` 和目标限制沿同一个 `eK` 的复合，两者使用同一个实际源 `K`。它构造 `LK,LK′ : Submodule ℤ ℂ` 和 `eLK : LK ≃ₗ[ℤ] LK′`；两侧集合分别恰为完整 `uK,uK′` 的值域，每个 `η : K` 对应一个实际 `x : LK`，满足 `(x : ℂ) = uK η` 和 `(eLK x : ℂ) = uK′ (eK η)`。目标值域等式使用实际 `eK` 的满射性，没有把两侧原 `Γ,Γ′` 的 Lean 宇宙合并。

在上述全部原条件下，水平平移关于原紧开拓扑的连续性和坐标求值的单射性，将每个完整偏移格子连续且单射地映入各自原 `R.range,R′.range`；各自原像的诱导离散性由此内部给出 `DiscreteTopology LK` 和 `DiscreteTopology LK′`。前批实际周期像 `Q ≤ K` 实现源旧周期基的两个向量，同一个原周期线性等价 `AP` 对全部核偏移的配对实现目标旧周期基，因此两侧完整偏移集合都张成整个实水平平面。实际离散性与完整实张成均为推导结果，没有新增离散、满秩或格子条件。

在同样全部原条件下，每个完整格子元素还满足 `(eLK x : ℂ) = AP (x : ℂ)`，所以完整整数对应在原水平平面中就是同一个已构造 `AP` 的限制。已有匹配格子周期基构造进一步给出完整核的两组新实基 `bk,bk′ : Basis (Fin 2) ℝ ℂ`：对每个 `η : K`，存在同一个整数系数函数 `m : Fin 2 → ℤ`，分别表示 `uK η` 和 `uK′ (eK η)`；源新基的每个向量都由实际完整核元素实现。原完整稳定子的受控满射与全部元素等变性、原 horoball 几何、同一个 `d` 的稳定子与完整核对应、两侧相等有限指数及有限周边商群的逐代表对应全部保留。

完整 Mostow–Prasad 仍未完成。精确 holonomy 阶数与流形尖点的环面／克莱因瓶分类、实际有限体积尖点与二秩注入存在、同一个给定同伦等价 `h` 的原生接入、完整原甲板群的受控等变性与粗稠密性、原边界交比以及完整等距代表的存在性和唯一性仍待推进。当前结论使用给定的同一个单射二秩注入，不证明每个紧流形存在这种注入；紧、非紧尖点、非可定向和两侧原度量范围继续保留。

验证范围是整个新匿名 Lean 应用，0 错误、0 警告，未新增具名声明或保留 olean；默认 heartbeat 上限仍为 200000，未提高或重置。30 个既有依赖的打印闭包仅使用标准三公理白名单的子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定原 H³ 至黎曼流形 M 的实际商覆盖与逐点甲板表示、源与目标原黎曼度量及距离相容性、局部微分同胚与内积相容、原目标有限体积和非平凡实际单位无穷远稳定子时，构造实际二秩注入

给定原 `F : H³ → M` 及其实际完整甲板群的商覆盖、实际 `ρ` 在每个原 H³ 点上与原甲板作用相同、原基点 `p`，源 H³ 与目标 M 的原黎曼度量各自与原空间距离一致，原 `F` 为局部微分同胚并满足逐点原内积相容性，原目标总体积有限，而且实际字面单位无穷远稳定子 `P = h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，新的完整匿名应用内部构造单射 `j : Multiplicative (ℤ × ℤ) →* coveringDeckGroup F`。它保留已有原生构造的 `H ≤ P`、实际偏移 `w` 与整数子模 `L`：`H` 在 `P` 内正规且指数至多 2，经 H 到 P 再到完整原甲板群的字面嵌入给出每个 H 元素的实际水平平移，L 恰为全部 w 值域，原诱导拓扑下 L 离散，原水平商紧且 L 张成整个实水平平面。这里没有给定 j、格子基、偏移逆映射、表示忠实性或离散性、格子或满秩条件。

在上述全部原条件下，原商覆盖的自由甲板作用与实际逐点 `ρ` 求值内部给出完整原 `ρ` 的单射性；已有原甲板像离散构造内部给出其原紧开拓扑诱导像的离散性。实际水平平移相乘的偏移相加，单位偏移为零，由此构造 `W : Additive H →+ L`。若两个 W 值相同，原实际表示把相应商元素送为单位等距映射，再由原覆盖的实际自由作用推出两者相等，所以 W 单射。L 的实际值域等式给出 W 满射，进而内部构造实际 `eW : Additive H ≃+ L`；没有预设逆映射或抽象群交换性。

在同样全部原条件下，已有原 L 离散性与完整实张成内部组成实际整数格子，已有格子有限生成与秩定理及基重编号构造 `bZ : Basis (Fin 2) ℤ L`。两整数坐标先经实际二维线性等价写到 L，再经实际 `eW⁻¹` 回到 H，已有加法／乘法标记等价得到实际 `eJ : Multiplicative (ℤ × ℤ) ≃* H`。原 `j` 是同一个 `eJ` 后接 H 到 P 再到完整原甲板群的字面子群嵌入，不是另选表示或给定注入。

在上述全部原条件下，实际 j 单射，并且 `j.range = H.map P.subtype`、`j.range.subgroupOf P = H`；原像在 P 中的相对指数恰为 H.index，非零且至多 2。这一相对指数不表示 j 在完整原甲板群中有限指数，也不声称 H 在完整原甲板群内正规。每个实际 j 元素在原表示中的作用恰为以实际整数格子基向量为周期的水平平移，偏移由输入的两个整数坐标给出；H 的每个实际元素都由某个 j 元素实现。因此在这些原生几何条件下，单射二秩注入由原有限体积格子内部产生。

完整 Mostow–Prasad 仍未完成。当前原生结论仍假设实际单位无穷远稳定子非平凡，并未证明相关非紧有限体积流形的尖点或非平凡稳定子存在。它没有接入同一个给定同伦等价 h 的完整原甲板群同构，也尚未把新构造 j 接入已合并的两侧完整稳定子、完整平移核及匹配格子构造。完整原甲板群的受控等变性与粗稠密性、原边界交比、流形尖点的环面／克莱因瓶分类及完整等距代表存在性与唯一性仍待推进；紧、非紧尖点、非可定向和两侧原度量范围继续保留，不声称每个紧流形存在这样的二秩注入。已有两侧抽象完整群构造在其历史条件下保留，当前应用使用上述原生覆盖和度量条件，不将它们混为同一条件列表。

验证范围是整个新匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留 olean；默认 heartbeat 上限仍为 200000，未提高或重置。8 个既有依赖的打印闭包仅使用标准三公理白名单的子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致、原 FM 为局部微分同胚并逐点保持原内积、源有限体积及非平凡实际单位无穷远稳定子时，将同一个给定同伦等价接入完整外围群、平移核和匹配格子

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群的商覆盖，原 `ρ`、`ρ'` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p，以及同一个给定同伦等价 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且实际字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，新的完整匿名应用将 h 的实际完整甲板群同构与原生二秩注入接入已有两侧完整稳定子、平移核和匹配格子构造。当前应用不要求另外给定 d、j、表示忠实性或离散性、格子基或偏移逆映射。M 与 N 的原类型宇宙独立；这一条件结论不要求新增 N 的度量或体积假设，完整 Mostow–Prasad 终点仍保留两侧原度量和有限体积范围。

在上述全部原条件下，已有原生同伦提升构造内部选择原目标基点、连续提升 `Lh`、完整原甲板同态 τh 及同构 d。d 的同态恰为同一个 τh，Lh 保持原基点、投影到同一个给定 h，并对每个完整原甲板元素等变；原基本群自然性把同一个 d 与 h 的诱导映射绑定，而且任何满足这份原自然性的完整群同构都等于 d。两侧原实际商覆盖和逐点求值内部给出原表示各自的单射性和原紧开拓扑诱导像的离散性。没有用一个抽象同构替换给定 h 的实际诱导同构。

在同样全部原条件下，原生有限体积构造的所有 H、w、L 输出保持：H 仅在原稳定子内正规，有限指数至多 2；每个原 H 元素实际作用为水平平移，L 恰为全部 w 值域，L 原诱导拓扑下离散、水平商紧且张成整个实水平平面。实际整数基 bZ、实际 `eJ : Multiplicative (ℤ × ℤ) ≃* H` 和完整原甲板群内的单射 j 仍由原格子与偏移逆映射内部构造，保留字面子群嵌入、完整值域、稳定子内相对指数及每个整数坐标的实际平移公式。随后把这同一个 j 和 h 所构造的同一个 d 输入完整两侧构造，消除历史抽象应用中预设 d、j 和忠实／离散表示的前提；非平凡实际稳定子的存在仍为原条件。

在上述全部原条件下，历史两侧构造的全部输出现在落在这两份原实际甲板群及这个同一个 d、j 上：原固定边界射线、单位时间因子、两侧原等距共轭坐标、完整二秩周期及满秩格子、原实际水平平移、满射且有加性距离控制的二秩等变映射、两侧完整字面单位无穷远稳定子 P、P′、原 horoball 分离与高度保持、非零相对指数和完整 commensurator 等式均保持。原完整稳定子满足 `P.map d.toMonoidHom = P′`，内部构造 eP 在每个原 P 元素上的完整原群值恰为 d 的值。另一满射且有加性距离控制的映射 fP 对每个原 P 元素满足同一个 d 的等变关系。

在同样全部原条件下，两侧完整字面线性核 K、K′ 恰由实际水平仿射表示的线性部分定义，每个核元素恰对应原共轭表示中的实际水平平移；它们仅在 P、P′ 内正规、具有相同有限指数，并由同一个 d 精确匹配。实际有限商同构在每个代表元上跟随 eP，实际 eK 在完整原群上的每个值仍跟随同一个 d。两侧全部核偏移格子 LK、LK′ 具有精确值域、原诱导离散性和完整实张成；实际整数线性等价 eLK 在每个完整 LK 元素上等于同一个既有实周期映射，两侧整数周期基、全部匹配整数坐标及源基向量实现均保持。这里没有增加目标固定边界射线、目标满秩、完整稳定子、完整平移核、格子或周期对应的前提。

完整 Mostow–Prasad 仍未完成。原源实际单位无穷远稳定子非平凡仍是假设，相关非紧有限体积尖点或稳定子的实际存在尚未推出。当前连续 Lh 对完整原甲板群等变，但未断言它具有度量控制；当前有度量控制的 fP 只对外围 P 等变，并未断言它投影后同伦于给定 h。完整原甲板群的受控等变映射与粗稠密性、与同一个 h 的受控映射同伦连接、原边界交比、流形尖点的环面／克莱因瓶分类及最终等距代表存在性与唯一性仍待推进；紧、非紧尖点、非可定向及两侧原度量终点继续保留。不声称 K 在完整原群内正规、j 在完整原群内有限指数，或每个紧流形存在这种二秩注入。

验证范围是整个新匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置。既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源原 gH 与 gM 各自的距离一致性、原 FM 的局部微分同胚与逐点原内积相容、源有限体积和非平凡实际单位无穷远稳定子及同一个给定同伦等价时，两侧完整外围线性核的指数均至多 2

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群的商覆盖，原 `ρ`、`ρ'` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p 和同一个给定 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，完整匿名应用保留 h 的实际连续提升、完整原甲板群同构 d、内部构造的原生二秩注入 j，以及全部两侧完整外围群、平移核、受控外围映射和匹配格子输出，并进一步证明同一构造中的完整线性核 `K.index ≤ 2`、`K'.index ≤ 2`。M、N 的原类型宇宙独立；这个条件结论不增加 N 的度量或体积前提，完整刚性终点仍要求两侧原度量及有限体积。

在上述全部原条件下，K、K′ 仍是两侧实际水平仿射表示线性部分的完整字面核，分别是完整外围群 P、P′ 的子群。原实际覆盖导出的完整自由甲板作用经过原等距共轭和 P 的字面嵌入，内部给出实际 `RP` 的自由作用。直接调用既有自由单位无穷远作用定理，构造 `HSharp : Subgroup P`、实际仿射表示及 `HSharp.index ≤ 2`。两份实际水平图表逐点相等，将 HSharp 中的每个水平平移接入同一个 K，得到 `HSharp ≤ K`；随后直接使用钉版 Mathlib 的 `Subgroup.index_antitone` 推出 K 的指数至多 2。已有同一个 h 导出的 eP 在每个原群元素上跟随 d，并精确输送完整核，故已有 `K.index = K'.index` 将同一界传到 K′。没有增加自由作用、指数界、辅助平移子群或核对应的公开前提。

这里的两个指数及核正规性只相对于 P、P′。上述全部原条件下，此前的完整偏移格子、全部整数坐标和同一个实际周期映射对应继续保留；指数至多 2 本身尚不是流形尖点的环面／克莱因瓶分类，也不证明原源非平凡稳定子或非紧有限体积尖点的存在。当前连续提升对完整原甲板群等变但未断言度量控制；有距离控制的外围映射只对 P 等变，未断言它投影后同伦于给定 h。完整原群的受控等变性、粗稠密性、与同一个 h 的同伦连接、边界交比及最终等距代表存在性与唯一性仍未完成，紧、非紧尖点、非可定向和两侧原度量终点范围均保留。

验证范围是整个新的匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置。38 个既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源原 gH 与 gM 各自的距离一致性、原 FM 的局部微分同胚与逐点原内积相容、源有限体积和非平凡实际单位无穷远稳定子及同一个给定同伦等价时，受控外围映射连续且在原 H³ 上与该 h 的提升 P 等变同伦

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群商覆盖，原 `ρ`、`ρ′` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p 和同一个给定 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，完整匿名应用保留 h 的实际连续提升 Lh、完整原甲板群同构 d、内部构造的原生二秩注入 j，以及全部两侧完整外围群、完整线性核指数至多 2、受控外围映射和匹配格子输出，并进一步证明同一实际受控外围映射 fP 连续，且在原 universal H³ 上有连接 fP 与这个同一个原生 Lh 的 P 等变连续同伦。M、N 原类型宇宙独立；这个条件结论不增加 N 的度量或体积前提，完整刚性终点仍要求两侧原度量及有限体积。

在上述全部原条件与同一构造中，fP 的连续性直接来自它的实际原周期仿射高度坐标公式、连续线性映射及原等距坐标。进一步，对每一个连续映射 `LhP : C(H³, H³)`，若它在每个实际 P 元素上跟随同一个 d，则构造从这个 fP 到这个 LhP 的实际 `ContinuousMap.Homotopy`，在每个单位区间参数下对每个原 P 元素等变。原 P 的作用由原 ρ 的单位元和乘法关系内部构造；证明直接复用既有双曲插值同伦及其等变性。这个全称量化是输出，不增加公开的提升、连续性、作用或同伦根前提。同一个给定 h 的原生 Lh 已对完整甲板群等变；原 ρ、ρ′ 的逐点评价与 `d.toMonoidHom = τ` 使它满足此输出中的条件。

上述全部原条件下，这个新增同伦只在原 universal H³ 上对外围群 P 等变。fP 对完整原甲板群 Γ 的等变性、在原 M 上下降得到的全局映射及与给定 h 的全局同伦仍未证明；也未断言 Lh 或插值同伦的度量控制。实际非平凡稳定子／有限体积尖点存在、环面／克莱因瓶流形尖点分类、完整 Γ 的受控等变映射及粗稠密性、原边界交比和最终等距代表存在性与唯一性仍未完成。完整 Mostow–Prasad 终点继续包含紧、非紧尖点、非可定向、两侧原度量及同一个给定 h。

验证范围是整个新的匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留应用 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置，无旧编译重放。40 个既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源原 gH 与 gM 各自的距离一致性、原 FM 的局部微分同胚与逐点原内积相容、源有限体积和非平凡实际单位无穷远稳定子及同一个给定同伦等价时，实际受控外围映射是 H³ 同胚且其逆对完整目标外围群等变

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群商覆盖，原 `ρ`、`ρ′` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p 和同一个给定 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，完整匿名应用保留全部原生提升 Lh、完整甲板群同构 d、内部二秩注入 j、两侧完整外围群、完整核指数至多 2、匹配格子及原 H³ 上的 P 等变同伦输出，并进一步构造实际 `eFP : H³ ≃ₜ H³`，在每个原 H³ 点上满足 `eFP p = fP p`。它的逆在每个原目标外围群 P′ 元素及每个原 H³ 点上跟随同一个 `d.symm`：`eFP.symm (ρ′ η p) = ρ (d.symm η) (eFP.symm p)`。M、N 原类型宇宙独立；这个条件结论不增加 N 的度量或体积前提，完整终点仍要求两侧原度量及有限体积。

在上述全部原条件与同一构造中，直接复用实际周期基给出的连续线性等价 AP、实际水平平移 cP、原高度上的恒等同胚、WithLp 的乘积同胚、正高度子类型限制和原坐标同胚，再与同一原 g、g′ 等距坐标复合，构造 eFP。其前向映射精确等于实际 fP；双侧逆关系及逆连续性来自这些既有同胚构造。已有精确 `P.map d.toMonoidHom = P′` 使每个目标外围元素的 d 逆像属于 P；原前向等变性和 eFP 的实际逆关系随即给出上述逆等变性。没有增加公开同胚、逆映射、逆连续性、单射性或作用前提。此前连接 fP 与同一个给定 h 的原生 Lh 的 universal H³ 上 P 等变同伦仍保留。

上述全部原条件下，这个同胚作用于原 universal H³；尚未构造它在原 M、N 上下降的全局映射或同伦，也未证明 fP 是等距映射、对完整 Γ 等变，或 Lh 具有度量控制。实际非平凡稳定子／有限体积尖点存在、环面／克莱因瓶流形尖点分类、完整 Γ 受控等变映射及粗稠密性、原 M 上与同一个 h 的全局同伦、原边界交比和最终等距代表存在性与唯一性仍未完成。完整 Mostow–Prasad 继续包含紧、非紧尖点、非可定向、两侧原度量及同一个给定 h。

验证范围是整个新的匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留应用 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置，无旧编译重放。40 个既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源原 gH 与 gM 各自的距离一致性、原 FM 的局部微分同胚与逐点原内积相容、源有限体积和非平凡实际单位无穷远稳定子及同一个给定同伦等价时，同一受控外围映射诱导两侧外围轨道商的同胚

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群商覆盖，原 `ρ`、`ρ′` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p 和同一个给定 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，完整匿名应用保留全部原生提升 Lh、完整甲板群同构 d、内部二秩注入 j、两侧完整外围群、完整核指数至多 2、匹配格子、原 H³ 上的 P 等变同伦、实际 eFP 同胚及其逆的 P′ 等变性，并进一步构造实际 `EQ : OrbitQuotient (ρ.comp P.subtype) ≃ₜ OrbitQuotient (ρ′.comp P′.subtype)`。在每个原 H³ 点 p 上，其前向值精确等于同一实际 fP p 的目标轨道投影；其逆在每个原目标代表点 p 上精确等于同一 eFP.symm p 的源轨道投影。M、N 原类型宇宙独立；这个条件结论不增加 N 的度量或体积前提，完整终点仍要求两侧原度量及有限体积。

在上述全部原条件与同一构造中，同一个内部 `eP : P ≃* P′`、eFP 的原前向等变性和实际单射性，给出两侧字面 orbitSetoid 关系的双向等价，随后直接调用钉版 Mathlib 的 `Homeomorph.Quotient.congr`。没有增加商同胚、双射、逆映射、作用或共轭根前提。完整应用直接从已构造的同一 eFP 的连续性和逐点 `eFP p = fP p` 推出原 fP 连续，省去重复坐标连续性推导，保留全部父批结论。

上述全部原条件下，新增同胚作用于外围轨道商 H³/P 与 H³/P′；它们不是原 M、N 的完整 Γ 轨道商。尚未构造原 M、N 上的全局映射或同伦，也未证明 fP 是等距映射、对完整 Γ 等变，或 Lh 具有度量控制。实际非平凡稳定子／有限体积尖点存在、环面／克莱因瓶流形尖点分类、完整 Γ 受控等变映射及粗稠密性、原 M 上与同一个 h 的全局同伦、原边界交比和最终等距代表存在性与唯一性仍未完成。完整 Mostow–Prasad 继续包含紧、非紧尖点、非可定向、两侧原度量及同一个给定 h。

验证范围是整个新的匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留应用 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置，无旧编译重放。41 个既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 给定两侧原 H³ 实际商覆盖及逐点甲板表示、源原 gH 与 gM 各自的距离一致性、原 FM 的局部微分同胚与逐点原内积相容、源有限体积和非平凡实际单位无穷远稳定子及同一个给定同伦等价时，同一外围轨道商同胚同伦于原生提升的外围商映射

给定原 `FM : H³ → M`、原 `FN : H³ → N` 及各自实际完整甲板群商覆盖，原 `ρ`、`ρ′` 在每个原 H³ 点上分别等于各自原甲板作用，原源基点 p 和同一个给定 `h : M ≃ₕ N`；源 H³ 的原 gH 和 M 的原 gM 各自与原距离一致，原 FM 为局部微分同胚并逐点保持原内积，原 gM 总体积有限，而且字面 `h3OriginalUnitInfinitySubgroup ρ` 非平凡，在原流形、可测、Borel、T3 和距离结构下，完整匿名应用保留全部原生 Lh／完整甲板群同构 d／内部二秩 j／两侧完整外围群／完整核指数至多 2／匹配格子／原 H³ 上的 P 等变同伦／同一 fP 的实际同胚 eFP／逆的 P′ 等变性／实际外围轨道商同胚 EQ 和双向投影公式，并进一步给出：每个跟随同一个 d 的连续 P 等变提升 LhP，都有实际连续外围商映射 Λ，满足每个原 H³ 代表点上的 `Λ (π p) = π′ (LhP p)`；同一个 EQ 到这个 Λ 有实际商同伦 HQ，并与实际原 H³ 上的 P 等变同伦 HhP 在每个时间 t、每个原代表点 p 上精确交换：`HQ (t, π p) = π′ (HhP (t, p))`。M、N 原类型宇宙独立；这个条件结论不增加 N 的度量或体积前提，完整终点仍要求两侧原度量及有限体积。

在上述全部原条件和同一构造下，同一个给定 h 的原生 Lh 进一步显式满足全部原甲板元素及原点上的表示等变性 `Lh (ρ a x) = ρ′ (d a) (Lh x)`；它来自原完整甲板等变性、两侧逐点原表示等式和同一个 `d.toMonoidHom = τh`。因此前段的普遍外围商同伦适用于这个同一原生 Lh，商同伦两端仍是同一实际 EQ 与这个原生提升诱导的实际 Λ。

在上述全部原条件与实际对象下，直接复用 Mathlib 的连续常量群作用开放商映射接口，比较字面 orbitSetoid 与群轨道关系；原单位时间区间与这个实际投影的乘积仍是开放商映射。投影后的原 HhP 在实际乘积投影的每个纤维上相同，直接供给既有 `IsQuotientMap.lift`；其 `lift_comp` 给出上述逐时间、逐代表点精确公式。终点限制给出连续 Λ，商归纳给出 HQ 的零端点，另一端点由定义给出。没有增加作用、开放商映射、商覆盖、商同伦、尖点存在或新连续性根前提。

上述全部原条件下，新增 HQ 只作用于外围轨道商 H³/P 与 H³/P′；尚未构造原 M、N 的完整 Γ 商上的全局同伦，也未证明 fP 对完整 Γ 等变、是等距映射，或 Lh／HhP 具有度量控制。实际非平凡稳定子／有限体积尖点存在、环面／克莱因瓶流形尖点分类、完整 Γ 受控等变映射及粗稠密性、原 M 上与同一个 h 的全局同伦、原边界交比和最终等距代表存在性与唯一性仍未完成。完整 Mostow–Prasad 继续包含紧、非紧尖点、非可定向、两侧原度量及同一个给定 h。

验证范围是整个新的匿名 Lean 应用，0 错误、0 警告，未新增显式具名声明或保留应用 olean；默认 heartbeat 上限 200000，递归深度与 heartbeat 均未提高或重置，无旧编译重放。47 个既有依赖的打印闭包只使用标准三公理白名单子集，不构成匿名应用自身的具名闭包报告。逃逸审计仍未完成，登记依 CLAUDE §3.9 暂缓，阻塞见 [issue #11339](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。

### 每元素作用为实际水平平移、整数子模恰等于完整偏移范围时的轨道商乘积坐标

在前批相同条件下——原 FM、FN 是各自完整 deck 群的 H³ 商覆盖，原 ρ、ρ′ 在每点等于原 deck 作用，源原 gH、gM 分别满足原距离恒等式，FM 的局部微分同胚条件与逐点原内积相容各自成立，源原 gM 总体积有限，原单位无穷远稳定子仍假设非平凡，并固定同一个给定同伦等价 h——前批已经成立的全部原生提升、同一个完整 d、内部构造的 j、外围对应、受控 fP、完整平移核与原偏移格子、外围商同胚和同伦输出保持原条件有效；本批证明、输出一个普遍的平移轨道商乘积结果：对每个实际表示 r，若每个群元素作用等于偏移 u 的水平平移，且 L 的底层集合恰等于全部 u 的范围，则存在实际同胚 `H³/r ≃ₜ (ℂ/L) × (0,∞)`，每个代表元 p 的像精确等于水平商类与原正高度。前批保留的两侧完整核 τ、τ′ 已分别给出这两个前提，因而该已证明结果适用于它们：

`H³/τ ≃ₜ (ℂ/LK) × (0,∞)`，`H³/τ′ ≃ₜ (ℂ/LK′) × (0,∞)`。

这里 τ、τ′ 使用前批返回的 R、R′（由同一 g、g′ 共轭原表示所得）及各自完整核；LK、LK′ 分别是前批从各自完整核实际偏移范围构造并沿用的原格子；每个原 H³ 代表元 p 的像精确等于 `(其原水平坐标的格子商类, 其原正高度)`，普遍结果证明了此公式，前批已分别构造两侧所需的实际平移与范围条件；本批的第二个输出在同一匿名应用中将已证明的普遍结果分别应用于两侧表示，返回两个同胚及各自逐代表元公式。新源码不重新证明或直接返回前批的原生几何存在结果，原生条件与全部输出沿用已通过的前批证明；普遍乘积结果是本批证明的输出，不是新假设。先复用原双曲坐标同胚得到实际水平坐标与正高度的乘积，再将原加法格子投影与高度恒等映射组合成开放商。证明其纤维关系恰等于原 τ 的轨道关系后，直接复用商关系同胚与商映射核同胚。没有将半开基本域的集合等价当作同胚，也没有假设商坐标、开放商或同胚存在。

本批普遍构造及两侧实例化的整份匿名 Lean 应用通过串行核验，0 errors、0 warnings，默认 200000 heartbeats 与递归限制不变，无重置、无新显式具名声明、无新 application olean；47 条打印闭包只涉及既有依赖，均落在标准三公理子集内。匿名 example 没有具名闭包报告，旧成功编译未重放。

这批只建立完整平移核轨道商的实际拓扑乘积坐标。完整 Mostow–Prasad 刚性仍 ACTIVE/INCOMPLETE，保持紧／非紧尖点、非可定向、两侧原度量与同一个给定 h 的范围；尖点及非平凡稳定子的存在、环面／克莱因瓶流形尖点分类、full-Γ 受控映射与粗稠密、原 M 上到同一个 h 的全局同伦、原边界交比以及最终唯一等距代表仍未闭合。

逃逸审计未完成；登记依 CLAUDE §3.9 暂缓：[既有阻塞](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。

### 两侧每元素为水平平移、偏移范围完整且匹配整数周期分解与源基向量实现成立时的二维加法环面坐标

在原 FM、FN 是各自完整 deck 群的 H³ 商覆盖、原 ρ、ρ′ 在每点等于原 deck 作用、源原 gH 与 gM 分别满足各自原距离恒等式、FM 为局部微分同胚且逐点保持原内积、源原 gM 总体积有限、原单位无穷远稳定子仍假设非平凡，并固定同一个给定同伦等价 h 的条件下，前批原生提升、同一个完整 d、内部 j、外围对应、受控 fP、两侧完整平移核与各自原偏移格子、外围商同胚及同伦输出保持有效。本批新匿名应用证明整数基格子的水平商同胚于两个单位加法圆；再从前批已返回的两侧核表示 τ、τ′、同一个核群等价 eK、完整偏移范围 LK、LK′、实际匹配整数周期分解及每个源基向量的实际核元素实现，内部推导两侧各自格子恰等于各自原实基 bk、bk′ 的整数张成，构造两个水平商同胚，并与已建立的核商乘积坐标复合：

`ℂ/LK ≃ₜ (ℝ/ℤ) × (ℝ/ℤ)`，`ℂ/LK′ ≃ₜ (ℝ/ℤ) × (ℝ/ℤ)`；`H³/τ ≃ₜ ((ℝ/ℤ) × (ℝ/ℤ)) × (0,∞)`，`H³/τ′ ≃ₜ ((ℝ/ℤ) × (ℝ/ℤ)) × (0,∞)`。

这里每个 `ℝ/ℤ` 是 `UnitAddCircle`，即实数按 1 的全部整数倍取商；两个圆的乘积称二维加法环面。LK、LK′ 分别沿用各自原格子，未断言它们是同一个复数子集；τ、τ′ 使用前批同一 g、g′ 共轭所得的 R、R′，而非直接替换未共轭原表示。对每个水平代表元 z，两个圆的坐标精确为 `(bk.equivFun z 0 mod ℤ, bk.equivFun z 1 mod ℤ)`，目标侧使用各自原 bk′；对每个原 H³ 代表元 p，核商的像精确为这两个原水平基坐标商类及 p 的原正高度。目标侧基向量的核元素实现由同一个 eK、匹配整数周期和原基对应实际推导；格子整数张成等式及同胚均为本批输出，未作为原几何问题的新假设。

证明复用原基的连续线性等价、两坐标同胚、两个加法圆投影的开放商乘积、整数张成当且仅当各基坐标来自整数的既有结果，以及商关系和商映射核的既有同胚。新源码在一份匿名命令内完成普遍水平商构造、两侧整数张成推导、四个同胚及全部逐代表元公式；沿用前批已通过的原生几何条件与输出，不重新编译旧原生成功应用。整版串行 Lean 核验为 0 errors、0 warnings，默认 200000 heartbeats 与递归限制不变、无预算重置，无新显式具名声明或 application olean；47 条打印闭包仅为既有依赖且落在标准三公理子集内，匿名 example 没有具名闭包报告。

本批给出完整平移核轨道商的实际拓扑乘积识别。完整外围群 P 的商、克莱因瓶商、光滑结构及整个尖点的流形分类，尖点与非平凡稳定子的存在，full-Γ 受控映射与粗稠密，原 M 上到同一个 h 的全局同伦，原边界交比及两侧原度量的最终唯一等距代表仍未闭合。完整 Mostow–Prasad 目标保持紧／非紧尖点、非可定向、两侧原度量和同一个给定 h 的原范围，仍 ACTIVE/INCOMPLETE。

逃逸审计未完成；登记依 CLAUDE §3.9 暂缓：[既有阻塞](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。

### 给定等距表示、正规子群及其核轨道商坐标同胚时的剩余商作用与完整轨道商

在原 FM、FN 完整 deck 群商覆盖、原 ρ、ρ′ 逐点等于 deck 作用、源原 gH 与 gM 分别与原距离一致、FM 为局部微分同胚并逐点保持原内积、源原 gM 有限体积、非平凡原单位无穷远稳定子及同一个给定同伦等价 h:M≃ₕN 的前提下，沿用既有原生构造返回的同一 P、P′、正规完整平移核 K、K′、原共轭表示 R、R′ 及前批两侧核商坐标 EH、EH′；本批构造 P/K、P′/K′ 在各自实际核轨道商上的逐元素同胚作用，并分别经 EH、EH′ 运到两个单位加法圆的乘积再乘正高度。当前源码通过逐元素限制公式把原 τ、τ′ 与 R|P 再限制到 K、R′|P′ 再限制到 K′ 精确识别；EH、EH′ 来自已验前批成果，未增加它们存在的新原生前提。

一般机制对任意等距表示 r、正规子群 K 及核轨道商坐标同胚 H 成立：先用正规共轭保持核轨道关系构造群到核商同胚群的同态 D；逐代表元证明 K 在核商上作用平凡，再用 QuotientGroup.lift 得到 A:G/K→Homeomorph(X/K)。运到坐标空间的同态 B 满足 B(c)(H(q))=H(A(c)(q))。剩余轨道关系实际定义为存在 c 使 B(c)y=y′，没有供应新剩余作用或轨道关系假设。两次真实商投影与 H 的复合是商映射，其纤维等价于完整 G 轨道关系；反向由核元素 k 与原代表 g 给出完整群元素 k*g。因此构造完整 G 轨道商到坐标空间剩余轨道商的同胚，每个 x 的像精确为 [H([x]K)]。

在两侧同一原生对象上，完整商分别指 R|P、R′|P′ 的 H³ 轨道商；两侧各自的同胚及代表元公式在同一份匿名命令中应用上述机制。原生父成果已给出 K、K′ 正规、两侧商群有限且指数不超过二；本批的剩余群即这些原商群。两侧格子、基与坐标仍各用原对象，未断言它们相等，也未在本批证明两侧剩余作用在原 eQ 下的共轭或等变关系。旧原生 SAME-h/full-d/native-j、受控 fP 及外围同伦结果保持有效，未重编译旧成功证明。

当前应用零错误、零警告，默认 heartbeats 200000 与递归限制不变，无新显式具名声明、application olean、sorry 或私有公理；打印公理闭包仅为四条既有依赖，均为标准三公理子集，匿名应用没有具名闭包报告。五个先前整版候选全部排除，包括退出码零但仍有两条警告的版本，未部分接受。

这只是原完整周边群的拓扑轨道商识别，尚未证明剩余作用的自由性、克莱因瓶情形、光滑尖点流形分类或实际尖点存在，也不提供 full-Γ 控制与粗稠密、原 M 上到同一个 h 的全局同伦、边界交比或两侧原度量的最终唯一等距代表。完整 Mostow–Prasad 刚性仍 ACTIVE/INCOMPLETE，包含紧与非紧尖点及非可定向范围。逃逸审计未完成，登记依 CLAUDE §3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549。

### 原完整表示自由且沿用既有剩余作用公式时，两侧剩余商作用的自由性

在前批原 FM、FN 完整 deck 群商覆盖、原 ρ、ρ′ 逐点等于 deck 作用、源原 gH 与 gM 分别与原距离一致、FM 为局部微分同胚并逐点保持原内积、源原 gM 有限体积、原单位无穷远稳定子仍假设非平凡、同一个给定同伦等价 h:M≃ₕN 的条件下，沿用已经返回的同一 P、P′、正规完整平移核 K、K′、共轭表示 R、R′、核表示 τ、τ′、核商坐标 EH、EH′ 及上一段实际构造的 A、A′、B、B′；本批证明这四个剩余商作用都是自由的，即任一剩余群元素固定各自核商或坐标空间的任一点，就必须是单位元。两侧原对象与 M、N 的独立类型宇宙保持原样。

一般机制适用于任意自由等距表示 r、正规子群 K、每元素满足 τ(k)=r(k) 的同一核表示、核商同胚 H，以及满足 A([g])([x]K)=[r(g)x]K、B(c)(H(q))=H(A(c)(q)) 的任意同一 A、B。若 c 固定 q，取 q 的原代表 x 和 c 的原群代表 g；核轨道商等式给出实际 k∈K，使 r(k)(r(g)x)=x。完整 r 的自由性推出 k*g=1，再经真实商群同态和 [k]=1 推出 c=1。H 的可逆性把该结论运到同一 B，证明 B(c)y=y 也蕴含 c=1。证明不重建另一组作用或坐标，也不以核表示自由性替代完整表示自由性。

两侧原生应用分别从实际 hQ、hQN 的完整 deck 作用消去律及原每点表示公式推导原 ρ、ρ′ 自由；再用前批已经返回的逐元素共轭等式 R(η)=g*ρ(η)*g⁻¹、R′(η)=g′*ρ′(η)*g′⁻¹ 和同一 g、g′，内部推导完整 R|P、R′|P′ 自由，然后把上述机制应用于同一 τ、τ′、EH、EH′、A、A′、B、B′。这些对象存在及其作用公式沿用已验父成果，未向原生几何问题添加新的自由性、作用或坐标存在假设。旧原生 SAME-h/full-d/native-j、受控 fP、外围商同胚与同伦输出按既有证据保留，不重编译旧成功源码。

本批是一份匿名 Lean 命令，整版串行核验零错误、零警告，默认 heartbeats 200000 和递归限制不变；无新显式具名声明、application olean、sorry 或私有公理。三条打印闭包仅属于既有依赖，均为标准三公理子集；匿名应用没有具名闭包报告。两份早先整版候选均排除，包括零错误但含两条未使用变量警告的版本。本批是既有覆盖消去律和商群组件的精确组合应用，不主张新的经典数学定理或已完成库内具名登记。

自由性只涉及同一原共轭完整周边表示的剩余商作用；两侧剩余作用在原 eQ 下的共轭、有限自由作用的覆盖构造、克莱因瓶与光滑尖点流形分类、实际尖点存在、full-Γ 控制与粗稠密、原 M 上到同一个 h 的全局同伦、边界交比及两侧原度量的最终唯一等距代表仍未闭合。完整 Mostow–Prasad 刚性仍 ACTIVE/INCOMPLETE，保留紧／非紧尖点、非可定向、两侧原度量与同一个给定 h 的范围。逃逸审计未完成，登记依 CLAUDE §3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549。

### 给定两侧等距表示及正规核、核表示逐元素等于各自限制、外围同构与核同构逐元素相容、剩余同构逐代表元相容、外围等变同胚及满足原代表／坐标公式的同一剩余作用和核商坐标同胚时的剩余作用共轭

在前批原 FM、FN 完整 deck 群商覆盖、原 ρ、ρ′ 逐点等于 deck 作用、源原 gH 与 gM 分别与原距离一致、FM 为局部微分同胚并逐点保持原内积、源原 gM 有限体积、原单位无穷远稳定子仍假设非平凡、同一个给定同伦等价 h:M≃ₕN 的条件下，沿用已返回的同一完整 d、外围同构 eP、核同构 eK、剩余同构 eQ、原 g、g′ 共轭表示 R、R′、受控 fP 及其同胚实现 eFP、正规完整平移核 K、K′、核表示 τ、τ′、各自坐标 EH、EH′ 和实际剩余作用 A、A′、B、B′；本批内部构造核轨道商之间的同胚 U 和坐标空间之间的同胚 V，证明它们按同一个原 eQ 传递这些剩余作用。

一般机制以原外围群同构 eP、每元素一致的核对应 eK、τ 与完整表示 r 的限制等式、另一侧对应的限制等式、剩余同构 eQ 的逐代表元公式，以及一个按 eP 等变的同胚 F 为条件。先从这些条件实际证明两侧核轨道关系在 F 下等价，再复用 Homeomorph.Quotient.congr 构造 U，而非供应一个新核商同胚假设。对每个原代表 x 及目标代表 x′，分别证明 U([x]K)=[F(x)]K′ 和 U⁻¹([x′]K′)=[F⁻¹(x′)]K；再从同一 A、A′ 的逐代表元公式及同一 eQ([η])=[eP(η)] 证明 U(A(c)q)=A′(eQ(c))(U(q))。该机制不要求作用传递、群有限或 F 为等距映射。

坐标同胚实际定义为 V=EH′∘U∘EH⁻¹，逐点满足 V(EH(q))=EH′(U(q))，其逆满足 V⁻¹(EH′(q′))=EH(U⁻¹(q′))。由同一 B、B′ 的原 EH/A、EH′/A′ 公式推出 V(B(c)y)=B′(eQ(c))(V(y))。V 在两侧各自“两个单位加法圆的乘积再乘正高度”坐标空间之间作用；这未断言两侧原格子、基或坐标同胚是同一个对象，也未断言 V 或原 fP 已是等距映射。

原生应用在一份匿名命令内由同一原 eFP、g、g′ 内部构造 F(x)=g′(eFP(g⁻¹(x)))。通过原 eFP(x)=fP(x)、原 fP 的逐外围元素等变公式、原 eP 对完整 d 的逐元素实现，以及原 R、R′ 的共轭等式，证明这个同一 F 对完整 R|P、R′|P′ 按原 eP 等变，再将上述机制应用于同一 τ、τ′、eK、eQ、EH、EH′、A、A′、B、B′。原 eFP 和原 fP 等变公式来自已验父成果，并非原几何问题新增的存在或等变前提；原 M、N 的独立类型宇宙和两侧各自对象保持原范围。旧 SAME-h/full-d/native-j、受控 fP、外围商同胚及同伦、核坐标与剩余作用自由性结果沿用历史已验源码，未重编译旧成功证明。

本批整版串行 Lean 核验零错误、零警告，默认 heartbeats 200000 与递归限制不变；无新显式具名声明、application olean、sorry 或私有公理。两条打印闭包仅为既有依赖且属于标准三公理子集，匿名应用没有具名闭包报告。本批是商同胚组件与同一原生对象的精确组合应用，不主张新的经典数学定理、具名库声明或已完成登记。

本批闭合的是已验原生对象之间的剩余作用同胚共轭；有限自由剩余作用的覆盖构造、克莱因瓶与光滑尖点流形分类、实际尖点及非平凡稳定子存在、full-Γ 控制与粗稠密、原 M 上到同一个给定 h 的全局同伦、原边界交比和两侧原度量的最终唯一等距代表仍未闭合。完整 Mostow–Prasad 刚性仍 ACTIVE/INCOMPLETE，保留紧／非紧尖点、非可定向、两侧原度量和同一个给定 h 的原范围。逃逸审计未完成，登记依 CLAUDE §3.9 暂缓：https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549。

### 局部紧 Hausdorff 空间上的有限自由同胚作用及其实际轨道关系已给定时，原商映射的有限覆盖与纤维点数

对有限群 C、局部紧 Hausdorff 空间 Y、同一同胚作用 B 及同一 setoid s，若 B 逐点自由且 s.r(y,y′) 当且仅当存在 c 使 B(c)(y)=y′，本次匿名 Lean 应用内部构造逐点满足 c • y=B(c)(y) 的 MulAction，由 B 的连续性和自由性得到连续及可消去作用；用 s 的对称性证明实际 Quotient.mk s 的纤维正是该作用轨道，直接应用 Mathlib 的有限真不连续作用覆盖接口，返回该实际商映射的 IsQuotientCoveringMap、IsCoveringMap 及每条纤维的点数等于 Nat.card C。纤维点数通过商映射满射取原像，再应用实际 fiberEquivGroup 与 Nat.card_congr 得到。

在既有原 FM/FN 全 deck 商覆盖、ρ/ρ′ 逐点 deck 求值、源原 gH/gM 各自距离恒等式、FM 局部微分同胚与逐点内积相容、源原 gM 有限体积、仍假设的原 unit-infinity 子群非平凡及同一给定同伦等价 h:M≃ₕN 条件下，应用叶使用此前实际返回的两侧正规核 K/K′、Finite(P/K)/Finite(P′/K′)、核指数各至多 2、同一剩余作用 B/B′ 的逐点自由性及实际 s/s′ 的轨道公式；在两侧同一坐标载体 (UnitAddCircle × UnitAddCircle) × 正实高度上，内部从 isOpen_Ioi 得到高度子型局部紧性，返回两侧实际 Quotient.mk s 与 Quotient.mk s′ 的覆盖，以及每条纤维点数分别等于原剩余群基数、等于原核指数，因而各至多 2。自由性使用此前完整原 deck 自由性所得结果，不以仅核自由性代替；这些叶输入是已有输出，不是原几何问题的新存在假设。本次没有换成另一个标准轨道商，也没有重编译原 native 构造；原 M/N 独立宇宙、同一 h 和两侧原度量保留在历史已验构造中。

本批完整成功源码为一份匿名 example，零错误、零警告，默认 200000 heartbeats 及递归限制未改；首版 6 错误、3 未抑制警告的候选整份排除。只打印两条既有依赖的标准三公理子集闭包，匿名应用没有具名闭包报告；零新显式具名声明、零 application olean，不主张新定理准入、新颖性或冻结。复用 Mathlib 的 isQuotientCoveringMap_of_properlyDiscontinuousSMul、Finite.to_properlyDiscontinuousSMul、fiberEquivGroup、Nat.card_congr 和 Subgroup.index_eq_card。此有限剩余覆盖不证明原 M 尖点存在、非平凡稳定子存在、光滑 torus/Klein 尖点分类、full-Γ 控制／粗稠密性、原 M 上同一 h 的全局同伦、边界 crossratio 或最终唯一等距映射；完整紧／非紧尖点／非可定向 Mostow–Prasad 目标仍未完成。

信息逃逸审计未完成；登记按 CLAUDE §3.9 暂缓：[既有案号](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


### 群在拓扑乘积上的同一个同胚表示固定第二坐标、第一坐标不依赖第二坐标且已给截面点时的水平作用构造

给定群 `C`、拓扑空间 `U,V`、截面点 `t₀ : V`，以及保持第二坐标且第一坐标不依赖第二坐标的同一个 `B : C →* Homeomorph (U × V)`，本批匿名 Lean 应用内部构造 `b : C →* Homeomorph U`，满足 `b(c)(u) = (B(c)(u,t₀)).fst` 和每一点的 `B(c)(u,t) = (b(c)(u),t)`。其逆来自原来 `B(c⁻¹)`，连续性及群规律来自原来 `B`；若同一个 `B` 的作用逐点自由，则构造出的 `b` 也逐点自由。这里的坐标不变性是一般乘积引理的条件；下述原生应用内部从原来几何数据导出它们。

### 原来几何条件及同一组叶端恒等式下，两侧残余作用的水平分解

在原来 `FM,FN` 是完整甲板群商覆盖、`ρ,ρ′` 在每一点等于甲板作用、源端原来的 `gH,gM` 距离恒等式分别成立、`FM` 是局部微分同胚且保持每一点原来的内积、源端原来的 `gM` 总体积有限、原来的单位无穷远稳定子非平凡仍为假设、给定同一个 `h : M ≃ₕ N` 且 `M,N` 类型宇宙独立的条件下，沿用已经构造的两侧原生数据，并给定其同一个正规核、基、坐标同胚、代表元作用及交织恒等式和残余作用逐点自由性，本批叶端匿名应用内部构造两侧水平作用 `b,b′`，满足每个高度的 `B(c)(u,t)=(b(c)(u),t)` 与 `B′(c′)(u′,t′)=(b′(c′)(u′),t′)`、两侧原来的仿射代表元公式及两侧逐点自由性。这些叶端恒等式和自由性来自既有原生构造；本批没有重新证明完整的原生几何存在结论。

具体地，原来的 `P = h3OriginalUnitInfinitySubgroup R` 及目标端等式通过子群成员身份给出单位零标架固定。复用原来的实际无穷远稳定子定理，导出水平坐标独立于高度且高度固定。对同一个实际基 `bk`，投影 `π(z)=([bk.equivFun z 0],[bk.equivFun z 1])` 的满射性由两个实数商代表元及 `bk.equivFun.symm` 内部证明；同一个坐标代表元和作用交织恒等式随即给出 `B([η])(π(z),t)=(π(rP(η)(z)),t)`，目标侧使用原来的 `tP`。在上述原生条件及同一组叶端恒等式的作用域内，由满射性和一般乘积分解得到两侧 `b,b′` 及自由性；没有增加原生水平作用或高度不变性的存在假设。有限残余群及原来核指数至多二沿用此前结果，这次构造本身对任意群成立。

本批是一个完整编译通过、零错误零未抑制警告的匿名应用，包含一般乘积分解、归一化双曲空间叶端构造及两侧原生应用；没有新增具名声明或保留应用 olean。三条打印结果只涉及既有依赖声明的公理闭包，不是匿名应用的具名闭包报告。它没有构造残余商与水平商乘积之间的同胚，也没有完成光滑环面／克莱因瓶尖点分类。原流形尖点／非平凡稳定子存在、完整甲板群控制与粗稠密、原流形上同伦于同一个给定 `h`、边界交比及原来两度量之间唯一等距映射仍待证明。连通、完备、曲率 −1、有限体积且包含非紧尖点和不可定向情形的完整 Mostow–Prasad 目标仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。本批不据此宣称规范冻结或登记完成。


### 已给群、拓扑空间、同一水平与乘积同胚表示满足逐点分解，且商关系等于该乘积作用轨道关系时的商乘积同胚

给定群 `C`、拓扑空间 `U,V`、同一个 `b : C →* Homeomorph U` 与 `B : C →* Homeomorph (U × V)`，若每一点满足 `B(c)(u,t)=(b(c)(u),t)`，且同一个 `s : Setoid (U × V)` 满足 `s.r y y′ ↔ ∃ c, B(c)(y)=y′`，匿名 Lean 应用内部构造水平轨道关系 `sU` 和实际同胚 `F : Quotient s ≃ₜ (Quotient sU × V)`，满足 `sU.r u u′ ↔ ∃ c, b(c)(u)=u′` 与每一点的 `F(mk_s(u,t))=(mk_sU(u),t)`。这个构造对任意群和任意拓扑空间成立，不要求有限性、自由性、紧性或非空性。

在同一组条件下，从原来的 `b` 内部实现群作用及逐元素连续性，复用实际轨道商的开放性和开放商映射的乘积定理，得到 `q=(mk_sU,id)` 是开放商映射。原来的 `s` 恰好等于实际 `q` 的核关系；复用相同关系的商同胚与商映射核商同胚，给出上述实际 `F` 及其代表元公式。商乘积拓扑由这些既有定理导出，没有把所需的同胚或拓扑桥接当成新的条件。

### 原 FM、FN 完整甲板群商覆盖与逐点甲板表示、源原 gH/gM 分别的距离恒等式、原 FM 局部微分同胚及逐点内积保持、源原 gM 有限体积、假设原单位无穷远稳定子非平凡、同一 h:M≃ₕN 及独立 M/N 宇宙条件下，沿用两侧原外围限制作用、同一正规核、基、坐标、水平与乘积作用、逐点分解、精确残余轨道关系及原基坐标、正高度和残余商代表元恒等式时的外围商乘积分解

在原来 `FM,FN` 是完整甲板群商覆盖、`ρ,ρ′` 在每一点等于甲板作用、源端原来的 `gH,gM` 距离恒等式分别成立、`FM` 是局部微分同胚且保持每一点原来的内积、源端原来的 `gM` 总体积有限、原来的单位无穷远稳定子非平凡仍为假设、给定同一个 `h : M ≃ₕ N` 且 `M,N` 类型宇宙独立的条件下，沿用已经构造的两侧原生对象，并给定其同一个正规核、基、坐标同胚、水平与乘积作用、实际残余关系及代表元恒等式，叶端匿名应用内部构造两侧 `sU,sU′`、残余商同胚 `F,F′` 及外围轨道商同胚 `Q,Q′`，满足两侧实际水平轨道关系、两侧残余商代表元公式、`Q(q)=F(E(q))` 与 `Q′(q′)=F′(E′(q′))`，以及两侧每个双曲空间点的原来基坐标与原来高度公式。这些叶端对象和恒等式是既有原生构造的精确输出；本应用没有重新证明完整的原生几何存在结论。

具体地，沿用同一个原来外围作用 `r = R.comp P.subtype` 和目标作用，以及同一个原来的 `E,E′`、`H,H′`、基 `bk,bk′` 和上批构造的 `b,b′`。在上述原生条件与同一组叶端公式的作用域内，`Q` 是原来 `E` 与构造出的 `F` 的实际复合，并满足 `Q(orbitQuotientMk r p)=(mk_sU([bk.equivFun z 0],[bk.equivFun z 1]),height(p))`，其中 `z` 是同一个 `p` 的水平坐标，第二坐标带原来的正高度证明；目标侧同理。两侧有限残余群、自由性与原来核指数至多二沿用既有结果；本次商乘积构造不需要把它们作为额外条件。

该匿名应用完整编译通过，零错误、零未抑制警告；三条打印结果涉及既有依赖声明的公理闭包，未提供匿名应用的具名闭包报告。本交付没有新增具名库定理或规范冻结声明。原流形中的尖点区域嵌入、一般尖点／非平凡稳定子存在、光滑环面／克莱因瓶分类、完整甲板群控制与粗稠密、原流形上同伦于同一个给定 `h`、边界交比及原来两度量之间唯一等距映射仍待证明。包含紧与非紧尖点、不可定向情形及两侧原来度量的完整 Mostow–Prasad 目标仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


### 给定原 FM/FN 的完整甲板群商覆盖、逐点甲板表示、同一归一化等距变换的原 R/R′ 共轭公式、同一 P/P′ 与 T/T′ 的原高区域分离，以及同一 bk/bk′、sU/sU′ 和同一 R/R′ 限制于 P/P′ 的实际轨道商乘积同胚 Q/Q′ 的逐点基坐标／正高度公式时，两侧高坐标区域到原 M/N 的开嵌入（M/N 宇宙独立）

给定原来的完整甲板群商覆盖 `FM : H³ → M`、`FN : H³ → N`，在每一点等于甲板作用的 `ρ,ρ′`，同一个归一化等距变换 `g,g′` 及满足原来共轭公式的 `R,R′`，以及同一个外围子群 `P,P′`、阈值 `T,T′`、原来高区域分离关系和上批商乘积同胚 `Q,Q′` 的逐点基坐标／高度公式，两侧匿名 Lean 应用内部构造连续开放的下降映射 `ψ,ψ′`，并构造开嵌入 `Θ : {z : Quotient sU × Ioi 0 // T < z.2} → M` 及目标侧的对应映射。`M,N` 的类型宇宙保持独立。

在这些原来覆盖与同一组叶端条件下，构造满足每一点的 `ψ(qP x)=FM(g.symm x)`、`ψ(qP(g p))=FM p` 和 `Θ(z)=ψ(Q.symm z.val)`。每个满足 `T < height(g p)` 的原来点 `p` 都有坐标 `z`，其底层值恰为 `Q(qP(g p))`，且 `Θ(z)=FM p`；实际像集恰为 `FM '' {p | T < height(g p)}`。目标侧保留原来 `FN,g′,P′,T′,Q′` 的全部对应公式。

在同一组叶端条件下，高度的连续性从原来上半空间坐标同胚导出，因此高区域开放。完整甲板群作用的轨道／覆盖纤维关系从原来商覆盖与逐点甲板作用公式导出；归一化高区域的分离从原来分离关系导出。复用实际连续群作用的开放商映射、商下降连续性、开放映射下降和连续单射开放映射的开嵌入判据，再沿同一个 `Q,Q′` 限制到高坐标区域。构造没有新增一个作为条件的嵌入、开放性、分离结论或尖点存在结论。

这组叶端输入沿用既有原生构造，其原来几何条件仍是两侧完整甲板群商覆盖、逐点甲板作用恒等式、源端分别给出的原来 `gH,gM` 距离恒等式、`FM` 局部微分同胚与逐点原来内积保持、原来 `gM` 有限总体积、仍假设的非平凡单位无穷远稳定子、同一个给定 `h : M ≃ₕ N` 及独立的 `M,N` 类型宇宙。本次源文件验证这些精确叶端输入之下的后果，没有重新证明原来几何存在构造，也没有在当前叶端定理中使用度量或 `h` 来完成全局刚性。

通用的匿名准备应用在任意独立类型宇宙的群 `G`、拓扑空间 `X,M` 上，给定同胚表示、连续开放映射、精确完整轨道／纤维关系、精确子群轨道商关系、开放集及高区域分离时，构造连续开放的商下降映射，并证明它限制在该开放集的商像上是开嵌入。通用准备与两侧原生应用分别完整编译通过，合计两条匿名应用，零错误、零未抑制警告。七条打印结果只涉及既有依赖声明的公理闭包，没有匿名应用的具名闭包报告；本交付没有新增具名库定理或冻结声明。

一般尖点／非平凡稳定子存在、光滑环面／克莱因瓶分类、完整甲板群控制与粗稠密、原流形上同伦于同一个给定 `h`、边界交比以及两侧原来度量之间唯一等距映射仍待证明。包含紧与非紧尖点、不可定向情形及两侧原来度量的完整 Mostow–Prasad 目标仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


给定原来的 `FM : H³ → M`、`FN : H³ → N`、目标端完整甲板群商覆盖及逐点甲板作用恒等式，同一个 `P,P′`，同一个给定同伦等价 `h : M ≃ₕ N` 及连续提升 `Lh` 满足 `FN(Lh p)=h(FM p)`，同一个连续 `fP`、外围商同胚 `EQ` 与连续映射 `Λ` 满足 `EQ(qM p)=qN(fP p)`、`Λ(qM p)=qN(Lh p)`，以及同一个实际同伦 `HhP : fP.Homotopy Lh` 和外围商同伦 `HQ` 满足每个时间和点的 `HQ(t,qM p)=qN(HhP(t,p))`，再给定同一个归一化等距变换 `g` 与共轭表示 `R`、阈值 `T`、基 `bk`、水平商 `sU`、商乘积同胚 `Q` 的逐点基圆坐标／高度公式，及上批连续映射 `ψM,Θ` 的精确公式 `ψM(qR x)=FM(g.symm x)`、`Θ z=ψM(Q.symm z.val)`，匿名 Lean 应用构造从同一高坐标域到原来 `N` 的连续映射 `F`，并构造实际同伦 `F.Homotopy (h.toFun.comp Θ)`。`M,N` 的类型宇宙独立；`qM,qN,qR` 分别是同一组原来表示及子群的轨道商映射。

在上述完整叶端条件下，内部由原来 `FN` 的商覆盖及逐点甲板作用构造连续下降 `Ψ`，满足 `Ψ(qN p)=FN p`；由同一个共轭公式构造归一化商同胚 `D`，满足 `D(qR x)=qM(g.symm x)`。构造的 `F z=Ψ(EQ(D(Q.symm z.val)))`，实际同伦 `H` 在每个时间 `t`、原来点 `p` 与满足 `z.val=Q(qR(g p))` 的高坐标 `z` 上满足 `H(t,z)=FN(HhP(t,p))`。每个满足 `T<height(g p)` 的原来点 `p` 都有这一精确坐标 `z`，且 `Θ z=FM p`、`F z=FN(fP p)`、`H(1,z)=h(FM p)`。

本次复合直接使用既有的商同胚、商下降连续性与同伦复合／前复合／端点改写 API；给定的外围同伦及代表公式沿用之前的原生构造，没有把本次所需的原来 `N` 中同伦作为新条件。当前叶端没有重建原来几何存在；源端覆盖／逐点作用及源端原来度量、有限体积、仍假设的非平凡无穷远稳定子保留在既有构造的条件中，没有在本次叶端作为显式参数使用或被本次证明消去。

这一条匿名条件应用完整编译通过，零错误、零未抑制警告。四条打印结果只报告既有依赖声明的公理闭包，没有匿名应用的具名闭包报告。本批交付研究说明，新增具名库定理与冻结声明均为零。上述条件应用没有证明目标高区域包含关系或整个原来 `M` 上同伦于给定 `h`；一般尖点／非平凡稳定子存在、光滑环面／克莱因瓶分类、完整甲板群控制与粗稠密、边界交比、两侧原来度量之间唯一等距映射仍待证明。包含紧与非紧尖点、不可定向情形的完整 Mostow–Prasad 刚性目标仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


沿用原来独立类型宇宙的 `M,N`、覆盖映射 `FM,FN`、等距表示及同一外围子群，给定同一个归一化 `g,g′` 与目标共轭表示 `R′`、原来匹配周期基 `bp,bp′` 和中心 `cP`，同一个连续外围映射的精确公式 `fP p=g′.symm(h3PeriodAffineHeightExtension bp bp′ cP (g p))`，同一个外围商同胚 `EQ(qM p)=qN(fP p)`，上批同一源归一化商同胚 `D(qR x)=qM(g.symm x)` 与目标下降 `Ψ(qN p)=FN p`，两侧原来阈值 `T,T′`、基 `bk,bk′`、水平商 `sU,sU′`、商乘积同胚 `Q,Q′` 的逐点基圆坐标／高度公式，及同一连续 `ψM,ψN,Θ,Θ′` 的原来代表公式和商坐标复合公式、既有的目标 `Θ′` 开嵌入，再给定同一个指定 `h : M ≃ₕ N`、上批 `F z=Ψ(EQ(D(Q.symm z.val)))` 与实际同伦 `H : F.Homotopy(h.toFun.comp Θ)`、同一个 `HhP : fP.Homotopy Lh` 及上批逐时间／原点同伦代表公式，匿名条件应用内部构造两侧更深坐标域之间的同胚和原来 `N` 中的映射／同伦。匹配周期基 `bp,bp′` 与商坐标基 `bk,bk′` 保持为原来的分别给定对象，没有新增两组基相等的条件。

在上述完整叶端条件下，实际外围公式直接给出每个原点的 `height(g′(fP p))=height(g p)`。目标归一化轨道关系由原来共轭公式导出，再复用商同胚构造 `D′(qR′ x)=qN(g′.symm x)`。同一个坐标同胚 `E=Q′ ∘ D′.symm ∘ EQ ∘ D ∘ Q.symm` 在每一点保持高度，并满足原点代表公式 `E(Q(qR(g p)))=Q′(qR′(g′(fP p)))`。

在上述同一组条件下，取实际共同深度 `S=max T T′`，用既有子类型同胚限制得到两侧同一水平商乘积的深区域同胚 `Edeep`，并构造实际包含映射 `iM,iN`。定义原来 `N` 中的 `Fdeep=F.comp iM`；逐点证明 `Fdeep z=Θ′(iN(Edeep z))`，由既有目标嵌入、深区域开放包含及同胚复合得到 `IsOpenEmbedding Fdeep`。实际像集恰为 `FN '' {p : H³ | S<height(g′ p)}`。这个目标包含和像集等式是当前叶端推导的结论，没有作为新条件输入。

在上述同一组条件下，上批同伦经实际源包含前复合成为 `Hdeep : Fdeep.Homotopy(h.toFun.comp(Θ.comp iM))`。对每个时间和原点，只要深坐标 `z.val=Q(qR(g p))`，就有 `Hdeep(t,z)=FN(HhP(t,p))`。每个满足 `S<height(g p)` 的原来点 `p` 都有这一精确坐标，满足 `Θ(iM z)=FM p`、`Fdeep z=FN(fP p)`、`(Edeep z).val=Q′(qR′(g′(fP p)))` 和 `Hdeep(1,z)=h(FM p)`。同伦的目标空间是整个原来 `N`，没有证明它的全过程停留在目标深尖点中。

当前叶端的源 `D,Ψ,F,H`、目标下降 `ψN`、目标坐标映射 `Θ′` 及其开嵌入结论均沿用已核验的原生输出；当前只构造新的目标归一化、深区域对应、目标像集和受限同伦。原来覆盖／甲板作用恒等式、源端分别给出的原来度量距离关系、局部微分同胚与逐点原来内积保持、有限总体积及仍假设的非平凡单位无穷远稳定子保留在既有构造的条件中，没有被当前叶端消去或重新证明存在。

这一条匿名条件应用完整编译通过，零错误、零未抑制警告；两次完整失败尝试全部排除。四条打印结果只涉及既有依赖声明的公理闭包，没有匿名应用的具名闭包报告。本批交付研究说明，新增具名库定理与冻结声明均为零。上述有条件深区域对应不证明一般尖点／非平凡稳定子存在、光滑环面／克莱因瓶分类、完整甲板群控制与粗稠密、整个原来 `M` 上同伦于指定 `h`、边界交比或两侧原来度量之间唯一等距映射。包含非紧尖点和不可定向情形的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


在原来 `M` 的拓扑、原来覆盖 `FM : H³ → M` 与实际 `IsQuotientCoveringMap FM (coveringDeckGroup FM)`、逐点等距表示 `ρ η x=η • x`、同一归一化 `g` 和完整甲板表示 `R η=g*ρ η*g⁻¹`、同一外围子群 `P` 与正阈值 `T`、每个 `η∈P` 保持 `height(g(ρ η p))=height(g p)`，及原来的完整甲板群高区域分离结论（两个原点 `p,ρ η p` 经 `g` 后高度均大于 `T` 则 `η∈P`）下，匿名条件应用证明：对每个实数 `a>T`，原来流形中的深闭截断像集 `FM '' {p : H³ | a≤height(g p)}` 是闭集。这里没有把所求闭性、局部有限性、截断函数或紧核心作为前提。

在上述同一组条件下，既有双曲距离控制对数高度之差，给出正间隔 `log a-log T`。完整甲板群深区域饱和的每个闭包点都落在某个平移后的 `T` 高区域中；在这个开放邻域内，原来高区域分离与外围高度保持使饱和集落在同一个平移后的闭 `a` 水平集内，故其闭包点仍在饱和集中。实际原来覆盖的纤维关系将这一饱和集识别为 `FM ∘ g.symm` 下的原来深截断像集逆像，再直接复用商拓扑的闭集判据把闭性下降到原来 `M`。证明无需另设陪集族局部有限的条件。

本叶端沿用此前原生构造给出的高度保持及高区域分离输出；原来度量、局部微分同胚、有限体积和非平凡无穷远稳定子等几何根条件仍在此前构造中，当前没有重建或消去这些条件。完整匿名应用编译零错误、零未抑制警告；首轮整体失败因强制类型转换、命名空间和集合成员语法错误被全部排除，修复保持同一数学陈述与预算。三条打印结果只涉及既有依赖声明的公理闭包，没有匿名应用的具名闭包报告。本批同步研究说明，新增具名库定理与冻结声明均为零。

在上述同一组条件下，对每个 `a>T`，原来深闭截断像集 `FM '' {p : H³ | a≤height(g p)}` 是闭集；截断函数及全局同伦尚未构造。一般尖点存在、有限尖点分解、紧核心、完整甲板群粗控制、边界交比，以及包含非紧尖点与不可定向情形、保持两侧原来度量和同一个指定 `h` 的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


在原来独立类型宇宙的 `M,N` 及各自拓扑、原来 `FM,FN,fP`、实际源商覆盖 `IsQuotientCoveringMap FM (coveringDeckGroup FM)`、逐点原甲板等距作用 `ρ η x=η • x`、同一源归一化 `g,R,P` 与共轭公式 `R η=g*ρ η*g⁻¹`、正阈值 `T` 下的外围高度保持及完整甲板群高区域分离、同一原来商坐标 `bk,sU,Q` 的逐点基圆／高度公式、同一 `ψM,Θ` 的代表公式和既有源 `Θ` 开嵌入、同一 `T′` 与原来深包含 `iM` 的逐点值恒等式、同一个指定 `h : M ≃ₕ N`、原来 `Fdeep,Hdeep : Fdeep.Homotopy(h.toFun.comp(Θ.comp iM))`，以及上批每个原来深点的精确坐标／`Θ(iM z)=FM p`／`Fdeep z=FN(fP p)` 输出下，匿名条件应用构造了整个原来 `M` 上的实际映射 `G : C(M,N)` 和同伦 `J : h.toFun.Homotopy G`。这一构造只修改一处给定原生尖点；没有把所求闭性、截止函数、重叠一致性或全局同伦作为前提。

在上述同一组条件下，取实际 `S=max T T′`、`a=S+1`、`b=S+2`、`A=FM '' {p : H³ | a≤height(g p)}` 和 `U=range(Θ.comp iM)`。前批已核验的闭性证明体以原样局部证明项接入当前同一个匿名消费者，从实际原来覆盖、甲板作用、归一化和高区域分离内部推出 `IsClosed A`。原点坐标公式与源嵌入给出 `A⊆U`，以及每个源深坐标 `z` 的 `Θ(iM z)∈A ↔ a≤height(z)`。构造的连续截止函数为 `β(z)=projIcc 0 1 (height(z)-a)`；高度不超过 `a` 时为 `0`，高度至少 `b` 时为 `1`。这里 `b-a=1`，没有额外的间隔假设。

在上述同一组条件下，原来源嵌入到其像 `U` 的同胚给出实际逆坐标。源尖点内的映射取原来 `Hdeep.symm` 在 `t*β` 时的值，另一块区域取同一个原指定 `h`；实际邻域覆盖为两个开放集合 `I×U` 和 `I×(M\A)`。在重叠区域，已证明的坐标成员关系推出 `β=0`，两块映射因此逐点相等。直接复用 Mathlib 的邻域覆盖拼接接口 `ContinuousMap.liftCover` 得到连续 `J`，并核验其零端为同一个 `h`、一端为实际 `G`。没有把该接口解释成闭覆盖拼接，也没有增加局部紧性或正规空间条件。

在上述同一组条件下，每个时间及每个原来 `m∉A` 都满足 `J(t,m)=h m`。对每个高度 `height(g p)≥b` 的原来点 `p`，原来精确源坐标 `z.val=Q(qR(g p))` 满足每个时间的 `J(t,FM p)=Hdeep.symm(t,z)`，终点为 `G(FM p)=FN(fP p)`。同伦的目标仍是整个原来 `N`，没有证明全过程留在目标尖点中，也没有断言 `G` 在整个流形上是等距映射或满足完整甲板群粗控制。

本叶端沿用原来 `ψM,Θ,iM,Fdeep,Hdeep` 和原点输出；此前原来度量、有限体积及非平凡无穷远稳定子等几何根条件保留在此前构造的上下文中，当前没有重建或消去这些条件。当前同一个匿名消费者接入已有闭性证明，没有新增具名闭性包装或重放旧编译。完整应用编译零错误、零未抑制警告。四条打印结果只涉及既有依赖声明的公理闭包，没有匿名应用的具名闭包报告。本批同步研究说明，新增具名库定理与冻结声明均为零。

一处给定原生尖点的局部同伦现已在上述完整条件下延伸为原来 `M` 上的实际全局同伦。一般尖点／非平凡稳定子存在、有限尖点分解与紧核心、同时处理全部尖点并具有完整甲板群粗控制的全局映射、边界交比及保持两侧原来度量的唯一等距映射仍未证明。包含非紧尖点与不可定向情形、同一个指定 `h` 和独立 `M,N` 类型宇宙的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


在原来独立类型宇宙的 `M,N` 及各自拓扑、原来 `FM,FN` 与完整甲板群的实际两侧商覆盖 `hQM,hQN`、逐点 `ρ η p=η • p` 和 `ρ′ η p=η • p`、同一个指定 `h : M ≃ₕ N`、原来连续 `fP,Lh`、同一个完整甲板群同构 `d`、原来逐点投影 `FN(Lh p)=h(FM p)` 和完整群等变公式 `Lh(ρ η p)=ρ′(d η)(Lh p)`、同一个 `HhP : fP.Homotopy Lh`、同一原生尖点 `g,R,P,T,T′,sU,Q` 的原来深坐标与 `Θdeep=Θ.comp iM,Fdeep,Hdeep`、每个时间和每个原点坐标代表的 `Hdeep(t,z)=FN(HhP(t,p))`，以及前批实际全局 `G,J : h.toFun.Homotopy G` 的原来逐点输出下，匿名条件应用构造了原来整个 `H³` 上的连续 `Lg` 和实际 `K : Lh.Homotopy Lg`。这里每个原点代表仍满足 `z.val=Q(qR(g p))`；前批全局同伦是已有输入，所求覆盖提升、完整群逐时等变和深点上的楼上相等式没有作为前提。

在上述同一组条件下，取原来 `S=max T T′`、`a=S+1`、`b=S+2` 和 `A=FM '' {p : H³ | a≤height(g p)}`；前批输出是每个时间与每个 `m∉A` 的 `J(t,m)=h m`，以及每个原来 `b` 深点的同一精确坐标 `z` 和逐时 `J(t,FM p)=Hdeep.symm(t,z)`。将同一个 `J` 沿原来 `FM` 预合成，再以同一个原来 `Lh` 作为零端提升，直接调用 Mathlib 的 `IsCoveringMap.liftHomotopy`。实际 `K` 对每个时间和每个原点满足 `FN(K(t,p))=J(t,FM p)`，零端仍为 `Lh`，终点 `Lg` 覆盖原来 `G`。

在上述同一组条件下，对完整原甲板群的每个 `η`、每个时间和每个原点，比较 `K(t,ρ η p)` 与 `ρ′(d η)(K(t,p))`。两条连续路径在原来 `FN` 下的投影相等，零端由原来 `Lh` 的同一 `d` 等变性相等；覆盖路径提升的唯一性直接给出逐时相等。因此终点 `Lg` 也保持同一个完整群同构 `d`，没有重新选择群同构或改变指定基点，也没有假定原来同伦固定基点。量词覆盖完整甲板群，包括反定向元素，不要求只取外围子群或定向保持元素。

在上述同一组条件下，对每个原来 `FM p∉A` 的点，实际投影同伦恒等于 `h(FM p)`；提升路径唯一性推出每个时间的 `K(t,p)=Lh p` 和终点 `Lg p=Lh p`。对每个 `height(g p)≥b` 的原来深点，前批同一坐标 `z.val=Q(qR(g p))` 与原来逐时 `Hdeep` 代表公式表明 `K(t,p)` 和 `HhP.symm(t,p)` 的投影相等，零端都为原来 `Lh p`，同一唯一性推出每个时间的楼上相等式 `K(t,p)=HhP.symm(t,p)`。因此终点在楼上直接满足 `Lg p=fP p`。

当前完整匿名应用编译零错误、零未抑制警告；三条打印结果只涉及既有依赖声明的公理闭包，没有匿名应用的具名闭包报告。本批同步研究说明，新增具名库定理和冻结声明均为零。当前覆盖消费者继承此前原生几何、两侧原来度量、有限体积及尖点稳定子等条件，没有重建或消去这些根条件。一处给定原生尖点的实际全局提升及同一个完整群同构的逐时等变已在上述条件下证明；一般尖点存在、有限尖点分解与紧核心、全部尖点同时控制、完整甲板群粗控制与粗稠密、边界交比和两侧原来度量间的唯一等距映射仍未证明。包含非紧尖点与不可定向情形、同一个指定 `h` 及独立 `M,N` 类型宇宙的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


在原来任意类型宇宙的流形 `M` 及其拓扑、T3、可测与 Borel 结构、原来 `H³` 流形结构、原来黎曼度量 `gH,gM` 与 `gH.edist=H³.edist`、原来覆盖 `F:H³→M` 和完整甲板群的实际商覆盖、原来局部微分同胚与每点切向内积拉回、同一 `ρ` 和每个完整甲板元素在每个原点的评价 `ρ η p=η • p` 下，匿名应用构造了任意正半径双曲球的统一正且有限原体积，并给出了厚点处明确半径的原度量及原体积保持。这里 `δ>0`，厚点条件是每个非单位的完整原甲板元素都满足 `δ≤dist p (ρ η p)`；量词包含反定向元素，没有限制为外围子群。覆盖及度量根条件继承既有原流形构造，所求统一半径和球体积下界没有作为前提。

在上述原来条件下，任取参考点 `p₀:H³`，令 `c(r)` 为原来内蕴三维 Hausdorff 测度的 `ball p₀ r` 体积。既有原生测度非零性给出支撑点，支撑定义保证该点每个正半径球体积为正；原生等距变换的传递性和 Hausdorff 测度保持把此正性及体积等式传到每个中心。原生适当度量空间中的紧闭球及既有紧集有限测度性给出 `c(r)<∞`。因此每个 `r>0`、每个原点 `p` 都有 `gH.volumeMeasure(ball p r)=c(r)` 和 `0<c(r)<∞`，不需要另行假设开集正测度实例或球体积的显式积分公式。

在上述原来条件下，对每个 `δ` 厚点 `p`，完整群位移下界与三角不等式给出 `δ/4` 球内任意 `x,y` 的轨道最小距离等于原来 `dist x y`。原来覆盖纤维距离公式于是给出 `gM.edist(F x)(F y)=edist x y`。既有等距片 Hausdorff 体积公式与原来两侧黎曼体积绑定进一步给出该球内每个子集 `A` 的 `gM.volumeMeasure(F '' A)=gH.volumeMeasure A`；此子集结论不另要求可测性。

在上述原来条件下，对每个 `δ` 厚点 `p` 和每个 `0<r≤δ/4`，覆盖满射与同一纤维距离公式还给出整个原来内蕴目标球的精确像：`F '' ball p r={m | gM.edist(F p)m<ENNReal.ofReal r}`。纤维距离的严格上界直接选出同一纤维的甲板代表；此代表落在原来半径 `r` 的球内。因此该目标球在同一 `gM.volumeMeasure` 下的体积精确为 `c(r)`，与中心无关，正且有限。

当前完整匿名应用编译零错误、零未抑制警告；四条打印结果仅为既有依赖声明的标准公理闭包，没有匿名应用的具名闭包报告。本批同步研究说明，新增具名库定理及冻结声明均为零。这一球体积前提尚未使用原来目标总有限体积；有限体积球堆积、厚部全有界及闭性到紧致性的推导仍未完成。一般尖点存在、有限尖点分解与紧核心、全部尖点同时控制、完整甲板群粗控制、边界交比及最终唯一等距映射也仍未证明。包含非紧尖点与不可定向情形、两侧原来度量、同一个指定 `h` 及独立 `M,N` 类型宇宙的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


在原来任意类型宇宙的流形 `M` 及其原拓扑、T3、可测与 Borel 结构、原来黎曼度量 `gM`、原来覆盖 `F:H³→M` 与完整甲板群的实际商覆盖、同一 `ρ` 的每元素每点评价、实际原来甲板作用的适当不连续性、原来轨道同胚 `j` 及其已导出的原内蕴度量等距绑定、原来总有限体积，以及前批已证明的厚点球体积输出下，匿名条件应用证明了原流形的 `δ` 厚部紧致。这里 `δ>0`，原来楼上厚部 `D` 定义为每个非单位完整甲板元素都满足 `δ≤dist p (ρ η p)` 的原点集合，原来楼下厚部是 `K=F '' D`。前批球体积输出是同一函数 `c(r)` 对每个 `r>0` 为正，且每个原来厚点与每个 `0<r≤δ/4` 的整个原内蕴目标球在同一 `gM.volumeMeasure` 下精确具有体积 `c(r)`；其原来 `gH` 度量与体积条件仍由前批构造继承。所求紧致性、有限网和闭性没有作为前提。

在上述原来条件下，每个完整甲板元素的位移函数连续，故全部闭位移不等式的交 `D` 为闭集。对任意完整群元素 `b`，以 `b⁻¹ηb` 改写位移并用原来 `ρ b` 的等距性，推出 `D` 在整个原来甲板作用下不变。原来覆盖纤维的轨道关系于是给出 `F ⁻¹' K=D`；商覆盖的闭集判据推出原拓扑中的 `K` 闭。完整群量词包含反定向元素，没有只取外围子群或定向保持子群。

在上述原来条件下，原来轨道等距绑定内部给出所有原内蕴扩展距离有限，并把原来轨道商的完备性传递到同一 `gM` 的内蕴度量；此度量由原来扩展距离取得，没有另选目标度量。对任意 `ε>0`，取 `r=min(δ/4,ε/3)`，则 `r>0` 且 `2r≤ε`。在 `K` 中取极大 `ε` 分离子集，其原来半径 `r` 的球两两不交，并由前批实际球体积等式全部具有同一个正体积 `c(r)`。这些球的体积求和不超过同一原来总有限体积。有限非负扩展实数和中，达到一个固定正阈值的项只能有限多个，故此分离子集有限；极大性给出覆盖整个 `K` 的有限 `ε` 球网。每个正尺度均有此有限网，所以 `K` 全有界，结合原来完备度量中的闭性，得到原拓扑中的紧致性。

当前完整匿名应用编译零错误、零未抑制警告；五条打印结果仅涉及既有依赖声明的标准公理闭包，没有匿名应用的具名闭包报告。本批同步研究说明，新增具名库定理及冻结声明均为零。原厚部紧致性已在上述实际覆盖、原度量、原总有限体积及已证明球体积条件下推出；Margulis 薄部分类、一般尖点存在与有限尖点分解、紧核心、全部尖点同时控制、完整群粗控制、边界交比及最终唯一等距映射仍未证明。包含非紧尖点与不可定向情形、两侧原来度量、同一个指定 `h` 及独立 `M,N` 类型宇宙的完整 Mostow–Prasad 刚性仍未完成。

逃逸审计尚未完成；登记依 CLAUDE §3.9 暂停：[未决记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 原始覆盖下近单位元交换子的统一消失

固定原始覆盖映射 `F : H³ → M`、完整甲板群 `coveringDeckGroup F`、其商覆盖性质，以及同一等距表示 `ρ`，要求对每个甲板变换和每个点都有 `ρ(g)(p)=g·p`。这里包含反向等距变换，不限制为定向或外围子群。对原始等距变换对应的实际 `4×4` Lorentz 矩阵使用辅助行和算子范数；该范数只服务于估计，不改变任何流形的原始度量。

在这些条件下，存在一个只依赖原始覆盖与作用的自然数 `N`：对每个序列 `a : ℕ → coveringDeckGroup F` 和每个根元素 `b`，若所有 `a(n)` 与 `b` 的实际矩阵距单位矩阵都不超过 `1/16`，令 `z₀=b`、`zₙ₊₁=a(n)zₙa(n)⁻¹zₙ⁻¹`，则每个 `n≥N` 都有 `zₙ=1`。这个 `N` 同时适用于所有上述序列和根元素。

单位元孤立性从原始商覆盖导出：在参考点 `(0,1)`，覆盖的局部不相交性提供邻域和半径 `r>0`；Lorentz 核与距离的关系给出 `cosh(dist(p,ρ(g)p))=L(ρ(g))₀₀`。矩阵元素由辅助范数控制，所以偏差小于 `cosh(r)-1` 时，位移小于 `r`，邻域及其平移相交，原始甲板变换只能为单位元。随后，近单位元矩阵的逆范数不超过 `2`，已有单位群交换子估计给出每次至多 `1/2` 的收缩。因此 `‖L(ρ(zₙ))-I‖≤(1/2)ⁿ/16`，几何收敛与上述孤立性给出统一深度。

这是覆盖层面的前置结果；它不使用有限体积、`gM` 或给定同伦等价 `h`，也不选择或改变它们。由近单位元元素生成的子群是否幂零、从原始点的小位移到 Margulis 结论的桥、有限尖点分解和紧核心仍未证明。完整 Mostow–Prasad 仍未完成，终点保留两边原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立类型宇宙、非紧尖点与非可定向情形。

逃逸审计未完成，登记按 CLAUDE §3.9 暂停；相关障碍见 [原有问题记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 原始甲板群的近单位元生成子群幂零性

固定原始 `F : H³ → M`、完整甲板群、商覆盖性质和同一表示 `ρ`，要求每个元素、每个点都有 `ρ(g)(p)=g·p`。对实际 Lorentz 矩阵使用辅助行和算子范数，令 `S={g | ‖L(ρ(g))-I‖≤1/16}`、`H=Subgroup.closure S`。在这些条件下，`H` 是幂零群。集合与生成运算均在原始完整甲板群内，包含反向等距变换的原始作用域；辅助矩阵范数不替换流形度量。

证明内部使用前一步的统一交换子深度，再对任意根元素按消失深度归纳其上中心列成员关系。零深度迫使根为单位元；后继步把一个生成元前插到任意序列中，使该生成元与根的交换子进入上一层上中心列。取该正规子群的商群，根像的中心化子拉回为子群；它包含所有生成元，因而包含其整个闭包，将交换关系推广到每个群元素，得到根进入下一层上中心列。

在实际 `H` 中，生成集合取原始 `S` 在子群强制转换下的原像；实际矩阵单位元关系给出单位元属于该集合，其闭包为整个 `H`。子群中的递归交换子强制转换后逐层等于同一原始甲板群中的递归交换子，所以同一个统一深度适用。全部生成元均进入同一有限层上中心列，闭包使该层等于整个 `H`，给出幂零性。所求的幂零性、上中心列成员关系与闭包上的交换关系都没有作为前提。

这仍是矩阵近单位元条件下的覆盖层前置结果，不使用有限体积、`gM` 或给定 `h`，也不选择或改变它们。原始点的小位移到几何 Margulis 结论的桥、薄部与有限尖点分类、紧核心、边界交比和最终唯一等距代表仍未完成。完整 Mostow–Prasad 终点保留两边原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立类型宇宙、非紧尖点和非可定向情形。

逃逸审计未完成，登记按 CLAUDE §3.9 暂停；相关障碍见 [原有问题记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 原始有界位移给出实际 Lorentz 矩阵与逆的统一界

在原始双曲三维空间度量中固定 `p₀=h3CoordinatePoint 0 1`。对每个 `R≥0`，存在只依赖 `R` 和固定参考标架的 `C>0`，使每个满足 `dist(p₀,e(p₀))≤R` 的原始等距变换 `e`，其实际 Lorentz 矩阵及 `e⁻¹` 的实际 Lorentz 矩阵在辅助行和算子范数下都不超过 `C`。量词涵盖所有等距变换，包括反向变换；矩阵范数仅用于估计，不替换原始双曲度量。所求矩阵界或紧性没有作为前提。

构造取四个原始参考点到 `p₀` 的距离之和 `D`、固定标架展开系数的非负范数总和加一 `K`，以及 `B=cosh(R+D)`，得到 `C=4KB`。原始 cosh 距离核识别第零 Lorentz 坐标；自核等式控制每个空间坐标。等距性与三角不等式将四个标架点的像限制在距离 `R+D` 内，固定线性展开把坐标界转成每个矩阵项的界，再用行和范数得到统一矩阵界。逆变换在 `p₀` 的位移等于正向位移，故同一 `C` 同时控制逆矩阵。

本步是几何 Margulis 路线所需的有界性前置结果。匿名精确检查通过，未新增具名或冻结声明，也不声明新的可复用库准入。有限矩阵覆盖到原始短词陪集的有限指数桥、点的小位移 Margulis 结论、薄部与有限尖点分类、紧核心、边界交比和最终唯一等距代表仍未完成。完整 Mostow–Prasad 终点保留两边原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立类型宇宙、非紧尖点和非可定向情形。

逃逸审计未完成，登记按 CLAUDE §3.9 暂停；相关障碍见 [原有问题记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 原始有界位移元素的有限分片与近单位元差

固定原始任意类型宇宙中的 `M`、映射 `F : H³ → M`、完整甲板群和同一表示 `ρ`，要求每个元素、每个点都有 `ρ(g)(p)=g·p`。在原始双曲度量中取 `p₀=h3CoordinatePoint 0 1`。对每个 `R≥0`，存在有限片数 `m` 和映射到 `Fin m` 的分片标记，定义在所有满足 `dist(p₀,g·p₀)≤R` 的原始甲板群元素上。若 `v,w` 标记相同，则实际 `ρ(v⁻¹w)` 的 Lorentz 矩阵在辅助行和算子范数下满足 `‖L(ρ(v⁻¹w))-I‖≤1/16`。范围包括反向等距变换；原始元素、作用和乘逆运算均保留，矩阵范数不替换双曲度量。

证明内部先由原始标架和 cosh 距离核构造同一正数 `C`，同时控制满足位移界的实际矩阵及其逆。对该辅助范数，实际四阶实矩阵空间有限维，半径 `C` 的闭球紧，因此可用有限个半径 `δ=1/(32C)` 的开球覆盖。为每个原始元素选择覆盖中心，并把中心编号到有限类型。标记相同使两矩阵距离小于 `2δ`；原始矩阵乘法与逆的等式给出 `L(ρ(v⁻¹w))-I=L(ρ(v)⁻¹)(L(ρ(w))-L(ρ(v)))`，由同一逆矩阵界和乘法范数估计得到 `1/16` 的界。所求矩阵界、有限覆盖、片数和标记都没有作为前提。

本步只建立有限分片及片内原始差的近单位元条件；这一前置结果本身不需要商覆盖性质。将它与原始商覆盖下已得到的矩阵近单位元生成子群幂零性组合，还需要原始短词与陪集增长的有限指数桥，不能据此提前声称小位移群已虚幂零。点的小位移 Margulis、任意原始点的传输、薄部与有限尖点分类、紧核心、边界交比和最终唯一等距代表仍未完成。完整 Mostow–Prasad 终点保留两边原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立类型宇宙、非紧尖点和非可定向情形。匿名精确检查未新增具名或冻结库声明，也不声明新的可复用库准入。

逃逸审计未完成，登记按 CLAUDE §3.9 暂停；相关障碍见 [原有问题记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 有限位移颜色到虚幂零性的一般群作用引理

对任意独立类型宇宙中的群 `G` 与伪度量空间 `X`，固定同一个逐元素等距的群作用、原点 `p:X`、幂零子群 `H≤G` 及自然数 `m`。若给**全部**满足原距离 `dist(p,g•p)≤1` 的原群元素赋色到 `Fin m`，且每对同色原元素 `v,w` 都满足 `v⁻¹w∈H`，则由全部满足 `dist(p,g•p)<1/((m:ℝ)+1)` 的原元素生成的子群 `Γ` 是虚幂零群：存在幂零且有限指数的 `K≤Γ`。`H` 和 `K` 无须正规，生成集合无须有限；有限指数及虚幂零性没有作为前提。

证明在原作用下建立乘积位移的次可加性及逆位移相等，故长度至多 `m` 的小位移生成词都落入同一个单位位移域。一般短词增长论证表明：无限传递作用中，每个含基点的有限集合都有某个对称生成元将一个点送出集合；否则闭包归纳和传递性会使该有限集合包含全部点。归纳因此给出任意 `n` 下由长度至多 `n` 的词到达的 `n+1` 个不同点。对 `Γ/K` 的实际左陪集作用取 `K=H.subgroupOf Γ`，有限颜色的鸽巢原理给出每组 `m+1` 个短词中的同陪集碰撞，与无限作用的增长矛盾，得到实际有限陪集及有限指数。交换嵌套子型的两项成员证明，构造 `K` 到 `Γ.subgroupOf H` 的乘法等价，由幂零群的子群仍幂零传回 `K`。

实质证明保留为 `D5/S3/Combinatorics/GroupActions/FiniteColorVirtualNilpotence.lean` 的一个公开 `result`，所有短词构造都在其活证明路径内；没有另加 bind-only 伴随声明或原生几何包装。它是对无界任意群和作用的普遍证明，不是有限枚举或数值实例；不声明文献新颖性。具名 Lean 编译已通过，实际结论的公理闭包仅含标准三公理。对应 Scribe 源、标准生成的 Blueprint 文档镜像和首次冻结工件均已提供。

本结论仍以实际有限颜色及实际幂零子群为条件。原始 H³ 表示与前两批颜色、幂零性成果到本引理的精确连接，以及原始几何源恢复，仍未完成；不能据这个一般条件结论声称原始甲板小位移群已虚幂零。任意原始点传输、几何 Margulis、薄部与有限尖点分类、紧核心、边界交比及完整 Mostow–Prasad 仍未完成；终点保持两边原始度量、同一给定 `h` 和完整诱导 `d`、独立宇宙、非紧尖点及非可定向情形。

本公开引理的逃逸审计未完成：有限六码模板不能忠实携带原来的任意群／作用／伪度量／实数／无界词望远镜；依赖族接口下仍缺完整源码重构与发生绑定、精确 realization bridge、全族 variation、逐角色 sensitivity、实际 observational dependence 及当前绑定证据。登记按 CLAUDE §3.9 暂停，见 [本引理的具体障碍记录](https://github.com/the-omega-institute/trureturing/issues/13225)。未声明 `declared_validated`；此前几何审计的独立历史仍见 [原记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549)。


## 统一生成词交换子深度到实际生成子群幂零性

对任意类型宇宙中的群 `G`、任意子集 `S` 和自然数 `N`，若对每个长度恰为 `N`、所有字母均属于同一个 `S` 的列表，以及每个原始根元素 `b∈S`，从 `z=b` 开始按列表从左到右反复作 `z↦a*z*a⁻¹*z⁻¹`，最终都得到单位元，则实际生成子群 `Subgroup.closure S` 幂零。同一个 `N` 必须同时适用于所有上述词和根；不要求 `S` 有限、对称、正规或包含单位元，空集与 `N=0` 也在范围内。这里没有假设所求的幂零性、有限指数或上中心列终止。

证明在实际生成子群 `H` 内取原始 `S` 经包含映射的原像 `T`，其闭包为整个 `H`。对深度 `n` 归纳：凡被全部长度 `n` 的 `T` 词消去的根，都属于第 `n` 层上中心列。零深度由空词直接迫使根为单位元。后继步把任意生成元 `a` 前插到原词，归纳得到 `a` 与根的交换子属于前一层。在该正规上中心子群的商群中，原始生成元的像因此与根像交换。根像的中心化子拉回是包含全部 `T` 的子群，故包含整个 `H`；交换关系遂推广到所有原始 `H` 元素，将根送入下一层。这个推广没有把生成集假设成对交换子封闭。

包含映射逐层保持交换子以及完整列表 fold，因此原始 `G` 中的统一消失条件传到同一个 `H`。所有原始 `T` 元素都进入第 `N` 层，该层作为子群包含它们的整个闭包，所以等于 `H`。实质证明保留为 `D5/S3/Combinatorics/GroupWords/UniformCommutatorNilpotence.lean` 的一个公开结论；这是无界任意群、任意生成集合和任意深度的普遍证明，列表不是有界枚举的认证输入。它提取此前原生近单位元生成子群论证中的一般代数步骤，不声明文献新颖性。

这个一般结论仍以实际统一交换子消失为前提。前批原始 H³ 几何源与部分原始输入在本地丢失，当前新增证明是重新构造的一般群论引理，不是原始几何源的逐字恢复，也不重新认证丢失的历史输入。原始覆盖、完整甲板群、同一 `ρ` 及每元素每点评价、实际 Lorentz 矩阵近单位元集合与本引理之间的精确连接仍未完成；有限颜色引理到原始小位移群的连接也仍未完成。不能据此声称原始小位移群已虚幂零。

当前具名模块定向编译已通过，零错误、零未抑制警告。完整 Mostow–Prasad 仍未完成，终点保留两边原始度量、同一个给定 `h` 和完整诱导 `d`、独立类型宇宙、非紧有限体积尖点及非可定向情形；任意原始点传输、几何 Margulis、薄部与有限尖点分类、紧核心及边界交比仍未闭合。信息逃逸登记按当前 CLAUDE §3.9 暂缓，本新引理没有完成登记，也未声明 `declared_validated`；此前几何审计历史及有限颜色引理的具体障碍分别保留在 [原记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549) 和 [有限颜色引理记录](https://github.com/the-omega-institute/trureturing/issues/13225)。


## 赋范环表示的单位元隔离间隙到近单位元生成子群幂零性

对任意独立类型宇宙中的群 `G` 与赋范环 `R`，要求环范数次可乘且 `‖1‖=1`，固定同一个群同态 `f:G→Rˣ`。若存在实际正实数 `ε`，使每个原群元素 `g` 都满足 `‖(f g:R)-1‖<ε → g=1`，则集合 `S={g | ‖(f g:R)-1‖≤1/16}` 在原群内生成的实际子群 `Subgroup.closure S` 幂零。这个隔离条件必须另行证明；仅有连续表示或给群选择离散拓扑不够。无需群有限生成、集合正规或环完备，也不假设所求幂零性或统一交换子深度。

证明先把近单位元单位 `u` 的逆写成 `1-(u-1)u⁻¹`，由三角不等式与次可乘性推出其逆范数不超过 `2`。直接复用钉版 Mathlib 的单位群交换子估计，两端均在 `1/16` 范围内时，每次与生成元取交换子使根的偏差范数至多减半；新根仍在同一范围内。对任意字母列表归纳得到完整嵌套交换子的范数界 `(1/2)^length * ‖f(b)-1‖`，字母从左到右处理。几何收敛选出同一个自然数 `N`，满足 `(1/2)^N/16<ε`，实际隔离条件于是使所有长度 `N` 的原始生成词同时消去所有原始生成根。此前统一生成词幂零判据把这个已导出的深度条件推广到整个实际生成子群。

实质证明保留为 `D5/S3/Combinatorics/GroupWords/NearIdentityNilpotence.lean` 的一个公开结论。它是任意群、任意赋范环与无界任意生成词的通用收缩论证，不是有限枚举或数值认证实例，不声明文献新颖性。定向 Lean 编译与精确应用检查通过，零错误、零未抑制警告；独立群／环宇宙、带实际正隔离间隙的整数单位群及有理数赋范域特例均已检查。具名结论的公理闭包仅含标准三公理；对应 Scribe 文档源、标准生成的 Blueprint 镜像与首次冻结工件已经提供。

本结论尚未构造原始 H³ 覆盖、完整甲板群的实际 Lorentz 单位群表示或其实际正隔离间隙，也没有恢复此前丢失的原生几何源或重新认证原始输入。实际 Lorentz 近单位元集合、有限颜色和原始小位移群到这两个一般判据的连接仍未完成，不能据此声称原始小位移群已虚幂零。任意原始点的几何 Margulis、薄部与有限尖点分类、紧核心、边界交比及完整 Mostow–Prasad 仍未完成；终点保留两边原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立流形宇宙、非紧有限体积尖点与非可定向情形。

信息逃逸登记依当前 CLAUDE §3.9 暂缓，本批未完成登记，未声明 `declared_validated`；原有几何审计历史及有限颜色引理具体障碍保留在 [原记录](https://github.com/the-omega-institute/trureturing/issues/11339#issuecomment-5904703549) 和 [有限颜色引理记录](https://github.com/the-omega-institute/trureturing/issues/13225)。


## 完整甲板作用与逐点 Lorentz 表示下的实际单位元隔离

固定原始双曲三维上半空间的距离及参考点 `p₀=(0,1)`。对任意独立类型宇宙中的拓扑空间 `M` 和映射 `F:H³→M`，取保持 `F` 的全部自同胚组成的完整甲板群 `D={e:H³≃ₜH³ | ∀p,F(e(p))=F(p)}`，作用为原自同胚的逐点评价。假设同一个 `F` 是这个完整作用的商覆盖。再固定一个群同态 `f:D→(Matrix (Fin 4) (Fin 4) ℝ)ˣ`，要求每个原元素和每个原点都满足 `f(g)·v(p)=v(g·p)`，其中

`v(z,t)=((‖z‖²+t²+1)/(2t), Re(z)/t, Im(z)/t, (‖z‖²+t²−1)/(2t))`。

在这些条件下，原完整群中存在实际正数 `ε`，满足 `‖f(g)−I‖<ε → g=1`；因此同一个集合 `{g:D | ‖f(g)−I‖≤1/16}` 生成的子群幂零。矩阵使用行和算子范数，原始双曲距离保持原样；没有有限生成、定向保持或紧致性要求，也没有假设所求隔离间隙或幂零性。

实际间隙来自原覆盖：参考点有一个邻域 `U`，非单位甲板元素的平移与 `U` 不相交。取原距离下包含于 `U` 的正半径球 `B(p₀,r)`，令 `ε=cosh(r)−1>0`。原距离公式推出 `cosh(dist(p₀,p))=v(p)₀`；`v(p₀)=(1,0,0,0)` 与同一个逐点矩阵公式于是给出 `cosh(dist(p₀,g·p₀))=f(g)₀₀`。该矩阵项的偏差由行和算子范数控制，范数小于 `ε` 就使原位移小于 `r`。这让 `g·p₀` 同时属于 `g·U` 和 `U`，覆盖局部不相交性迫使 `g=1`。直接应用已冻结的 `NearIdentityNilpotence.result` 得到上述实际生成子群幂零性。

这里的矩阵单位群同态及其每元素每点公式仍是显式条件。从同一个原等距表示 `ρ` 构造该同态并证明完整逐点公式、接入实际有限位移颜色、证明原小位移群虚幂零，仍需完成。完整 Mostow–Prasad 刚性仍未完成，保留两侧原始度量、同一个给定同伦等价 `h` 及其完整诱导同构 `d`、独立流形宇宙、非紧有限体积尖点和非可定向情形。


## 从原始 H³ 等距群构造完整 Lorentz 矩阵表示

固定原始上半空间的双曲距离与上一节的坐标 `v(z,t)`。对全部原始等距变换 `e:H³≃ᵢH³`，包括反向变换，构造群同态 `L:(H³≃ᵢH³)→(Matrix (Fin 4) (Fin 4) ℝ)ˣ`，使每个原始点都满足 `L(e)·v(p)=v(e(p))`。本构造不输入矩阵表示、逐点矩阵公式、定向保持条件或更换后的度量。

首先由原始 arsinh 距离公式推出完整两点恒等式 `cosh(dist(p,q))=v(p)₀v(q)₀−v(p)₁v(q)₁−v(p)₂v(q)₂−v(p)₃v(q)₃`。取四个原始点 `(0,1),(1,1),(i,1),(0,2)`。令 `Bₑ` 的列为这四点在 `e` 下的 Lorentz 坐标，`Kₑ` 的行为同一坐标的 Lorentz 双线性读出。原等距性给出 `KₑBₑ=K₁B₁`；两个原始参考矩阵的逆由有理系数直接验证，所以每个 `Kₑ` 可逆。定义 `Aₑ=Kₑ⁻¹K₁`，两点距离核使 `Kₑv(e(p))=K₁v(p)`，从而得到每点公式。原四点坐标张成全部四维空间，因此该公式唯一确定矩阵；依此证明 `A_(e*f)=AₑA_f`、`A₁=I` 和逆元公式，并构造上述矩阵单位群同态。

对任意原始拓扑空间 `M`、同一个映射 `F:H³→M` 和完整甲板群 `D`，若原始评价作用满足商覆盖性质，且同一个群同态 `ρ:D→(H³≃ᵢH³)` 对每个元素及每个点满足 `ρ(g)(p)=g·p`，则复合 `f=L∘ρ` 自动满足上一节的完整逐点公式。在这些条件下，原距离的覆盖邻域推出 `ε=cosh(r)−1>0` 的实际矩阵行和算子范数隔离间隙，直接调用已有近单位元幂零定理，得到同一个 `{g:D | ‖f(g)−I‖≤1/16}` 生成的子群幂零。这里已经消去上一节中另行输入 `f` 及其逐点公式的条件；商覆盖与同一 `ρ` 的原始评价桥仍是条件。

本批是以当前原始 H³ 源及钉版上游矩阵接口重新构建的证明，不是丢失历史几何源的逐字恢复或原输入重新认证。现有结果的绑定应用仅作为临时精确编译证据，不新增绑定库定理或首次冻结。实际有限位移颜色与原小位移群虚幂零性的连接、任意点 Margulis、薄部和有限尖点分类、紧核心及全局边界控制仍未完成。完整 Mostow–Prasad 目标仍保留两侧原始度量、同一个给定 `h` 及其完整诱导同构 `d`、独立流形宇宙、非紧有限体积尖点与非可定向情形。


## 原参考点处统一小位移生成子群的虚幂零性

固定同一个原始双曲三维上半空间、双曲距离和参考点 `p₀=(0,1)`。存在仅由这个原模型选定的正数 `ε`：对任意独立类型宇宙中的拓扑空间 `M`、映射 `F:H³→M` 及其完整甲板群 `D`，若同一个 `F` 是完整原始评价作用的商覆盖，且同一个群同态 `ρ:D→(H³≃ᵢH³)` 对每个元素和每个原点满足 `ρ(g)(p)=g·p`，则原群中由全部 `{g:D | dist(p₀,g·p₀)<ε}` 生成的子群虚幂零。`ε` 在引入 `M,F,ρ` 之前选定；不输入矩阵界、颜色或虚幂零性，也不要求有限生成、定向保持或紧致性。

令上一节构造的矩阵为 `Aₑ`，四点列矩阵为 `Bₑ`。由逐点公式得 `Aₑ=BₑB₁⁻¹`。对任意 `R≥0`，令 `D₀` 为四点到 `p₀` 的距离之和，`B=cosh(R+D₀)`，`C=4B‖B₁⁻¹‖+1>0`。Lorentz 自配对为一给出每个坐标的绝对值不超过第零坐标，原始距离核给出第零坐标为 `cosh(dist(p₀,p))`；因此原位移不超过 `R` 时 `‖Aₑ‖≤C`。逆元的原位移相等，故同一个 `C` 也界住 `‖A_(e⁻¹)‖`。范数仍为矩阵行和算子范数。

有限维矩阵闭球紧致。取 `δ=1/(64C)` 的有限球覆盖，对位移不超过 `R` 的全部原始等距变换选择覆盖中心作为有限颜色。同色的 `a,b` 满足 `‖A_b−A_a‖<2δ`，由 `A_(a⁻¹b)−I=A_(a⁻¹)(A_b−A_a)` 得 `‖A_(a⁻¹b)−I‖≤1/16`。对 `R=1` 固定颜色数 `m`，选择 `ε=1/(m+1)>0`，再将颜色沿同一个 `ρ` 拉回原完整甲板群。商覆盖的局部不相交邻域及 `L∘ρ` 的完整逐点公式，按前两节推导出近矩阵单位元子群 `H` 幂零；同色商落在同一个 `H` 中。直接应用已冻结的 `FiniteColorVirtualNilpotence.result`，得到上述原小位移生成子群虚幂零，无需 `H` 正规或生成元有限。

本批只保留数学说明；现有冻结群论与钉版矩阵、紧致性结果的绑定应用作为临时精确编译证据，不新增绑定 Lean 库声明、Describe、登记或冻结。结论限于原参考点，实际商覆盖和同一 `ρ` 的每元素每点评价桥仍为前提；任意点的统一 Margulis、薄部分类、有限尖点、紧核心及全局边界控制仍未完成。完整 Mostow–Prasad 刚性仍未完成，保留两侧原度量、同一个给定同伦等价 `h` 及其完整诱导同构 `d`、独立流形宇宙、非紧有限体积尖点和非可定向情形。


## 同一原距离下每个原点的统一小位移结论

存在仅由原始 H³ 上半空间选定的正数 `ε`：对任意独立类型宇宙中的拓扑空间 `M`、映射 `F:H³→M` 及其完整甲板群 `D`，若同一个 `F` 是完整甲板群原始评价作用的商覆盖，且同一个等距群同态 `ρ:D→(H³≃ᵢH³)` 对每个甲板元素和每个原点满足 `ρ(g)(x)=g·x`，则对每个原点 `p`，原群中由全部 `{g:D | dist(p,g·p)<ε}` 生成的子群虚幂零。`ε` 在引入 `M,F,ρ,p` 之前选定，所有距离均为同一个原始双曲距离；不输入点的可传递性、矩阵界、颜色或虚幂零性，不要求有限生成、定向保持、有限体积或紧致性。

写 `p=(z,t)`，由已有水平平移及正比例缩放构造原始等距变换 `sₚ=translation(z)·dilation(t)`，直接验证 `sₚ(p₀)=p`。对同一个原群上的同一个 `ρ`，取 `ρₚ(g)=sₚ⁻¹ρ(g)sₚ`，并复合上一节构造的 Lorentz 表示 `L`。每个元素和每个原点都满足 `L(ρₚ(g))v(x)=v(sₚ⁻¹(g·sₚ(x)))`，同时 `dist(p₀,ρₚ(g)(p₀))=dist(p,g·p)`。只对矩阵表示作共轭，原群、原始评价作用、同一个 `F` 和所求位移生成子群均保持原样。

在原点 `p` 直接使用原商覆盖的局部不相交邻域，取其原距离正半径球 `B(p,r)`。上述公式在 `p₀` 的第零坐标给出 `cosh(dist(p,g·p))=(L(ρₚ(g)))₀₀`，因此同一个近矩阵单位元子群 `Hₚ` 获得实际正隔离间隙 `cosh(r)−1`，由已冻结近单位元定理得 `Hₚ` 幂零。将上一节在 `p₀`、位移界一处已选定的有限颜色沿 `ρₚ` 拉回，颜色数 `m` 与 `p,M,F,ρ` 无关，同色商落在同一个 `Hₚ`。在原点 `p` 调用已冻结有限颜色群论结果，以同一个 `ε=1/(m+1)>0` 得到上述原小位移生成子群虚幂零。覆盖邻域及 `Hₚ` 可随点变化，最终 `ε` 不随点变化。

本批的完整任意点精确应用和点变换公式已通过编译，完整应用的具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。这些绑定应用仅作临时精确证据，本批追加数学说明，不新增绑定 Lean 库声明、Describe、登记或冻结。实际双曲流形的原度量商覆盖及同一 `ρ` 的完整评价桥仍待构造；薄部分类、有限尖点、紧核心、全局边界控制以及完整 Mostow–Prasad 刚性仍未完成，保留两侧原度量、同一个给定同伦等价 `h` 及完整诱导同构 `d`、独立流形宇宙、非紧有限体积尖点和非可定向情形。


## TauCeti 的完整甲板群入口与钉版差异

对 TauCeti 固定修订 `f610f8c59f917604dd7eec0960479700e3a4edb5` 的源码审查找到以下复用入口；本节报告源码中的声明和依赖，不报告在本仓编译通过或公理闭包核验。

- [Deck/Quotient/ActingGroup.lean](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/TauCeti/AlgebraicTopology/UniversalCover/Deck/Quotient/ActingGroup.lean) 的 `TauCeti.Deck.IsQuotientCoveringMap.deckMulEquiv` 接受 `IsQuotientCoveringMap f G`、楼上 `PreconnectedSpace E` 和 `Nonempty E`，声明 `G ≃* deck f`；其逐点评价及逆评价引理连接原作用与完整甲板变换。`toDeckHom_surjective` 在非空分支用同一纤维中的作用元素和覆盖提升唯一性识别任意甲板变换，空空间分支则直接处理。
- [Deck/Quotient/Covering.lean](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/TauCeti/AlgebraicTopology/UniversalCover/Deck/Quotient/Covering.lean) 的 `TauCeti.Deck.IsRegular.isQuotientCoveringMap` 接受楼上预连通性、`IsRegular p` 和 `IsCoveringMap p`，声明同一个 `p` 是完整 `deck p` 作用的商覆盖；同文件也有任意作用群的商覆盖到正规甲板作用的方向。它没有从任意覆盖自动取得正规性。
- [Hyperbolic/Mostow.lean](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/TauCeti/Geometry/Manifold/Riemannian/Hyperbolic/Mostow.lean) 的 `IsMostowRigid` 定义针对同一个紧致、连通、无边界流形上维数至少三的两套双曲度量；`isMostowRigid_of` 接受这条刚性结论本身，`IsMostowRigid.isometry` 从刚性假设取等距映射。该文件还定义并特化通用命题 `MostowRigidity`，没有无刚性前提的证明，也没有给定同伦等价的同伦及唯一性、非紧有限体积尖点条款。此审查只对该文件作此判断，不推断整个生态不存在证明。

上游该修订的 [lean-toolchain](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/lean-toolchain) 为 `leanprover/lean4:v4.35.0-rc3`，[lake-manifest.json](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/lake-manifest.json) 的 mathlib 修订为 `6b7abb3c7686292736be2955bd3eb9ebf63b456a`。本仓当前钉版分别为 `v4.33.0` 和 `db584cd6d46c92f209a44c0f1c829460d327499d`。上游 [Deck/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/f610f8c59f917604dd7eec0960479700e3a4edb5/TauCeti/AlgebraicTopology/UniversalCover/Deck/Basic.lean) 依赖 `Mathlib.Topology.Covering.Deck`，本仓钉版缺此模块；因此这些入口不能直接作为当前依赖导入。按 A17.2，只能评估满足逐声明准入、版权与完整许可证、依赖适配、标准公理闭包及本仓钉版退役条件的移植，或保留为研究入口；本批没有移植、升级依赖或重证。

这为上一节仍缺少的完整甲板群商覆盖与每元素每点评价提供了具名候选。对原 H³ 的标准自由且适当不连续等距作用商，仍需在本仓核验楼上预连通性、完整甲板群的身份及作用对应、完整商覆盖字段，以及与同一个原等距表示的连接，再实际应用统一半径；源码命中不结算这些义务。对一般原始流形的覆盖与原度量保持、薄部和有限尖点分类、紧核心及完整 Mostow–Prasad 目标也仍未完成，范围继续包含两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧尖点及非可定向情形。


## 标准原轨道商的完整甲板群与统一小位移结论

固定同一个原始 H³ 上半空间及双曲距离。对任意类型宇宙中的群 `Γ` 和等距群同态 `ρ:Γ→(H³≃ᵢH³)`，假设作用自由，即 `ρ(g)(p)=p` 推出 `g=1`，并假设适当不连续，即任意紧集 `K,L` 满足 `{g | (ρ(g) '' K ∩ L).Nonempty}` 有限。取原轨道商投影 `F=orbitQuotientMk ρ` 及保持同一个 `F` 的全部自同胚组成的完整原甲板群 `D`。存在一个在引入 `Γ,ρ,p` 之前选定的正数 `ε`，使每个原点 `p` 的 `{g:D | dist(p,g·p)<ε}` 生成子群虚幂零。此标准商应用已经实际构造 `ρD:D→(H³≃ᵢH³)`、每元素每点评价 `ρD(g)(x)=g·x` 和完整 `D` 作用的商覆盖性质，没有把这三项所求桥作为前提；不要求有限生成、正规性、定向保持、有限体积或紧致性。

原坐标同胚把连续满射 `(z,s)↦(z,exp(s))` 从 `ℂ×ℝ` 送到同一个原 H³；以 `log(t)` 构造逆原像，得到原楼上预连通性。原模型的已有 proper 性及自由、适当不连续作用给出标准轨道商覆盖，再经现有 `standardOrbitHomeomorph` 转到同一个 `F`。使用上一节具名上游作用群与完整甲板群等价的最小源码适配：保持版权、完整许可证及不可变来源，补写钉版缺少的原评价作用，复用提升唯一性和原作用群等价证明。由条件 `F∘e=F` 与逐点条件的函数外延等价，将上游完整甲板子群识别为原来的全部 `F` 保持自同胚，所得 `μ:Γ≃*D` 对每个点满足 `μ(g)·x=ρ(g)(x)`。取 `ρD=ρ∘μ⁻¹`，由 `μ(μ⁻¹(g))=g` 得到完整逐点评价桥，原群没有换成较小的作用子群。

原 `F` 的商映射性质由原作用群的商覆盖给出；每个完整甲板元素的连续性来自原自同胚。用 `μ` 将原纤维轨道关系和原不相交邻域传到完整 `D`，实际履行商覆盖结构的所有字段。然后直接应用前批的 `all_points_cutoff`，取得在所有 `Γ,ρ,p` 之前选定的同一个 `ε` 和上述完整原甲板群中的实际生成子群。轨道商载体属于 `Type 0`，作用群 `Γ` 可属于任意宇宙；此应用使用统一半径结果的 `Type 0` 特化，没有把原来任意 `M,N` 宇宙的完整目标改为同宇宙目标。

完整具名标准商应用、完整甲板群实现、原 H³ 预连通性及所复用上游群等价的本地适配均通过编译，零错误、零警告，打印公理闭包仅含 `propext, Classical.choice, Quot.sound`。本批是已有冻结及钉版结果、具名上游源码和原模型的绑定应用；代码只作本地临时精确证据，交付此数学说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不升级依赖。此结果结算的是标准原轨道商应用；对一般原始流形的实际覆盖与原度量识别、薄部及有限尖点分类、紧核心和全局边界控制仍未完成。包含两侧原度量、同一个给定 `h` 与完整 `d`、独立流形宇宙、非紧有限体积尖点及非可定向情形的完整 Mostow–Prasad 刚性仍未完成。


## 原 H³ 表示对全部 Lorentz 向量及非零 null 向量的保持

对前批从全部原 H³ 等距变换构造的同一个四维矩阵表示 `Aₑ`，令 `J=diag(1,-1,-1,-1)`，则对每个原等距变换，包括反向变换，有 `AₑᵀJAₑ=J`。因此对任意两个四维实向量 `x,y`，原 Lorentz 双线性形式满足 `⟨Aₑx,Aₑy⟩ₗ=⟨x,y⟩ₗ`；并有 `Aₑx≠0 ∧ ⟨Aₑx,Aₑx⟩ₗ=0` 当且仅当 `x≠0 ∧ ⟨x,x⟩ₗ=0`。这把原来在 H³ 坐标像上的两点距离核扩展到全部向量，不另行假设 Lorentz 保持性，不更换原表示或原双曲距离。

沿用原四点列矩阵 `Bₑ` 和读出矩阵 `Kₑ`：定义展开给出 `Kₑ=BₑᵀJ`，原逐点作用公式给出 `AₑB₁=Bₑ`。由已验证的 `KₑBₑ=K₁B₁` 得 `B₁ᵀ(AₑᵀJAₑ)B₁=B₁ᵀJB₁`；已有 `B₁` 的可逆性及其转置的可逆性允许消去两侧，得到所求全矩阵恒等式。调用钉版矩阵乘法与点积接口得全部向量的形式保持；原 `Aₑ` 可逆性使 `Aₑx=0` 当且仅当 `x=0`，从而得到非零 null 向量的完整等价。

完整精确源码已编译通过，零错误、零警告，上述三个具名目标的公理闭包仅含 `propext, Classical.choice, Quot.sound`。本批是原距离核、原表示构造与钉版矩阵接口的绑定及规范化应用，代码只作本地临时精确证据，不新增绑定 Lean 库声明、Describe、登记或冻结。它只结算全部向量的 Lorentz 形式及非零 null 向量保持；尚未构造归一化 null 球面的边界同胚或识别原 H³ 的理想边界。一般原流形的原度量覆盖、薄部及有限尖点分类、紧核心、全局边界控制和完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 原 H³ 等距群在归一化 null 球面上的实际同胚作用

令 `S={x:ℝ⁴ | x₀=1 ∧ ⟨x,x⟩ₗ=0}`，其中 Lorentz 形式仍为前节的 `diag(1,-1,-1,-1)`。对每个原 H³ 等距变换 `e` 及同一个原矩阵表示 `Aₑ`，实际构造 `bₑ(x)=Aₑx/(Aₑx)₀`，得到 `b:(H³≃ᵢH³)→(S≃ₜS)` 的群同态。它包含原全部等距变换，没有定向保持限制，也没有输入待证明的边界作用或同胚假设。

前节使 `Aₑx` 非零且为 null。null 向量若第零坐标为零，其余三个坐标的平方和为零，全部坐标必为零；因此分母处处非零。归一化保留 null 条件并将第零坐标置一。非零标量缩放不改变归一化，配合原矩阵乘法公式得到单位元和乘法作用律；原 `e⁻¹` 的同一公式构造逆映射。矩阵向量乘法连续，逐点非零分母使倒数及归一化连续；对逆映射同样成立，完整履行同胚的双向连续性字段。

完整精确作用、乘法、逆等价、连续性、同胚和群同态已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。前批原全向量 Lorentz 代数已独立审查通过；本批延伸经 kernel 核验及调用方检查，没有新增独立多视角审查，不冒称新增共识。代码仍为原模型证明及钉版矩阵、连续性接口的本地临时绑定证据，不新增绑定 Lean 库声明、Describe、登记或冻结。本结果尚未把归一化 null 球面识别为原 H³ 的理想边界；原流形的度量覆盖、薄部及有限尖点分类、紧核心、全局边界控制和完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 原 H³ 的正时间单位双曲面坐标与实际逆映射

保留原 H³ 上半空间度量及前节 Lorentz 坐标 `v(z,t)=((|z|²+t²+1)/(2t), Re(z)/t, Im(z)/t, (|z|²+t²−1)/(2t))`。它实际给出原载体与 `U={w:ℝ⁴ | ⟨w,w⟩ₗ=1 ∧ w₀>0}` 的双向等价；逆映射为 `z=(w₁+i w₂)/(w₀−w₃), t=1/(w₀−w₃)`，没有将满射、正时间分支或逆关系放在假设中。

单位 Lorentz 方程与三个空间坐标平方非负，推出每个 `w∈U` 都有 `w₀−w₃>0`，因此逆映射确实落在原正高度载体。逐坐标核对 `v(fromFutureUnit w)=w`；原距离核 `cosh(dist(p,q))=⟨v(p),v(q)⟩ₗ` 及 `cosh` 比较公式证明 `v` 单射，从而履行两个逆关系。同一个原等距矩阵 `Aₑ` 满足 `Aₑv(p)=v(e(p))`，故它在全部正时间单位向量上保持单位方程和严格正时间坐标，包含原全部等距变换，没有定向保持限制。

完整逆公式、双向等价与正时间分支保持已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。本批经 kernel 核验及调用方检查，没有新增独立多视角审查。它是原距离核与钉版比较、坐标及代数接口的临时精确绑定证据；不新增绑定 Lean 库声明、Describe、登记或冻结。这里未证明两模型的同胚、测地射线分类或原 H³ 理想边界识别；薄部、有限尖点、紧核心、原流形度量覆盖及完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点和非可定向情形。


## 原 H³ 度量中的显式等距直线及 null 端点收敛

对每个前节归一化 null 向量 `x`，正时间单位双曲面中的 `wₓ(t)=(cosh t, sinh t·x₁, sinh t·x₂, sinh t·x₃)` 经实际逆坐标映射给出原 H³ 上的 `γₓ(t)`。空间坐标平方和为一及 `cosh²t−sinh²t=1` 保证该构造对全部实参数有定义；原距离核与 `cosh(s−t)` 加减公式给出 `dist(γₓ(s),γₓ(t))=|s−t|`。因此它是原度量中的实际等距直线，限制于非负参数便得到测地射线，没有另设度量或假定曲线已等距。

沿 `t→+∞`，`v(γₓ(t))/v(γₓ(t))₀` 实际收敛到同一个 `x`。第零坐标恒为一；其余坐标为 `(sinh t/cosh t)·xᵢ`。将该比例写成 `(1−exp(−t)²)/(1+exp(−t)²)`，用钉版指数极限和非零极限分母证明逐坐标收敛，再得到整个四维向量的收敛。

实际距离公式、等距性及端点收敛的完整源码已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。失败的中间端点尝试排除；本批由协作实施、kernel 核验及调用方检查，没有新增 SSHX 多视角共识。源码仍为原距离核与钉版双曲函数、有限坐标和极限接口的临时精确绑定证据，不新增绑定 Lean 库声明、Describe、登记或冻结。本节没有分类从固定或任意起点出发的全部射线，也未证明不同起点射线的有界距离等价或完整理想边界识别；原流形度量覆盖、薄部、有限尖点、紧核心和完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 固定原点出发的全部原 H³ 度量射线的唯一方向

令原点为 `o=(0,1)`。对任何原载体上的函数 `r:ℝ→H³`，若 `r(0)=o`，且所有非负 `s,t` 满足原距离等式 `dist(r(s),r(t))=|s−t|`，则存在唯一归一化 null 向量 `x`，使全部非负参数满足 `r(t)=γₓ(t)`。这里不约束负参数；任何定义在非负实数上的度量射线延拓为全实函数后均属于该陈述，没有输入方向、双曲函数坐标或曲线方程假设。

将原距离核用于 `r(t),o`，得到第零 Lorentz 坐标 `cosh t`；单位方程给出空间坐标平方和 `sinh²t`。再将核用于 `r(t),r(1)`，得到空间内积 `sinh t·sinh 1`。因此三个差值 `v(r(t))ᵢ·sinh 1−v(r(1))ᵢ·sinh t` 的平方和为零，逐项均为零。由严格正的 `sinh 1` 构造 `x=(1,v(r(1))₁/sinh 1,v(r(1))₂/sinh 1,v(r(1))₃/sinh 1)`，证明其 null 条件；原坐标单射推出整条非负射线相等。参数 `1` 处的同一公式证明方向唯一，保留射线的正向。

完整构造、全非负参数相等和存在唯一结论已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`；失败的坐标推断及平方求解尝试排除。本批经 kernel 核验、调用方检查和协作方只读语义检查，没有新增 SSHX 多视角共识。它是原距离核及钉版双曲函数、平方非负、坐标和逻辑接口的临时精确绑定证据；不新增绑定 Lean 库声明、Describe、登记或冻结。结论仅分类从固定 `o` 出发的原度量射线，未处理任意起点射线的有界距离商或完整理想边界识别；原流形度量覆盖、薄部、有限尖点、紧核心和完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 固定原点射线的同步有界距离判别

对前节原 H³ 等距射线 `γₓ,γᵧ`，存在实常数 `C` 使所有非负参数满足 `dist(γₓ(t),γᵧ(t))≤C`，当且仅当 `x=y`。原距离核给出 `cosh(dist(γₓ(t),γᵧ(t)))=1+sinh²t·δ/2`，其中 `δ=(x₁−y₁)²+(x₂−y₂)²+(x₃−y₃)²`。`δ=0` 时平方非负逐坐标推出方向相同；方向相同时距离恒为零。

若 `δ>0` 而距离始终不超过 `C`，距离非负先给出 `C≥0`。取实际非负参数 `t=arsinh(sqrt(2 cosh C/δ))`，则 `sinh²t·δ=2 cosh C`，原距离公式变为 `cosh(distance)=1+cosh C`；另一方面 `cosh` 在非负数上的单调性使其不超过 `cosh C`，矛盾。此处使用显式有限见证，没有输入增长估计或无穷远分离假设。再实际调用前节全部射线分类：从同一个固定 `o=(0,1)` 出发的任意两条原度量射线，若同步参数距离有统一上界，则它们在所有非负参数逐点相等。

完整距离公式、方向判别的双向结论及任意固定原点射线的逐点相等均已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。失败的插入顺序和坐标求解尝试排除；本批由协作实施、kernel 核验及调用方检查，没有新增 SSHX 多视角共识。源码仍为原距离核、既证射线分类及钉版双曲函数、平方与比较接口的临时精确绑定证据，不新增绑定 Lean 库声明、Describe、登记或冻结。这只处理同一固定起点与同步非负参数；任意起点的射线有界距离商、完整理想边界识别、原流形度量覆盖、薄部、有限尖点、紧核心及完整 Mostow–Prasad 仍未完成，保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 原等距变换与实际射线端点的相容性

对每个原 H³ 等距变换 `e` 和归一化 null 方向 `x`，变换后实际曲线 `e(γₓ(t))` 的归一化 Lorentz 坐标沿 `t→+∞` 收敛到此前构造的同一个 `bₑ(x)=Aₑx/(Aₑx)₀`。因此该 null 球面作用确实与这些原度量射线的端点极限相容，没有另输入边界延拓、端点作用或相容性假设。

原矩阵公式、矩阵乘法连续性及既证射线端点收敛给出 `Aₑ(v(γₓ(t))/v(γₓ(t))₀)→Aₑx`。其第零坐标始终严格正：原 `v(γₓ(t))₀` 与 `v(e(γₓ(t)))₀` 都正。闭序极限给出 `(Aₑx)₀≥0`，前节非零 null 向量的时间坐标非零将它加强为严格正。倒数在非零极限处分母连续；归一化的非零缩放不变性与同一个原矩阵公式，最终得到所述实际端点收敛。

全原等距群的正时间 null 保持与实际端点相容性均已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。失败的序极限方向与子类型展开尝试排除；本批经 kernel 核验及调用方检查，没有新增 SSHX 多视角共识。代码仍是原模型证明及钉版矩阵、倒数、缩放和极限接口的临时精确绑定证据，不新增绑定 Lean 库声明、Describe、登记或冻结。这里没有把任意起点的全部度量射线按有界距离取商并识别为该球面，也未证明全局边界控制、薄部、有限尖点、紧核心、原流形度量覆盖或完整 Mostow–Prasad；保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 任意原 H³ 起点的度量射线分类与唯一 null 端点

对任意原 H³ 点 `p=(z,t)`，直接复用既有正高度缩放与水平平移，构造原 H³ 等距变换 `eₚ`，并核对 `eₚ(0,1)=p`。任何满足原距离等式的非负参数射线 `r` 若从 `p` 出发，均唯一表示为 `r(s)=eₚ(γₓ(s))`；证明实际将射线用 `eₚ⁻¹` 拉回标准原点，再调用已证全部射线分类。对从同一个任意 `p` 出发的两条射线，同步非负参数距离有统一上界仍推出逐点相等，实际调用既证有界距离判别，没有将表示或方向放入假设。

进而对任意 `r:ℝ→H³`，只要所有非负 `s,t` 满足 `dist(r(s),r(t))=|s−t|`，便存在唯一归一化 null 向量 `a`，使 `v(r(t))/v(r(t))₀→a` 随 `t→+∞` 成立。没有固定起点或端点假设，也不约束负参数。取其实际起点 `r(0)`，任意起点分类与原等距端点相容性给出极限 `a=bₑₚ(x)`；分类等式在最终非负参数上成立，足以迁移极限。四维实向量空间的 Hausdorff 极限唯一性给出 `a` 的唯一性。

任意起点等距运输、射线唯一分类、同起点有界距离相等及全部原度量射线的唯一端点均已本地编译通过，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。运输分类的失败结构投影尝试排除；最终全部端点应用首轮成功。本批由协作实施运输分类、调用方实施端点应用、kernel 核验和调用方检查，没有新增 SSHX 多视角共识。临时源码仅新增对既有热缓存 `HyperbolicDilation` 的引用，无依赖构建或钉版升级；源码仍为原模型和既证射线结果的临时精确绑定证据，不新增绑定 Lean 库声明、Describe、登记或冻结。尚未证明不同起点的射线同步距离有界当且仅当端点相同，也未完成射线商拓扑与 null 球面的识别、原流形度量覆盖、薄部、有限尖点、紧核心或完整 Mostow–Prasad；保留两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。
## 不同原 H³ 起点射线的有界距离与端点判别

对任意两条原 H³ 度量射线 `r,s:ℝ→H³`，仅要求所有非负参数满足原距离等式 `dist(r(u),r(t))=|u−t|` 及 `s` 的对应等式。允许 `r(0)` 与 `s(0)` 不同。已证明：存在统一实数上界 `C` 使所有非负 `t` 满足 `dist(r(t),s(t))≤C`，当且仅当两条射线实际归一化 Lorentz 坐标在 `t→+∞` 的唯一 null 端点相同。起点等距运输、方向及端点均由射线构造，不放入额外假设；负参数不受约束。

证明将射线表示为原等距变换作用后的 `e(γₓ(t))` 与 `f(γᵧ(t))`，其原坐标分别分解为 `exp(−t)P+sinh(t)U` 与 `exp(−t)Q+sinh(t)V`。原距离的 `cosh` 因而等于一个一致有界的混合项加 `sinh(t)²·⟨U,V⟩`。两个正时间 null 向量的配对等于正时间坐标之积乘实际端点空间坐标平方距离的一半，所以非负，且仅在端点相同时为零。若距离有界而配对为正，显式选取 `arsinh(sqrt(A/⟨U,V⟩))` 的非负参数产生矛盾；反向配对为零时，混合项的绝对值界经已有 `arsinh` 与 `cosh` 比较给出原距离上界。最后使用任意起点射线分类和实际极限唯一性，消去变换与方向表示。

完整跨起点距离公式、配对的双向有界性、实际端点判别及任意射线应用的精确组合源码已通过缓存保护入口编译，零错误、零警告，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。本批经 kernel 核验和协作方只读语义复核，没有新增 SSHX 多视角共识。首轮跨距离单元的钉版接口名错误已修复，失败结果排除；最终组合首轮成功。所有精确源码保留于临时路径，按 §3.2 如实判 `proof_shape: bind-only`、`admission_basis: none`，不新增绑定 Lean 库声明、Describe、登记或冻结。不改 imports、依赖钉版、判官或工具。

该判别仍不等于射线商拓扑与 null 球面的同胚，也未完成原流形度量覆盖、薄部、有限尖点、紧核心或完整 Mostow–Prasad。完整目标继续保留两侧原度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 原 H³ 度量射线的有界距离商与 null 球面等价

取全部满足非负参数原 H³ 距离等式的射线，起点任意，负参数不受约束。实际关系 `RayBounded` 定义为同步非负参数距离存在统一实数上界；由已证不同起点判别，它等价于两条射线实际归一化 Lorentz 极限端点相同，并确实满足自反、对称和传递性。

端点映射沿该关系下降到真正的射线商 `RayBoundary`。每个 null 点的原 H³ 显式射线提供逆映射；实际极限唯一性核对其端点，商相等由原有界距离关系证明。两个复合均为恒等，得到射线商与归一化 null 球面的集合等价；任意代表的商像仍是它实际射线的唯一端点。逆映射选用标准原点的代表，不要求输入射线固定起点，也没有拓扑假设。

实际有界关系、商等价和代表端点公式的完整组合源码已通过缓存保护入口编译，零错误、零警告，无 `sorry`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`；协作方只读语义复核通过，没有新增 SSHX 多视角共识。该增量是既证原射线结果与 `Quotient` API 的实际消费，按 §3.2 如实判 `proof_shape: bind-only`、`admission_basis: none`；精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结。

目前仅建立集合等价，尚未赋予或识别射线商拓扑，不主张与 null 球面同胚；原流形度量覆盖、薄部、有限尖点、紧核心和完整 Mostow–Prasad 仍未完成，原有两侧度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、尖点及非可定向目标继续保留。


## 原 H³ 射线的自然商拓扑与 null 球面同胚

射线空间采用原 H³ 函数空间 `ℝ→H³` 的逐点乘积拓扑，再取非负参数原距离等式所定义的子类型；负参数的任意扩展不受限制。射线商采用实际同步非负参数有界距离关系的 `Quotient` 拓扑。

实际端点可由两个原度量点计算：归一化 `v(r(1))−exp(−1)·v(r(0))`，其时间坐标严格为正。原坐标映射 `v` 的连续性、乘积拓扑中的两点评价及非零倒数证明端点连续；该映射通过真正的 `Quotient.lift` 连续下降。反向采用显式原 H³ 射线，其连续性由真实正时间单位双曲面逆坐标和原坐标同胚证明，再组合自然商映射。已证两复合恒等，故同胚的正反方向均具有上述拓扑中的连续性，任意商代表对应自身实际唯一端点。

完整两点评价端点公式、严格正时间分母、原坐标与标准代表连续性、实际商同胚及代表公式的精确组合源码已通过缓存保护入口编译，零错误、零警告，无 `sorry`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。协作方只读语义复核通过，没有新增 SSHX 多视角共识。失败的函数表达式规范化、子类型拓扑推断和常数标量类型推断尝试均已修复，失败结果排除。按 §3.2 如实判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无新增 imports 或钉版升级。

这里指逐点乘积拓扑及其实际商拓扑；没有证明紧开拓扑、其他视觉边界定义或紧化与该商相同。原流形度量覆盖、薄部、有限尖点、紧核心和完整 Mostow–Prasad 仍未完成；两侧原度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 真正非负参数射线的紧开拓扑商与原乘积拓扑商对应

采用钉版 `ContinuousMap.compactOpen` 的实际连续映射空间 `C(ℝ≥0,H³)`，取原 H³ 度量等距射线子类型，再按全部非负参数的同步原距离有统一上界形成自然商。射线起点任意。以 `r(t.toNNReal)` 连接既有非负实参数证明，实际非负参数 `atTop` 极限及其唯一性均由已证原端点极限迁移；两点评价公式和严格正时间分母给出紧开拓扑中的端点连续性。

显式原 H³ 射线的联合连续性经实际逆坐标证明；钉版 `ContinuousMap.continuous_of_continuous_uncurry` 将该族送入紧开拓扑映射空间，并保留原度量等距性。端点按实际有界距离关系连续下降，标准射线提供连续逆映射，两个复合恒等，得到紧开拓扑射线商与归一化 null 球面的同胚。

原逐点乘积拓扑射线商与该紧开拓扑射线商通过同一实际端点对应。代表等式进一步核对：任意原实参数射线的商类映为其自然非负参数限制射线的商类。这里识别的是两个自然商；没有证明两个原始射线空间或其拓扑相同，原乘积模型的负参数任意扩展仍不受限制。

完整非负参数端点、实际紧开拓扑连续性、商同胚及自然限制代表公式已通过缓存保护入口编译，零错误、零警告，无 `sorry`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。协作方只读语义复核通过，没有新增 SSHX 多视角共识。失败的记号作用域、函数复合规范化和未标注参数类型推断尝试均已修复，失败结果排除；未改预算。该增量按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结。只引用钉版已有热缓存的紧开拓扑与非负实数极限模块，无钉版升级。

这里未识别另一视觉边界定义或紧化，也未从格子同构构造全局边界映射。原流形度量覆盖、薄部、有限尖点、紧核心和完整 Mostow–Prasad 仍未完成；两侧原度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 原 H³ 等距群在实际紧开拓扑射线商上的忠实作用

任意原 H³ 等距变换 `e` 直接后合成真实 NNReal 度量射线 `r`，得到 `t↦e(r(t))`；复用钉版 compact-open 后合成连续性，原距离不变保持实际同步有界距离关系。该作用经真正的商下降，逆映射来自原 `e⁻¹`，并满足单位与乘法律。商代表公式核对它确实来自实际射线后合成；原 NNReal 极限推导端点相容，最后才证明与既有 null 球面同胚作用共轭，未通过共轭定义商作用。

忠实性证明使用四个明确的归一化 null 向量。原 Lorentz 配对与已证严格正时间尺度迫使固定这些 null 点的作用尺度全部为一；四向量矩阵可逆，故原矩阵恒等，再由原坐标作用公式和坐标单射性恢复原等距变换恒等。最终证明实际消费该结论和商端点相容性，得到实际紧开拓扑射线商作用单射。作用及忠实性均由原等距变换构造，不输入边界作用或忠实性假设；允许全部原等距变换，包括反向者。

完整实际后合成、原有界关系保持、商同胚、群律、代表公式、端点共轭、四 null 点忠实性及商作用单射的精确组合源码已通过缓存保护入口编译，零错误、零警告，无 `sorry`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。实际作用单元和最终组合首轮成功；忠实性单元的有限向量索引规范化及函数表达式改写失败已修复并排除，未改预算。协作方只读语义复核通过，没有新增 SSHX 多视角共识。按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无新增 imports、钉版升级或工具改动。

这里只研究固定原等距变换的自然射线商作用，未引入等距群参数的联合拓扑，也未证明格子边界刚性、boundary centralizer 平凡、原流形度量覆盖、薄部、有限尖点、紧核心或完整 Mostow–Prasad。两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 保持未来单位双曲面的 Lorentz 矩阵到原 H³ 等距变换的唯一反向构造

给定可逆实四维矩阵 `A`，仅假设它对全部原 Lorentz 向量保持配对，并将每个正时间单位向量送到正时间向量，构造唯一原 H³ 等距变换 `e`，使此前同一个 `actionMatrix e` 精确等于输入 `A`。允许全部原等距变换，包括反向者；没有将原等距变换存在、原距离保持或逆矩阵的未来保持放入假设。

逆矩阵的未来保持由正向假设实际推出：对未来单位向量 `w`，`z=A⁻¹w` 的配对仍为一，故其时间坐标非零。若时间为负，则 `-z` 是未来单位向量；但 `A(-z)=-w` 的时间为负，与正向假设矛盾。正反矩阵因此给出真实未来单位双曲面的双射。经既证原 H³ 坐标双射运输得到原点集双射；配对与原距离的 `cosh` 核公式、非负距离上的单调比较证明该同一个双射保持原距离。全点坐标公式及 `matrix_ext` 证明矩阵回读，原坐标单射性证明唯一性。

逆未来性、实际原等距变换、坐标公式、矩阵回读及唯一重建的精确组合源码经缓存保护入口首轮编译成功，零错误、零警告，无 `sorry`，五个具名目标的公理闭包仅含 `propext, Classical.choice, Quot.sound`。协作方实施与调用方只读语义复核均完成，没有新增 SSHX 多视角共识。源码 SHA256 为 `8491a37e7818723243a40886d5e387749a47ea5a066eec1dabd0efdaf48c9d9d`，94476 字节；路径 `.lake/mostow-h3-future-lorentz-reconstruction.lean`，相邻编译收据记录真实退出码。按 §3.2 作为既有模型及钉版矩阵、双射、距离核接口的临时绑定证据，判 `proof_shape: bind-only`、`admission_basis: none`，不新增绑定 Lean 库声明、Describe、登记或冻结；无新增 imports、钉版升级、预算或工具改动。

该反向构造补齐原 H³ 等距变换表示的代数方向，仍未从抽象格子同构构造输入矩阵 `A`。一般原流形的原度量覆盖、薄部、有限尖点、紧核心、全局边界控制及完整 Mostow–Prasad 继续未完成；保留两侧原度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、非紧有限体积尖点及非可定向情形。


## 有限阶原 H³ 等距变换的实际内部固定点与自由作用的无挠性

对任意原 H³ 等距变换 `e`、正整数 `n` 及原群等式 `eⁿ=1`，从实际有限轨道构造原 H³ 点 `p`，证明 `e(p)=p`。结论包含反向等距变换，不需要离散性、有限体积或预先给定固定点。

取标准原点 `p₀`，令 `W=Σ₀≤i<n v(eⁱ(p₀))`。各项时间坐标严格为正，故 `W₀>0`；每对轨道点的 Lorentz 配对等于其原距离的 `cosh`，至少为一，因此 `⟨W,W⟩≥n²>0`。同一个原矩阵 `Aₑ` 循环置换该轨道和，故 `AₑW=W`。实际向量 `W/sqrt(⟨W,W⟩)` 是未来单位向量，既证 `fromFutureUnit` 提供原 H³ 点；原作用公式与坐标单射性恢复该点的固定性。

该固定点构造被下一结论实际消费：对任意群宇宙中的原 H³ 等距表示 `ρ`，若 `ρ(g)(p)=p` 总能推出 `g=1`，则每个非单位 `g` 的原像 `ρ(g)` 都非有限阶。这里仅使用原自由作用；没有把无挠性或忠实性另列为前提。它为虚幂零小位移子群的中心元素分析提供前提，还未证明这些子群的共同边界点、薄部分解或有限尖点。

两个具名目标的精确组合源码已通过缓存保护入口第二轮完整编译，零错误、零警告，无 `sorry`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮范围非空条件及单位等距变换接口错误已修复；失败的完整源码和日志保留排除，没有接纳部分失败证明。协作方实施、调用方只读语义复核完成，没有新增 SSHX 多视角共识。源码 `.lake/mostow-h3-finite-order-fixed-point.lean` 的 SHA256 为 `2de0eccf7ab68388c06a11ce7825a58f0a071ff5cbe74340ec1d310a7cd1c814`，98189 字节，相邻收据记录实际退出码。该原模型与钉版有限和、配对、距离核及未来单位坐标的应用按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无 imports、依赖钉版、预算或工具改动。

本批未构造由同一个给定 `h` 和完整 `d` 导出的全局边界映射或格子共轭。一般原流形的原度量覆盖、薄部、有限尖点、紧核心及完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整诱导 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 原有界位移逃逸序列的边界固定性与同一幂子列的中心化子

给定实际原 H³ 序列 `pₖ` 和实际归一化 null 点 `b`，明确假设 `normalize(v(pₖ))→b` 且逆时间坐标 `v(pₖ)₀⁻¹→0`。若原等距变换 `g` 满足统一原距离界 `dist(pₖ,g(pₖ))≤C`，则证明同一个实际原边界作用固定 `b`。这里不假设固定性，不另给变换后序列的极限，包含反向等距变换。

实际原作用公式与距离核给出 `⟨normalize(v(pₖ)),A_g normalize(v(pₖ))⟩=v(pₖ)₀⁻² cosh(dist(pₖ,g(pₖ)))`。配对非负，由统一距离界及逆时间收敛夹逼至零；实际矩阵乘法和配对的连续性把极限识别为 `⟨b,A_g b⟩`。既证正时间 null 配对为零的端点判别因此推出 `g(b)=b`。

该结论由同一原幂子列的中心化子应用实际消费：若 `pₖ=eⁿᵏ(p₀)` 满足上述同一个 `b` 的两个极限，则每个原环境等距变换 `g` 只要与原 `e` 交换，都固定同一个 `b`。幂交换与原等距性实际给出所有 `k` 的 `dist(pₖ,g(pₖ))=dist(p₀,g(p₀))`；没有为不同 `g` 重新选序列或端点。此处仍未从原离散性或自由作用内部构造 `nₖ,b` 及这两个极限。

这恢复旧共同边界构造所需的一条最小源码桥。已只读检查 38 个同级 worktree 的 `.lake` 顶层与明确 Mostow 子目录，以及 81 份定位类 JSON，未找到旧匿名应用的两个接受基线对应的精确源码；旧笔记不能作为可导入定理。当前两具名目标经缓存保护入口第二轮完整编译成功，零错误、零警告，无 `sorry`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮邻域记号错误的完整失败源码与日志保留排除。协作方实施、调用方只读语义复核完成，没有新增 SSHX 多视角共识。源码 `.lake/mostow-h3-escaping-orbit-centralizer.lean` 的 SHA256 为 `8c0518ca6f8f955d54febffb653c7b3a9dfb8de35efb0b5cfae7f2c3a1f61e8d`，101894 字节；相邻收据记录实际退出码。

该原模型与既证 null 配对判别、钉版极限及夹逼接口的应用按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无 imports、依赖钉版、预算或工具改动。实际逃逸序列与 null 极限存在性、虚幂零小位移子群的共同边界控制、薄部及有限尖点、原流形的原度量覆盖和完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 原有界幂轨道的实际内部固定点与自由作用的幂逃逸

对任意原 H³ 等距变换 `e` 和原点 `p`，仅假设存在统一原距离界 `dist(p,eⁿ(p))≤C`，构造原点 `q` 并证明 `e(q)=q`。包含反向等距变换，不输入固定点，也不需要离散性、等距群参数拓扑、定向或有限体积假设。

实际 Cesàro Lorentz 均值 `Wₙ=(n+1)⁻¹ Σ₀≤i<n+1 v(eⁱ(p))` 的时间坐标至少为一，配对 `⟨Wₙ,Wₙ⟩` 也至少为一；这由原距离核 `cosh(dist)≥1` 和有限求和直接推出。三角不等式与标准原点距离核把原幂轨道距离界转为所有原 Lorentz 坐标的统一范数界，均值因此落在实际有限维紧闭球中。选取严格递增的收敛子列；同一个原矩阵满足精确伸缩和式 `AₑWₙ−Wₙ=(n+1)⁻¹(v(eⁿ⁺¹(p))−v(p))`，右端由轨道界趋零，故实际极限 `w` 被 `Aₑ` 固定。极限仍满足时间和配对至少为一，正时间单位归一化及既证 `fromFutureUnit`、原作用公式和坐标单射性给出真正原 H³ 固定点。

该构造被原自由作用的下一结论实际消费：对任意群宇宙中的原等距表示 `ρ`，若原固定点推出群元素为单位元，则每个非单位 `g` 在每个原点 `p` 的非负整数幂轨道都无统一原距离界。无挠性、原幂逃逸或离散性均未另列为前提。此结论提供此前中心化子边界桥所需的逃逸起点，尚未选出实际幂子列及 null 极限。

两个具名目标经缓存保护入口第二轮完整编译成功，零错误、零警告，无 `sorry`，公理闭包仅含 `propext, Classical.choice, Quot.sound`；已成功基底的字节前缀保持不变。首轮有限索引、局部定义、强制转换及求和化简错误的完整失败源码与日志保留排除。协作方实施、调用方只读语义复核完成，没有新增 SSHX 多视角共识。源码 `.lake/mostow-h3-bounded-orbit-fixed-point.lean` 的 SHA256 为 `11980c869bd41d80f99a6431aefa1bdba0bb6408d11aa54f6b2add1827a4009a`，110674 字节，相邻编译收据记录真实退出码。

该原模型与既证坐标、有限轨道及钉版有限和、紧子列和极限接口的应用按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无 imports、依赖钉版、预算或工具改动。原小位移虚幂零子群的共同边界点、薄部与有限尖点、一般原流形的原度量覆盖、全局格子边界控制及完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向目标继续保留。


## 从原自由作用内部构造非单位元素中心化子的同一共同边界点

对任意群宇宙中的原 H³ 等距表示 `ρ`，仅假设其原作用自由，并取实际非单位元素 `g`，内部构造同一个实际归一化 null 点 `b`，使每个与原 `ρ(g)` 交换的原环境等距变换都固定 `b`。顶层没有预给无限阶元素、幂子列、边界点、极限、方向、离散性、等距群参数拓扑或有限体积前提；包含反向等距变换。

自由作用与已证有界幂轨道固定点构造给出 `ρ(g)` 在标准原点的幂轨道无界，实际为每个自然数 `k` 选择幂指数，使原位移超过 `2k+2`。原标准点距离核及指数函数界推出这些轨道点的时间坐标趋于正无穷，逆时间趋零。实际归一化坐标逐坐标范数至多一，故位于四维实向量空间的紧闭单位球；内部提取严格递增的收敛子列。极限第零坐标为一，Lorentz 自配对等于逆时间平方的极限零，因而构造真实 `b : NullSphere`。最后实际消费前批幂子列中心化子桥：所有交换者在同一子列上的原位移恒定，所以全部固定同一个内部选出的 `b`。

完整具名构造经缓存保护入口首轮编译成功，零错误、零警告，无 `sorry`，公理闭包仅含 `propext, Classical.choice, Quot.sound`；无失败尝试，已成功基底的字节前缀未改。协作方实施、调用方只读语义复核完成，没有新增 SSHX 多视角共识。源码 `.lake/mostow-h3-free-element-centralizer-boundary.lean` 的 SHA256 为 `0ea486f8d82de5cd4770ea6f0c25b2effa219267268a0971c212829fbb806150`，114348 字节，相邻收据记录真实退出码。

该原模型与已证幂逃逸、实际端点桥及钉版紧子列、极限、指数接口的应用按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`，精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结；无 imports、依赖钉版、预算或工具改动。这里结算了原自由作用中单个非单位元素的中心化子共同边界点构造，尚未组装幂零子群共同点、虚幂零有限边界轨道、薄部与有限尖点或全局格子刚性。两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向的完整 Mostow–Prasad 继续未完成。


## 原自由幂零等距群的实际共同 null 边界点

对任意类型宇宙中的幂零群 `G` 及原 H³ 自由等距表示 `ρ`，内部构造实际归一化 null 点 `b`，使所有原 `ρ(g)` 均固定同一个 `b`。无需离散性、有限生成、无限阶元素、预给边界点、定向或有限体积前提，包含反向等距变换。

平凡群分支选取已构造的实际 null 点并消费原单位作用公式。非平凡分支直接复用钉版 `Group.IsNilpotent.center_ne_bot` 和 `Subgroup.ne_bot_iff_exists_ne_one` 选择实际非单位中心元素 `z`；原自由作用的已证完整中心化子构造提供同一个实际 `b`。中心关系及同一个 `ρ` 的乘法保持证明所有原 `ρ(g)` 都与 `ρ(z)` 交换，故它们全部固定此同一个内部构造的点。没有把中心化子结论、逃逸序列或实际 null 极限另列为前提。

完整具名应用经缓存保护入口第二轮编译成功，零错误、零警告，无 `sorry`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮虽 exit0 但有两项局部实例书写警告，其完整源码与日志保留排除；按钉版建议修复，没有关闭 linter。协作方实施、调用方只读语义复核完成，没有新增 SSHX 多视角共识。源码 `.lake/mostow-h3-nilpotent-common-boundary.lean` 的 SHA256 为 `e5fa43a6dcb2c6c7ab1007fb5d4ea4b81d59bba187ee6e583ec3cd12f3fbeeec`，115521 字节，相邻收据记录真实退出码。仅新增钉版已有热缓存 `Mathlib.GroupTheory.Nilpotent`，未升级依赖或构建新闭包。

该实际原几何构造与既有中心和群同态接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确源码保持临时证据，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。这里只结算原自由幂零作用的共同边界点，尚未构造虚幂零有限边界轨道、薄部与有限尖点、原流形原度量覆盖或全局格子边界刚性。两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向的完整 Mostow–Prasad 继续未完成。


## 原自由虚幂零作用的实际有限边界轨道与小位移子群应用范围

对任意类型宇宙中的群 `G`、原 H³ 自由等距表示 `ρ` 及实际有限指数幂零子群 `H≤G`，内部构造实际归一化 null 点 `b`，证明整个 `G` 在同一个原边界作用下的 `b` 轨道有限。不要求 `H` 正规，也不输入边界点、有限轨道、离散性、有限体积或定向；包含反向等距变换。

实际限制同一个 `ρ` 到 `H`，由原自由性继承子群自由性，消费前批幂零共同点构造得到由 `H` 固定的实际 `b`。当 `x⁻¹y∈H` 时，原表示的乘法保持与原 null 作用的乘法公式给出 `ρ(x)b=ρ(y)b`。因此实际轨道函数下降到非正规左陪集商 `G/H`；钉版有限指数接口给出该商有限，真实 `Quotient.lift` 的有限像包含整个原 `G` 的轨道。没有把有限像或商作用另列为假设。

与现有统一小位移结论的只读组合范围已核对：`all_points_cutoff` 给出的是实际 `S_p=Subgroup.closure {d : fullDeckGroup F | dist p (d • p)<ε}` 的虚幂零性。应用本批结论时取 `G:=S_p`，把同一个原 deck 表示限制到 `S_p`，并取虚幂零性提供的内部见证 `H≤S_p`。原覆盖的 `IsCancelSMul` 与同一表示的评价相容性提供自由性，故得到的是小位移生成子群 `S_p` 的实际有限边界轨道；没有把 `H` 在 `S_p` 中的有限指数误作其在完整 deck 群中的有限指数，也不声称整个有限体积格子有有限边界轨道。这里只核对精确接口，没有新增组合包装或重编既有统一小位移源码。

完整具名应用经缓存保护入口第二轮真实编译成功，host `90512` exit0，零错误、零警告，无 `sorryAx`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮陪集关系字段和群同态改写错误的完整失败源码与日志保留排除；成功基底的字节前缀未改。协作方实施、调用方只读复核实际限制、陪集下降和应用范围，没有新增 SSHX 共识。源码 `.lake/mostow-h3-virtually-nilpotent-finite-boundary-orbit.lean` 的 SHA256 为 `fe5ea1ce1a680bbcaaf352f08611668789aa9d747f82689ed0cf9b27e7d54679`，117259 字节，相邻收据记录实际退出码。仅新增钉版已有热缓存 `Mathlib.GroupTheory.Index`，未升级依赖或构建新闭包。

该原模型与既证幂零共同点、陪集和有限像接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确 Lean 源码保持临时证据，远端 PR CI 仅验证本 Library 说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。有限轨道的更精确 elementary 分类、薄部尖点和轴管、有限尖点与紧核心、一般原流形的原度量覆盖、全局边界控制及格子共轭仍未完成。两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向的完整 Mostow–Prasad 继续未完成。


## 原自由作用的有限边界轨道给出同一个全群共同固定点

对实际原 H³ 等距变换 `e`、正整数 `n` 和实际归一化 null 点 `b`，若原边界作用满足 `eⁿ(b)=b` 但 `e(b)≠b`，则构造原内部点 `p` 并证明 `e(p)=p`。包含反向等距变换，没有把内部固定点或未归一化周期另列为前提。

令 `A` 为原 `e` 的实际 Lorentz 矩阵。归一化周期先给出 `Aⁿb=μb` 及真实正数 `μ`。同一原幂矩阵与 `A` 交换，故 `Aⁿ(Ab)=μAb`；原 null 配对的非负性和零配对端点判别把 `e(b)≠b` 转为 `⟨b,Ab⟩>0`。Lorentz 配对保持于是强迫 `μ²=1`，正性进一步给出 `μ=1`。实际循环和 `W=Σ₀≤i<n Aⁱb` 被 `A` 固定，时间坐标严格为正；其自配对是全非负的双和，含严格正的 `b,Ab` 交叉项，故也严格为正。真实正时间 timelike 归一化及原 `fromFutureUnit` 构造因此给出原内部固定点。

这被任意群宇宙中的原自由表示 `ρ` 实际消费：给定同一个实际 `b` 的原全群边界轨道有限，在该有限轨道上限制 `ρ(g)` 的实际原边界双射，钉版周期点接口提供 `b` 的正周期。若 `ρ(g)` 移动 `b`，前述构造给出原内部固定点；原自由性推出 `g=1`，与移动矛盾。因此每个原 `ρ(g)` 都固定这个同一个 `b`。这里没有声称该共同固定点唯一。

与前批实际虚幂零构造的只读组合也已核对：前批从同一个 `ρ` 与实际内部有限指数幂零子群构造 `b` 及其有限轨道，本批保持该同一个 `b` 并给出全群共同固定性。消费现有 `all_points_cutoff` 时仍取 `G:=S_p` 为实际小位移生成子群，同一个 deck 表示限制到 `S_p`，实际 `H≤S_p` 为其虚幂零内部见证；原覆盖的自由性和评价相容性提供所需前提。输出是每个这样的 `S_p` 固定一个内部构造的实际原边界点，未声称完整 deck 群有共同点，尚未推出尖点或轴管。

两个具名目标经缓存保护入口第二轮真实编译成功，host `2961` exit0，零错误、零警告，无 `sorryAx`，各具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮有限轨道函数展开的两处接口错误已具体修复，完整失败源码与日志保留排除；没有接纳整轮失败中的局部成功块。协作方实施、调用方只读复核同一缩放、正配对循环和、有限轨道上的真实周期及组合范围，没有新增 SSHX 共识。源码 `.lake/mostow-h3-finite-boundary-orbit-common-fixed.lean` 的 SHA256 为 `a97d22ce831b0103fa51e774a2a076b1baa9d0c95d5a465fd2fd869bb7e9586a`，123809 字节；相邻收据记录实际退出码。成功基底字节前缀未改，没有新增 import 或依赖构建。

该原模型与已有配对、周期点、有限和及未来单位接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确 Lean 保持本地临时证据，远端 CI 仅验证本 Library 说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。单位缩放的平移与 horoball 分支、非单位缩放的共同第二端点与轴分支、薄部与有限尖点、一般原流形的原度量覆盖及完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向范围继续保留。


## 任意实际共同边界点的原等距归一化与同一表示的真实共轭

对任意实际 `b : NullSphere`，内部构造原 H³ 等距变换 `e`，使同一个原边界作用将 `b` 送到固定实际 `t:=nullFramePoint 3`，其坐标逐字为 `![1,0,0,1]`。未输入归一化等距变换、Lorentz 矩阵存在性或反射保持性，允许反向等距变换。

若 `b=t`，取原单位等距变换。否则取真实向量 `w=b−t`，其时间坐标为零；原 null 配对非负性和零配对端点判别给出 `⟨b,t⟩>0`，故 `q=⟨w,w⟩=−2⟨b,t⟩<0`。实际秩一矩阵 `A=I−(2/q)w⊗(w₀,−w₁,−w₂,−w₃)` 的原乘向量公式为 `Ax=x−(2⟨x,w⟩/q)w`。逐字配对计算证明其保持所有向量的 Lorentz 配对，平方为单位矩阵，且时间坐标保持。由此构造真实矩阵单位并消费前批 `futureLorentzIsometry`，获得实际原 `e`；同一个 `actionMatrix e` 回读为 `A`，真实 `Ab=t` 和第零坐标为一给出所需原边界归一化。没有仅凭一个未经验证的空间正交反射声称原等距变换存在。

这被同一原表示的共同点应用实际消费：对原 `ρ` 和所有 `ρ(g)` 固定的同一个 `b`，上述构造提供同一个 `e`。原作用乘法、逆元及单位公式实际推出 `e⁻¹(t)=b`，继而证明所有同一个 `eρ(g)e⁻¹` 的原边界作用固定同一个 `t`。由此前实际小位移生成子群的共同点构造，得到其进入固定无穷远稳定子接口的真实归一化入口；尚未从这一入口推出平移核、尖点或轴管分类。

两主目标经缓存保护入口第二轮真实编译成功，host `77597` exit0，零错误、零警告，无 `sorryAx`，具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮矩阵乘向量改写方向及已闭合目标后的多余 tactic 已具体修复，完整失败源码与日志整体保留排除。协作方实施、调用方只读复核真实矩阵、全向量配对与时间保持、原等距重建及同一表示共轭，没有新增 SSHX 共识。源码 `.lake/mostow-h3-boundary-normalization.lean` 的 SHA256 为 `8d282a27ad7a50c2175299192376e8288fce19960bfb7f0e6e57ebbdf9d32869`，130182 字节，相邻收据记录实际终态。最新成功基底完整字节前缀保留，没有新增 import、依赖版本或构建闭包。

旧 Library 归一化笔记没有可定位的精确接受源码，未当作可调用 Lean 定理；本批直接复用已有真实原 Lorentz 接口补齐源码桥。该原模型与配对、矩阵及未来单位接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确 Lean 保持本地临时证据，远端 required CI 仅验证本 Library 说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。单位与非单位缩放的精确几何分类、薄部、有限尖点和紧核心、一般原流形的原度量覆盖及完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向范围继续保留。


## 同一原无穷远稳定子的实际高度缩放、乘法律与 horoball 精确像

对同一个原 H³ 等距变换 `e`，定义实际正数 `λ(e)=(actionMatrix e *ᵥ (nullFramePoint 3).val)₀`，其正性由真实未来 null 作用推出。若同一个原归一化边界作用固定 `t:=nullFramePoint 3`，原未归一化作用实际满足 `Aₑt=λ(e)t`。这里未把高度缩放、群特征或 horoball 像作为输入，包含反向等距变换。

精确原坐标公式给出 `⟨v(p),t⟩=1/height p.coordinates`，原高度的严格正性清除分母。原全向量 Lorentz 配对保持与同一原作用公式据此推出 `λ(e)/height (e(p)).coordinates=1/height p.coordinates`，故实际原高度满足 `height (e(p)).coordinates=λ(e)·height p.coordinates`。这个高度是原上半空间坐标中的 `height p.coordinates`，没有换成另一模型的额外高度函数。

对两个分别固定同一个实际 `t` 的原等距变换 `e,f`，同一原矩阵的乘法保持和上述真实射线缩放给出 `λ(ef)=λ(e)λ(f)`。没有声称这个公式对不稳定 `t` 的任意原元素也成立。高度律由真实几何消费者进一步消费：对任意实数阈值 `T`，证明原 `e` 的实际集合像 `e '' {p | T<height p.coordinates}` 恰等于 `{p | λ(e)T<height p.coordinates}`。正乘子给出正向包含，原 `e` 的满射性与同一个高度律给出反向包含；不需要预给逆元素高度律或假设 horoball 像。单位缩放因而保持这些原水平 horoball，非单位缩放则精确改变其阈值；这里尚未证明完整 deck 群中的 horoball 分离或商尖点存在性。

四个具名目标经缓存保护入口第二轮真实编译成功，host `32197` exit0，零错误、零警告，无 `sorryAx`，各具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。首轮原高度定义展开及正乘法不等式实例解析的三处错误已具体修复，完整失败源码和日志整体保留排除，没有接纳失败批的局部成功块。协作方实施、调用方只读复核真实原高度、同一射线缩放、乘法适用范围和实际集合像的两向证明，没有新增 SSHX 共识。源码 `.lake/mostow-h3-infinity-height-horoball.lean` 的 SHA256 为 `43ff950597de486b444c63cbb8a605ae063601ef475d72806429f0ec8ea91429`，133861 字节，相邻收据记录真实终态。已成功归一化基底的完整字节前缀保留，没有新增 import、依赖版本或构建闭包。

该原模型与已有配对、正时间 null 作用、矩阵及满射接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确 Lean 保持本地临时证据，远端 required CI 仅验证本 Library 说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。下一源码桥是从同一实际矩阵恢复水平仿射／相似分解，再消费原自由作用及离散性进入单位与非单位缩放分类；实际薄部尖点和轴管、有限尖点与紧核心、一般原流形的原度量覆盖及完整 Mostow–Prasad 继续未完成。两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向范围继续保留。


## 同一原无穷远稳定子的水平仿射评价、实际相似比与单位缩放平面等距双射

对同一个原 H³ 等距变换 `e`，仅假设其实际原 null 边界作用固定 `t:=nullFramePoint 3`。令 `A=actionMatrix e` 和前批真实正数 `λ=infinityScale e`，实际定义复平面映射 `Fₑ(z)` 的实部为 `λ(A₁₀+A₁₁ Re z+A₁₂ Im z)`，虚部为 `λ(A₂₀+A₂₁ Re z+A₂₂ Im z)`，证明每个原点 `p` 的同一原 `e(p)` 的水平坐标恰等于 `Fₑ` 作用于原 `p` 的水平坐标。没有输入水平映射表示、仿射评价、正交矩阵或另一平面作用。

原射线公式 `At=λt` 实际给出 `A₁₀+A₁₃=0` 和 `A₂₀+A₂₃=0`；原高度律和同一个原矩阵的乘向量公式消去所有高度分母及二次坐标项，得到上述对全部原高度成立的评价。原全向量配对保持再分别应用于实际 `t` 和两个标准横向基向量，推出 `A₀₁=A₃₁`、`A₀₂=A₃₂`；同一配对作用于横向基向量自身及彼此，给出两列平方和为一及其交叉乘积和为零。故从这个同一个实际 `Fₑ` 的复数范数平方计算推出 `‖Fₑ(z)−Fₑ(w)‖=λ‖z−w‖`，并给出同一个原欧氏距离的精确缩放，没有可定向前提。

单位缩放分支 `λ=1` 是真实消费者：实际距离等式给出 `Fₑ` 的等距性；对任意目标水平坐标 `z`，原 `e` 的满射性提供一个映到原 `coordinatePoint z 1` 的实际原点，前述全部高度评价由此证明同一个 `Fₑ` 满射。通过真实 `Equiv.ofBijective` 构造实际 `R : ℂ ≃ᵢ ℂ`，并保留 `R(p水平坐标)=e(p)水平坐标` 对全部原点的评价关系。反向原等距变换包含在内，未声称这些平面等距变换全部是平移。

四个具名目标经缓存保护入口第三轮真实编译成功，host `55246` exit0，零错误、零警告，无 `sorryAx`，各具名公理闭包仅含 `propext, Classical.choice, Quot.sound`。两轮完整失败源和日志整体保留排除：首轮六处高度分母、复数投影名称及平方化简错误与四项未使用 simp 参数，第二轮两处公共原高度分母消去错误；均按实际诊断修复，没有关闭 linter 或接纳失败批的局部成功。协作方实施、调用方只读复核同一原矩阵的行列关系、实际范数正根和原满射构造，没有新增 SSHX 共识。源码 `.lake/mostow-h3-infinity-horizontal.lean` 的 SHA256 为 `b15a0078aeb0121122e2ddf830d22cb0d6aec39278928af42ab5d11bc1c57efc`，142264 字节，相邻收据记录真实终态。已成功高度源码的完整字节前缀保留，imports、版本及构建闭包未改。

后续先库后证已定位钉版根命名空间的 `linear_isometry_complex` 和 `IsometryEquiv.toRealLinearIsometryEquiv`／`toRealAffineIsometryEquiv`；对应 olean 均实际在位。它们可消费本批真实单位缩放平面等距双射，不需重证旋转／反射分类或仿射化。本批没有新增这些 import 或声称已经得到群表示、平移核及指数界。该原模型与配对、坐标、范数及双射接口的消费按 §3.2 判 `proof_shape: bind-only`、`admission_basis: none`；精确 Lean 保持本地临时证据，远端 required CI 仅验证本 Library 说明，不新增绑定 Lean 库声明、Describe、登记或冻结，不改预算、工具或判官。原单位自由作用的平移核、非单位共同中心与轴、薄部尖点和轴管、有限尖点与紧核心、一般原流形原度量覆盖及完整 Mostow–Prasad 继续未完成；两侧原度量、同一个给定 `h` 与完整 `d`、独立宇宙、非紧有限体积尖点及非可定向范围继续保留。


### 原单位缩放自由群的正规有限指数平移核

对任意宇宙的原群 `G`、同一个原表示 `ρ : G →* (H3 ≃ᵢ H3)`，假设原作用逐点自由，且每个原 `ρ(g)` 固定实际无穷远点 `nullFramePoint 3`、满足 `infinityScale (ρ(g)) = 1`。实际构造子群 `H ≤ G`，证明 `H.Normal`、`H.FiniteIndex`、`H.index ≤ 2`，并构造同一个偏移函数 `u : H → ℂ`，使全部 `h : H` 满足原等距映射等式 `ρ(h) = horizontalTranslation (u(h))`。有限指数性质独立证明，排除无限指数在自然数索引中记为零所造成的漏洞；没有可定向假设。

构造消费上述全部原点水平评价与原高度律，得到同一作用的真实平面群表示 `r : G →* (ℂ ≃ᵢ ℂ)`；平面固定点在原高度一的点上提升为原固定点，因此消费同一个原自由性。钉版 Mazur–Ulam 接口给出真实线性表示 `Q(g)(z) = r(g)(z) − r(g)(0)`。钉版根命名空间的 `linear_isometry_complex` 分类同一个 `Q(g)`；非单位旋转的实际仿射中心 `r(g)(0)/(1−a)` 被原自由性排除。两个反射的积是旋转，因此全部非单位线性像相同；通过实际单射 `Q.range → Bool` 得到有限线性像和基数至多二。取 `H = Q.ker`，消费现有 `Subgroup.finiteIndex_ker` 与 `Subgroup.index_ker` 得到所需正规性、真正有限指数及指数界。核中原水平评价与原高度律最后恢复原 `horizontalTranslation` 的全部点评价，进而得到原等距映射等式。

四个具名目标的精确临时 Lean 已真实编译通过，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-unit-infinity-translation-kernel.lean` 为 151347 字节，SHA256 `ce1701e3e0a94e240276227372957deab8a9f8b50fa10acd40f2e7b978a667b8`。复用两个已有热缓存钉版 import：`Mathlib.Analysis.Normed.Affine.MazurUlam`、`Mathlib.Analysis.Complex.Isometry`；前述成功水平源码的完整 142264 字节连续块位于这两个 import 后的偏移 89，逐字保持。没有新增依赖闭包构建或版本变更。

该现有原模型及钉版分类接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据；远端 required CI 验证说明，尚无新增绑定 Lean 声明或完整官方验收。上述结果要求全部群元素单位缩放，未证明一般小位移群满足此条件。非单位共同中心与轴、离散平移群与实际尖点、有限体积薄部分解、原流形覆盖及同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 仍未完成。


### 原非单位缩放的唯一中心与交换者共同测地轴

对同一个原 `e : H3 ≃ᵢ H3`，假设它固定实际无穷远点且实际正缩放 `λ = infinityScale e ≠ 1`，内部构造唯一水平坐标 `z : ℂ` 满足同一个 `infinityHorizontalMap e z = z`。当 `λ < 1` 时，原水平距离等式构造实际压缩映射，消费钉版 Banach 不动点接口；当 `λ > 1` 时，先证明原逆等距变换稳定同一点及 `λ(e) λ(e⁻¹) = 1`，在实际原逆水平映射上构造中心，再由原水平复合与逆关系恢复同一个原 `e` 的存在唯一性。没有预设中心或可定向性。

实际构造 `verticalAxisLine z t = coordinatePoint z (exp t)`，识别为原 `horizontalTranslation z` 作用于已有原 `geodesicLine`。原距离律证明它是整个实直线到原 `H3` 的等距映射；原正高度的对数与坐标重构证明其像恰为所有水平坐标等于 `z` 的原点，因此得到完整原测地轴。对任意原 `f : H3 ≃ᵢ H3`，若它也稳定同一个无穷远点且与原 `e` 交换，原水平复合律和中心唯一性推出 `infinityHorizontalMap f z = z`。对每个实际 `s > 0`，证明同一个原 `f(z,s) = (z, infinityScale f · s)`；再用实际原逆 `f⁻¹` 证明整个原轴的集合像等于自身，未把正向包含冒充集合相等。本批无需自由性、离散性或方向假设。

四个具名目标的精确临时 Lean 已真实编译通过，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-nonunit-common-axis.lean` 为 160707 字节，SHA256 `1d6a8fcd1359f057fd32df8b3e3729bb18b7dcb663950de79c7634e2798c0c38`。仅增加已有热缓存钉版 `Mathlib.Topology.MetricSpace.Contracting` import；成功平移核源码完整 151347 字节连续块在新 import 后偏移 48 逐字保留，无新增依赖闭包构建。

该原模型与现有压缩映射、测地线及坐标接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 保持本地临时证据，远端 required CI 验证说明。尚未证明一般群所有元素与本批原 `e` 交换，亦未得到离散轴群循环性、原轴管商或有限体积薄部分解；同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 及官方验收继续未完成。


### 原幂零自由群的共同轴与单射缩放字符

保留任意宇宙的同一个原群 `G`、真实 `[Group.IsNilpotent G]`、原表示 `ρ : G →* (H3 ≃ᵢ H3)`、同一个原逐点自由性，以及全部原群元素稳定实际无穷远点的条件。若存在一个原群元素满足实际 `infinityScale (ρ(g)) ≠ 1`，则内部构造一个水平坐标 `z`，使全部原 `ρ(G)` 保持同一个完整原测地轴。保留每个原群元素对全部正高度点的实际作用 `ρ(g)(z,s) = (z, infinityScale (ρ(g)) · s)`，以及整个原轴集合像等于自身，没有额外提供全群交换或共同轴前提。

实际非单位元素先推出原 `G` 非平凡；现有 `Group.IsNilpotent.center_ne_bot` 提供真实非平凡中心元素 `c`。由于同一个原 `ρ(c)` 与原非单位元素交换，前述共同轴消费者适用。若原 `ρ(c)` 的缩放等于一，其对该轴高度一的实际原点作用就是固定点，原自由性迫使 `c = 1`，与所取中心元素矛盾。因此同一个原 `ρ(c)` 是非单位缩放，对它再次消费唯一中心与交换者共同轴；中心性把该实际同轴结论推广到全部原 `ρ(G)`。

原稳定缩放的实际乘法律和单位元律构造真实 `infinityScaleCharacter : G →* ℝ`（实数乘法幺半群），并保留全部值严格正。其核中元素固定实际共同轴高度一的原点，因此同一个原自由性给出核平凡；现有群到幺半群的 `injective_iff_map_eq_one` 得到实际字符单射。实数乘法交换性与这个真实单射最后推出原 `g * h = h * g`，未把交换性作为前提。

五个具名目标的精确临时 Lean 已真实编译通过，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-nilpotent-common-axis.lean` 为 165186 字节，SHA256 `aacd20386d782dfcbb79cfc0749112e51352ed8e8b66f5ab29b7bc276333db66`；前述成功非单位轴源码为 offset0 完整字节前缀，未新增 import、依赖构建或版本变更。

该已有幂零中心、原轴与缩放接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 保持本地临时证据，远端 required CI 验证说明。结论目前要求原群本身幂零及已归一化稳定实际无穷远点；尚未完成一般虚幂零全群分类、离散轴群循环性与真实轴管商、尖点平移格子与有限体积薄部分解，亦未完成原流形覆盖、同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 或官方验收。


### 原虚幂零非单位分支的全群同轴分类

进一步只要求同一个任意宇宙原群 `G` 存在真正有限指数子群 `H`，且 `H` 本身幂零；保留同一个原 `ρ`、全部原群元素逐点自由、稳定实际无穷远点，以及至少一个原非单位缩放元素。证明原全群的实际 `infinityScaleCharacter` 单射、全部原群元素交换，并内部构造全 `ρ(G)` 共同的完整原测地轴，保留每个原群元素对全部正高度点的实际缩放评价及整个原轴像等于自身。不要求 `H` 正规或 `G` 幂零。

真正 `H.FiniteIndex` 提供任意原元素的正幂落在 `H`。将同一个原非单位元素取正幂，并消费原缩放正性与实数正幂单射，得到 `H` 中的实际非单位元素，因此上述幂零字符单射可用于原限制表示。若某个全群原元素 `g` 缩放等于一，其落在 `H` 的正幂仍缩放为一；`H` 的真实字符单射迫使同一个原 `g` 的该正幂等于一。既有原有限阶等距变换固定点定理构造原 `ρ(g)` 的实际固定点，原自由性最终迫使 `g = 1`。因此全群字符也单射，实数乘法交换性得到原全群交换性；最后对原非单位元素消费已验交换者共同轴，得到全部原群元素的真实同轴结论。无额外无挠、正规核或预设轴前提。

三个具名目标的精确临时 Lean 首轮真实编译通过，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-virtually-nilpotent-common-axis.lean` 为 169830 字节，SHA256 `5c4d17b63da957f9d8b5b9ee21b8171a6229826287ca518ed533108e355768ec`；前述成功幂零源码完整 offset0 字节前缀保留，没有新增 import 或依赖构建。

该已有有限指数正幂、原有限阶固定点及原缩放轴接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 保持本地临时证据，远端 required CI 验证说明。尚未消费原作用离散性以得到循环轴群及真实轴管商，亦未完成单位缩放尖点的平移格子、有限体积薄部分解、原流形覆盖或同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad；完整官方验收仍未完成。


### 原对数字符、实际轴位移与离散轴群循环性

由同一个原表示的实际正缩放字符构造 `infinityLogScaleCharacter : Additive G →+ ℝ`，在前述自由、虚幂零、稳定实际无穷远点及存在非单位缩放元素的条件下，证明同一个对数字符单射。对内部构造的同一完整原轴，保留全部原群元素和全部实参数的实际评价 `ρ(g)(verticalAxisLine z t) = verticalAxisLine z (log(infinityScale (ρ(g))) + t)`；原轴的等距性给出实际位移距离恰为 `|log(infinityScale (ρ(g)))|`，无需方向假设。

循环性进一步消费显式绑定同一原 `ρ` 的轨道间隔条件：每个原 `p` 存在 `r > 0`，全部 `g ≠ 1` 满足 `r ≤ dist p (ρ(g)(p))`。把这个条件应用于同一内部轴点，得到实际对数字符像与 `Ioo 0 r` 不交；钉版 `AddSubgroup.cyclic_of_isolated_zero` 构造该像的代数生成元。通过真实字符像的原像和字符单射，得到原 `generator : G`，使每个原 `g` 都是该元素的某个整数幂。这里 `AddSubgroup.closure` 是代数生成的子群，没有将它解释成拓扑闭包。原 `H.FiniteIndex`、`H` 幂零、同一个自由作用与原表示均保留，未预设轴、生成元或群循环性。

六个具名目标的精确临时 Lean 已完整编译通过，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-axis-log-discrete-cyclic.lean` 为 176980 字节，SHA256 `aece6b0ab135644aeb8487a459e4e0154663969d6c9aca732c2ee4ee69a536e4`。仅复用已有热缓存钉版 `Mathlib.GroupTheory.Archimedean` import；此前成功虚幂零源码的完整 169830 字节连续块在该新 header 后偏移 39 保留，没有新增依赖闭包构建。

该原轴、实对数及既有子群循环分类接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批没有从 `ProperSpace H3` 推断原作用离散，亦未构造一般原流形的覆盖及 deck 作用来提供所需间隔。真实轴管商、单位缩放尖点平移格子与有限体积薄部分解，以及同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 同一原表示的 properly discontinuous 性质内部推出间隔与循环性

复用现有 `D5/S3/Geometry/MostowPrasadCovering.lean` 的 `representationMulAction ρ` 和 `ProperlyDiscontinuousRepresentation ρ`，把局部作用逐字绑定为原 `ρ(g)(p)`。同一个原表示的紧集像交有限性构造该作用的 `ProperlyDiscontinuousSMul`，原等距性提供逐元素连续性。既有邻域分离接口和实际原度量球给出每个原点的真实正半径；若非单位原元素的实际位移小于该半径，原像交中的同一点强迫该元素固定原点，再由原自由性推出其为单位元。因而上述原轨道间隔由原自由性与同一 `ρ` 的 properly discontinuous 性质内部推出，无需另供间隔前提。

将这个内部间隔实际代入已编译的原对数字符消费者，在原全群存在真正有限指数幂零子群、稳定实际无穷远点及具有非单位缩放元素的条件下，得到同一个原 `G` 的真实生成元，其整数幂覆盖全部原群。没有用 `ProperSpace H3` 代替作用的 properly discontinuous 性质，也没有换用一个与 `ρ` 无关的作用实例。

两个具名目标的完整精确临时 Lean 首轮真实编译通过，host `46417` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-proper-discrete-cyclic.lean` 为 179235 字节，SHA256 `6889650df9fc589a7944ad67c22ccf6d07f85e96e7522bfc543dcaab0d04eecc`。仅新增已有热缓存 canonical covering import；上一成功 176980 字节源码在 43 字节 header 后完整保留，没有新增依赖闭包构建或版本变更。

该既有原作用、邻域分离及已验循环性接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 保持本地临时证据，远端 required CI 验证说明。这里仍明确消费同一原表示的 properly discontinuous 前提；一般原流形原度量覆盖与完整 deck 作用尚未内部构造来提供它。未归一化原表示的统一分类、真实轴管商、尖点平移格子与有限体积薄部分解，以及同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 同一原表示限制与实际环境等距共轭保持自由性和 properly discontinuous 性质

对原 `ρ : G →* (H3 ≃ᵢ H3)` 构造真实共轭同态 `g ↦ e * ρ(g) * e⁻¹`，其原点评价逐字为 `e(ρ(g)(e.symm p))`。原自由性及 canonical `ProperlyDiscontinuousRepresentation ρ` 分别传递到同一原表示的任意实际子群限制和这个实际共轭表示，未输入新的自由性、proper 性质或替代作用。

子群限制的自由性通过 subtype 单射回到原元素；proper 性质通过同一紧集交点有限集合在 `Subtype.val` 下的单射原像得到。共轭作用的固定点通过实际 `e.symm` 拉回原固定点；对紧集 `K,L`，同一个 `e.symm` 的实际像仍紧，每个同一原元素 `g` 的共轭交点拉回为 `ρ(g)` 在这两个原紧像中的交点。因此共轭交点元素集合包含于一个由原 proper 性质得到的有限集合。原 H³ 度量及全原群元素均保留，包含反向等距变换。

五个具名构造与保持目标的完整精确临时 Lean 首轮真实编译通过，host `82888` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-representation-preservation.lean` 为 181958 字节，SHA256 `5c2dc12c9c23e21bbe39cda4fd97631b9f6b20333b21a2c8ec14dd0923408022`；前述成功 proper 源码为完整 offset0 字节前缀，未新增 import 或依赖构建。协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原同态、subtype 原像、紧像及固定点接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批闭合下一步实际共同边界归一化所需的性质传递，尚未组装未归一化原群分类；一般原流形覆盖供给 proper 性质、真实尖点和轴管商、有限体积薄部分解及完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 未归一化原自由 proper 虚幂零表示的内部 elementary 分类

统一消费者只输入任意宇宙的同一个原 `ρ : G →* (H3 ≃ᵢ H3)`、原自由性、canonical 同一 `ρ` 的 properly discontinuous 性质及真正有限指数幂零子群 `H≤G`。内部消费实际有限边界轨道与原自由作用周期点构造，得到原全群共同固定的实际 `b : NullSphere`，再内部构造同一个原等距变换 `e` 将它送到实际无穷远点，并保留逆作用将无穷远点送回同一个 `b`。前批保持定理把原自由性与 proper 性质传递给真实 `eρe⁻¹`，全部原群元素的无穷远稳定性也内部推出；没有输入边界点、归一化、轨道间隔、轴或生成元。

在单位缩放分支，内部构造原 `G` 中正规且真正有限指数至多二的子群 `K`，以及实际水平位移 `u : K → ℂ`，逐元素保留 `eρ(h)e⁻¹ = horizontalTranslation (u h)` 和原表示评价 `ρ(h) = e⁻¹ * horizontalTranslation (u h) * e`。在非单位缩放分支，消费归一化后同一原群的自由、proper、有限指数幂零及非单位条件，得到原 `generator : G`，使全部原群元素为其整数幂。包含反向等距变换，不要求 `H` 正规或原 `G` 本身幂零。这里单位分支尚未给出平移像的离散自由整数模、格子秩或商尖点。

完整具名目标的精确临时 Lean 第二轮真实编译通过，host `50945` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-elementary-classification.lean` 为 185261 字节，SHA256 `08436a6ca32a0681416132c1e620a6f0c285d4b8cebc5219350d88211ce2956c`。首轮四项局部 proper 性质隐式紧集推断及级联错误的完整源码、日志保留排除；修复局部声明的完整类型，数学目标未改。前述成功保持源码为完整 offset0 字节前缀，无新增 import、依赖构建或版本变更。协作实施与调用方只读语义复核完成，没有新增 SSHX 共识。

该已证共同点、实际归一化、性质保持及两分支消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批结算的是上述原表示前提下的 elementary 分类；一般原流形的原度量覆盖及完整 deck 作用仍须提供这些前提。真实平移格子、尖点与轴管商、有限体积薄部分解、同一个给定 `h`／完整 `d` 的全局刚性及完整 Mostow–Prasad 官方验收继续未完成。


### 原单位缩放平移核的实际离散整数模与秩至多二

对同一原自由、proper、稳定实际无穷远点且全部缩放为一的表示 `ρ`，内部构造原 `G` 中正规有限指数至多二的实际平移核 `K`。同一个原水平平移映射的单射性和乘法律把原位移函数构造成真实加法同态 `U : Additive K →+ ℂ`；原自由性证明它单射，全部 `h : K` 的原点评价仍为 `ρ(h) = horizontalTranslation (U h)`。无需原群虚幂零或预给平移字符、格子、离散像前提。

实际限制同一个原 `ρ` 到 `K` 并传递原自由与 canonical proper 性质。在原点 `coordinatePoint 0 1` 的实际轨道间隔，以及同一个原高度一坐标映射的连续性，给出该原度量球在实际位移像中的原像恰为 `{0}`。因此真实整数子模 `L := U.range.toIntSubmodule` 是离散的；没有把欧氏离散性或另一个作用间隔作为输入。钉版 `ZLattice.Basic` 中无需满张成前提的离散子模接口给出 `Module.Finite ℤ L` 和 `Module.Free ℤ L`。离散子模的实／整数张成秩等式、实际 `span ℤ L = L` 及 `Complex.basisOneI` 的实维数二，进一步证明 `Module.finrank ℤ L ≤ 2`。未假设或推出满秩二、余紧性、有限体积或实际商尖点。

七个具名构造与目标的完整精确临时 Lean 第二轮真实编译通过，host `41330` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-unit-translation-discrete-module.lean` 为 192890 字节，SHA256 `caa349e0ac84eb8a6c62ffa1e485b50a0f22f4e570803a4534b716a77e6ccfc8`。首轮三项原坐标化简与未导入维数名称的错误源码日志完整保留排除；用实际坐标／高度评价与已导入原复数基修复，未弱化结论。仅新增热缓存钉版 `Mathlib.Algebra.Module.ZLattice.Basic`；前述成功分类源码在 45 字节 header 后完整保留，无新依赖构建或版本变更。协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原平移、作用间隔、坐标连续性及已有离散整数模接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。下一步可把实际离散平移模接回未归一化分类，并处理原尖点和轴管商；一般原流形原度量覆盖、有限体积薄部分解及同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 和官方验收继续未完成。


### 原 horoball 上的实际单位缩放等距作用与商投影覆盖性

对同一个原单位缩放、稳定实际无穷远点的等距表示 `ρ` 及任意真实阈值 `T`，定义实际原子空间 `{p : H3 // T < height p.coordinates}`。其度量逐字继承原 H³ 度量；实际原坐标的连续性给出这个 horoball 开放，现有局部紧接口提供实际子空间的局部紧性。没有换用独立模型或供给另一高度函数。

原正向及逆向高度律在单位缩放条件下内部证明原 `ρ(g)` 及其逆元均保持同一个 horoball。由此构造同一个原群的真实受限等距表示，逐元素保留其 subtype 值等于原 `ρ(g)(p)`，乘法和单位评价也内部验证。受限固定点通过实际 subtype 包含拉回原固定点，因此原自由性传递；实际 subtype 包含将紧集送为原 H³ 紧集，同一 `g` 的受限交点送为原交点，原 canonical proper 性质给出受限交点集合有限。最后复用 `orbitQuotientMk_isCoveringMap`，证明这个实际受限 horoball 的轨道商投影是拓扑覆盖映射。无需虚幂零、平移字符、满秩二、有限体积或预给尖点前提。

七个具名构造与目标的完整精确临时 Lean 第二轮真实编译通过，host `33889` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-unit-horoball-action-covering.lean` 为 198787 字节，SHA256 `87105223e774ae161056af7e107f53f60a45cea669e6a3b39c331fc77233f022`；前述成功单位平移模源码为完整 offset0 字节前缀，无新增 import、依赖构建或版本变更。首轮虽 exit0 但含两项 noop tactic 警告，完整源码日志保留排除；仅删除两项无作用的 `change`，未关闭 linter。协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该实际原子空间、等距表示限制、紧像与 canonical 商覆盖接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。这里覆盖性是上述实际 horoball 的轨道商投影的拓扑结论；尚未构造其商黎曼度量、体积、到原流形尖点的嵌入或完整 deck 群下的 horoball 分离。一般原流形的原度量覆盖、有限体积薄部分解及同一个给定 `h`／完整 `d` 的完整 Mostow–Prasad 和官方验收继续未完成。


### 实际原覆盖与同一表示的纤维保持性内部推出原度量轨道间隔

对任意独立宇宙的实际目标空间 `M`、实际覆盖 `π : H3 → M` 及同一个原等距表示 `ρ : G →* (H3 ≃ᵢ H3)`，只要求原作用逐点自由以及逐元素逐原点的实际纤维保持 `π(ρ(g)(p)) = π(p)`。内部得到每个原点的正数 `r`，使全部非单位原 `g` 的原位移满足 `r ≤ dist p (ρ(g)(p))`，没有另供轨道间隔或 properly discontinuous 性质。

既有覆盖的局部同胚与局部单射接口提供实际 `π` 在原点附近的开放单射邻域，原 H³ 度量球提供真实正半径。若某个原 `ρ(g)(p)` 位于该球中，同一 `π` 的纤维保持与单射性迫使它等于原 `p`，再由原自由性推出 `g=1`。该原间隔实际代入已编译轴群消费者：保留同一个原群、实际无穷远稳定性、真正有限指数幂零子群及存在原非单位缩放元素，内部构造原群整数幂生成元。未将覆盖换成另一作用，也未把原目标空间与原 H³ 合并为一个宇宙。

两个具名目标的完整精确临时 Lean 首轮真实编译通过，host `26940` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-orbit-gap.lean` 为 200772 字节，SHA256 `40cb28b6aa11ce05c9421efe5e99fbcfa8212d9198c0e62d39d82a11144076ca`；此前成功 horoball 源码为完整 offset0 字节前缀，没有新增 import、依赖构建或版本变更。调用方实际编译与同一覆盖／原自由性／原度量语义复核完成，没有新增 SSHX 共识。

该既有原覆盖、局部单射、原度量球及轴循环性消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批消费真正给定的 `π` 及同一表示的纤维保持性；尚未从一般原 `M,N` 的双曲流形假设内部构造其原度量普适覆盖、完整 deck 表示或这些数据。间隔到原 compact-pair properly discontinuous 性质的证明仍在推进；原商度量、体积、尖点分离、完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 单点原轨道间隔推出紧集交点有限性与实际原覆盖作用的 proper 性质

对同一个原等距表示 `ρ`，仅需在一个原点 `p₀` 给出正数 `r`，使非单位元素的原位移至少为 `r`。原乘法律与同一个原等距变换将 `g⁻¹h` 的位移传递为两个轨道点的距离，因此不同原群元素的 `p₀` 轨道点彼此距离至少为 `r`。原 H³ 的紧闭球和钉版 totally bounded 接口提供有限个半径 `r/3` 的覆盖球；给有界位移原元素选择所属球心，相同球心将迫使两轨道点距离小于 `2r/3`，与原间隔矛盾。因此对每个实际实数界 `R`，原集合 `{g | dist p₀ (ρ(g)(p₀)) ≤ R}` 有限。未给出任何群元素集合有限性前提。

两个实际原紧集 `K,L` 在同一个 `p₀` 的原距离分别有界。如果同一原 `ρ(g)` 将 `K` 的某点送入 `L`，原三角不等式和原等距性便给出该同一 `g` 在 `p₀` 的位移至多为两界之和。原紧集交点元素集合包含于刚证明有限的原位移集合，故得到 canonical `ProperlyDiscontinuousRepresentation ρ`。这没有仅凭 `ProperSpace H3` 推断作用 proper；正轨道间隔与同一原等距作用均实际参与证明。

最后消费前批真实覆盖、同一表示纤维保持及原自由性所内部构造的原间隔，得到实际覆盖作用的 canonical proper 性质。保持任意原群宇宙与独立目标空间宇宙；无需另供 proper 性质或轨道间隔，也不要求覆盖纤维轨道传递性。一般原流形原度量覆盖的构造仍须另行完成。

三个具名目标的完整精确临时 Lean 第二轮真实编译通过，host `6444` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-proper-action.lean` 为 204716 字节，SHA256 `b0af58ed2b9a0f074937f3adf7eb2916f7aa57781383f2aca95289be93fee627`；此前成功原覆盖间隔源码为完整 offset0 字节前缀，无新增 import、依赖构建或版本变更。首轮两处接口名称和存在量词展开错误的完整源码日志保留排除；使用实际 root `isCompact_closedBall` 与 `exists_prop` 修复，没有弱化目标。协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原等距乘法、紧闭球、有限球覆盖与紧集距离界消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批消除了实际覆盖作用另供 proper 性质的前提，未从一般原 `M,N` 双曲流形数据内部构造该覆盖。原商度量、体积、尖点分离、完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 实际原覆盖内部提供 proper 性质后的未归一化原群分类

统一消费者只输入任意宇宙的同一原等距表示 `ρ`、原自由性、独立目标宇宙的实际覆盖 `π : H3 → M`、同一表示逐点纤维保持，以及原群中真正有限指数幂零子群 `H`。先内部消费前批原覆盖间隔与紧集交点有限性，得到 canonical 同一 `ρ` 的 proper 性质；再消费此前共同边界点与真实原等距共轭分类。因此实际共同边界点、正逆归一化、归一化后的自由性与 proper 性质均内部提供，无需另给 proper 性质、间隔、边界点、归一化或生成元。

单位缩放分支返回原群中正规有限指数至多二的实际平移核 `K`、单射实际加法位移字符 `U : Additive K →+ ℂ`，以及逐元素的真实共轭平移等式和原表示等式。实际 `U.range.toIntSubmodule` 是离散、有限、自由的整数模，整数秩至多二；同时对任意实际高度阈值，归一化后的同一表示在原 horoball 子空间的轨道商投影是拓扑覆盖。非单位缩放分支返回同一个原 `G` 的整数幂生成元。保留反向等距变换，不要求原 `H` 正规，也未推出秩恰二、余紧性、有限体积或尖点嵌入。

完整具名目标 `virtuallyNilpotentFreeOriginalCoveringRepresentation_elementaryModuleClassification` 的精确临时 Lean 第四次实际编译 exit0，host `65796`；完整日志零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-elementary-module.lean` 为 208343 字节，SHA256 `f6e1b487e09a366471923df202b8b6290e196a87c74dec657acfef257bf1cd94`；前批成功 proper 源码为完整 offset0 前缀，无新增 import、依赖构建或版本变更。前两次命名空间及局部 proper 类型推断失败的完整源码日志保留排除；第三次日志虽无诊断，但恢复后进程句柄失效，实际退出码无法读取，故不作为成功证据。第四次同时读取实际退出码并持久化，源码未改。协作实施与调用方只读语义复核完成，没有新增 SSHX 共识。

该原覆盖、既有分类、真实平移模和 horoball 覆盖消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批组装实际原覆盖前提下的统一分类，尚未从一般原流形假设构造覆盖或完整 deck 表示。原商度量与体积的匹配、尖点分离、有限体积薄部分解、完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 实际原覆盖作用内部推出同一原群可数

对同一个任意宇宙的原等距表示 `ρ`，仅要求在一个原点有正轨道间隔，前批证明使每个实际自然数界的原位移元素集合有限。钉版可数并接口使这些有限集合的自然数并可数；每个原群元素的实际位移是实数，`exists_nat_ge` 提供包含它的自然数界。因此全部原群元素包含于这个可数并，得到真实 `Countable G`，没有可数性、有限生成或虚幂零输入，也没有只证明轨道点集合可数后遗漏原元素的单射性。

实际原覆盖消费者从原自由性、真正给定的覆盖和同一表示逐点纤维保持内部提供间隔，故同一原 `G` 可数。目标空间与原群保持独立宇宙，不要求覆盖满射或纤维轨道传递性。这里仍消费实际给定覆盖，未从一般原流形数据构造它；群可数也不提供有限体积或完整刚性。

两个具名目标 `originalRepresentation_countableGroup_of_pointGap` 与 `freeOriginalCoveringRepresentation_countableGroup` 的完整精确临时 Lean 首轮真实编译通过，host `70182` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-countable-group.lean` 为 209739 字节，SHA256 `a7f48c2cde61982babb04b0fba333110d126a67912e54263124e0c46a462e9cd`；前批成功原覆盖分类源码为完整 offset0 前缀，无新增 import、依赖构建或版本变更。实际退出码已读取并持久化，协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原有界位移有限性、可数并和自然数上界接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批可消除后续原覆盖作用消费者的外供群可数性前提；原流形度量覆盖构造、原商度量与体积的匹配、尖点分离、完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 同一实际覆盖的原轨道商到原底空间同胚

对任意独立宇宙的实际底空间 `M`、同一原等距表示 `ρ` 与真正给定的实际覆盖 `π : H3 → M`，另明确要求 `π` 满射、同一表示逐点纤维保持，以及同一原群在每条实际纤维上传递：若 `π p = π q`，存在原 `g : G` 使 `ρ(g)(p)=q`。内部构造真实 `e : OrbitQuotient ρ ≃ₜ M`，逐原点满足 `e (orbitQuotientMk ρ p) = π p`。没有把纤维保持偷换成纤维传递，没有假设这个同胚，也不需要原自由性或 proper 性质。

同一 `π` 的 quotient lift 借助纤维保持良定义；纤维传递使其单射，实际满射性使其满射。原覆盖连续性给出正向连续性，实际满射覆盖的 quotient-map 接口和精确的逆复合等式 `e.symm ∘ π = orbitQuotientMk ρ` 给出逆向连续性。因此不是仅构造集合等价，也没有换用另一个覆盖或另一个原作用。这里得到拓扑同胚，未宣称它保持原 `M` 度量、黎曼结构或体积；构造一般原流形的实际覆盖及完整 deck 纤维传递性仍须独立完成。

具名目标 `originalCoveringRepresentation_orbitQuotientHomeomorph` 的完整精确临时 Lean 首轮真实编译通过，host `80961` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-quotient-homeomorph.lean` 为 211714 字节，SHA256 `ba0fd7d8216b3c887978f83a7f3a0ddd949978c54e92c403e743c581c883c30d`；前批成功原群可数源码为完整 offset0 前缀，无新增 import、依赖构建或版本变更。实际退出码已读取并持久化，协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该实际 quotient lift、覆盖连续性和 quotient-map 接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。既有 canonical `IsometricOrbitMetric.orbitMetricSpace` 和 `orbitProperSpace` 可提供实际轨道商度量及其 proper 性质，不能据此直接认定原底空间度量匹配。本批不完成原商度量与体积的匹配、尖点分离、完整给定 `h`／完整 `d` 的 Mostow–Prasad 或官方验收。


### 实际原覆盖作用的轨道商投影在原正半径球上保距

对同一个原等距表示 `ρ` 和原点 `p`，真实正轨道间隔 `r` 使每个非单位原元素在 `p` 的位移至少为 `r`。若原 `x,y` 均在实际球 `ball p (r/4)`，三角不等式和同一 `ρ(g)` 的等距性给出非单位平移的 `dist x (ρ(g)(y))` 至少为 `dist x y`。单位元素给出原距离本身；canonical `IsometricOrbitMetric.orbitDistance` 的实际轨道距离下确界因此逐字等于原 `dist x y`。没有另供局部保距结论，没有重证或替换 canonical 商度量。

实际原覆盖消费者仅需原自由性、真正给定的覆盖 `π` 和同一表示的纤维保持，内部提供每个原点的正间隔及 canonical proper 性质。在由这个实际 proper 证明给出的 `orbitMetricSpace ρ` 中，实际 `orbitQuotientMk ρ` 限制到每个原点附近的某个正半径球是 `Isometry`。原群和目标空间保持独立宇宙，不要求有限生成、虚幂零、满射或纤维轨道传递性。商度量保持原 quotient topology；该结论尚未与原底空间 `M` 的实际度量相匹配。

两个具名目标 `originalRepresentation_orbitDistance_eq_dist_of_pointGap` 与 `freeOriginalCoveringRepresentation_locallyIsometricOrbitProjection` 的完整精确临时 Lean 第二轮真实编译通过，host `67218` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-original-cover-locally-isometric-orbit.lean` 为 214278 字节，SHA256 `d5f05f64042315b6f625f7dba38a7ba1ab885324bbc74133d9c7b4765f92b56a`；仅新增 43 字节的热缓存 canonical `IsometricOrbitMetric` import，其后完整保留前批成功原商同胚源码，无新依赖构建或版本变更。首轮实际 exit0 但含一条局部 `letI` 风格警告，完整源码日志保留排除；仅改证明内部绑定为 `let`，未关闭 linter。第二轮实际退出码已读取并持久化，协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原三角估计、已有轨道距离下确界与实际 canonical 商度量消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。后续原度量桥仍须从一般原流形条件内部构造覆盖及 H³ 等距识别；原商到 `M` 同胚的保距性、体积匹配、尖点分离、完整给定 `h`／完整 `d` 的 Mostow–Prasad 和官方验收继续未完成。


### 原 H³ 距离的实际坐标方向右侧度量斜率

在同一个原 `H3` 和同一个原 `dist` 中，对任意原点 `p`、实际欧氏 `Ambient ℂ = WithLp 2 (ℂ × ℝ)` 方向 `v`，构造坐标扰动 `p.coordinates + s • v`。原高度正性与连续性内部保证它在零的邻域仍属于实际正半空间；域外返回原 `p` 仅使函数全域定义，不影响该邻域中的真实扰动。随后证明当实际 `s → 0+` 时，`dist (nativeCoordinatePerturbation p v s) p / s` 收敛到 `‖v‖ / height p.coordinates`。没有换用另一个距离，也未将距离函数在零的普通可微性作为输入或结论。

原距离的实际 `2 * arsinh` 公式将正步长扰动距离写为 `2 * arsinh (s * K(s))`，其中 `K(s)` 趋于 `‖v‖ / (2 * height p)`。钉版 `arsinh` 的导数与补洞斜率连续性给出 `arsinh(z)/z → 1`；完整保留零方向分支，避免要求 `v ≠ 0`。显式坐标消费者使用实际 `WithLp` 的 L² 距离接口，将方向范数识别为 `sqrt(‖a‖²+b²)`，得到右侧极限 `sqrt(‖a‖²+b²) / height p`。没有把默认乘积的 max 范数误当作欧氏平方和。

五个具名构造与目标的完整精确临时 Lean 第四轮真实编译通过，host `40015` exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。源码 `.lake/mostow-h3-native-coordinate-infinitesimal-metric.lean` 为 219775 字节，SHA256 `b3845c4fc791a948e7b8397cf24950838c196161ba09ed4b2ad82219b38b350d`；仅新增 45 字节热缓存 `Mathlib.Analysis.Calculus.Deriv.Slope` import，其后完整保留前批成功局部商保距源码，无新依赖构建或版本变更。前两轮实际类型与滤子推断失败的源码日志保留排除；第三轮实际 exit0 但含三条冗余 tactic 警告，也保留排除。只补明确类型并去除冗余，未弱化右侧极限、原距离或零方向分支，未关闭 linter。最终实际退出码已读取并持久化，协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该实际原距离公式、欧氏范数、导数斜率和滤子连续性接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批识别的是原坐标直线的局部右侧度量速度，尚未构造实际黎曼度量、其曲率或与原距离的完整内蕴等式。固定外部库的 scalar derivative bound 到内蕴距离 Lipschitz 接口可用于后续实际 `log height` 下界；仍须提供同一实际模型的切向度量和导数界。完整原流形覆盖、原度量／体积匹配、尖点分离、给定 `h`／完整 `d` 的 Mostow–Prasad 与官方验收继续未完成。


### 原 Lorentz 坐标嵌入的真实导数、切向正定配对与原等距作用变换律

对同一个实际原点 `p` 和实际方向 `(a,b) : ℂ × ℝ`，显式构造四个原 Lorentz 坐标的方向导数 `nativeLorentzCoordinateTangent p a b`。它不是只有形式上的候选向量：原正高度邻域内实际坐标扰动的平方范数和四个有理坐标函数的导数，逐分量组合为真实 `HasDerivAt`，其函数逐字是原 `v (nativeCoordinatePerturbation p (WithLp.toLp 2 (a,b)) s)`。

两个实际方向 `(a,b),(c,d)` 的原 Lorentz 配对满足精确恒等式：负配对等于 `(a.re*c.re + a.im*c.im + b*d) / height(p)^2`。同一导数向量与原 `v(p)` 正交；其负自配对是 `(‖a‖²+b²) / height(p)^2`，因此只要实际方向非零就严格为正。原高度正性和实际欧氏平方和均参与证明，没有给出正定性前提，没有把默认 max 范数当作欧氏范数。

对任意同一个原 `e : H3 ≃ᵢ H3`，同一原扰动经实际 `e` 再经原 `v` 的函数，其真实导数是 `actionMatrix e` 乘以上述真实导数向量。这里消费已验的逐原点 `action_formula`，将同一个实际矩阵视为连续线性映射并使用导数链式法则；没有另供 `e` 的光滑性、另一个作用或替代度量。该结论仍是原 Lorentz 坐标中的曲线导数变换律，尚未单独构造全局平滑切丛或证明内蕴距离相等。

三个连贯临时源码增量都真实编译 exit0，零错误、零警告，无 `sorryAx`，公理闭包仅含 `propext, Classical.choice, Quot.sound`。实际导数与双线性配对源码 `.lake/mostow-h3-native-lorentz-coordinate-tangent.lean` 为 225174 字节，SHA256 `522fb8d31093c04b58ccf0b715255cdffad30775a158640a0c4bc8d144257b0f`，仅在完整前批成功源码前增加 44 字节热缓存 `Deriv.Prod` import。正交及正定性源码 `.lake/mostow-h3-native-lorentz-tangent-positive.lean` 为 227021 字节，SHA256 `9aa02734e9f5e46da13327aefd6a2af2c6682c718b644565752258d07637a721`，首轮 host `21797` 通过。原等距导数变换的完整累计源码 `.lake/mostow-h3-native-isometry-lorentz-derivative.lean` 为 227805 字节，SHA256 `11ee5c7bd6437e34fb48d31e0a37e892ad5808cf06ec9202fabeb07bd97f1738`，第二轮真实编译通过；后两批保持各自成功前批为完整 offset0 前缀，无新 import。所有失败或含警告轮次的完整源码日志保留排除，未降低陈述或关闭 linter。实际退出码和完整公理输出保留，协作实施与调用方只读复核完成，没有新增 SSHX 共识。

该原有理坐标导数、Lorentz 配对代数和既有线性作用接口消费者按 `proof_shape: bind-only`、`admission_basis: none` 保留本 Library 说明，精确 Lean 为本地临时证据，远端 required CI 验证说明。本批为同一原模型的黎曼度量构造提供真实切向数据；仍须构造实际平滑度量与全局内蕴距离匹配、曲率 −1、原流形覆盖和体积绑定。有限体积格子同构产生边界交比保持的全局推导、完整给定 `h`／完整 `d` 的 Mostow–Prasad 及官方验收继续未完成。


### 原 Lorentz 坐标的实际逆恢复及任意曲线坐标导数（2026-10-06）

本闭合小批接续原等距的 Lorentz 导数变换，仍使用同一原 H3、原 `v` 与原坐标。`nativeLorentz_heightDifference` 给出 `v p 0 - v p 3 = 1 / height p.coordinates`；其非零性由原点的正高度内部推出。实际高度、水平实部、水平虚部依次由 `1/(v₀-v₃)`、`v₁/(v₀-v₃)`、`v₂/(v₀-v₃)` 恢复。

对于任意实际曲线 `Q : ℝ → H3`，若 `v ∘ Q` 在实际参数 `s` 的导数为 `u : Fin 4 → ℝ`，则原高度的导数为 `-(u 0-u 3) * height (Q s).coordinates ^ 2`；原水平实部导数为 `height (Q s).coordinates * u 1 - (Q s).coordinates.1.fst.re * height (Q s).coordinates * (u 0-u 3)`，虚部对应以 `u 2` 和实际虚部替换。三个 `HasDerivAt` 结论用同一个 `Q,s,u`，不额外假设原坐标曲线已有导数；实际分母非零由上述恒等式证明。本批不主张全局光滑度或原内蕴距离兼容已完成。

完整累计临时源码 `.lake/mostow-h3-native-lorentz-coordinate-recovery.lean` 为 232372 字节，SHA256 `148c523af6ae45d9793245275610fb29db0495ffd097430e2170d650dfda6a45`，前批 227805 字节源码为完整 offset0 前缀，无新 import。第三轮真实编译 exit0，零错误、零警告，173 条公理输出仅含 `propext, Classical.choice, Quot.sound`，无 `sorryAx`；完整日志 22695 字节，SHA256 `c106d5f416580419634afc48d620a669fe6446a7beef5d5faa5f0bec31417f0d`。调用方已核对源码、前缀、预登记、日志及真实退出收据的长度和哈希，排除前两轮失败；没有新增 SSHX 共识。

逐声明 `proof_shape: bind-only`、`admission_basis: none`：复用现有 Lorentz 高度配对恒等式、分量导数及除法求导，新增步骤为实际参数绑定与代数规范化。只提交本 Library 复用说明，精确 Lean 与成功/失败证据留在本次临时结果目录；远端 CI 验证本说明，不代表完整 Mostow 验收。全局原光滑度量、原内蕴距离等式、曲率 −1、原流形覆盖/有限体积及同一规定 `h,d` 的完整 Mostow–Prasad 仍未闭合。


### 原等距映射的实际坐标导数及切向配对保持（2026-10-06）

此闭合单元将两个相邻成功批次接成同一原等距切空间作用接口。`nativeLorentzTangentDirection p w` 从原 `v p` 的 Lorentz 正交向量 `w` 明确恢复原 `Ambient ℂ = WithLp 2 (ℂ × ℝ)` 方向；在 `pairing (v p) w = 0` 下，恢复方向的原 Lorentz 坐标切向量等于同一个完整 `w`，未另加切向量实现假设。

对于同一实际 `e : H3 ≃ᵢ H3`、原点 `p` 及任意方向 `(a,b)`，定义 `nativeIsometryCoordinateDirection e p a b` 为在原 `e p` 恢复 `actionMatrix e *ᵥ nativeLorentzCoordinateTangent p a b` 所得的方向。该方向的实际 Lorentz 切向量等于上述矩阵像，正交性由原 `action_formula` 与全向量 `action_preserves_pairing` 内部推出。原 `e` 作用于原坐标扰动后的高度、水平实部、水平虚部，在同一参数零点分别有此方向对应分量的实际 `HasDerivAt`。本批还核验原扰动在零处确为同一 `p`。

两任意方向 `(a,b),(c,d)` 的像满足明确双线性等式：像方向的原坐标欧氏内积除以 `height (e p).coordinates ^ 2`，等于 `(a.re*c.re+a.im*c.im+b*d)/height p.coordinates ^ 2`。这包含不同方向之间的配对保持，既未供给原 `e` 光滑性前提，也未替换原空间距离；结论当前是明确原坐标导数与代数切向形式，尚未当作全局 `mfderiv` 或已构造光滑度量的保持。

切向恢复源码 `.lake/mostow-h3-native-lorentz-tangent-recovery.lean` 为 235989 字节，SHA256 `6316cdc805f3e21535ff483e03a3af7983de62af5e2d5975e50bec20f0c30518`，第三轮真实 exit0、零错误/警告，175 条标准公理闭包输出。原等距坐标导数及双线性配对源码 `.lake/mostow-h3-native-isometry-coordinate-derivative.lean` 为 240434 字节，SHA256 `9a6b255f6fb1547a747d558abc063e2caa50ed493f292e04024734a551896f25`，第二轮真实 exit0、零错误/警告，182 条标准公理闭包输出；成功日志 23884 字节，SHA256 `73cd724fc6887c5de7d46879f36144f12a4bde9c6b13abfd6e62765672ffef46`。两批各保持成功前批完整 offset0 前缀，无新 import；公理仅 `propext, Classical.choice, Quot.sound`，无 `sorryAx`。调用方复核全部源码/前缀/预登记/日志/真实退出收据哈希，失败轮次完整保留排除，没有新增 SSHX 共识。

逐声明 `proof_shape: bind-only`、`admission_basis: none`：现有全向量 Lorentz 保持、原实际曲线坐标求导及实际坐标切向配对供给原子事实，本批为绑定及规范化。只交付此 Library 复用说明，精确 Lean 与证据保留在临时结果目录；远端 CI 验证说明。原全局光滑度量、原全局光滑等距作用与 `mfderiv`、原内蕴距离等式、曲率 −1、原流形覆盖/有限体积和同一规定 `h,d` 的完整 Mostow–Prasad 仍未完成。


### 原 H3 拓扑上的实际光滑坐标图与高度缩放（2026-10-06）

本闭合小批仍使用同一原 `H3`、原 `coordinatesHomeomorph` 和原度量诱导的拓扑。`nativeAmbientEuclideanIsometry` 复用 `Complex.orthonormalBasisOneI.prod (OrthonormalBasis.singleton (Fin 1) ℝ)`，经 `finSumFinEquiv` 重索引取 `.repr`，得到原 `Ambient ℂ = WithLp 2 (ℂ × ℝ)` 到 `EuclideanSpace ℝ (Fin 3)` 的实线性等距；没有将原坐标欧氏范数改成默认乘积最大范数。

原坐标映射及其欧氏三维组合都是实际 `IsOpenEmbedding`：原高度正域的开放性由原连续高度投影证明，组合的是原同胚和上述线性等距。使用原 `rayOrigin` 内部提供 `Nonempty H3`，再复用 `singletonChartedSpace` 与 `isManifold_singleton`，在同一原拓扑上得到实际 `ChartedSpace`、`IsManifold (𝓡 3) ∞ H3`，以及原欧氏坐标映射的全局 `ContMDiff`。这一步未安装新的空间距离或假设原内蕴距离兼容。

`nativeEuclideanHeightCLM` 为原线性等距逆映射后接原 `WithLp.sndL`；其作用于原欧氏坐标时确等于同一 `height p.coordinates`。由实际线性映射和原坐标的光滑性得到原高度全局 C∞。`nativeHeightInverseSquare p = (height p.coordinates ^ 2)⁻¹` 也全局 C∞、处处严格正；实际分母非零和正性由原点的正高度内部推出，未供给额外正性或光滑性前提。

完整累计临时源码 `.lake/mostow-h3-native-euclidean-open-chart.lean` 为 244302 字节，SHA256 `dc8a876210963a0902d75fef3a9e4a87a91cc7510b49434e9e183b772a717d08`；前批 240434 字节成功源码完整保持在 offset199，仅加入具名热缓存 import。第六轮 host `17811` 真实 exit0，零错误/警告，192 条公理闭包仅含 `propext, Classical.choice, Quot.sound`，无 `sorryAx`。成功日志 25101 字节，SHA256 `89ee87b7ba1ae6d686db26b14a8da93e57c4fb46b6c7b5e7de1f5a6292270e56`。调用方已复核全部源、前缀、预登记、日志、真实退出收据哈希及全部公理输出；先前失败或中止轮次完整保留排除。实际修复只处理 scope、具名 smooth multiplication instance 与定义等式包装，没有改陈述、pin 或关闭检查，没有新增 SSHX 共识。

逐声明 `proof_shape: bind-only`、`admission_basis: none`：复用既有实线性等距基、原同胚、开放嵌入单图册及光滑复合/幂/逆函数规则；本批只交付此 Library 复用说明，精确 Lean 与证据保留在临时结果目录，远端 CI 验证说明。实际光滑 `g` 的构造、原全局等距作用光滑性及 `mfderiv`、原内蕴距离等式、曲率 −1、原流形覆盖/有限体积和同一规定 `h,d` 的完整 Mostow–Prasad 仍未完成。


### 原 H3 光滑切丛上的实际黎曼度量

在原 `H3` 的同一拓扑和上述实际欧氏三维单图册上，构造 `nativeRiemannianMetric : Bundle.ContMDiffRiemannianMetric (𝓡 3) ∞ NativeEuclidean3 (fun p : H3 => TangentSpace (𝓡 3) p)`。对任意原点 `p` 和两个实际切向量 `V,W`，其内积精确为 `⟪V,W⟫_ℝ / height p.coordinates ^ 2`；这里的欧氏切向量表示来自该原坐标图。原正高度内部给出对称性和严格正定性，度量的切向单位球正是欧氏空间中以原高度为半径的球，因而满足实际有界性要求。

实际单图册的切向坐标变换、切丛正向及逆向平凡化均为恒等连续线性映射。原高度负二次幂的全局光滑性因此给出上述双线性形式作为切丛截面的全局 C∞，没有把逐点正定形式直接当作光滑度量。同一原欧氏坐标开放嵌入还内部提供 `SecondCountableTopology H3`，无需添加第二可数性假设。

该精确构造及内积公式已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用的是既有单图册、切丛平凡化、欧氏内积和光滑标量乘法接口；本项交付为 Library 复用说明。尚须证明原等距作用的实际 `mfderiv` 保持该度量、其内蕴距离等于原 H3 距离，以及实际曲率 −1。一般原流形的覆盖和体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 及官方验收仍未完成。


### 原 H3 全部等距映射的全局光滑性

对任意同一个原 `e : H3 ≃ᵢ H3`，在原 H3 拓扑上的实际欧氏三维图册中，`nativeIsometry_contMDiff e` 给出 `ContMDiff (𝓡 3) (𝓡 3) ∞ e`。这一量化同样适用于原 `e.symm`，不要求定向性，也不额外假设 `e` 已经光滑；原空间距离及原映射均保留。

原水平坐标的实部、虚部和原高度全局光滑，因此原 Lorentz 嵌入 `v` 的四个实际有理分量全局光滑。已有原作用公式 `v (e p) = actionMatrix e *ᵥ v p` 将同一 `v ∘ e` 识别为一个实际连续线性映射与 `v` 的复合。实际分母 `v (e p) 0 - v (e p) 3` 等于原高度倒数，由原正高度内部保证处处非零；其三个有理恢复公式给出原 `e` 的高度、水平实部和虚部的光滑性。最后由原坐标开放嵌入的实际单图册接口得到 `e` 的全局 C∞，没有把曲线方向导数直接当作全局微分。

该精确原映射结论及所有所用坐标光滑接口已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用既有原线性作用、实际逆坐标恢复和光滑复合／除法／开放嵌入接口；本项交付为 Library 复用说明。实际 `mfderiv` 的方向识别及对上述黎曼度量的保持、原内蕴距离等式、曲率 −1、一般原流形覆盖和体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 及官方验收仍未完成。


### 原等距映射的实际流形微分与黎曼内积保持

对于任意原 `e : H3 ≃ᵢ H3`、原点 `p` 及两个实际切向量 `V,W : TangentSpace (𝓡 3) p`，已核验
`nativeRiemannianMetric.inner (e p) (mfderiv (𝓡 3) (𝓡 3) e p V) (mfderiv (𝓡 3) (𝓡 3) e p W) = nativeRiemannianMetric.inner p V W`。这里使用同一原等距映射、同一原拓扑上的实际光滑图册，以及上述由原高度负二次幂构造的实际黎曼度量；结论适用于任意两向量，也包括逆映射和反定向等距映射。

原欧氏坐标映射就是实际 `extChartAt`，其实际 `mfderiv` 为恒等连续线性映射。原正高度邻域中的坐标扰动曲线具有实际 `HasMFDerivAt`；连续性由原坐标开放嵌入恢复。将已核验的原等距全局光滑性与该曲线、原坐标图复合，微分链式法则和真实曲线导数的唯一性识别出 `mfderiv e p` 对每个原坐标方向的作用，恰为原 Lorentz 作用后的切向恢复方向。原双线性配对保持和原坐标线性等距的内积保持随即给出上述黎曼内积等式；由线性等距的满射性推广至任意实际 `V,W`，无需额外提供微分或内积保持前提。

该精确微分及内积保持结论已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用的是实际图册微分、曲线导数、既有原 Lorentz 作用和双线性配对接口；本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。原 H3 距离与此度量内蕴距离的等式、实际曲率 −1、一般原流形覆盖及体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 原高度的实际微分与对数高度的黎曼导数界

在同一原 H3 光滑图册及上述实际黎曼度量上，`nativeLogHeight p = Real.log (height p.coordinates)` 全局 C∞。原高度的实际流形微分是 `nativeEuclideanHeightCLM`；对任意实际切向量 `V : TangentSpace (𝓡 3) p`，原对数高度的实际 `mfderiv` 与实值 `mvfderiv` 均精确等于 `nativeEuclideanHeightCLM V / height p.coordinates`。这些结论通过真实坐标图微分、线性高度投影和对数求导得到，分母非零由原正高度内部保证，无需额外提供高度或对数高度的光滑性及导数前提。

实际黎曼切向长度满足 `Real.sqrt (nativeRiemannianMetric.inner p V V) = EuclideanNorm(V) / height p.coordinates`，其中 `EuclideanNorm` 明确指原坐标线性等距所取的三维欧氏模型范数。原高度线性投影的绝对值不超过该欧氏模型范数，因此得到真正的导数界
`|mvfderiv (𝓡 3) nativeLogHeight p V| ≤ Real.sqrt (nativeRiemannianMetric.inner p V V)`。此处右端是所选实际黎曼度量的切向长度；欧氏模型范数仅在上述精确缩放等式内使用。

原高度实际微分、对数高度光滑性、精确微分公式及其黎曼导数界已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用原坐标图、原正高度、欧氏线性投影界及光滑对数求导接口；本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。将此导数界接到固定上游的内蕴距离估计仍需实际导入和编译；原两点距离与所选度量内蕴距离的等式、曲率 −1、一般原流形覆盖及体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 固定上游距离接口的实际复用与原等距的内蕴保距

固定上游版本 `432c38f2aa5a30efb13871292d17b4a3309a496a` 的 `PoincareLib.Geometry.Riemannian.Metric`、`Topology.MetricSpace.Completeness` 及 `Distance.Basic`、`Distance.DerivativeLipschitz`、`Distance.TangentBound` 五个模块，以原源码字节组成完整依赖闭包，已在本项目钉版 Lean／mathlib 环境中实际编译通过。这仅验证上述接口及其实际消费者，不等于复现上游完整庞加莱定理终点。所选实际 `nativeRiemannianMetric` 与上游 `RiemannianMetric 3 H3` 的类型定义一致，其 `edist` 正是安装该度量切向内积后取得的 `Manifold.riemannianEDist`。

对任意原点 `p,q`，实际原对数高度满足
`edist (nativeLogHeight p) (nativeLogHeight q) ≤ PoincareMT.RiemannianMetric.edist nativeRiemannianMetric p q`。这里直接应用固定上游 `edist_le_mul_edist_of_derivative_bound`，取常数 1，并用上述全局光滑性和真正的黎曼导数界逐项满足前提；不需要先假设原 H3 距离与内蕴距离相等。

对任意同一个原 `e : H3 ≃ᵢ H3`，已有实际全局光滑性与 `mfderiv` 内积保持满足固定上游 `edist_le_mul_of_inner_mfderiv_le` 的常数 1 前提，得到内蕴距离不增。将同一结论应用于原 `e.symm` 和原像点，推出
`PoincareMT.RiemannianMetric.edist nativeRiemannianMetric (e p) (e q) = PoincareMT.RiemannianMetric.edist nativeRiemannianMetric p q`，包含逆映射和反定向等距映射。此保距结论由真实微分和上游积分估计内部推出，无需提供内蕴保距前提。

上述实际原对象消费者已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`；上游五模块编译同样零错误、零警告，未修改其源码或项目钉版。复用的是固定上游距离估计与本项目已有实际光滑／微分界接口；本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。原两点距离等于该度量内蕴距离的结论、实际曲率 −1、一般原流形覆盖及体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 原竖直曲线的实际黎曼速度、长度与内蕴距离

对于任意原水平坐标 `z : ℂ`，原曲线 `verticalAxisLine z t = coordinatePoint z (Real.exp t) (Real.exp_pos t)` 在同一原 H3 图册上全局 C∞。其实际 `HasMFDerivAt` 的方向是原坐标线性等距作用于 `(0, Real.exp t)` 后所得的切向量；真实坐标图求导与原开放嵌入给出该流形微分，并非仅列出一个候选方向。

上述实际曲线微分代入原高度负二次幂的实际黎曼内积，得到 `g.inner (γ t) (mfderiv γ t 1) (mfderiv γ t 1) = 1`。原高度正好为 `Real.exp t`，其平方与方向高度分量的平方相消；不把默认欧氏切向范数当作所选黎曼范数。实际安装该 `g` 的局部 `RiemannianBundle` 后，曲线真实切向范数为 1，故 `g.pathELength γ a b = ENNReal.ofReal (b-a)`。

对任意 `a ≤ b`，真实光滑曲线的长度给出 `g.edist (γ a) (γ b) ≤ ENNReal.ofReal (b-a)`。原对数高度沿同一竖直曲线精确等于参数 `t`；已核验的全局对数高度导数距离界给出反向不等式，因此实际所选度量的竖直内蕴距离精确为 `ENNReal.ofReal (b-a)`。不需要假设原 H3 距离与此内蕴距离已全局相等。

上述实际光滑性、曲线微分、速度、长度与有序区间内蕴距离等式已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用实际图册求导、指数求导、原黎曼内积公式、路径长度积分及已核验的对数高度下界；本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。任意原两点的原距离与所选内蕴距离等式、实际曲率 −1、一般原流形覆盖及体积绑定、同一规定 `h,d` 的完整 Mostow–Prasad 和官方验收仍未完成。


### 原 H3 任意两点的黎曼距离兼容

对同一原 H3 中任意两点 `p,q`，已核验
`PoincareMT.RiemannianMetric.edist nativeRiemannianMetric p q = edist p q`，其 `toReal` 精确等于原 `dist p q`。这里保留原点、原空间距离、原拓扑、原欧氏三维图册与实际高度负二次幂黎曼度量，不额外提供两点齐性或距离兼容前提。

原 Lorentz 嵌入中两个时间分量相等的点，其差向量具有零时间分量。不同点时，该向量的 Lorentz 自配对非零，由原双曲距离的 cosh 核内部证明；真实 Lorentz 反射将两点互换、固定原 `rayOrigin` 并保持所有未来向量的正时间分量，因此构成实际原 H3 等距映射。同一点由恒等映射处理。先应用原 `originTransport p` 的逆，再应用此原点固定反射，得到一个实际原等距映射，将 `p` 送到原起点、`q` 送到 `verticalAxisLine 0 (dist p q)`，包含 `p=q`。

已核验的原等距内蕴保距与原竖直曲线内蕴距离公式，将任意原两点的实际所选度量距离识别为 `ENNReal.ofReal (dist p q)`，从而得到上述全局等式。局部显式安装同一实际 `nativeRiemannianMetric` 的 `Bundle.RiemannianBundle` 后，原 H3 满足实际 `IsRiemannianManifold (𝓡 3) H3`；没有将默认欧氏切向范数当作此黎曼范数。

上述原点固定等距、原两点竖直规范化、全局距离等式及原黎曼流形兼容已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。复用原 Lorentz 反射／正时间重建、原距离核、已核验的实际内蕴保距和竖直长度接口；逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。实际曲率 −1、一般原流形覆盖及有限体积绑定、非紧尖点和完整给定 `h,d` 的 Mostow–Prasad 及官方验收仍未完成。


### 原 H3 的平坦切丛度量、实际联络存在性与对数高度梯度

在同一原 H3 拓扑及实际欧氏三维单图册上，`nativeFlatRiemannianMetric` 是实际全局 C∞ 黎曼度量，其两切向量内积为原图册模型的欧氏内积。正定性、切向单位球有界性及切丛截面的光滑性均已内部证明。原 `FiberBundle.extend` 在此实际单图册上恰为常值切向场；其真实总空间截面可微性由公开扩张接口给出。

固定上游版本 `432c38f2aa5a30efb13871292d17b4a3309a496a` 的一般 Levi–Civita 存在定理，实际应用于同一原 H3 的上述平坦度量及原高度负二次幂度量，分别给出真正兼容、无挠联络数据的存在性。所需原流形图册、全局光滑度量、Hausdorff 性与第二可数性来自已有原对象构造，未提供额外联络存在前提。LC／梯度依赖闭包含 13 个原源码模块及一个只将未使用参数 `D` 重命名为 `_D` 的梯度兼容模块；该兼容改动保留声明、类型和数学定义，不关闭检查。

对于任意上述实际平坦 Levi–Civita 数据 `D`，原 `nativeLogHeight` 的实际 `D.gradient` 等于原高度倒数乘以高度投影的欧氏对偶单位向量。该向量的实际自内积为 1，故平坦度量下真实梯度范数平方精确为原高度平方的倒数；梯度识别直接由公开 `inner_gradient`、已核验的原对数高度实际微分及对偶向量内积公式推出。原高度倒数的实际微分以及 `exp(±2*logheight)` 的精确原高度公式也已核验。

上述原对象构造与消费者已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。常值切向场的实际协变导数为零、平坦曲率与真正 Hessian、原高度缩放度量的曲率 −1 仍待闭合；一般原流形的通用度量覆盖及有限体积尖点绑定、完整给定 `h,d` 的 Mostow–Prasad 和官方验收仍未完成。


### 原 H3 的实际平坦联络、零曲率与无条件对数高度 Hessian

对同一原 H3 的实际平坦度量及任意实际 Levi–Civita 数据 `D`，原常值切向场的 Lie 括号和协变导数均为零。原欧氏坐标图的真实 `mfderiv` 为恒等映射；公开 `mpullback_mlieBracket` 将目标欧氏空间常值场的零括号搬回原切丛。真实常值切丛截面的可微性、常数内积的零微分及原零括号代入公开 Koszul 恒等式，再由正定内积，内部推出 `D.connection (fun _ => Y) p = 0`，没有额外提供联络为零的前提。

上游实际点态曲率使用的 `FiberBundle.extend` 在原单图册上恰为同一常值场，因此其一阶、二阶协变导数及括号项均为零；得到原平坦度量实际 `D.curvature p U V W = 0` 和实际总化截面曲率为零。此处零曲率包含退化向量对；后续高度缩放度量的曲率 −1 仍须保留向量对线性无关或 Gram 非零条件。

原对数高度的真正 Hessian 现无条件满足 `D.hessian nativeLogHeight p V W = -nativeEuclideanHeightCLM V * nativeEuclideanHeightCLM W / height p.coordinates ^ 2`。先前辅助定理的联络为零前提由上述原对象证明内部闭合；保留相同原度量、实际 `D`、原函数、原点和切向量。

上述原联络、平坦曲率和无条件 Hessian 已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。原高度缩放度量的实际曲率 −1、一般原流形覆盖与有限体积尖点绑定、完整给定 `h,d` 的 Mostow–Prasad 及官方验收仍未完成。


### 原高度缩放度量的实际共形曲率 −1

在同一原 H3 切丛上，实际 `positiveScaling nativeFlatRiemannianMetric (exp(-2*nativeLogHeight))` 与原 `nativeRiemannianMetric` 是同一度量结构。原内积等式、原正高度及 `exp(-2*logheight)=height⁻²` 内部给出该结构等式，随后沿其搬运给定原度量的同一个实际 Levi–Civita 数据 `Dprime`；等式消去保证搬运前后的实际截面曲率相等。

固定上游一般 Levi–Civita 存在定理内部选择平坦数据 `Dflat`，公开共形截面曲率公式消费已经核验的实际平坦零曲率、无条件原对数高度 Hessian、梯度范数平方及指数高度恒等式。Hessian 与方向微分平方逐项抵消，剩下原高度平方乘以其负倒数，精确得到 `Dprime.sectionalCurvature p V W = -1`。本项向量对前提是原平坦度量下正交且分别单位长度；保留同一原 `p,V,W,Dprime`，没有提供曲率值或联络为零的额外前提。

所需固定上游共形闭包含 33 个模块，原源码均保留并核验固定 Git blob。实际洁净编译使用先前梯度未使用参数的重命名，以及三个明确的兼容模块：两个证明局部类绑定 `letI` 改为 `let`，两个分别属于不同模块的辅助引理显式省去未使用的自动节假设；后两项保留原结论和证明正文，去掉冗余前提。没有关闭检查或添加公理。

上述实际度量等式、依赖数据搬运及原曲率消费者已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。任意原线性无关向量对的曲率接口、一般原流形覆盖与有限体积尖点绑定、完整给定 `h,d` 的 Mostow–Prasad 及官方验收仍未完成。


### 原 H3 的每个实际非退化切平面曲率 −1

对同一原 `nativeRiemannianMetric` 的任意实际 Levi–Civita 数据 `Dprime`，原高度倒数对切向量的缩放，将原度量的正交单位向量对变成平坦度量的正交单位向量对。原实际曲率张量的公开多线性接口及实际度量双线性，分别给出截面曲率分子与 Gram 分母的相同非零缩放因子；在实际商中消去该因子，把已核验的原平坦正交单位向量对曲率 −1 搬回原度量的正交单位向量对。

固定上游 `SpaceForm.Sectional` 的一般正交单位向量对接口内部完成切平面基变换，推出同一原 `p,V,W,Dprime` 在原 Gram 非零条件下实际截面曲率为 −1。原度量 Gram 等于欧氏 Gram 乘原高度四次幂的倒数；公开 Mathlib Gram 行列式判据把同一原向量对的实际线性无关转成欧氏 Gram 非零，从而得到每个实际线性无关向量对的原截面曲率 −1。没有假设平面基变换不变性或预先提供曲率 −1；没有对退化向量对声称 −1。

固定上游截面曲率闭包的 35 个模块已实际编译验收，原源码及固定 Git blob 均保留并核验。除继承的 LC／共形兼容处理外，本闭包四个模块仅作明确的最小兼容修正：弃用引理别名与 tactic 改用公开同义接口，证明局部类型类绑定按现行接口书写，去掉被检查器指出未使用的自动节假设及冗余化简参数；没有关闭检查或添加公理。

上述原非退化切平面消费者已通过完整累计 Lean 编译，零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。一般原流形的万能度量覆盖、实际 H3 分类及有限体积尖点绑定、完整给定 `h,d` 的 Mostow–Prasad 和官方验收仍未完成。


### 原双曲模型的实际可缩性与 H3 单连通性

任意原实内积空间 `E` 上的 `HyperbolicSpace E`，通过原 `coordinatesHomeomorph` 与原欧氏环境中的正高度半空间同胚。公开半空间凸性接口给出该真实正高度子集的凸性，原水平零向量及高度 1 给出内部非空见证；`Convex.contractibleSpace` 再沿原坐标同胚搬回真正原双曲空间，得到实际 `ContractibleSpace` 实例。没有把正高度子集替换成整个环境空间，也没有提供外部收缩同伦或可缩性前提。

同一实例实际应用于原 `HyperbolicThreeSpace`，并由已有 Mathlib 可缩空间单连通接口得到实际 `SimplyConnectedSpace`。这些原实例检查及完整累计 Lean 编译均零错误、零警告，公理闭包仅含 `propext, Classical.choice, Quot.sound`。逐声明 `proof_shape: bind-only`、`admission_basis: none`，本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证本说明。一般原流形的万能度量覆盖和 H3 分类、有限体积尖点及完整给定 `h,d` 的 Mostow–Prasad 与官方验收仍未完成。


### 原光滑标准覆盖的完备拉回度量与第二可数性

同一原完备、道路连通的三维流形 M 和指定原黎曼度量 g，在 g 的真实内蕴距离与原扩展距离相等时，原路径类标准覆盖获得实际提升光滑图册、局部微分同胚投影和 g 的实际完整微分拉回度量。欧氏图册在内部给出局部道路连通及半局部单连通，覆盖的分离性质给出真实 T3 结构；恒等等距映射显式绑定原扩展度量与指定 g 的内蕴扩展度量，内部传递完备性。

消费固定上游真实 MetricComplete 与闭球紧致公开接口，实际内蕴有限距离使可数闭球覆盖同一连通覆盖空间，再由 sigma-compact 与欧氏图册得到该原标准覆盖的 SecondCountableTopology。无需底空间紧致、有限基本群、外供覆盖第二可数性或有限覆盖度。对同一原 H3/native g，已验的真正 native 内蕴距离等于原距离在内部履行兼容性，得到实际 native g 完备性及原 H3 标准覆盖第二可数性。

固定来源为 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a。真实 MetricComplete 与 CompleteBalls 使用完整最小导入闭包，其余覆盖提升与完备拉回证明保留具名上游 source-slice 来源；不冒领未导入的完整 NeckCap/Harnack 扩展模块验收。完整累计临时 Lean 真实 exit 0，零错误、零警告，298 项公理报告仅含 propext、Classical.choice、Quot.sound，18 个新增目标实际接受。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证说明。实际全局负曲率指数映射与 H3 分类、完整 deck 与体积/Haar 绑定、有限体积尖点及完整给定 h,d 的 Mostow–Prasad 与官方验收仍未完成。


### 真实负正规系数 Jacobi ODE 的双曲函数解与唯一性

消费固定上游原 IsJacobiSolOn 方程及 Linear.IsSolOn 唯一性，对任意原实赋范向量空间和真实常系数算子 A，内部证明核向量与负正规特征值对应的 t/sinh/cosh 模型确实满足原方程。方程符号保持 y'=v、v'=-Ay；正规特征值 -c² 给出正加速度双曲正弦模型。沿真实算子范数界和原初值，公开 ODE 唯一性把任意真正原方程解识别为已证明模型，并得到 c=1 的 sinh/cosh 正规公式。无需额外 CompleteSpace、外供解公式或替代解谓词。

两个固定上游模块与完整累计临时 Lean 均真实 exit 0，零错误、零警告。301 项公理报告仅含 propext、Classical.choice、Quot.sound，3 个新增目标已实际验收。原草稿保留；derived 仅显式化复合/逐点加法表达式并删除一个编译器确认冗余的 ring。proof_shape: bind-only，admission_basis: none。本段是原 ODE 模型与唯一性消费者，实际流形 Jacobi 场的平行传输、曲率系数归约和原指数映射还须在后续内部证明，不能把它们升为最终 Mostow 新前提。完整 Mostow–Prasad 与官方验收仍未完成。


### 同一原光滑标准覆盖的单连通性、平凡基本群与实际提升

消费此前已接受的同一原路径类 UniversalCover 与原投影，欧氏图册在内部给出局部道路连通和半局部单连通，实际公开标准覆盖定理给出该原覆盖的 SimplyConnectedSpace。实际任意原覆盖基点上的每个闭路均与常闭路同伦，真正原覆盖基本群的每个元素等于 1，原投影诱导的基本群同态像为底子群；不将底流形 M 的基本群误称平凡。

同一原投影确实是覆盖且满射，并具有基点指定的连续映射唯一提升。提升试验域 A 与原流形 M 的 universes 独立；A 的单连通性属于真正通用提升定理的上下文，该原覆盖本身的单连通性由前述真实定理取得。无需外供原覆盖单连通性、额外度量相容性、全局紧致、有限基本群或有限覆盖度。

没有新增上游导入或重复编译已接受的 canonical24。独立小消费者与完整累计临时 Lean 均真实 exit 0、零错误、零警告；307 项公理报告仅含 propext、Classical.choice、Quot.sound，6 个新增消费者及3个真实公共目标接受。proof_shape: bind-only，admission_basis: none。本项交付为 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证说明。实际原 H3 分类与负曲率全局指数、完整 deck/体积/Haar、有限体积尖点及给定 h,d 的完整 Mostow–Prasad 与官方验收仍未完成。


### 原边界交比的正缩放与全部零锥配对保持

对同一原 NullSphere 上的指定单射 F，真正四个互异原点的核交比保持，在内部给出由三个原锚点构造的正缩放因子。实际非对角核比例满足该缩放的双因子分解；对原零锥上的全部点对，缩放后的 F 原向量保持原 Lorentz 配对。对角比例仍为 0；对角配对保持由原零向量条件证明，没有把非对角比例的正性或分解错误推广到对角。

无需外供比例分解、正缩放存在性或原 Lorentz 线性等距。独立新模块实际导入已接受的原 native 基底，完整新证明正文通过 Lean 编译，真实 exit 0、零错误、零警告；新目标 nativeBoundaryKernelScale_reconstruction 的公理闭包仅含 propext、Classical.choice、Quot.sound。导入的基底已有 301 项标准公理报告，其源码、实际导入 olean 及依赖哈希再次核对一致；新正文与累计源的追加部分逐字相同。本项验收范围为完整新模块及其目标。

固定上游来源沿用 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a，以及此前已核验的原 Lorentz／边界构造。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，精确 Lean 为临时编译证据，远端 CI 验证说明。缩放零锥到原等距的重构、有限体积推出同一真正 F 及交比性质、给定 h,d 的完整 Mostow–Prasad 与官方验收仍未完成；这些中间输入不升为最终新前提。


### 同一原零锥缩放配对到唯一原 H3 等距的重构

同一原 NullSphere 映射 F 的正缩放若保持原零锥全部点对的 Lorentz 配对，四个固定原零框架点便在内部给出真正原 Lorentz 线性等距。像框架的独立性由原 Gram 恒等式与配对非退化性证明；原 FutureUnit 的两个正零向量分解进一步证明同一矩阵保持未来分支。原 futureLorentzIsometry 随后构造唯一真正原 H3 等距 e，其原 nullSphereAction 恰为同一 F。无需外供矩阵、像框架独立性、未来保持或 H3 等距；定向反转仍包含在原等距群内。

窄完整 Lean 模块真实 exit 0、零错误、零警告；全部 82 项公理报告仅含 propext、Classical.choice、Quot.sound，覆盖 nativeFutureUnit_positiveNullDecomposition、nativePositiveConeAction_futureTime、nativeScaledCone_reconstructOriginalIsometry 三个新目标。源码在实际编译前后不变，原接受基底、实际生成 olean、完整日志、退出结果及原依赖再次独立核对一致。验收范围为该完整窄模块与三个新目标。

固定来源沿用 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a，以及此前已验证的原 Lorentz／边界构造。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。正缩放与全部配对由此前交比结果内部产生；有限体积给出同一真实 F 与交比性质、给定 h,d 的完整 Mostow–Prasad 及官方验收仍待完成。唯一性在本段指同一 F 的边界作用，尚不替代仅由给定群共轭或原同伦类得出的最终唯一性。


### 同一原边界交比与完整给定群同构的原等距共轭

同一原 NullSphere 单射 F 保持真正四个互异原点的核交比时，内部构造的正缩放与全部零锥配对保持给出唯一原 H3 等距 e，其实际 nullSphereAction 为 F。若 F 对同一原表示 ρ、σ 与完整指定群同构 d 等变，原边界作用的忠实性进一步给出对每个原群元素 γ 的完整共轭等式 e * ρ γ * e⁻¹ = σ (d γ)。源群与目标群的 universes 独立，原完整等距群保留定向反转。

独立小模块实际导入此前已接受的窄零锥重构基底；新证明正文真实 exit 0、零错误、零警告，三个新目标的公理闭包仅含 propext、Classical.choice、Quot.sound。新源与实际编译快照一致，3071 字节完整证明尾与候选逐字一致；实际导入的基底源码、olean 及此前 82 项标准公理验收再次核对，43 项绑定工件独立验证一致。验收范围为完整导入消费者的三个新目标。

固定来源沿用 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a 与此前原 Lorentz／边界构造。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。这里的唯一性包含同一 F 的边界作用；仅由给定共轭或原同伦类推出最终唯一性，以及从原有限体积内部构造同一 F 与交比性质，仍须完成。完整 Mostow–Prasad 与官方验收未完成。


### 由原稠密吸引点得到仅依赖完整给定共轭的唯一性

消费仓内原稠密吸引点中心化子定理与原忠实 NullSphere 边界表示。三个原零框架点内部给出避开任意两个原边界点的见证；原吸引点稠密性由实际原表示 ρ 的迭代趋近性质定义。边界中心化子平凡随后通过原边界作用忠实性转回完整原 H3 等距群，包含定向反转。

同一完整指定群同构 d 的任意两个原等距共轭变换 e、f，只要分别对所有原群元素满足原共轭等式，就有 e = f。此唯一性无额外的同一 F 边界作用条件。结合此前同一原 F 的交比重构与实际等变性，得到唯一原等距共轭变换的存在；原群与目标群的 universes 独立。

完整独立消费者实际导入已接受的原交比共轭模块与仓内原中心化子定理，真实 exit 0、零错误、零警告；三个新目标的公理闭包仅含 propext、Classical.choice、Quot.sound。实际源码、编译快照、完整派生证明尾、生成 olean、终态及导入基底一致；仓内原定理的实际源码与选中的项目 olean 也逐项绑定核对，27 项工件独立验证通过。验收范围为完整新消费者及其三个新目标。

来源为仓内 D5.S3.Geometry.MostowPrasadRigidity 的原动力学／中心化子定理，此前已接受的原 Lorentz／边界构造，以及固定上游 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a。proof_shape: bind-only，admission_basis: none。本项为 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。原有限体积推出吸引点稠密性、同一实际 F 及交比保持仍待内部证明；这些中间输入不升为完整 Mostow 的新前提。原同伦类的完整存在唯一性、完整 Mostow–Prasad 与官方验收未完成。


### 原边界归一化动作的真实微分与切向配对缩放

对每个原 H3 等距 e 与原 NullSphere 点 x，原 Lorentz 矩阵 A 的归一化作用在真实原环境空间 Fin 4 → ℝ 上具有实际 HasFDerivAt。令 t = (A x)₀，其连续线性微分在任意原向量 u 上为 t⁻¹ Au − ((Au)₀/t²) Ax；分母非零与 t > 0 均由原未来分支作用内部证明。原完整等距群保留定向反转，不需要外供微分、共形性、Möbius 或 Beltrami 条件。

实际原切向子空间由 u₀ = 0 与 pairing x u = 0 定义。真实原球面值曲线的导数内部满足这两个约束，原动作的真实曲线链式法则给出同一微分。该微分把原切向子空间送到实际像点的切向子空间，并使任意原切向 u、v 的 Lorentz 配对乘以正因子 1/t²；所有混合项由原零向量与切向方程消去。原 Fin 4 的 Pi 范数没有被当作欧氏球面度量。

完整独立消费者实际导入已接受的原窄零锥重构模块与三个公开 Mathlib 微分模块，真实 exit 0、零错误、零警告；两个新目标的公理闭包仅含 propext、Classical.choice、Quot.sound。原始证明尾保留，派生尾仅作十项明确的证明/API 对齐，命题保持不变。实际源码、编译快照、完整派生尾、生成 olean、终态、导入基底及选中的 Mathlib 源码/olean 共 62 项绑定工件独立核对通过；导入基底已有 82 项标准公理报告。验收范围为完整新消费者与两个新目标。

来源为仓内原 Lorentz/NullSphere 构造与 Mathlib@db584cd6d46c92f209a44c0f1c829460d327499d，固定上游复用范围沿用 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。实际球面流形微分、原 round 度量及复有限图的绑定仍须完成；未知边界映射 F 的构造和弱正则性、有限体积/完整尖点消费者、给定 h,d 的完整 Mostow–Prasad 与官方验收未完成。


### 原局部流的 C¹ 变分见证与完整初值／时间微分

在有限维完备实赋范空间 E 上，同一原时间依赖向量场 f 的联合函数为 C²，原 Φ 是指定基点、正初值半径与包含初始时间的区间上的实际 IsLocalFlow 时，公开 exists_isVariationalFlowProjection_one_of_C2 在内部构造正时间 T、正半径 ρ 和 C¹ 连续线性算子值函数 Y。它在真实开球与时间开区间的乘积上满足原结构 IsVariationalFlowProjection 的完整微分方程：DΦ(x,t)(u,s) = Y(x,t)u + s • f(t,Φ(x,t))。初值方向与时间方向属于同一原 Φ 的联合微分，不是分别存在但未绑定的两个候选。

真实增广向量场在内部构造实际局部流，变分解唯一性将其投影识别为原 Φ 的初值微分；两个正邻域取最小值保证光滑性和微分恒等式在同一非空局部域同时成立。没有外供 Y 的存在、光滑性或原 Φ 的联合微分公式。辅助公开 fderiv_Phi_eq_coprod_fromAugFlow_aux 保留原 C¹ 向量场及实际增广局部流上下文，其增广局部流由 C² 见证定理内部履行。

来源为 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a 的 PoincareLib.Analysis.ODE.LocalFlow.HigherRegularity.{VariationalCoproductDerivative,VariationalLevelOneWitness}，原作者为 qinz1yang/differential-geometry 的 DifferentialGeometry contributors，比较版本 1b535dd102b94cc42b107cca27059687888f08b3，Apache-2.0。固定来源的 14 个有序前置模块已实际编译或复用此前验收，零错误、零警告；其源码与固定原字节和 Git blob 均一致。逐项核对源码、日志、退出结果、预登记、实际生成 olean、原源码与导入检查，共 99 项工件独立验证一致。

两个既有公开定理的完整递归公理闭包由只导入实际已接受模块的小检查验收，仅含 propext、Classical.choice、Quot.sound；本项没有新增证明包装或重复编译已接受正文。proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。该结果是向量空间中的原局部流变分定理；流形测地线／Jacobi 场、全局原指数映射及 H3 分类的实际绑定，96 模块的完整更高正则性闭包、有限体积尖点和未知边界映射 F、给定 h,d 的完整 Mostow–Prasad 与官方验收仍未完成。


### 同一原局部流在任意有限阶的真实变分正则性

公开 exists_isVariationalFlowProjection_of_C 对每个自然数 k 证明：在有限维完备实赋范空间 E 上，同一原向量场 f 的联合函数全域为 C^(k+1)，原 Φ 为指定基点、正初值半径且初始时间处于区间内部的实际 IsLocalFlow 时，内部构造正 T、正 ρ 及 C^k 连续线性算子值函数 Y，并使同一原 Φ 的完整联合微分满足 DΦ(x,t)(u,s) = Y(x,t)u + s • f(t,Φ(x,t))。光滑性和此恒等式在同一真实开球与时间开区间的乘积上成立。

零阶由原 C¹ 变分见证取得；归纳步在实际有限维增广空间 E × (E →L[ℝ] E) 中构造真实增广局部流，应用对任意原空间成立的归纳假设，再由原后继阶见证回接同一个原 Φ。没有外供高阶 Y 或联合微分公式。量词是每个有限 k 各自存在 T、ρ、Y；本结果不声称一个统一邻域或一个统一 Y 上的 C∞ 结论。

来源为 frenzymath/Poincare-Conjecture@432c38f2aa5a30efb13871292d17b4a3309a496a 的 PoincareLib.Analysis.ODE.LocalFlow.HigherRegularity.VariationalLinearMapSmoothness。原作者为 qinz1yang/differential-geometry 的 DifferentialGeometry contributors，比较版本 1b535dd102b94cc42b107cca27059687888f08b3，Apache-2.0。原完整模块与有序前置已真实编译或复用此前验收，零错误、零警告；固定原字节、Git blob、实际导入源码和 olean 一致。只导入原已接受模块的小检查打印该既有公开定理的完整递归公理闭包，仅含 propext、Classical.choice、Quot.sound，没有新增证明包装或重复编译已接受正文。

proof_shape: bind-only，admission_basis: none。本项交付 Library 复用说明，Lean 为临时编译证据，远端 CI 验证说明。统一 C∞／真实流形测地线及 Jacobi 场的实际绑定、全局原指数映射与 H3 分类、完整有限体积尖点和未知 F 的弱正则性、给定 h,d 的完整 Mostow–Prasad 与官方验收仍未完成。
