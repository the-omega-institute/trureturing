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
