---
bibkey: regge1961coordinates
authors: Tullio Regge
year: 1961
title: General relativity without coordinates
doi: 10.1007/BF02733251
url: https://doi.org/10.1007/BF02733251
claim: Regge describes approximating curved spaces by higher-dimensional polyhedra; flat local pieces require gluing and transport data to describe global geometry.
strata_touched: []
license: citation-only
triage: anchor
---

# Flat pieces, gluing and transport

## Source boundary

The [publisher record](https://link.springer.com/article/10.1007/BF02733251) identifies T. Regge, *Il Nuovo Cimento* 19, 558–571 (1961). Its accessible summary describes a coordinate-free approach that approximates curved spaces by higher-dimensional polyhedra and uses simplicial decompositions. The article body was not verified here; no precise action, field equation or theorem number from it is imported. The two-dimensional illustration below is elementary exposition, not a quotation or a new result attributed to a particular passage.

## Elementary angle deficit

Take Euclidean triangles glued isometrically along matching edges, forming an oriented triangulated surface near an interior vertex. Suppose its incident triangle angles at that vertex are $\theta_1,\ldots,\theta_k$. The total intrinsic angle is $\sum_j\theta_j$ and the deficit is

$$
\delta=2\pi-\sum_{j=1}^k\theta_j.
$$

To see the transport interpretation, cut along one radial edge and unfold the incident triangles into a Euclidean sector. Parallel transport is constant in that unfolded plane, but identifying the two bounding rays closes a sector of angle $\sum_j\theta_j$ into the surface. The resulting rotation is the missing angle $\delta$ modulo $2\pi$, with sign reversed if the orientation of traversal is reversed. Flat interiors therefore coexist with nontrivial transport around a vertex. Boundary vertices and singular nonmanifold gluings need different local contracts.

The local shapes alone do not determine the glued surface: edge identifications, lengths and orientations are additional data. Similarly, the [static circuit contraction identity](../Computability/brylinski2001universal.md#static-composition-retains-coherent-information) retains port order and complex matrix entries rather than only local probabilities. This is a correspondence between descriptions of composition, not a claim that the geometries or their resource costs coincide.

For AURIC, the occupancy pyramid is a three-dimensional convex set of local means. A four-dimensional simplex is a different object. Relating a network of AURIC ports to a spacetime triangulation would require a specified map preserving the relevant incidence, metric, causal and transport data. Neither the common use of local building blocks nor the angle-deficit illustration supplies that map or establishes a physical ontology.

This note contains original citation-only exposition and no copied article text or figures.
