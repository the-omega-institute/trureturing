/- GID: D5/S3/Topology/TauCeti/Geometry/Convex/ConvexSpace/Barycenter
   generality: G
   mirror-B: none(waiver:upstream-support-documented-in-module)
   mirror-E: none(waiver:abstract-support-without-experimental-evidence)
   anchors: []
   utility: none
   digest: TauCeti port: Barycenters of faces under vertex maps; sphere-homology support. -/

import Mathlib.Geometry.Convex.ConvexSpace.Barycenter

/-!
This file is a source port adapted from TauCetiProject/TauCeti at immutable
revision `5a01f5fe3621126cccf9ba22e700493cbc7b7156`, source path
`TauCeti/Geometry/Convex/ConvexSpace/Barycenter.lean`. Changes: import paths are namespaced under
`D5.S3.Topology.TauCeti` for this repository's pinned Mathlib. The original
Tau Ceti copyright and Apache-2.0 terms are retained in
`docs/reports/licenses/tauceti-sphere-port-LICENSE.txt`. Retire this port only
when this repository's own pinned Mathlib provides an equivalent declaration
at the full telescope and all live consumers compile with direct replacement.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Barycenters of faces under maps of vertices

Mathlib's `Convexity.StdSimplex.subBarycenter S hS` is the barycenter of the face of a standard
simplex spanned by a nonempty finite set `S` of vertices. This file records that an injective map
of vertices, acting on the standard simplex by `Convexity.StdSimplex.map`, sends the barycenter of
the face spanned by `S` to the barycenter of the face spanned by the image of `S`. For instance,
the inclusion of a facet of the standard simplex sends barycenters of faces of the facet to
barycenters of the corresponding faces of the simplex, which is how barycentric subdivision
restricts to faces.
-/

public section

namespace Convexity.StdSimplex

variable {K M N : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Replacing the finite set in a face barycenter by an equal set does not change the
barycenter. -/
lemma subBarycenter_congr {S T : Finset M} (h : S = T) (hS : S.Nonempty) :
    subBarycenter (K := K) S hS = subBarycenter T (h ▸ hS) := by
  subst h
  rfl

/-- An injective map of vertices sends the barycenter of the face spanned by `S` to the
barycenter of the face spanned by the image of `S`. -/
@[simp]
lemma map_subBarycenter (f : M ↪ N) (S : Finset M) (hS : S.Nonempty) :
    (subBarycenter (K := K) S hS).map f = subBarycenter (S.map f) (hS.map) := by
  ext n
  simp [weights_subBarycenter, Finsupp.mapDomain_finsetSum]

end Convexity.StdSimplex
