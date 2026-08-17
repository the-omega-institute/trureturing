/- GID: D5/S0/Diagonal/Equivariance/EquivariantExposure
   generality: G
   mirror-B: D5/B/S0/Diagonal/Equivariance/EquivariantExposure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A single value determines an equivariant map on a transitive action. -/

/- Library-search audit trail (2026-08-17):
   * Repository searches for pretransitive equivariant-map extensionality found no equivalent
     declaration; existing D5 results concern equivariant escape counts and probabilities.
   * Pinned-mathlib semantic and declaration searches found no matching extensionality theorem.
     The proof directly reuses `MulAction.isPretransitive_iff_base` from Mathlib.
-/

import Mathlib.GroupTheory.GroupAction.Transitive

namespace D5.S0.Diagonal.Equivariance.EquivariantExposure

/-- On a transitive domain, two equivariant maps are equal if they agree at one point. -/
theorem equivariant_maps_eq_of_eq_at {G X Y : Type*} [Group G]
    [MulAction G X] [MulAction G Y] [MulAction.IsPretransitive G X]
    (f g : X -> Y)
    (hf : forall (a : G) (x : X), f (a • x) = a • f x)
    (hg : forall (a : G) (x : X), g (a • x) = a • g x)
    (base : X) (hbase : f base = g base) : f = g := by
  funext x
  obtain ⟨a, ha⟩ :=
    (MulAction.isPretransitive_iff_base (G := G) base).mp inferInstance x
  calc
    f x = f (a • base) := congrArg f ha.symm
    _ = a • f base := hf a base
    _ = a • g base := congrArg (fun y => a • y) hbase
    _ = g (a • base) := (hg a base).symm
    _ = g x := congrArg g ha

end D5.S0.Diagonal.Equivariance.EquivariantExposure
