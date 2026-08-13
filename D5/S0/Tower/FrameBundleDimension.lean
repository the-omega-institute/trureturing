/- GID: D5/S0/Tower/FrameBundleDimension
   generality: G
   mirror-B: D5/B/S0/Tower/FrameBundleDimension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A local frame-coordinate space over n coordinates has dimension n+n^2. -/

import Mathlib.LinearAlgebra.Dimension.Constructions

namespace D5.S0.Tower.FrameBundleDimension

universe u

/-- A base vector together with the coefficient matrix of a local frame. -/
abbrev FrameCoordinateSpace (K : Type u) (n : Nat) :=
  (Fin n → K) × (Fin n → Fin n → K)

/-- A base point contributes `n` coordinates and its local frame contributes `n^2`. -/
theorem frame_coordinate_finrank (K : Type u) [Field K] (n : Nat) :
    Module.finrank K (FrameCoordinateSpace K n) = n + n * n := by
  rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Module.finrank_pi_fintype]
  simp [Module.finrank_fintype_fun_eq_card]

end D5.S0.Tower.FrameBundleDimension
