/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/CubeCoordinateNormalization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/CubeCoordinateNormalization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Finite]
   utility: none
   digest: Transport cube flips through translations and coordinate permutations. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeBitMoves

/-! Translation and permutation of the coordinates of a nine-cube. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization

open BalancedCriticalSpectrum (Q flip)

abbrev Vertex := Fin 9 → Bool

def origin : Vertex := fun _ => false

/-- Read coordinates in the order specified by `σ`, using differences from
the center as the new Boolean coordinates. -/
def normalize (σ : Equiv.Perm (Fin 9)) (center : Vertex) : Vertex ≃ Vertex where
  toFun x i := x (σ i) != center (σ i)
  invFun x i := x (σ.symm i) != center i
  left_inv x := by
    funext i
    simp only [Equiv.apply_symm_apply]
    cases x i <;> cases center i <;> rfl
  right_inv x := by
    funext i
    simp only [Equiv.symm_apply_apply]
    cases x i <;> cases center (σ i) <;> rfl

private theorem normalize_center (σ : Equiv.Perm (Fin 9)) (center : Vertex) :
    normalize σ center center = origin := by
  funext i
  change (center (σ i) != center (σ i)) = false
  cases center (σ i) <;> rfl

private theorem normalize_flip (σ : Equiv.Perm (Fin 9)) (o x : Q 9) (i : Fin 9) :
    normalize σ.symm o (flip x i) = flip (normalize σ.symm o x) (σ i) := by
  funext j
  by_cases hj : j = σ i
  · subst j
    rw [BalancedCriticalSpectrum.flip_apply_same]
    change (flip x i (σ.symm (σ i)) != o (σ.symm (σ i))) =
      Bool.not (x (σ.symm (σ i)) != o (σ.symm (σ i)))
    simp only [Equiv.symm_apply_apply, BalancedCriticalSpectrum.flip_apply_same]
    cases x i <;> cases o i <;> rfl
  · have hi : σ.symm j ≠ i := fun h => hj ((σ.symm_apply_eq).mp h)
    simp [normalize, BalancedCriticalSpectrum.flip, hj, hi]

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
