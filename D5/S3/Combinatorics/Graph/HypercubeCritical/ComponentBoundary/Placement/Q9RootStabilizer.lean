/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9RootStabilizer
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9RootStabilizer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Cube translations and coordinate permutations compose as a cube normalization. The same transformations preserve the degree of every induced support. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9FiveAxisOrbitCover
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized

/-! The two generators of the rooted five-axis contact action. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9RootStabilizer

open BalancedCriticalSpectrum (Q)
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open private normalize_hammingDist from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9SharedContactNormalized

open D5.S3.Combinatorics.Graph.HypercubeCritical (cubeBitVec)
open D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.CubeCoordinateNormalization
  (normalize origin)
open Q9FiveAxisOrbitCover (Pattern Word swapAxes swapRoots)

private def swapWord (x : Word) : Word :=
  if x.getLsbD 3 = x.getLsbD 4 then x else x ^^^ 24

private def swap34 : Equiv.Perm (Fin 9) := Equiv.swap 3 4

/-- The coordinate swap defined on cube vertices is the bitwise action used
to calculate the orbit of the even contact layer. -/
theorem cubeBitVec_swap34 (x : Word) :
    normalize swap34 origin (cubeBitVec 9 x) = cubeBitVec 9 (swapWord x) := by
  funext i
  change (x.getLsbD (swap34 i).val != false) = (swapWord x).getLsbD i.val
  fin_cases i <;> cases h3 : x[3] <;> cases h4 : x[4] <;>
    simp [swap34, Equiv.swap_apply_def, swapWord, BitVec.getLsbD_xor, h3, h4]

/-- Translation by the root displacement exchanges the roles of the roots. -/
theorem cubeBitVec_translate03 (x : Word) :
    normalize (Equiv.refl _) (cubeBitVec 9 (3 : Word)) (cubeBitVec 9 x) =
      cubeBitVec 9 (x ^^^ 3) := by
  funext i
  change (x.getLsbD i.val != (3 : Word).getLsbD i.val) = (x ^^^ 3).getLsbD i.val
  rw [BitVec.getLsbD_xor]

/-- A second coordinate normalization can be absorbed into the original frame. -/
theorem normalize_comp (σ τ : Equiv.Perm (Fin 9)) (o z : Q 9) :
    (normalize σ o).trans (normalize τ z) =
      normalize (τ.trans σ) ((normalize σ o).symm z) := by
  ext x i
  change ((x (σ (τ i)) != o (σ (τ i))) != z (τ i)) =
    (x (σ (τ i)) != (z (σ.symm (σ (τ i))) != o (σ (τ i))))
  rw [Equiv.symm_apply_apply]
  cases x (σ (τ i)) <;> cases o (σ (τ i)) <;> cases z (τ i) <;> rfl


/-- Translation and coordinate permutation act by graph isomorphisms. -/
def normalizeIso (σ : Equiv.Perm (Fin 9)) (o : Q 9) : hypercube 9 ≃g hypercube 9 where
  toEquiv := normalize σ o
  map_rel_iff' := by
    intro x y
    change hammingDist (normalize σ o x) (normalize σ o y) = 1 ↔ hammingDist x y = 1
    rw [normalize_hammingDist]

open Classical in
/-- The same action on an induced support preserves regularity. -/
theorem normalize_regular {C : Finset (Q 9)} {d : ℕ}
    (h : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree d)
    (σ : Equiv.Perm (Fin 9)) (o : Q 9) :
    ((hypercube 9).induce ((C.map (normalize σ o).toEmbedding : Finset (Q 9)) : Set (Q 9))).IsRegularOfDegree d := by
  let g := normalizeIso σ o
  have hmap : Set.BijOn g (C : Set (Q 9)) (C.map (normalize σ o).toEmbedding : Set (Q 9)) := by
    rw [Finset.coe_map]
    exact g.injective.bijOn_image
  let e := g.induce hmap
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact (e.degree_eq y).trans (h.degree_eq y)

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9RootStabilizer
