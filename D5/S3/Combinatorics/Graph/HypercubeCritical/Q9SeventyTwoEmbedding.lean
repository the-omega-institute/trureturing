import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm
import Batteries.Tactic.OpenPrivate

/-! Translate the root to zero and choose axes for a cubical embedding of
the compressed graph. Each compressed edge retains a midpoint touching
exactly its endpoints among the eight high vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced IsSwitching switchingVector)
open BalancedCubeLowerBound (coordinateSlice)
open Q9GrayPlacementNormalForm (normalize_hammingDist origin)
open Q9SeventyTwoThinSlice (modelRootNeighbors rootSecondAxes compressed_root_axes)
open Q9EightCubicGraphCertificate (modelAdj)
open private huangMatrix from D5.S3.Combinatorics.Graph.HypercubeSubQuorum
open private edge matrix_row from D5.S3.Combinatorics.Graph.HypercubeCritical.HuangCubeCovariance
open private matrix_flip_zero from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCriticalSpectrum

local notation "flip" => BalancedCriticalSpectrum.flip
local notation "cubeNormalize" => Q9GrayPlacementNormalForm.normalize
attribute [local instance] Classical.propDecidable

private theorem normalize_flip (σ : Equiv.Perm (Fin 9)) (o x : Q 9) (i : Fin 9) :
    cubeNormalize σ.symm o (flip x i) = flip (cubeNormalize σ.symm o x) (σ i) := by
  funext j
  by_cases hj : j = σ i
  · subst j
    rw [BalancedCriticalSpectrum.flip_apply_same]
    change (flip x i (σ.symm (σ i)) != o (σ.symm (σ i))) =
      Bool.not (x (σ.symm (σ i)) != o (σ.symm (σ i)))
    simp only [Equiv.symm_apply_apply, BalancedCriticalSpectrum.flip_apply_same]
    cases x i <;> cases o i <;> rfl
  · have hi : σ.symm j ≠ i := fun h => hj ((σ.symm_apply_eq).mp h)
    simp [Q9GrayPlacementNormalForm.normalize, BalancedCriticalSpectrum.flip, hj, hi]

/-- Every actual thin half yields one of the two graph models embedded in
the coordinate-zero eight-cube, starting from one of the five root patterns.
The midpoint test used in the embedding enumeration holds for every edge. -/
theorem normalized_embedding {C : Finset (Q 9)} (hC : C.card = 72)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (b : Bool) (hs : (coordinateSlice C b).card = 20) :
    ∃ (g : Q 9 ≃ Q 9) (σ : Fin 9 ≃ Fin 9)
      (wagner : Bool) (pattern : Fin 5) (p : Fin 8 ↪ Q 9),
      (∀ x i, g (flip x i) = flip (g x) (σ i)) ∧
      (∀ x, g x 0 = false ↔ x 0 = b) ∧
      p 0 = origin ∧ (∀ k, p k ∈ (coordinateSlice C b).image g ∧ p k 0 = false) ∧
      (∀ a, p (modelRootNeighbors wagner a) =
        flip (flip origin ((a.castLE (by decide : 3 ≤ 8)).succ)) (rootSecondAxes pattern a)) ∧
      ∀ i j, modelAdj wagner i j = true →
        ∃ m ∈ (coordinateSlice C b).image g, m 0 = false ∧
          ∀ k, (hypercube 9).Adj m (p k) ↔ k = i ∨ k = j := by
  classical
  let S := coordinateSlice C b
  let G := (hypercube 9).induce (S : Set (Q 9))
  obtain ⟨wagner, vertices, first, second, σ, pattern, hrealize, hroot, hcut, hlabel⟩ :=
    compressed_root_axes hC hr hb b hs
  let root := (vertices 0).val
  let e := cubeNormalize σ.symm root
  let p := vertices.trans ((Function.Embedding.subtype _).trans e.toEmbedding)
  have hzero : e root = origin := by
    funext _
    simp [e, Q9GrayPlacementNormalForm.normalize, origin]
  have hplane (x : Q 9) : e x 0 = false ↔ x 0 = b := by
    have hr0 : root 0 = b := (Finset.mem_filter.mp (vertices 0).property).2
    have hcut' : σ.symm 0 = 0 := (σ.symm_apply_eq).mpr hcut.symm
    change (x (σ.symm 0) != root (σ.symm 0)) = false ↔ x 0 = b
    simp [hcut', hr0]
  have hmem (x : (S : Set (Q 9))) : e x.val ∈ S.image e ∧ e x.val 0 = false :=
    ⟨Finset.mem_image.mpr ⟨x.val, x.property, rfl⟩,
      (hplane x.val).mpr (Finset.mem_filter.mp x.property).2⟩
  refine ⟨e, σ, wagner, pattern, p, normalize_flip σ root, hplane, hzero,
    fun k => hmem (vertices k), ?_, ?_⟩
  · intro a
    change e (vertices (modelRootNeighbors wagner a)).val = _
    have hfirst : σ (first a) = (a.castLE (by decide : 3 ≤ 8)).succ :=
      Fin.ext (hlabel a).1
    rw [(hroot a).2]
    change cubeNormalize σ.symm root (flip (flip root (first a)) (second a)) = _
    rw [normalize_flip, normalize_flip, hfirst, (hlabel a).2]
    exact congrArg (fun x : Q 9 => flip (flip x ((a.castLE (by decide : 3 ≤ 8)).succ))
      (rootSecondAxes pattern a)) hzero
  · intro i j hij
    obtain ⟨hne, m, hm, hi, hj⟩ := (hrealize i j).mp hij
    have hc : G.degree m = 2 := hm
    have hsub : ({vertices i, vertices j} : Finset (S : Set (Q 9))) ⊆ G.neighborFinset m := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact (G.mem_neighborFinset _ _).mpr hi.symm
      · exact (G.mem_neighborFinset _ _).mpr hj.symm
    have hneighbors : G.neighborFinset m = {vertices i, vertices j} := by
      symm
      apply Finset.eq_of_subset_of_card_le hsub
      simp [G.card_neighborFinset_eq_degree, hc, vertices.injective.ne hne]
    refine ⟨e m.val, (hmem m).1, (hmem m).2, fun k => ?_⟩
    change hammingDist (e m.val) (e (vertices k).val) = 1 ↔ _
    rw [normalize_hammingDist]
    change G.Adj m (vertices k) ↔ _
    rw [← G.mem_neighborFinset, hneighbors]
    simp only [Finset.mem_insert, Finset.mem_singleton, vertices.injective.eq_iff]

#print axioms normalized_embedding

/-- The signed values in either coordinate-zero half force every value in
the opposite half. The formula also applies at zeros off the support. -/
theorem signed_half_completion (C : Finset (Q 9)) (s : Q 9 → ℝ)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hs : IsSwitching C s) (y : Q 9) :
    switchingVector C s (flip y 0) =
      3 * switchingVector (coordinateSlice C (y 0)) s y -
        ∑ i ∈ Finset.univ.erase (0 : Fin 9),
          edge y i * switchingVector (coordinateSlice C (y 0)) s (flip y i) := by
  classical
  have hslice (x : Q 9) (hx : x 0 = y 0) :
      switchingVector (coordinateSlice C (y 0)) s x = switchingVector C s x := by
    simp [switchingVector, coordinateSlice, hx]
  have hsum : (∑ i ∈ Finset.univ.erase (0 : Fin 9), edge y i *
      switchingVector (coordinateSlice C (y 0)) s (flip y i)) =
      ∑ i ∈ Finset.univ.erase (0 : Fin 9), edge y i * switchingVector C s (flip y i) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hne : (0 : Fin 9) ≠ i := (Finset.mem_erase.mp hi).1.symm
    rw [hslice (flip y i) (Function.update_of_ne hne _ _)]
  have h := congrFun (BalancedCriticalSpectrum.ambient_eigenvector (d := 3) C s hr hs) y
  change (huangMatrix 9).mulVec (switchingVector C s) y = 3 * switchingVector C s y at h
  rw [matrix_row, ← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin 9))] at h
  have hz : edge y 0 = 1 := matrix_flip_zero y
  rw [hz, one_mul] at h
  rw [hslice y rfl, hsum, ← h, add_sub_cancel_left]

#print axioms signed_half_completion

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding
