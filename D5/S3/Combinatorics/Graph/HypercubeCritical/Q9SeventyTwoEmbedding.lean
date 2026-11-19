import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoThinSlice
import D5.S3.Combinatorics.Graph.HypercubeCritical.Q9GrayPlacementNormalForm

/-! Translate the root to zero and choose axes for a cubical embedding of
the compressed graph. Each compressed edge retains a midpoint touching
exactly its endpoints among the eight high vertices. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding

open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open Q9GrayPlacementNormalForm (normalize_hammingDist origin)
open Q9SeventyTwoThinSlice (modelRootNeighbors rootSecondAxes compressed_root_axes)
open Q9EightCubicGraphCertificate (modelAdj)

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
    ∃ (wagner : Bool) (pattern : Fin 5) (p : Fin 8 ↪ Q 9),
      p 0 = origin ∧ (∀ k, p k 0 = false) ∧
      (∀ a, p (modelRootNeighbors wagner a) =
        flip (flip origin ((a.castLE (by decide : 3 ≤ 8)).succ)) (rootSecondAxes pattern a)) ∧
      ∀ i j, modelAdj wagner i j = true →
        ∃ m : Q 9, m 0 = false ∧
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
  have hplane (x : (S : Set (Q 9))) : e x.val 0 = false := by
    have hr0 : root 0 = b := (Finset.mem_filter.mp (vertices 0).property).2
    have hx0 : x.val 0 = b := (Finset.mem_filter.mp x.property).2
    have hcut' : σ.symm 0 = 0 := (σ.symm_apply_eq).mpr hcut.symm
    change (x.val (σ.symm 0) != root (σ.symm 0)) = false
    simp [hcut', hr0, hx0]
  refine ⟨wagner, pattern, p, hzero, fun k => hplane (vertices k), ?_, ?_⟩
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
    refine ⟨e m.val, hplane m, fun k => ?_⟩
    change hammingDist (e m.val) (e (vertices k).val) = 1 ↔ _
    rw [normalize_hammingDist]
    change G.Adj m (vertices k) ↔ _
    rw [← G.mem_neighborFinset, hneighbors]
    simp only [Finset.mem_insert, Finset.mem_singleton, vertices.injective.eq_iff]

#print axioms normalized_embedding

end D5.S3.Combinatorics.Graph.HypercubeCritical.Q9SeventyTwoEmbedding
