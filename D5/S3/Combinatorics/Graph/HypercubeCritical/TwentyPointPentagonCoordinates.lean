/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonCoordinates
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonCoordinates
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Actual matching-coordinate rigidity of paired pentagons. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns

/-! Matching directions belong to genuine edges of the original induced support. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonCoordinates

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private paired_cycle_direction_data from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagon
open private compressed_distance low_not_three from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private five_distance_two_center five_star_negative from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns
open private diff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport

attribute [local instance] Classical.propDecidable

private theorem hamming_flip_both {n : ℕ} (x y : Q n) (t : Fin n) :
    hammingDist (flip x t) (flip y t) = hammingDist x y := by
  change (diff (flip x t) (flip y t)).card = (diff x y).card
  have hd : diff (flip x t) (flip y t) = diff x y := by
    ext k
    simp only [diff, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hkt : k = t
    · subst k
      cases hx : x t <;> cases hy : y t <;>
        simp [BalancedCriticalSpectrum.flip, hx, hy]
    · simp [BalancedCriticalSpectrum.flip, hkt]
  exact congrArg Finset.card hd

private theorem paired_cycle_injective_directions {n : ℕ} {S : Finset (Q n)}
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hbal : IsBalanced S)
    (eL : cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L)
    (eR : cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) R) :
    ∃ f : SideHigh ((hypercube n).induce (S : Set (Q n))) L ≃
        SideHigh ((hypercube n).induce (S : Set (Q n))) R,
      ∃ c : Fin 5 → Fin n,
        (∀ x y, (hypercube n).Adj x.val.val y.val.val ↔ f x = y) ∧
        (∀ i j, (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj
          (f (eL i)) (f (eL j)) ↔ i ≠ j ∧ ¬ (cycleGraph 5).Adj i j) ∧
        (∀ i, (f (eL i)).val.val = flip (eL i).val.val (c i)) ∧
        Function.Injective c := by
  obtain ⟨f, c, hf, hc, hflip, hcases⟩ := paired_cycle_direction_data hpart hdeg hlow hbal eL eR
  refine ⟨f, c, hf, hc, hflip, ?_⟩
  rcases hcases with hconstant | hinj
  · exfalso
    let A : Fin 5 → (S : Set (Q n)) := fun i => (eL i).val
    have hAinj : Function.Injective A := by
      intro i j he
      exact eL.injective (Subtype.ext he)
    have hdist (i j : Fin 5) (hij : i ≠ j) : hammingDist (A i).val (A j).val = 2 := by
      by_cases he : (cycleGraph 5).Adj i j
      · exact compressed_distance (eL.map_rel_iff.mpr he)
      · have hh := compressed_distance ((hc i j).mpr ⟨hij, he⟩)
        rw [hflip i, hflip j, hconstant i, hconstant j, hamming_flip_both] at hh
        exact hh
    have hcubeinj : Function.Injective (fun i => (A i).val) := by
      intro i j he
      exact hAinj (Subtype.ext he)
    obtain ⟨z, hz⟩ := five_distance_two_center (fun i => (A i).val) hcubeinj hdist
    have hedge (i : Fin 5) : (compressed ((hypercube n).induce (S : Set (Q n))) L).Adj
        (eL i) (eL (i + 1)) := by
      apply eL.map_rel_iff.mpr
      revert i
      decide +kernel
    choose P hP hAP hPA using fun i => (hedge i).2
    have hPz (i : Fin 5) : (P i).val ≠ z := by
      intro he
      have hneighbor (j : Fin 5) :
          ((hypercube n).induce (S : Set (Q n))).Adj (P i) (A j) := by
        change (hypercube n).Adj (P i).val (A j).val
        rw [he]; exact hz j
      exact low_not_three (hP i)
        (hAinj.ne (by decide : (0 : Fin 5) ≠ 1))
        (hAinj.ne (by decide : (0 : Fin 5) ≠ 2))
        (hAinj.ne (by decide : (1 : Fin 5) ≠ 2))
        (hneighbor 0) (hneighbor 1) (hneighbor 2)
    exact five_star_negative hbal A P hAinj hAP hPA hz hPz
  · exact hinj

#print axioms paired_cycle_injective_directions

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonCoordinates
