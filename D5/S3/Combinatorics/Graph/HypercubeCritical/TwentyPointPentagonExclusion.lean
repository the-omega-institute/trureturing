/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonExclusion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/TwentyPointPentagonExclusion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.InformationTheory.Hamming]
   utility: none
   digest: Actual independent low vertices exclude paired pentagons under Huang balance. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonDistinct

/-! Both direction alternatives are consequences of actual matching edges. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonExclusion

open SimpleGraph GirthSliceCounting
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open private shape distinct_direction_normal_form from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonDistinct
open private paired_cycle_injective_directions from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonCoordinates
open private SideHigh compressed from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointCompression
open private diff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CubeSmallSupport
open private common_middle_diff adj_of_diff_subset_card compressed_distance diff_self diff_symm from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointGeometry
open private five_star_negative from
  D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonSigns

attribute [local instance] Classical.propDecidable

private def bshape (i : Fin 5) : Finset (Fin 5) := insert i (shape i)
private def smallP (i : Fin 5) : Finset (Fin 5) := {i + 3}
private def largeP (i : Fin 5) : Finset (Fin 5) := {i + 2, i + 3, i + 4}
private def smallQ (i : Fin 5) : Finset (Fin 5) := {i, i + 2}
private def largeQ (i : Fin 5) : Finset (Fin 5) := Finset.univ.erase (i + 1)

private theorem index_adj_of_subset {n : ℕ} {c : Fin 5 → Fin n}
    (hc : Function.Injective c) {z x y : Q n} {X Y : Finset (Fin 5)}
    (hx : diff x z = X.image c) (hy : diff y z = Y.image c)
    (hsub : X ⊆ Y) (hcard : Y.card = X.card + 1) : (hypercube n).Adj x y := by
  apply adj_of_diff_subset_card
  · rw [hx, hy]
    exact Finset.image_subset_image hsub
  · rw [hx, hy, Finset.card_image_of_injective _ hc, Finset.card_image_of_injective _ hc]
    exact hcard

private theorem normal_low_patterns {n : ℕ} {c : Fin 5 → Fin n}
    (hc : Function.Injective c) (A B P Qs : Fin 5 → Q n) {z : Q n}
    (hA : ∀ i, diff (A i) z = (shape i).image c)
    (hB : ∀ i, diff (B i) z = (bshape i).image c)
    (hAd : ∀ i, hammingDist (A i) (A (i + 1)) = 2)
    (hBd : ∀ i, hammingDist (B i) (B (i + 2)) = 2)
    (hAP : ∀ i, (hypercube n).Adj (A i) (P i))
    (hPA : ∀ i, (hypercube n).Adj (A (i + 1)) (P i))
    (hBQ : ∀ i, (hypercube n).Adj (B i) (Qs i))
    (hQB : ∀ i, (hypercube n).Adj (B (i + 2)) (Qs i)) :
    (∀ i, diff (P i) z = (smallP i).image c ∨ diff (P i) z = (largeP i).image c) ∧
    (∀ i, diff (Qs i) z = (smallQ i).image c ∨ diff (Qs i) z = (largeQ i).image c) := by
  have hcardA (i : Fin 5) : (diff (A i) z).card = 2 := by
    rw [hA, Finset.card_image_of_injective _ hc]
    fin_cases i <;> decide +kernel
  have hcardB (i : Fin 5) : (diff (B i) z).card = 3 := by
    rw [hB, Finset.card_image_of_injective _ hc]
    fin_cases i <;> decide +kernel
  constructor
  · intro i
    have hh := common_middle_diff (hcardA i) (hcardA (i + 1)) (hAd i) (hAP i) (hPA i)
    have hI : shape i ∩ shape (i + 1) = smallP i := by fin_cases i <;> decide +kernel
    have hU : shape i ∪ shape (i + 1) = largeP i := by fin_cases i <;> decide +kernel
    rw [hA, hA, ← Finset.image_inter _ _ hc, ← Finset.image_union, hI, hU] at hh
    exact hh
  · intro i
    have hh := common_middle_diff (hcardB i) (hcardB (i + 2)) (hBd i) (hBQ i) (hQB i)
    have hI : bshape i ∩ bshape (i + 2) = smallQ i := by fin_cases i <;> decide +kernel
    have hU : bshape i ∪ bshape (i + 2) = largeQ i := by fin_cases i <;> decide +kernel
    rw [hB, hB, ← Finset.image_inter _ _ hc, ← Finset.image_union, hI, hU] at hh
    exact hh

private theorem independent_lows_small {n : ℕ} {c : Fin 5 → Fin n}
    (hc : Function.Injective c) (P Qs : Fin 5 → Q n) {z : Q n}
    (hP : ∀ i, diff (P i) z = (smallP i).image c ∨ diff (P i) z = (largeP i).image c)
    (hQ : ∀ i, diff (Qs i) z = (smallQ i).image c ∨ diff (Qs i) z = (largeQ i).image c)
    (hlow : ∀ i j, ¬ (hypercube n).Adj (P i) (Qs j)) :
    ∀ i, diff (P i) z = (smallP i).image c := by
  have hps (i : Fin 5) (hi : diff (P i) z = (largeP i).image c) :
      diff (Qs i) z = (smallQ i).image c := by
    rcases hQ i with hsmall | hlarge
    · exact hsmall
    · exact (hlow i i (index_adj_of_subset hc hi hlarge
        (by fin_cases i <;> decide +kernel) (by fin_cases i <;> decide +kernel))).elim
  intro i
  rcases hP i with hsmall | hlarge
  · exact hsmall
  · have hQi := hps i hlarge
    have hQnext : diff (Qs (i + 2)) z = (largeQ (i + 2)).image c := by
      rcases hQ (i + 2) with hs | hl
      · exact (hlow i (i + 2) (index_adj_of_subset hc hs hlarge
          (by fin_cases i <;> decide +kernel) (by fin_cases i <;> decide +kernel)).symm).elim
      · exact hl
    have hPnext : diff (P (i + 2)) z = (largeP (i + 2)).image c := by
      rcases hP (i + 2) with hs | hl
      · exact (hlow (i + 2) i (index_adj_of_subset hc hs hQi
          (by fin_cases i <;> decide +kernel) (by fin_cases i <;> decide +kernel))).elim
      · exact hl
    have hQnext' := hps (i + 2) hPnext
    have hh := congrArg Finset.card (hQnext'.symm.trans hQnext)
    rw [Finset.card_image_of_injective _ hc, Finset.card_image_of_injective _ hc] at hh
    have hs : (smallQ (i + 2)).card = 2 := by fin_cases i <;> decide +kernel
    have hl : (largeQ (i + 2)).card = 4 := by fin_cases i <;> decide +kernel
    omega

private theorem distinct_pentagons_negative {n : ℕ} {S : Finset (Q n)}
    (hbal : IsBalanced S) (A B P Qs : Fin 5 → (S : Set (Q n)))
    (c : Fin 5 → Fin n) (hc : Function.Injective c)
    (hflip : ∀ i, (B i).val = flip (A i).val (c i))
    (hno : ∀ i j, i ≠ j → ¬ (hypercube n).Adj (A i).val (B j).val)
    (hAd : ∀ i j, (cycleGraph 5).Adj i j → hammingDist (A i).val (A j).val = 2)
    (hBd : ∀ i j, i ≠ j → ¬ (cycleGraph 5).Adj i j →
      hammingDist (B i).val (B j).val = 2)
    (hAP : ∀ i, (hypercube n).Adj (A i).val (P i).val)
    (hPA : ∀ i, (hypercube n).Adj (A (i + 1)).val (P i).val)
    (hBQ : ∀ i, (hypercube n).Adj (B i).val (Qs i).val)
    (hQB : ∀ i, (hypercube n).Adj (B (i + 2)).val (Qs i).val)
    (hlow : ∀ i j, ¬ (hypercube n).Adj (P i).val (Qs j).val) : False := by
  obtain ⟨z, hz⟩ := distinct_direction_normal_form
    (fun i => (A i).val) (fun i => (B i).val) c hc hflip hno hAd hBd
  have hA (i : Fin 5) : diff (A i).val z = (shape i).image c := (hz i).1
  have hB (i : Fin 5) : diff (B i).val z = (bshape i).image c := by
    simpa only [bshape, Finset.image_insert] using (hz i).2
  have hA2 (i : Fin 5) : hammingDist (A i).val (A (i + 1)).val = 2 := by
    apply hAd
    fin_cases i <;> decide +kernel
  have hB2 (i : Fin 5) : hammingDist (B i).val (B (i + 2)).val = 2 := by
    apply hBd
    · fin_cases i <;> decide +kernel
    · fin_cases i <;> decide +kernel
  obtain ⟨hP, hQ⟩ := normal_low_patterns hc
    (fun i => (A i).val) (fun i => (B i).val)
    (fun i => (P i).val) (fun i => (Qs i).val) hA hB hA2 hB2 hAP hPA hBQ hQB
  have hsmall := independent_lows_small hc (fun i => (P i).val) (fun i => (Qs i).val) hP hQ hlow
  have hPinj : Function.Injective P := by
    intro i j he
    have hh := congrArg (fun x : (S : Set (Q n)) => diff x.val z) he
    rw [hsmall i, hsmall j] at hh
    simp only [smallP, Finset.image_singleton, Finset.singleton_inj] at hh
    exact add_right_cancel (hc hh)
  have hzP (i : Fin 5) : (hypercube n).Adj z (P i).val := by
    change (diff z (P i).val).card = 1
    rw [diff_symm, hsmall]
    simp [smallP]
  have hAz (i : Fin 5) : (A (i + 1)).val ≠ z := by
    intro he
    have hh := hA (i + 1)
    rw [he, diff_self] at hh
    have hc2 : ((shape (i + 1)).image c).card = 2 := by
      rw [Finset.card_image_of_injective _ hc]
      fin_cases i <;> decide +kernel
    rw [← hh] at hc2
    simp at hc2
  exact five_star_negative hbal P (fun i => A (i + 1)) hPinj
    (fun i => (hPA i).symm) (fun i => (hAP (i + 1)).symm) hzP hAz

private theorem paired_cycle_nonembedding {n : ℕ} {S : Finset (Q n)}
    {L R : Finset (S : Set (Q n))}
    (hpart : ((hypercube n).induce (S : Set (Q n))).IsBipartiteWith
      (L : Set (S : Set (Q n))) (R : Set (S : Set (Q n))))
    (hdeg : ∀ v, ((hypercube n).induce (S : Set (Q n))).degree v = 2 ∨
      ((hypercube n).induce (S : Set (Q n))).degree v = 3)
    (hlow : ∀ {v w}, ((hypercube n).induce (S : Set (Q n))).Adj v w →
      ((hypercube n).induce (S : Set (Q n))).degree v = 2 →
      ((hypercube n).induce (S : Set (Q n))).degree w = 2 → False)
    (hbal : IsBalanced S)
    (hL : Nonempty (cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) L))
    (hR : Nonempty (cycleGraph 5 ≃g compressed ((hypercube n).induce (S : Set (Q n))) R)) : False := by
  obtain ⟨eL⟩ := hL
  obtain ⟨eR⟩ := hR
  obtain ⟨f, c, hf, hcomp, hflip, hcinj⟩ :=
    paired_cycle_injective_directions hpart hdeg hlow hbal eL eR
  let A : Fin 5 → (S : Set (Q n)) := fun i => (eL i).val
  let B : Fin 5 → (S : Set (Q n)) := fun i => (f (eL i)).val
  have hedgeP (i : Fin 5) : (compressed ((hypercube n).induce (S : Set (Q n))) L).Adj
      (eL i) (eL (i + 1)) := by
    apply eL.map_rel_iff.mpr
    fin_cases i <;> decide +kernel
  have hedgeQ (i : Fin 5) : (compressed ((hypercube n).induce (S : Set (Q n))) R).Adj
      (f (eL i)) (f (eL (i + 2))) := by
    apply (hcomp i (i + 2)).mpr
    fin_cases i <;> decide +kernel
  choose P hP hAP hPA using fun i => (hedgeP i).2
  choose Qs hQ hBQ hQB using fun i => (hedgeQ i).2
  apply distinct_pentagons_negative hbal A B P Qs c hcinj hflip
  · intro i j hij hadj
    have he := (hf (eL i) (f (eL j))).mp hadj
    exact hij (eL.injective (f.injective he))
  · intro i j hij
    exact compressed_distance (eL.map_rel_iff.mpr hij)
  · intro i j hij hno
    exact compressed_distance ((hcomp i j).mpr ⟨hij, hno⟩)
  · exact hAP
  · exact hPA
  · exact hBQ
  · exact hQB
  · intro i j hadj
    exact hlow hadj (hP i) (hQ j)

#print axioms paired_cycle_nonembedding

end D5.S3.Combinatorics.Graph.HypercubeCritical.TwentyPointPentagonExclusion
