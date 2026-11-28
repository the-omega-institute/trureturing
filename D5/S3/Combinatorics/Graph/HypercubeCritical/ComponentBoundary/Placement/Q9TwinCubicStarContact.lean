/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TwinCubicStarContact
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Placement/Q9TwinCubicStarContact
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Two singleton cuts with the same three neighbours and a third singleton cut at a shared neighbour force a further distance-two contact. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut

/-! A contact-mask obstruction for Hong–Wu–Xia, arXiv:2610.09483v1,
§7, Problem 2. -/

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TwinCubicStarContact

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeGirth (flip_comm)
open Q9IsotropicHuang (parity)
open Q9MinimumDistanceOperator (minimumDisplacements)
open Q9WeightedSaturation (defect signedBiadjacency)
open Q9ContactMaskCut (cutMasks three_mask_cut_preserves_contact_fibre)
open private cutPairs mask translate translate_involution parity_translate contact_of_mask
  cutMasks_swap no_alternating_square_of_small_cut other_contact_of_three_mask_cut from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9ContactMaskCut
open private differingAxes mem_minimumDisplacements from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9MinimumDistanceOperator
open private diff_pair from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightContactStar
open private minimumDisplacements_swap_two from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TightDistanceTwoCenter

private theorem singleton_cut_axes {a c : Fin 9} (hac : a ≠ c) :
    a ∈ ({a} : Finset (Fin 9)) ∧ c ∉ ({a} : Finset (Fin 9)) :=
  ⟨Finset.mem_singleton_self a, fun hc => hac (Finset.mem_singleton.mp hc).symm⟩

private theorem singleton_cut_pair {a c : Fin 9} (hac : a ≠ c) :
    (a, c) ∈ cutPairs {a} :=
  Finset.mem_product.mpr ⟨(singleton_cut_axes hac).1,
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (singleton_cut_axes hac).2⟩⟩

private theorem same_first_ne (a : Fin 9) {c d : Fin 9} (hcd : c ≠ d) :
    (a, c) ≠ (a, d) := fun e => hcd (congrArg Prod.snd e)

open Classical in
private theorem opposite_companion_of_three_mask_cut
    {C D : Finset (Q 9)} {b : Bool} {A : Finset (Fin 9)} {x : Q 9}
    {p q r : Fin 9 × Fin 9}
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hsep' : ∀ v ∈ D, ∀ u ∈ C, 2 ≤ hammingDist v u)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0)
    (hx : x ∈ C) (hxb : parity x = b)
    (hp : p ∈ cutPairs A) (hq : q ∈ cutPairs A) (hr : r ∈ cutPairs A) (hpq : p ≠ q)
    (hcut : cutMasks C D b A = {mask p, mask q, mask r})
    (hpx : translate p x ∈ D) (hqx : translate q x ∈ D) :
    translate r (translate p x) ∈ C := by
  have hcard : (cutMasks C D b A).card ≤ 3 := hcut.symm ▸ Finset.card_le_three
  have hcut' : cutMasks D C b A = {mask p, mask q, mask r} :=
    (cutMasks_swap D C b A).trans hcut
  have hback : translate p (translate p x) ∈ C := by
    rw [translate_involution]
    exact hx
  exact Or.resolve_left
    (other_contact_of_three_mask_cut hsep' hrC hbC hpx
      ((parity_translate p x).trans hxb) hp hq hr hcut' hback)
    (no_alternating_square_of_small_cut hsep hrD hcD hbD hdetD
      hx hxb hcard hp hq hpq hpx hqx)

private theorem displacement_of_contact
    {C D : Finset (Q 9)} {b : Bool} {x : Q 9} {a c : Fin 9}
    (hac : a ≠ c) (hx : x ∈ C) (hxb : parity x = b) (hy : translate (a, c) x ∈ D) :
    ({a, c} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  have hdist : hammingDist x (translate (a, c) x) = 2 := by
    change (differingAxes x (flip (flip x a) c)).card = 2
    rw [diff_pair x hac, Finset.card_pair hac]
  exact mem_minimumDisplacements.mpr ⟨x, hx, _, hy, hxb, hdist, diff_pair x hac⟩

open Classical in
/-- The singleton mask cuts at `i`, `j`, and `k` force a contact with mask `{h,s}`. -/
theorem twin_cubic_stars_force_contact
    {C D : Finset (Q 9)} {b : Bool} {i j k h s t : Fin 9}
    (haxes : ([i, j, k, h, s, t] : List (Fin 9)).Nodup)
    (hi : cutMasks C D b {i} = {{i, k}, {i, s}, {i, t}})
    (hj : cutMasks C D b {j} = {{j, k}, {j, s}, {j, t}})
    (hk : cutMasks C D b {k} = {{k, i}, {k, j}, {k, h}})
    (hsep : ∀ u ∈ C, ∀ v ∈ D, 2 ≤ hammingDist u v)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hcC : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hcD : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hbC : IsBalanced C) (hbD : IsBalanced D)
    (hdetC : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w C false)).det = 0)
    (hdetD : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w D false)).det = 0) :
    ({h, s} : Finset (Fin 9)) ∈ minimumDisplacements C D b 2 := by
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at haxes
  obtain ⟨⟨hij, hik, hih, his, hit⟩, ⟨hjk, _, hjs, hjt⟩, ⟨hkh, hks, hkt⟩, ⟨hhs, _⟩, hst⟩ := haxes
  have hki := singleton_cut_pair (Ne.symm hik)
  have hkj := singleton_cut_pair (Ne.symm hjk)
  have hkh' := singleton_cut_pair hkh
  have hsep' (v : Q 9) (hv : v ∈ D) (u : Q 9) (hu : u ∈ C) :
      2 ≤ hammingDist v u := by
    rw [hammingDist_comm v u]
    exact hsep u hu v hv
  have finish {U V : Finset (Q 9)}
      (hsepUV : ∀ u ∈ U, ∀ v ∈ V, 2 ≤ hammingDist u v)
      (hsepVU : ∀ v ∈ V, ∀ u ∈ U, 2 ≤ hammingDist v u)
      (hrU : ((hypercube 9).induce (U : Set (Q 9))).IsRegularOfDegree 3)
      (hrV : ((hypercube 9).induce (V : Set (Q 9))).IsRegularOfDegree 3)
      (hcV : ((hypercube 9).induce (V : Set (Q 9))).Connected)
      (hbU : IsBalanced U) (hbV : IsBalanced V)
      (hdetV : ∀ w : Fin 9 → ℝ, (defect w (signedBiadjacency w V false)).det = 0)
      (hiUV : cutMasks U V b {i} = {{i, k}, {i, s}, {i, t}})
      (hjUV : cutMasks U V b {j} = {{j, k}, {j, s}, {j, t}})
      (hkUV : cutMasks U V b {k} = {{k, i}, {k, j}, {k, h}})
      {x : Q 9} (hx : x ∈ U) (hxb : parity x = b)
      (hix : translate (k, i) x ∈ V) (hjx : translate (k, j) x ∈ V) :
      ({h, s} : Finset (Fin 9)) ∈ minimumDisplacements U V b 2 := by
    have ih_mem {v : Q 9} (hv : v ∈ U) (hvb : parity v = b)
        (hiv : translate (k, i) v ∈ V) (hjv : translate (k, j) v ∈ V) :
        translate (i, h) v ∈ U := by
      have hm := opposite_companion_of_three_mask_cut hsepUV hsepVU hrU hrV hcV hbU hbV hdetV
        hv hvb hki hkj hkh' (same_first_ne k hij) hkUV hiv hjv
      simpa only [translate, flip_comm v k i, BalancedCriticalSpectrum.flip_flip] using hm
    have hikx : translate (i, k) x ∈ V := by
      simpa only [translate, flip_comm x k i] using hix
    rcases other_contact_of_three_mask_cut hsepUV hrV hbV hx hxb
        (singleton_cut_pair hik) (singleton_cut_pair his) (singleton_cut_pair hit) hiUV hikx with
      hsx | htx
    · refine displacement_of_contact hhs (ih_mem hx hxb hix hjx)
        ((parity_translate (i, h) x).trans hxb) ?_
      simpa only [translate, BalancedCriticalSpectrum.flip_flip] using hsx
    · let z := translate (s, t) x
      have shift_contact {a : Fin 9} (hak : a ≠ k) (has : a ≠ s) (hat : a ≠ t)
          (hcut : cutMasks U V b {a} = {{a, k}, {a, s}, {a, t}})
          (hax : translate (k, a) x ∈ V) :
          z ∈ U ∧ parity z = b ∧ translate (k, a) z ∈ V := by
        have hakx : flip (flip x a) k ∈ V := by
          simpa only [translate, flip_comm x k a] using hax
        have hm := three_mask_cut_preserves_contact_fibre {a} (a, k) (a, s) (a, t)
          (singleton_cut_axes hak) (singleton_cut_axes has) (singleton_cut_axes hat)
          (same_first_ne a hks) (same_first_ne a hkt) (same_first_ne a hst)
          hcut hsepUV hrU hrV hcV hbU hbV hdetV hx hxb hakx
        have he : flip (flip (flip (flip x a) t) a) s = z := by
          change _ = flip (flip x s) t
          rw [flip_comm x a t, BalancedCriticalSpectrum.flip_flip, flip_comm x t s]
        have hm' : z ∈ U ∧ parity z = b ∧ translate (a, k) z ∈ V := by
          rw [← he]
          exact hm
        exact ⟨hm'.1, hm'.2.1, by simpa only [translate, flip_comm z a k] using hm'.2.2⟩
      obtain ⟨hz, hzb, hiz⟩ := shift_contact hik his hit hiUV hix
      have hjz := (shift_contact hjk hjs hjt hjUV hjx).2.2
      refine displacement_of_contact hhs (ih_mem hz hzb hiz hjz)
        ((parity_translate (i, h) z).trans hzb) ?_
      change flip (flip (flip (flip (flip (flip x s) t) i) h) h) s ∈ V
      rw [BalancedCriticalSpectrum.flip_flip, flip_comm (flip x s) t i, flip_comm (flip (flip x s) i) t s,
        flip_comm x s i, BalancedCriticalSpectrum.flip_flip]
      exact htx
  obtain ⟨x, hx, hxb, hix⟩ := contact_of_mask hki (show mask (k, i) ∈ cutMasks C D b {k} by
    rw [hk]
    simp [mask])
  rcases other_contact_of_three_mask_cut hsep hrD hbD hx hxb hki hkj hkh' hk hix with hjx | hhx
  · exact finish hsep hsep' hrC hrD hcD hbC hbD hdetD hi hj hk hx hxb hix hjx
  · have hk' : cutMasks C D b {k} = {{k, i}, {k, h}, {k, j}} := by
      rw [hk, Finset.pair_comm ({k, j} : Finset (Fin 9)) {k, h}]
    let y := translate (k, i) x
    have hiy : translate (k, i) y ∈ C := by
      change translate (k, i) (translate (k, i) x) ∈ C
      rw [translate_involution]
      exact hx
    have hjy : translate (k, j) y ∈ C :=
      opposite_companion_of_three_mask_cut hsep hsep' hrC hrD hcD hbC hbD hdetD
        hx hxb hki hkh' hkj (same_first_ne k hih) hk' hix hhx
    rw [minimumDisplacements_swap_two C D b]
    exact finish hsep' hsep hrD hrC hcC hbD hbC hdetC
      ((cutMasks_swap D C b {i}).trans hi) ((cutMasks_swap D C b {j}).trans hj)
      ((cutMasks_swap D C b {k}).trans hk) hix ((parity_translate (k, i) x).trans hxb) hiy hjy

#print axioms twin_cubic_stars_force_contact

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Placement.Q9TwinCubicStarContact
