/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9TenProjectionOnlyK4
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Only the subdivided K4 orbit has ten patterns at the 28-point half threshold. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4TenProjectionOrbits
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9PairProjectionSharp
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowExterior
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenShadowSecondSharedLeaves

/-! For Hong–Wu–Xia, arXiv:2610.09483v1, §7 Problem 2, a ten-pattern
four-coordinate projection at the 28-point half threshold belongs to the
subdivided K4 orbit. A signed cube symmetry carries each orbit representative
to the first four coordinates, where the other five representatives are excluded. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenProjectionOnlyK4

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip)
open BalancedCubeComponentBoundary (directions)
open Q4SmallProjectionOrbits (neighborDirections permute)
open Q4TenProjectionOrbits (representative)
open Q9FourFiberSpectrum (leftProjection)
open Q9FourProjection (flipBit)
open Q9ThetaProjection (leftCode)
open private exists_signed_leftProjection from
  D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjectionOrbit

open Classical in
private theorem projection_min_degree_two {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (axes : Fin 4 ↪ Fin 9) :
    let P := S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))
    ∀ k ∈ P, 2 ≤ (neighborDirections P k).card := by
  intro P k hk
  obtain ⟨C, hreg', hb', hC, _, _⟩ :=
    exists_signed_leftProjection hreg hb axes (fun _ => false)
  have hleft : leftProjection C = P.map (cubeBitVec 4).toEmbedding := by
    rw [hC, Finset.map_eq_image]
    dsimp only [P]
    rw [Finset.image_image]
    apply Finset.image_congr
    intro x _
    change (fun i : Fin 4 => x (axes i) ^^ false) =
      cubeBitVec 4 ((cubeBitVec 4).symm (fun i => x (axes i)))
    rw [Equiv.apply_symm_apply]
    exact funext fun i => Bool.xor_false (x (axes i))
  have hmem (a : BitVec 4) : cubeBitVec 4 a ∈ leftProjection C ↔ a ∈ P := by
    rw [hleft]
    exact Finset.mem_map' (cubeBitVec 4).toEmbedding
  have hdirs : directions (leftProjection C) (cubeBitVec 4 k) = neighborDirections P k := by
    ext i
    simp only [directions, neighborDirections, Finset.mem_filter, Finset.mem_univ, true_and]
    have hflip : cubeBitVec 4 (flipBit k i) = flip (cubeBitVec 4 k) i :=
      cubeBitVec_xor_single k i
    rw [← hflip, hmem]
  rw [← hdirs]
  exact Q9FourFiberSpectrum.balanced_projection_min_degree_two hreg' hb' ((hmem k).mpr hk)

open Classical in
private theorem exists_normalized_projection {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 28 ≤ (S.filter (fun x => x j = b)).card)
    (axes : Fin 4 ↪ Fin 9) (R : Finset (BitVec 4))
    (σ : Equiv.Perm (Fin 4)) (t : BitVec 4)
    (hP : S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i))) =
      R.image (fun k => permute σ k ^^^ t)) :
    ∃ C : Finset (Q 9), ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced C ∧ C.image leftCode = R ∧ C.card = S.card ∧
      ∀ (j : Fin 9) (b : Bool), 28 ≤ (C.filter (fun x => x j = b)).card := by
  let project (x : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => x (axes i))
  let act (k : BitVec 4) : BitVec 4 := permute σ k ^^^ t
  let orderedAxes : Fin 4 ↪ Fin 9 :=
    ⟨fun i => axes (σ.symm i), axes.injective.comp σ.symm.injective⟩
  let mask : Q 4 := fun i => t.getLsbD (σ.symm i).val
  let undo (k : BitVec 4) : BitVec 4 := permute σ.symm (k ^^^ t)
  have hpermute (p : Equiv.Perm (Fin 4)) (k : BitVec 4) (i : Fin 4) :
      (permute p k).getLsbD i.val = k.getLsbD (p i).val :=
    congrFun ((cubeBitVec 4).apply_symm_apply (fun j => k.getLsbD (p j).val)) i
  have hundo (k : BitVec 4) : undo (act k) = k := by
    apply (cubeBitVec 4).injective
    funext i
    change (permute σ.symm (permute σ k ^^^ t ^^^ t)).getLsbD i.val = k.getLsbD i.val
    simp only [hpermute, BitVec.getLsbD_xor, σ.apply_symm_apply, Bool.xor_assoc,
      Bool.xor_self, Bool.xor_false]
  obtain ⟨C, hreg', hb', hC, hcard, p, m, hhalves⟩ :=
    exists_signed_leftProjection hreg hb orderedAxes mask
  refine ⟨C, hreg', hb', ?_, hcard, fun j b => ?_⟩
  · calc
      C.image leftCode = (leftProjection C).image (cubeBitVec 4).symm := by
        rw [leftProjection, Finset.image_image]
        rfl
      _ = (S.image project).image undo := by
        rw [hC, Finset.image_image, Finset.image_image]
        apply Finset.image_congr
        intro x _
        apply congrArg (cubeBitVec 4).symm
        funext i
        have hbit : (project x).getLsbD (σ.symm i).val = x (axes (σ.symm i)) :=
          congrFun ((cubeBitVec 4).apply_symm_apply (fun j => x (axes j))) (σ.symm i)
        change (x (axes (σ.symm i)) ^^ mask i) =
          ((project x ^^^ t).getLsbD (σ.symm i).val)
        rw [BitVec.getLsbD_xor, hbit]
      _ = R := by
        change S.image project = R.image act at hP
        rw [hP, Finset.image_image]
        rw [show undo ∘ act = (fun k => k) from funext hundo, Finset.image_id']
  · rw [hhalves]
    exact hhalf (p.symm j) (b ^^ m j)

open Classical in
private theorem normalized_representative_eq_five {C : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hsize : C.card = 72)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 28 ≤ (C.filter (fun x => x j = b)).card)
    {r : Fin 6} (hproj : C.image leftCode = representative r) : r = 5 := by
  fin_cases r
  · exact (Q9TenShadowSelfAdjoint.tenShadow_excluded_of_twenty_eight
      hreg hb hsize (hhalf 0 true) hproj).elim
  · exact (Q9TenShadowExterior.tenShadowRowsThreeFour_excluded hreg hb hproj).elim
  · obtain ⟨j, b, hle⟩ :=
      Q9TenShadowSecondSharedLeaves.tenShadowSecond_half_le_twentySeven hreg hb hsize hproj
    have hlower := hhalf j b
    omega
  · exact (Q9TenShadowExterior.tenShadowRowTen_excluded hreg hb hproj).elim
  · obtain ⟨axes, side, htwenty⟩ :=
      Q9TenShadowSharedLeaves.tenShadowSharedLeaves_three_halves hreg hb hsize hproj
    have hlower := hhalf (axes 0) (side 0)
    rw [htwenty 0] at hlower
    omega
  · rfl

open Classical in
/-- A ten-pattern projection of an order-72 Huang-balanced induced cubic support
with at least 28 vertices in every coordinate half is a permuted XOR translate
of the subdivided K4 representative. -/
theorem ten_projection_only_k4 {S : Finset (Q 9)}
    (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 28 ≤ (S.filter (fun x => x j = b)).card)
    (axes : Fin 4 ↪ Fin 9)
    (hten : (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card = 10) :
    ∃ (σ : Equiv.Perm (Fin 4)) (t : BitVec 4),
      S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i))) =
        (representative 5).image (fun k => permute σ k ^^^ t) := by
  have hanti := Q9FourProjection.four_projection_antipodal_complement_edges_of_pair_coverage
    hsize hreg hb axes
    (by
      intro i j hij b c
      exact Q9PairProjectionSharp.pair_projection_surjective_of_twenty_eight
        hsize hreg hb hhalf (axes.injective.ne hij) b c)
    (fun j b => (by decide : 24 < 28).trans_le (hhalf (axes j) b))
  obtain ⟨r, t, σ, hP⟩ :=
    Q4TenProjectionOrbits.ten_projection_orbit _ hten hanti (projection_min_degree_two hreg hb axes)
  obtain ⟨C, hreg', hb', hproj, hcard, hhalf'⟩ :=
    exists_normalized_projection hreg hb hhalf axes (representative r) σ t hP
  have hr := normalized_representative_eq_five hreg' hb' (hcard.trans hsize) hhalf' hproj
  exact ⟨σ, t, hr ▸ hP⟩

#print axioms ten_projection_only_k4

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9TenProjectionOnlyK4
