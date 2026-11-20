/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/Q9NineProjectionOrbit
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Archive.Sensitivity]
   utility: none
   digest: Transport the nine-point exclusion to any ordered four axes. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q4SmallProjectionOrbits
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9EightCycleProjection
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjection
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.HuangBalancedSymmetry
import Mathlib.Logic.Equiv.Fintype

/-! A signed symmetry of the nine-cube realizes any ordered four-axis
projection in the first four coordinates and preserves Huang balance. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjectionOrbit

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced flip flip_apply_same)
open BalancedCubeComponentBoundary (directions)
open Q4SmallProjectionOrbits (representative permute neighborDirections)
open Q9FourProjection (flipBit)
open Q9FourFiberSpectrum (leftProjection)
open Q9NineProjection (nineProjection balanced_projection_ne_nineProjection)

open Classical in
private theorem exists_signed_leftProjection {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (axes : Fin 4 ↪ Fin 9) (mask : Q 4) :
    ∃ C : Finset (Q 9), ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced C ∧ leftProjection C = S.image (fun x i => x (axes i) ^^ mask i) ∧
      C.card = S.card ∧ ∃ (p : Equiv.Perm (Fin 9)) (m : Q 9), ∀ (q : Fin 9) (b : Bool),
        (C.filter (fun y => y q = b)).card =
          (S.filter (fun x => x (p.symm q) = (b ^^ m q))).card := by
  obtain ⟨p, hp⟩ := Equiv.Perm.exists_extending_pair axes (fun i : Fin 4 => i.castAdd 5)
    axes.injective (Fin.castAdd_injective 4 5)
  have hp' (i : Fin 4) : p.symm (i.castAdd 5) = axes i :=
    p.symm_apply_eq.mpr (hp i).symm
  let m : Q 9 := Fin.append mask (fun _ : Fin 5 => false)
  let g : Q 9 ≃ Q 9 :=
    { toFun := fun x q => x (p.symm q) ^^ m q
      invFun := fun y q => y (p q) ^^ m (p q)
      left_inv := fun x => by
        funext q
        change ((x (p.symm (p q)) ^^ m (p q)) ^^ m (p q)) = x q
        simp only [p.symm_apply_apply, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]
      right_inv := fun y => by
        funext q
        change ((y (p (p.symm q)) ^^ m (p (p.symm q))) ^^ m q) = y q
        simp only [p.apply_symm_apply, Bool.xor_assoc, Bool.xor_self, Bool.xor_false] }
  have hg (x : Q 9) (j : Fin 9) : g (flip x j) = flip (g x) (p j) := by
    funext q
    change (flip x j (p.symm q) ^^ m q) = flip (g x) (p j) q
    by_cases hq : q = p j
    · subst q
      rw [flip_apply_same]
      change (flip x j (p.symm (p j)) ^^ m (p j)) = !(x (p.symm (p j)) ^^ m (p j))
      simpa only [p.symm_apply_apply, flip_apply_same] using Bool.not_xor (x j) (m (p j))
    · have hne : p.symm q ≠ j := fun h => hq (p.symm_apply_eq.mp h)
      have hsrc : flip x j (p.symm q) = x (p.symm q) := Function.update_of_ne hne _ _
      have hdst : flip (g x) (p j) q = g x q := Function.update_of_ne hq _ _
      rw [hsrc, hdst]
      rfl
  obtain ⟨hreg', hb'⟩ := HuangBalancedSymmetry.cube_action_regular_balanced g p hg hreg hb
  refine ⟨S.image g, hreg', hb', ?_, Finset.card_image_of_injective S g.injective, p, m, ?_⟩
  · rw [leftProjection, Finset.image_image]
    apply Finset.image_congr
    intro x _
    funext i
    change (x (p.symm (i.castAdd 5)) ^^ m (i.castAdd 5)) = (x (axes i) ^^ mask i)
    simp only [hp', m, Fin.append_left]
  · intro q b
    rw [Finset.filter_image, Finset.card_image_of_injective _ g.injective]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _
    change ((x (p.symm q) ^^ m q) = b) ↔ x (p.symm q) = (b ^^ m q)
    cases x (p.symm q) <;> cases m q <;> cases b <;> decide

open Classical in
private theorem exists_normalized_projection_orbit {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (axes : Fin 4 ↪ Fin 9) (b : Bool)
    (σ : Equiv.Perm (Fin 4)) (t : BitVec 4)
    (hP : S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i))) =
      (representative b).image (fun k => permute σ k ^^^ t)) :
    ∃ C : Finset (Q 9), ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3 ∧
      IsBalanced C ∧ leftProjection C = (representative b).image (cubeBitVec 4) ∧
      C.card = S.card ∧ ∃ (p : Equiv.Perm (Fin 9)) (m : Q 9), ∀ (q : Fin 9) (a : Bool),
        (C.filter (fun y => y q = a)).card =
          (S.filter (fun x => x (p.symm q) = (a ^^ m q))).card := by
  let project (x : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => x (axes i))
  let act (k : BitVec 4) : BitVec 4 := permute σ k ^^^ t
  change S.image project = (representative b).image act at hP
  -- The orbit action reads input bit `σ i` at output bit `i`.
  let orderedAxes : Fin 4 ↪ Fin 9 :=
    ⟨fun i => axes (σ.symm i), axes.injective.comp σ.symm.injective⟩
  let mask : Q 4 := fun i => t.getLsbD (σ.symm i).val
  let undo (k : BitVec 4) : BitVec 4 :=
    (cubeBitVec 4).symm (fun i => k.getLsbD (σ.symm i).val ^^ mask i)
  have hproject (x : Q 9) (i : Fin 4) : (project x).getLsbD i.val = x (axes i) :=
    congrFun ((cubeBitVec 4).apply_symm_apply (fun j => x (axes j))) i
  have hpermute (k : BitVec 4) (i : Fin 4) :
      (permute σ k).getLsbD i.val = k.getLsbD (σ i).val :=
    congrFun ((cubeBitVec 4).apply_symm_apply (fun j => k.getLsbD (σ j).val)) i
  have hdecode (k : BitVec 4) : cubeBitVec 4 (undo k) =
      (fun i : Fin 4 => k.getLsbD (σ.symm i).val ^^ mask i) :=
    (cubeBitVec 4).apply_symm_apply _
  have hundo (k : BitVec 4) : undo (act k) = k := by
    apply (cubeBitVec 4).injective
    rw [hdecode]
    funext i
    change ((permute σ k ^^^ t).getLsbD (σ.symm i).val ^^ t.getLsbD (σ.symm i).val) =
      k.getLsbD i.val
    simp only [BitVec.getLsbD_xor, hpermute, σ.apply_symm_apply, Bool.xor_assoc,
      Bool.xor_self, Bool.xor_false]
  obtain ⟨C, hreg', hb', hC, hcard, hhalves⟩ :=
    exists_signed_leftProjection hreg hb orderedAxes mask
  have hnormalized (x : Q 9) : (fun i : Fin 4 => x (orderedAxes i) ^^ mask i) =
      cubeBitVec 4 (undo (project x)) := by
    rw [hdecode]
    funext i
    exact congrArg (fun b : Bool => b ^^ mask i) (hproject x (σ.symm i)).symm
  refine ⟨C, hreg', hb', ?_, hcard, hhalves⟩
  calc
    leftProjection C = S.image (fun x => cubeBitVec 4 (undo (project x))) := by
      rw [hC]
      apply Finset.image_congr
      intro x _
      exact hnormalized x
    _ = (S.image project).image (fun k => cubeBitVec 4 (undo k)) :=
      (Finset.image_image (s := S) (f := project) (g := fun k => cubeBitVec 4 (undo k))).symm
    _ = ((representative b).image act).image (fun k => cubeBitVec 4 (undo k)) := by
      rw [hP]
    _ = (representative b).image (cubeBitVec 4) := by
      rw [Finset.image_image]
      apply Finset.image_congr
      intro k _
      exact congrArg (cubeBitVec 4) (hundo k)

open Classical in
/-- On any ordered four axes, the projection of a balanced induced cubic
nine-cube support excludes every XOR translate of every coordinate permutation
of the nine-point representative. -/
theorem balanced_projection_ne_nineProjection_orbit {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (axes : Fin 4 ↪ Fin 9) (σ : Equiv.Perm (Fin 4)) (t : BitVec 4) :
    S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i))) ≠
      (representative true).image (fun k => permute σ k ^^^ t) := by
  intro hP
  obtain ⟨C, hreg', hb', hrep, _, _⟩ :=
    exists_normalized_projection_orbit hreg hb axes true σ t hP
  apply balanced_projection_ne_nineProjection hreg' hb'
  rw [nineProjection, Finset.map_eq_image]
  exact hrep

open Classical in
/-- On any ordered four axes, each realized pattern has an occupied neighbor,
and the unique neighbor of any leaf has all four neighbors occupied. -/
theorem balanced_projection_no_isolated_and_leaf_full {S : Finset (Q 9)}
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S) (axes : Fin 4 ↪ Fin 9) :
    let P := S.image (fun v => (cubeBitVec 4).symm (fun i => v (axes i)))
    ∀ x ∈ P, (neighborDirections P x).Nonempty ∧
      ∀ i : Fin 4, neighborDirections P x = {i} →
        (neighborDirections P (flipBit x i)).card = 4 := by
  let project (v : Q 9) : BitVec 4 := (cubeBitVec 4).symm (fun i => v (axes i))
  let P := S.image project
  change ∀ x ∈ P, (neighborDirections P x).Nonempty ∧
    ∀ i : Fin 4, neighborDirections P x = {i} →
      (neighborDirections P (flipBit x i)).card = 4
  obtain ⟨C, hreg', hb', hC, _, _⟩ :=
    exists_signed_leftProjection hreg hb axes (fun _ => false)
  have hleft : leftProjection C = P.map (cubeBitVec 4).toEmbedding := by
    rw [hC, Finset.map_eq_image]
    change (S.image fun v i => v (axes i) ^^ false) = (S.image project).image _
    rw [Finset.image_image]
    apply Finset.image_congr
    intro v _
    exact (funext fun i : Fin 4 => Bool.xor_false (v (axes i))).trans
      ((cubeBitVec 4).apply_symm_apply (fun i => v (axes i))).symm
  have hflip (x : BitVec 4) (i : Fin 4) : cubeBitVec 4 (flipBit x i) = flip (cubeBitVec 4 x) i :=
    cubeBitVec_xor_single x i
  have hdirs (x : BitVec 4) : directions (leftProjection C) (cubeBitVec 4 x) =
      neighborDirections P x := by
    ext i
    simp only [directions, neighborDirections, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hleft, ← hflip x i]
    exact Finset.mem_map' (cubeBitVec 4).toEmbedding
  intro x hx
  have hx' : cubeBitVec 4 x ∈ leftProjection C := by
    rw [hleft]
    exact (Finset.mem_map' (cubeBitVec 4).toEmbedding).mpr hx
  obtain ⟨hne, hleaf⟩ := Q9FourFiberSpectrum.balanced_projection_no_isolated_and_leaf_full
    hreg' hb' hx'
  refine ⟨(hdirs x) ▸ hne, ?_⟩
  intro i hi
  have hfull := hleaf i ((hdirs x).trans hi)
  rwa [← hflip x i, hdirs (flipBit x i)] at hfull

open Classical in
/-- An order-72 Huang-balanced induced cubic support whose coordinate halves
all contain at least 30 vertices cannot realize exactly nine patterns
on any ordered choice of four distinct coordinates. -/
theorem four_projection_card_ne_nine {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 30 ≤ (S.filter (fun x => x j = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card ≠ 9 := by
  let P := S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))
  change P.card ≠ 9
  intro hcard
  have hanti := Q9FourProjection.four_projection_antipodal_complement_edges hsize hreg hb hhalf axes
  have hdegree := balanced_projection_no_isolated_and_leaf_full hreg hb axes
  obtain ⟨t, σ, horbit⟩ := Q4SmallProjectionOrbits.small_projection_orbit P (Or.inr hcard)
    hanti (fun x hx => (hdegree x hx).1) (fun x hx => (hdegree x hx).2)
  apply balanced_projection_ne_nineProjection_orbit hreg hb axes σ t
  simpa only [hcard, beq_self_eq_true] using horbit

#print axioms four_projection_card_ne_nine

open Classical in
/-- Each four-axis projection of an order-72 Huang-balanced induced cubic
support in the nine-cube has at least ten patterns if every coordinate half
contains at least 30 vertices. -/
theorem four_projection_card_ge_ten {S : Finset (Q 9)} (hsize : S.card = 72)
    (hreg : ((hypercube 9).induce (S : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced S)
    (hhalf : ∀ (j : Fin 9) (b : Bool), 30 ≤ (S.filter (fun x => x j = b)).card)
    (axes : Fin 4 ↪ Fin 9) :
    10 ≤ (S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))).card := by
  let P := S.image (fun x => (cubeBitVec 4).symm (fun i => x (axes i)))
  change 10 ≤ P.card
  have hge : 8 ≤ P.card := Q9FourProjection.four_projection_card_ge_eight hsize hreg hb hhalf axes
  have hneNine : P.card ≠ 9 := four_projection_card_ne_nine hsize hreg hb hhalf axes
  have hneEight : P.card ≠ 8 := by
    intro hcard
    have hanti :=
      Q9FourProjection.four_projection_antipodal_complement_edges hsize hreg hb hhalf axes
    have hdegree := balanced_projection_no_isolated_and_leaf_full hreg hb axes
    obtain ⟨t, σ, horbit⟩ := Q4SmallProjectionOrbits.small_projection_orbit P (Or.inl hcard)
      hanti (fun x hx => (hdegree x hx).1) (fun x hx => (hdegree x hx).2)
    have hP : P = (representative false).image (fun k => permute σ k ^^^ t) := by
      simpa [hcard] using horbit
    obtain ⟨C, hreg', hb', hrep, hcard', p, m, hhalves⟩ :=
      exists_normalized_projection_orbit hreg hb axes false σ t hP
    obtain ⟨i, b, htwenty⟩ :=
      Q9EightCycleProjection.normalized_exists_half_card_twenty hreg' hb' hrep (hcard'.trans hsize)
    have hlower := hhalf (p.symm (i.natAdd 4)) (b ^^ m (i.natAdd 4))
    rw [hhalves (i.natAdd 4) b] at htwenty
    omega
  omega

#print axioms four_projection_card_ge_ten

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.Q9NineProjectionOrbit
