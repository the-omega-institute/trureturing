/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9BinaryComplementSupport
   generality: G
   mirror-B: none(waiver:isolated-verification)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.LinearAlgebra.Dimension.Finite]
   utility: none
   digest: A saturated cubic pair forces twelve nonzero binary entries in one active face. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9ParityGreenBlock
import D5.S3.Combinatorics.Graph.HypercubeCritical.CubeEvenMinimumSupport

/-! The common crossing kernel at order 258 rules out an exterior center with
no selected neighbor. The binary face support bound then applies to the
complementary word on the actual cube. -/

set_option autoImplicit false

noncomputable section

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryComplementSupport

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q flip flip_adj IsBalanced IsSwitching)
open BalancedCubeComponentBoundary (regular_directions exterior_even)
open CubeEvenMinimumSupport (binaryFaceSupport exists_twelve_le_binaryFaceSupport_card)
open Q9BinaryEightAxis (eightAxisWeights parityBlock parityMatrix exists_eight_axis_complement_word)
open Q9IsotropicHuang (flipSign weightedAction)
open Q9IsotropicParityTransfer (ParityVertices parityCode)
open Q9MixedBoundaryCollisions (Separated)
open Q9ParityFoldedBoundary (parity parityFold dropCoordinate)
open Q9ParityGreenBlock (Outside crossing common_crossing_nullity)
open SupportedEigenSaturation (matrix_eq_zero_of_not_adj matrix_abs_of_adj)
open private directions_card from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
open private extendParity extendParity_apply extendParity_off parityBlock_mulVec weightedAction_off
  from D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryEightAxis
open private flipSign_cast from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9IsotropicHuang
open private separated_union_regular separated_union_balanced from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9MixedBoundaryCollisions

attribute [local instance] Classical.propDecidable

private theorem exterior_has_selected_neighbor {C D : Finset (Q 9)}
    (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    {σ τ : Q 9 → ℝ} (hsC : IsSwitching C σ) (hsD : IsSwitching D τ)
    (y : Q 9) (hy : y ∉ C ∪ D) :
    ((C ∪ D).filter (fun x => (hypercube 9).Adj y x)).Nonempty := by
  classical
  by_contra hnone
  let p := !parity y
  let z : Outside (C ∪ D) p :=
    ⟨y, Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩, by simp [p]⟩⟩
  let X := crossing C (C ∪ D) σ p
  let Y := crossing D (C ∪ D) τ p
  let V := X.mulVecLin.ker ⊓ Y.mulVecLin.ker
  have hcol {S : Finset (Q 9)} (hS : S ⊆ C ∪ D) (s : Q 9 → ℝ) :
      (crossing S (C ∪ D) s p).col z = 0 := by
    funext x
    have hn : ¬ (hypercube 9).Adj x.val y := fun h =>
      hnone ⟨x.val, Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp x.property).1, h.symm⟩⟩
    simp [crossing, Matrix.col, z, matrix_eq_zero_of_not_adj hn]
  let e : Outside (C ∪ D) p → ℝ := Pi.single z 1
  have he : e ∈ V := by
    refine ⟨LinearMap.mem_ker.mpr ?_, LinearMap.mem_ker.mpr ?_⟩
    · change X.mulVec (Pi.single z 1) = 0
      rw [Matrix.mulVec_single_one]
      exact hcol Finset.subset_union_left σ
    · change Y.mulVec (Pi.single z 1) = 0
      rw [Matrix.mulVec_single_one]
      exact hcol Finset.subset_union_right τ
  have hpos : 0 < Module.finrank ℝ V := by
    apply (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mpr
    refine ⟨⟨e, he⟩, fun h => ?_⟩
    have hz := congrFun (congrArg Subtype.val h) z
    simp [e] at hz
  have hdim := common_crossing_nullity hsep hrC hrD hc hd hsC hsD p
  change Module.finrank ℝ V = 258 - C.card - D.card at hdim
  rw [Finset.card_union_of_disjoint hsep.1] at hcard
  omega

private theorem flipSign_binary (i : Fin 9) (x : Q 9) : (flipSign i x : ZMod 2) = 1 := by
  have h := matrix_abs_of_adj (flip_adj x i)
  rw [← flipSign_cast] at h
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h with h | h
  · have hi : flipSign i x = 1 := by exact_mod_cast h
    simp [hi]
  · have hi : flipSign i x = -1 := by exact_mod_cast h
    rw [hi]
    decide

private theorem active_flip_sum_eq_zero (k : Fin 9) {p : Bool}
    (g : ParityVertices p → ZMod 2) (hg : (parityBlock (eightAxisWeights k) p).mulVec g = 0)
    (y : Q 9) : ∑ j : Fin 8, extendParity g (flip y (k.succAbove j)) = 0 := by
  have h : weightedAction (eightAxisWeights k) (extendParity g) y = 0 := by
    by_cases hy : parity y = !p
    · let z : ParityVertices (!p) := ⟨y, hy⟩
      rw [← parityBlock_mulVec (eightAxisWeights k) (fun _ => extendParity_off g)
        (x := z), show (fun x : ParityVertices p => extendParity g x.val) = g from
          funext (extendParity_apply g)]
      exact congrFun hg z
    · exact weightedAction_off (eightAxisWeights k) (fun _ => extendParity_off g) hy
  simpa [weightedAction, Fin.sum_univ_succAbove _ k, eightAxisWeights, Fin.succAbove_ne,
    flipSign_binary] using h

private theorem card_binaryFaceSupport_extendParity (k : Fin 9) (b p : Bool)
    (g : ParityVertices p → ZMod 2) :
    (binaryFaceSupport k b (extendParity g)).card =
      (Finset.univ.filter (fun x : ParityVertices p => x.val k = b ∧ g x ≠ 0)).card := by
  classical
  let S := Finset.univ.filter (fun x : ParityVertices p => x.val k = b ∧ g x ≠ 0)
  let project := parityFold (n := 8) k p
  have hinsert (x : ParityVertices p) (hx : x.val k = b) :
      k.insertNth (α := fun _ => Bool) b (project x) = x.val := by
    change k.insertNth (α := fun _ => Bool) b (dropCoordinate k x.val) = x.val
    rw [← hx]
    exact Fin.insertNth_self_removeNth k x.val
  have heq : S.image project = binaryFaceSupport k b (extendParity g) := by
    ext u
    simp only [S, binaryFaceSupport, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨x, ⟨hx, hg⟩, rfl⟩
      rwa [hinsert x hx, extendParity_apply]
    · intro hu
      let y : Q 9 := k.insertNth (α := fun _ => Bool) b u
      have hp : parity y = p := by
        by_contra hn
        exact hu (extendParity_off g hn)
      let x : ParityVertices p := ⟨y, hp⟩
      refine ⟨x, ⟨?_, ?_⟩, ?_⟩
      · exact Fin.insertNth_apply_same (α := fun _ => Bool) k b u
      · rwa [← extendParity_apply g x]
      · change k.removeNth (α := fun _ => Bool) y = u
        exact Fin.removeNth_insertNth (α := fun _ => Bool) k b u
  rw [← heq, Finset.card_image_of_injective _ project.injective]

/-- For each omitted axis, the common binary parity admits a complementary
kernel word with at least twelve nonzero entries on one active eight-face. -/
theorem exists_eight_axis_complement_word_face_support (k : Fin 9) {C D : Finset (Q 9)}
    (hsep : Separated C D) (hcard : (C ∪ D).card = 258)
    (hc : ((hypercube 9).induce (C : Set (Q 9))).Connected)
    (hd : ((hypercube 9).induce (D : Set (Q 9))).Connected)
    (hrC : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hrD : ((hypercube 9).induce (D : Set (Q 9))).IsRegularOfDegree 3)
    (hbC : IsBalanced C) (hbD : IsBalanced D) :
    ∃ p, (∃ v : parityCode (parityMatrix (eightAxisWeights k)) C p, v ≠ 0) ∧
      (∃ v : parityCode (parityMatrix (eightAxisWeights k)) D p, v ≠ 0) ∧
      ∃ g : ParityVertices p → ZMod 2, g ≠ 0 ∧ (∀ x, x.val ∈ C ∪ D → g x = 0) ∧
        (parityBlock (eightAxisWeights k) p).mulVec g = 0 ∧
        ∃ b : Bool, 12 ≤ (Finset.univ.filter
          (fun x : ParityVertices p => x.val k = b ∧ g x ≠ 0)).card := by
  classical
  obtain ⟨p, hpC, hpD, g, hg, hgU, hker⟩ :=
    exists_eight_axis_complement_word k hsep hcard hc hd hrC hrD hbC hbD
  have hreg := separated_union_regular hsep hrC hrD
  have hbalanced := separated_union_balanced hsep hbC hbD
  obtain ⟨σ, hsC⟩ := hbC
  obtain ⟨τ, hsD⟩ := hbD
  have hne : extendParity g ≠ 0 := by
    intro h
    exact hg (funext fun x => (extendParity_apply g x).symm.trans (congrFun h x.val))
  have hU : ∀ x ∈ C ∪ D, extendParity g x = 0 := by
    intro x hx
    by_cases hp : parity x = p
    · exact (extendParity_apply g ⟨x, hp⟩).trans (hgU _ hx)
    · exact extendParity_off g hp
  obtain ⟨b, hb⟩ := exists_twelve_le_binaryFaceSupport_card k (C ∪ D) (extendParity g) hne hU
    (fun y hy => (directions_card _ y).symm.trans (regular_directions _ hreg hy))
    (fun y hy => ⟨exterior_has_selected_neighbor hsep hcard hc hd hrC hrD hsC hsD y hy,
      directions_card _ y ▸ exterior_even _ hreg hbalanced y hy⟩)
    ⟨p, fun x hx => by_contradiction (fun hp => hx (extendParity_off g hp))⟩
    (active_flip_sum_eq_zero k g hker)
  exact ⟨p, hpC, hpD, g, hg, hgU, hker, b, card_binaryFaceSupport_extendParity k b p g ▸ hb⟩

#print axioms exists_eight_axis_complement_word_face_support

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9BinaryComplementSupport
