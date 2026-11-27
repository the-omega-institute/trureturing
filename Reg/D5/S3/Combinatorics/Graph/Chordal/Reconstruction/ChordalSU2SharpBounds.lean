import D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
import D5.S3.Combinatorics.Graph.Chordal.Characterization

/-! Concrete nonflat gains for the unit-quaternion reconstruction bounds. -/

open scoped Quaternion

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds

open SimpleGraph Omega.Geometry.UnitQuaternion Real

noncomputable section

local notation "U" => unitary ℍ[ℝ]

private theorem complete_chordal (n : ℕ) : (⊤ : SimpleGraph (Fin n)).IsChordal := by
  apply IsPEO.isChordal (ord := Fin.val)
  exact ⟨Fin.val_injective, fun _ _ _ _ _ h => h⟩

private theorem complete_clique_bound {n : ℕ} (s : Finset (Fin n))
    (_ : (⊤ : SimpleGraph (Fin n)).IsClique (↑s : Set (Fin n))) : s.card ≤ n := by
  simpa using Finset.card_le_univ s

private def rotation (x : ℝ) : U :=
  ofUnit ⟨cos x, sin x, 0, 0⟩ (by
    have h : ‖(⟨cos x, sin x, 0, 0⟩ : ℍ[ℝ])‖ ^ 2 = 1 := by
      rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
      nlinarith only [sin_sq_add_cos_sq x]
    nlinarith [norm_nonneg (⟨cos x, sin x, 0, 0⟩ : ℍ[ℝ])])

private theorem rotation_distance {x : ℝ} (hx : 0 ≤ x) (hπ : x ≤ π) :
    roundDist (rotation x) 1 = x := by
  unfold roundDist
  change arccos (((↑(rotation x) : ℍ[ℝ]) * star (1 : ℍ[ℝ])).re) = x
  rw [star_one, mul_one]
  exact arccos_cos hx hπ

private def singleEdge {V : Type*} [DecidableEq V] (a b : V) (q : U) (x y : V) : U :=
  if x = a ∧ y = b then q else if x = b ∧ y = a then q⁻¹ else 1

private theorem singleEdge_skew {V : Type*} [DecidableEq V] {a b : V}
    (hab : a ≠ b) (q : U) : (⊤ : SimpleGraph V).SU2Skew (singleEdge a b q) := by
  intro x y hxy
  unfold singleEdge
  split_ifs <;> simp_all

private theorem singleEdge_bound {V : Type*} [DecidableEq V] {a b : V}
    (q : U) {δ : ℝ} (hδ : 0 ≤ δ) (hq : roundDist q 1 ≤ δ) :
    (⊤ : SimpleGraph V).SU2TriangleBound (singleEdge a b q) δ := by
  have hi : roundDist q⁻¹ 1 ≤ δ := by
    simpa only [inv_one] using (round_inv q 1).le.trans hq
  intro x y z hxy hyz hxz
  have hxy' := hxy.ne
  have hyz' := hyz.ne
  have hxz' := hxz.ne
  unfold singleEdge
  split_ifs <;> simp_all [round_comm]

private theorem first_defect {n : ℕ} (hn : 2 ≤ n) :
    (⊤ : SimpleGraph (Fin n)).SU2TriangleBound
      (singleEdge ⟨0, by omega⟩ ⟨1, by omega⟩ (rotation (1 / 10))) (1 / 10) := by
  apply singleEdge_bound _ (by norm_num)
  rw [rotation_distance (by norm_num) (by linarith [pi_gt_three])]

example : (434 / 125 : ℝ) < 7 / 2 ∧ (7 / 2 : ℝ) < 4 ∧ (2 : ℝ) < 434 / 125 := by norm_num

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p ((434 / 125) * (1 / 10)) := by
  apply SimpleGraph.IsChordal.exists_su2_gain_potential_global_sharp (complete_chordal _)
    (by
      refine { preconnected := ?_, nonempty := inferInstance }
      intro x y
      rcases eq_or_ne x y with h | h
      · subst y
        exact Reachable.rfl
      · exact (show (⊤ : SimpleGraph (Fin 3)).Adj x y from h).reachable)
    (singleEdge_skew (by decide) _) (by norm_num)
  exact first_defect (by decide)

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (2 * (1 / 10)) :=
  (complete_chordal _).exists_su2_gain_potential_small_defect_two
    (singleEdge_skew (by decide) _) (by norm_num) (by linarith [pi_gt_three]) (first_defect (by decide))

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p ((8 / 5) * (1 / 10)) :=
  (complete_chordal _).exists_su2_gain_potential_small_defect_eight_fifths
    (singleEdge_skew (by decide) _) (by norm_num) le_rfl (first_defect (by decide))

example :
    ∃ p : Fin 3 → U, (⊤ : SimpleGraph (Fin 3)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (min (1 / 10) (π / 2)) :=
  (complete_chordal _).exists_cliqueThree_su2_gain_potential_min
    (singleEdge_skew (by decide) _) (by norm_num) (first_defect (by decide)) complete_clique_bound

example :
    ∃ p : Fin 4 → U, (⊤ : SimpleGraph (Fin 4)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (2 * (1 / 10)) :=
  (complete_chordal _).exists_cliqueFour_su2_gain_potential_two
    (singleEdge_skew (by decide) _) (by norm_num) (first_defect (by decide)) complete_clique_bound

example :
    ∃ p : Fin 5 → U, (⊤ : SimpleGraph (Fin 5)).SU2Fits
      (singleEdge 0 1 (rotation (1 / 10))) p (π / 2) :=
  (complete_chordal _).exists_cliqueFive_su2_gain_potential_half_pi
    (singleEdge_skew (by decide) _) complete_clique_bound

example : roundDist (singleEdge (0 : Fin 3) 1 (rotation (1 / 10)) 0 1 *
    singleEdge 0 1 (rotation (1 / 10)) 1 2) (singleEdge 0 1 (rotation (1 / 10)) 0 2) = 1 / 10 := by
  simp only [singleEdge]
  norm_num
  exact rotation_distance (by norm_num) (by linarith [pi_gt_three])

end

end Reg.D5.S3.Combinatorics.Graph.Chordal.Reconstruction.ChordalSU2SharpBounds
