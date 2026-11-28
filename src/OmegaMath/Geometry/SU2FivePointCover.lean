import OmegaBuild.Commands
import OmegaMath.Geometry.SphericalJung
import OmegaMath.Geometry.UnitQuaternionMetric

compile_only_with_mathlib

/-! Omega original.

Five points of the round three-sphere fit in a cap of cosine `-1/4`.
The proof treats a zero barycentric weight without a nondegeneracy assumption.
-/

open scoped Quaternion InnerProductSpace
open Set Real

noncomputable section

namespace Omega.Geometry.SphericalJung

/-- A family with cardinality at most the ambient dimension has a unit
normal to its affine differences, hence a constant projection. -/
theorem exists_unit_constant_projection {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] [Nonempty ι] (q : ι → E)
    (hn : Fintype.card ι ≤ Module.finrank ℝ E) :
    ∃ v : E, ‖v‖ = 1 ∧ ∀ i j, ⟪v, q i⟫_ℝ = ⟪v, q j⟫_ℝ := by
  let K := vectorSpan ℝ (range q)
  have hK : Module.finrank ℝ K < Module.finrank ℝ E := by
    change Module.finrank ℝ (vectorSpan ℝ (range q)) < _
    have hdim := finrank_vectorSpan_range_add_one_le ℝ q
    omega
  have horth := K.finrank_add_finrank_orthogonal
  obtain ⟨w, hw⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).mp
    (show 0 < Module.finrank ℝ Kᗮ by omega)
  have hw₀ : ‖(w : E)‖ ≠ 0 := norm_ne_zero_iff.mpr (fun h => hw (Subtype.ext h))
  refine ⟨‖(w : E)‖⁻¹ • (w : E), by simp [norm_smul, hw₀], fun i j => ?_⟩
  have hmem : q i - q j ∈ K := vsub_mem_vectorSpan ℝ (mem_range_self i) (mem_range_self j)
  have hz := (Submodule.mem_orthogonal K (w : E)).mp w.property _ hmem
  rw [real_inner_comm, inner_sub_right, sub_eq_zero] at hz
  simp only [real_inner_smul_left, hz]

end Omega.Geometry.SphericalJung

namespace Omega.Geometry.SU2Caratheodory

open UnitQuaternion
local notation "U" => unitary ℍ[ℝ]

/-- Every five unit quaternions have a common cap with cosine `-1/4`. -/
theorem exists_five_point_center (q : Fin 5 → U) :
    ∃ c : U, ∀ i, roundDist (q i) c ≤ arccos (-(1 / 4 : ℝ)) := by
  classical
  let x (i : Fin 5) := (q i : ℍ[ℝ])
  suffices ∃ v : ℍ[ℝ], ‖v‖ = 1 ∧ ∀ i, -(1 / 4 : ℝ) ≤ ⟪v, x i⟫_ℝ by
    obtain ⟨v, hv, h⟩ := this
    refine ⟨ofUnit v hv, fun i => (round_le_iff _ _ (arccos_nonneg _) (arccos_le_pi _)).2 ?_⟩
    simpa only [coe_ofUnit, real_inner_comm, cos_arccos (by norm_num : (-1 : ℝ) ≤ -(1 / 4))
      (by norm_num : -(1 / 4 : ℝ) ≤ 1)] using h i
  by_cases hz : (0 : ℍ[ℝ]) ∈ convexHull ℝ (range x)
  · obtain ⟨w, hw, hw₁, hwz⟩ := SphericalJung.exists_weights_of_mem_convexHull hz
    obtain ⟨k, hk⟩ : ∃ k, w k ≤ 1 / 5 := by
      by_contra! h
      have ht : (1 : ℝ) < ∑ i, w i := by
        calc
          1 = ∑ _ : Fin 5, (1 / 5 : ℝ) := by norm_num
          _ < _ := Finset.sum_lt_sum (fun i _ => (h i).le) ⟨0, by simp, h 0⟩
      linarith
    obtain ⟨v, hv, he⟩ := SphericalJung.exists_unit_constant_projection
      (fun i : Fin 4 => x (k.succAbove i)) (by rw [Quaternion.finrank_eq_four]; decide)
    let u := if 0 ≤ ⟪v, x k⟫_ℝ then v else -v
    have hu : ‖u‖ = 1 := by dsimp [u]; split_ifs <;> simpa using hv
    have hnon : 0 ≤ ⟪u, x k⟫_ℝ := by
      dsimp [u]
      split_ifs with h
      · exact h
      · rw [inner_neg_left]
        linarith
    let h := ⟪u, x (k.succAbove 0)⟫_ℝ
    have heq (i : Fin 5) (hi : i ≠ k) : ⟪u, x i⟫_ℝ = h := by
      obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hi
      dsimp only [u, h]
      split_ifs
      · exact he j 0
      · simpa only [inner_neg_left] using congrArg Neg.neg (he j 0)
    have hsum : (1 - w k) * h + w k * ⟪u, x k⟫_ℝ = 0 := by
      have hs : ∑ i, w i * ⟪u, x i⟫_ℝ = 0 := by
        simp only [← real_inner_smul_right, ← inner_sum, hwz, inner_zero_right]
      have hs' : (∑ i, w i * ⟪u, x i⟫_ℝ) =
          (∑ i ∈ Finset.univ.erase k, w i) * h + w k * ⟪u, x k⟫_ℝ := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k), Finset.sum_mul]
        congr 1
        exact Finset.sum_congr rfl (fun i hi => by rw [heq i (Finset.mem_erase.mp hi).1])
      have hw' : (∑ i ∈ Finset.univ.erase k, w i) = 1 - w k := by
        have hs := Finset.sum_erase_add (s := Finset.univ) w (Finset.mem_univ k)
        rw [hw₁] at hs
        linarith
      rwa [hs', hw'] at hs
    have hupper : ⟪u, x k⟫_ℝ ≤ 1 := by simpa [hu, x, norm_coe] using real_inner_le_norm u (x k)
    have hlow : -(1 / 4 : ℝ) ≤ h := by
      have hprod := mul_le_mul_of_nonneg_left hupper (hw k)
      nlinarith [hw k]
    refine ⟨u, hu, fun i => ?_⟩
    by_cases hi : i = k
    · subst i
      linarith
    · rw [heq i hi]
      exact hlow
  · obtain ⟨v, hv, hcap⟩ := SphericalJung.exists_cap x 4 (by decide)
      (.inr (by rw [Quaternion.finrank_eq_four])) (fun _ => norm_coe _) (by norm_num : (-1 : ℝ) ≤ 1)
      (fun i j _ => (real_inner_mem_Icc_of_norm_eq_one (norm_coe (q i)) (norm_coe (q j))).1) hz
    refine ⟨v, hv, fun i => ?_⟩
    have h := hcap i
    norm_num at h
    linarith

/-- Families with fewer than five points are padded using a surjection. -/
theorem exists_center_card_le_five {ι : Type*} [Fintype ι] [Nonempty ι]
    (q : ι → U) (hcard : Fintype.card ι ≤ 5) :
    ∃ c : U, ∀ i, roundDist (q i) c ≤ arccos (-(1 / 4 : ℝ)) := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card ι ≤ Fintype.card (Fin 5) by simpa using hcard)
  obtain ⟨c, hc⟩ := exists_five_point_center (fun i => q (Function.invFun e i))
  refine ⟨c, fun i => ?_⟩
  obtain ⟨j, rfl⟩ := Function.invFun_surjective e.injective i
  exact hc j

end Omega.Geometry.SU2Caratheodory
