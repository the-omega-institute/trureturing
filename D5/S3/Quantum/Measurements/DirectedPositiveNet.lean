/- GID: D5/S3/Quantum/Measurements/DirectedPositiveNet
   generality: G
   mirror-B: D5/B/S3/Quantum/Measurements/DirectedPositiveNet
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Positive increasing directed operator nets converge strongly to their order supremum. -/

import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic

namespace D5.S3.Quantum.Measurements.DirectedPositiveNet

open Filter Topology Complex
open scoped InnerProductSpace ComplexOrder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A positive increasing directed net converges strongly to its operator-order supremum. -/
theorem directed_positive_net_strong_of_isLUB
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {J : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
    (X : J → H →L[ℂ] H) (U : H →L[ℂ] H)
    (hpos : ∀ j, 0 ≤ X j) (hmono : Monotone X)
    (hU : IsLUB (Set.range X) U) :
    (∀ j, ‖X j‖ ≤ ‖U‖) ∧
      (∀ v, Tendsto (fun j => X j v) atTop (𝓝 (U v))) := by
  classical
  have hupper (j : J) : X j ≤ U := hU.1 ⟨j, rfl⟩
  have hnorm (j : J) : ‖X j‖ ≤ ‖U‖ :=
    CStarAlgebra.norm_le_norm_of_le_of_nonneg (hupper j) (hpos j)
  -- The positive square estimate is used on actual differences X k - X i.
  have square_estimate (D : H →L[ℂ] H) (hD : 0 ≤ D) (v : H) :
      ‖D v‖ ^ 2 ≤ ‖D‖ * (⟪D v, v⟫_ℂ).re := by
    let R : H →L[ℂ] H := CFC.sqrt D
    have hRpos : 0 ≤ R := CFC.sqrt_nonneg D
    have hRR : R * R = D := CFC.sqrt_mul_sqrt_self D hD
    have hRsa : star R = R := (IsSelfAdjoint.of_nonneg hRpos).star_eq
    have hRsym := ((ContinuousLinearMap.nonneg_iff_isPositive (f := R)).mp hRpos).isSymmetric
    have hRnorm : ‖R‖ ^ 2 = ‖D‖ := by
      rw [pow_two, ← CStarRing.norm_star_mul_self, hRsa, hRR]
    have hRv : ‖R v‖ ^ 2 = (⟪D v, v⟫_ℂ).re := by
      rw [← hRR]
      change ‖R v‖ ^ 2 = (⟪R (R v), v⟫_ℂ).re
      have heq : ⟪R (R v), v⟫_ℂ = ⟪R v, R v⟫_ℂ := hRsym (R v) v
      rw [heq]
      exact (inner_self_eq_norm_sq (𝕜 := ℂ) (R v)).symm
    have hop := R.le_opNorm (R v)
    have hsq := mul_self_le_mul_self (norm_nonneg _) hop
    calc
      ‖D v‖ ^ 2 = ‖R (R v)‖ ^ 2 := by rw [← hRR]; rfl
      _ ≤ (‖R‖ * ‖R v‖) ^ 2 := by simpa only [pow_two] using hsq
      _ = ‖D‖ * (⟪D v, v⟫_ℂ).re := by rw [mul_pow, hRnorm, hRv]
  let q : H → J → ℝ := fun v j => (⟪X j v, v⟫_ℂ).re
  have qmono (v : H) : Monotone (q v) := by
    intro i j hij
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive (f := (X j - X i))).mp
      (sub_nonneg.mpr (hmono hij))).re_inner_nonneg_left v
    change 0 ≤ (⟪(X j - X i) v, v⟫_ℂ).re at h
    simpa only [sub_apply, inner_sub_left, Complex.sub_re,
      sub_nonneg, q] using h
  have qbdd (v : H) : BddAbove (Set.range (q v)) := by
    refine ⟨(⟪U v, v⟫_ℂ).re, ?_⟩
    rintro _ ⟨j, rfl⟩
    have h := ((ContinuousLinearMap.nonneg_iff_isPositive (f := (U - X j))).mp
      (sub_nonneg.mpr (hupper j))).re_inner_nonneg_left v
    change 0 ≤ (⟪(U - X j) v, v⟫_ℂ).re at h
    simpa only [sub_apply, inner_sub_left, Complex.sub_re,
      sub_nonneg, q] using h
  let Q : H → ℝ := fun v => ⨆ j, q v j
  have qlim (v : H) : Tendsto (q v) atTop (𝓝 (Q v)) :=
    tendsto_atTop_ciSup (qmono v) (qbdd v)
  have qle (v : H) (j : J) : q v j ≤ Q v := le_ciSup (qbdd v) j
  let C : ℝ := ‖U‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hcauchy (v : H) : Cauchy (Filter.map (fun j => X j v) atTop) := by
    apply Metric.cauchy_iff.mpr
    refine ⟨inferInstance, ?_⟩
    intro ε hε
    let δ : ℝ := ε ^ 2 / (16 * C)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    have hevent : ∀ᶠ j in atTop, Q v - q v j < δ := by
      have ht : Tendsto (fun j => Q v - q v j) atTop (𝓝 (Q v - Q v)) :=
        tendsto_const_nhds.sub (qlim v)
      have hz : Tendsto (fun j => Q v - q v j) atTop (𝓝 0) := by simpa using ht
      exact (tendsto_order.mp hz).2 δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
    -- Directedness, rather than a max operation, provides the common upper index.
    have hsmall (i k : J) (hi : N ≤ i) (hik : i ≤ k) :
        ‖X k v - X i v‖ < ε / 2 := by
      let D : H →L[ℂ] H := X k - X i
      have hD : 0 ≤ D := sub_nonneg.mpr (hmono hik)
      have hDU : D ≤ U := by
        exact (sub_le_self _ (hpos i)).trans (hupper k)
      have hDn : ‖D‖ ≤ C :=
        (CStarAlgebra.norm_le_norm_of_le_of_nonneg hDU hD).trans
          (by dsimp [C]; linarith)
      have hDq : (⟪D v, v⟫_ℂ).re = q v k - q v i := by
        simp only [D, q, sub_apply, inner_sub_left, Complex.sub_re]
      have hgap0 : 0 ≤ q v k - q v i := sub_nonneg.mpr (qmono v hik)
      have hgap : q v k - q v i ≤ Q v - q v i := sub_le_sub_right (qle v k) _
      have hsq : ‖X k v - X i v‖ ^ 2 ≤ C * (Q v - q v i) := by
        change ‖D v‖ ^ 2 ≤ _
        calc
          ‖D v‖ ^ 2 ≤ ‖D‖ * (q v k - q v i) := by
            simpa only [hDq] using square_estimate D hD v
          _ ≤ C * (Q v - q v i) := mul_le_mul hDn hgap hgap0 hC.le
      have hstrict : C * (Q v - q v i) < ε ^ 2 / 16 := by
        calc
          C * (Q v - q v i) < C * δ := mul_lt_mul_of_pos_left (hN i hi) hC
          _ = ε ^ 2 / 16 := by dsimp [δ]; field_simp [ne_of_gt hC]
      nlinarith [norm_nonneg (X k v - X i v)]
    let t : Set H := (fun j => X j v) '' Set.Ici N
    refine ⟨t, ?_, ?_⟩
    · apply Filter.mem_map.mpr
      exact Filter.mem_of_superset (Ici_mem_atTop N) fun j hj => ⟨j, hj, rfl⟩
    · rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
      obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
      calc
        dist (X i v) (X j v) ≤ dist (X i v) (X k v) + dist (X k v) (X j v) :=
          dist_triangle _ _ _
        _ = ‖X k v - X i v‖ + ‖X k v - X j v‖ := by
          rw [dist_comm (X i v) (X k v), dist_eq_norm, dist_eq_norm]
        _ < ε / 2 + ε / 2 := add_lt_add (hsmall i k hi hik) (hsmall j k hj hjk)
        _ = ε := by ring
  have hlimits (v : H) : ∃ w, Tendsto (fun j => X j v) atTop (𝓝 w) :=
    cauchy_map_iff_exists_tendsto.mp (hcauchy v)
  choose s hs using hlimits
  let Slin : H →ₗ[ℂ] H :=
    { toFun := s
      map_add' := fun v w => by
        have ht : Tendsto (fun j => X j (v + w)) atTop (𝓝 (s v + s w)) := by
          simpa only [map_add] using (hs v).add (hs w)
        exact tendsto_nhds_unique (hs (v + w)) ht
      map_smul' := fun c v => by
        have ht : Tendsto (fun j => X j (c • v)) atTop (𝓝 (c • s v)) := by
          simpa only [map_smul, RingHom.id_apply] using (hs v).const_smul c
        exact tendsto_nhds_unique (hs (c • v)) ht }
  have hSbound (v : H) : ‖Slin v‖ ≤ ‖U‖ * ‖v‖ := by
    exact le_of_tendsto (hs v).norm (Eventually.of_forall fun j =>
      ((X j).le_opNorm v).trans (mul_le_mul_of_nonneg_right (hnorm j) (norm_nonneg v)))
  let S : H →L[ℂ] H := Slin.mkContinuous ‖U‖ hSbound
  have hS (v : H) : Tendsto (fun j => X j v) atTop (𝓝 (S v)) := hs v
  have positive_strong_limit (F : J → H →L[ℂ] H) (V : H →L[ℂ] H)
      (hF : ∀ v, Tendsto (fun j => F j v) atTop (𝓝 (V v)))
      (hFpos : ∀ᶠ j in atTop, 0 ≤ F j) : 0 ≤ V := by
    apply (ContinuousLinearMap.nonneg_iff_isPositive (f := V)).mpr
    apply (ContinuousLinearMap.isPositive_iff_complex V).mpr
    intro v
    have hclosed : IsClosed {z : ℂ | 0 ≤ z} := CStarAlgebra.isClosed_nonneg
    have ht : Tendsto (fun j => ⟪F j v, v⟫_ℂ) atTop (𝓝 ⟪V v, v⟫_ℂ) :=
      (hF v).inner tendsto_const_nhds
    have hscalar : 0 ≤ ⟪V v, v⟫_ℂ := by
      exact hclosed.mem_of_tendsto ht
        (hFpos.mono fun j hj =>
          ((ContinuousLinearMap.nonneg_iff_isPositive (f := (F j))).mp hj).inner_nonneg_left v)
    have hr := Complex.nonneg_iff.mp hscalar
    exact ⟨Complex.ext (by simp) (by simpa using hr.2), hr.1⟩
  have hSLUB : IsLUB (Set.range X) S := by
    constructor
    · rintro _ ⟨i, rfl⟩
      apply sub_nonneg.mp
      apply positive_strong_limit (fun j => X j - X i) (S - X i)
      · intro v
        simpa only [sub_apply] using (hS v).sub tendsto_const_nhds
      · exact (eventually_ge_atTop i).mono fun j hij => sub_nonneg.mpr (hmono hij)
    · intro V hV
      apply sub_nonneg.mp
      apply positive_strong_limit (fun j => V - X j) (V - S)
      · intro v
        simpa only [sub_apply] using tendsto_const_nhds.sub (hS v)
      · exact Eventually.of_forall fun j => sub_nonneg.mpr (hV ⟨j, rfl⟩)
  have hSU : S = U := hSLUB.unique hU
  exact ⟨hnorm, fun v => by simpa only [hSU] using hS v⟩

#print axioms directed_positive_net_strong_of_isLUB

end D5.S3.Quantum.Measurements.DirectedPositiveNet
