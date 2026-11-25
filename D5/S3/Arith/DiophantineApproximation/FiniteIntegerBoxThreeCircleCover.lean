/- GID: D5/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/FiniteIntegerBoxThreeCircleCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A missed strict phase window on a closed three-axis integer box forces a joint squared resonance of at most 43/9. -/
module

public import D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
import Mathlib.Tactic

/-!
Apply the four-dimensional integral-dual covering bound to a triangular lattice
using the basis construction of `FiniteRectangleCircleCover`. Padding each
axis by two recovers the full closed integer box from a strict distance bound
and makes the resulting resonance denominator nonzero.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Module WithLp
open scoped BigOperators RealInnerProductSpace

namespace D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover

private abbrev E := EuclideanSpace ℝ (Fin 4)

private noncomputable abbrev standard : Basis (Fin 4) ℝ E :=
  (EuclideanSpace.basisFun (Fin 4) ℝ).toBasis

private theorem standard_apply (k l : Fin 4) :
    standard k l = if l = k then 1 else 0 := by
  change EuclideanSpace.basisFun (Fin 4) ℝ k l = _
  rw [EuclideanSpace.basisFun_apply]
  exact PiLp.single_apply 2 ℝ k 1 l

private def coords (u : Fin 3 → ℝ) (z : ℝ) : E :=
  toLp 2 (Fin.snoc (α := fun _ => ℝ) u z)

private theorem coords_castSucc (u : Fin 3 → ℝ) (z : ℝ) (i : Fin 3) :
    coords u z i.castSucc = u i :=
  Fin.snoc_castSucc (α := fun _ => ℝ) z u i

private theorem coords_last (u : Fin 3 → ℝ) (z : ℝ) :
    coords u z (Fin.last 3) = z :=
  Fin.snoc_last (α := fun _ => ℝ) z u

private theorem coords_ext {x y : E}
    (haxes : ∀ i : Fin 3, x i.castSucc = y i.castSucc)
    (hlast : x (Fin.last 3) = y (Fin.last 3)) : x = y :=
  PiLp.ext (Fin.lastCases (motive := fun k => x k = y k) hlast haxes)

private noncomputable def boxEquiv (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) : E ≃ₗ[ℝ] E where
  toFun z := coords (fun i => z i.castSucc / R i)
    (((∑ i : Fin 3, z i.castSucc * θ i) - z (Fin.last 3)) / w)
  invFun z := coords (fun i => R i * z i.castSucc)
    ((∑ i : Fin 3, R i * z i.castSucc * θ i) - w * z (Fin.last 3))
  left_inv z := by
    have cancelAxis (i : Fin 3) (a : ℝ) : R i * (a / R i) = a := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ (hR i)]
    have cancelLast (a : ℝ) : w * (a / w) = a := by
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hw]
    apply coords_ext
    · intro i
      simp only [coords_castSucc, cancelAxis]
    · simp only [coords_last, coords_castSucc, cancelAxis, cancelLast]
      ring
  right_inv z := by
    have cancelAxis (i : Fin 3) (a : ℝ) : R i * a / R i = a :=
      mul_div_cancel_left₀ _ (hR i)
    apply coords_ext
    · intro i
      simp only [coords_castSucc, cancelAxis]
    · simp only [coords_last, coords_castSucc, sub_sub_cancel, mul_div_cancel_left₀ _ hw]
  map_add' x y := by
    apply coords_ext
    · intro i
      simp only [coords_castSucc, PiLp.add_apply, add_div]
    · simp only [coords_last, PiLp.add_apply, add_mul, Finset.sum_add_distrib, ← add_div]
      congr 1
      ring
  map_smul' c x := by
    apply coords_ext
    · intro i
      simp only [coords_castSucc, RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, mul_div_assoc]
    · simp only [coords_last, RingHom.id_apply, PiLp.smul_apply, smul_eq_mul, ← mul_div_assoc]
      congr 1
      simp only [mul_sub, Finset.mul_sum, mul_assoc]

private noncomputable def boxBasis (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) : Basis (Fin 4) ℝ E :=
  standard.map (boxEquiv R θ w hR hw)

private theorem boxBasis_axis (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) (i : Fin 3) :
    boxBasis R θ w hR hw i.castSucc =
      (1 / R i) • standard i.castSucc + (θ i / w) • standard (Fin.last 3) := by
  change boxEquiv R θ w hR hw (standard i.castSucc) = _
  apply coords_ext
  · intro k
    change coords (fun a => standard i.castSucc a.castSucc / R a) _ k.castSucc = _
    simp only [coords_castSucc, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      standard_apply, Fin.castSucc_inj, Fin.castSucc_ne_last, ite_false, mul_zero, add_zero]
    by_cases hk : k = i
    · subst k
      simp only [ite_true, mul_one]
    · simp only [hk, ite_false, zero_div, mul_zero]
  · have hsum : (∑ k : Fin 3, standard i.castSucc k.castSucc * θ k) = θ i := by
      simp only [standard_apply, Fin.castSucc_inj, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    change coords _ (((∑ k : Fin 3, standard i.castSucc k.castSucc * θ k) -
      standard i.castSucc (Fin.last 3)) / w) (Fin.last 3) = _
    rw [coords_last, hsum]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, standard_apply,
      Ne.symm (Fin.castSucc_ne_last i), ite_false, ite_true, sub_zero, mul_zero, mul_one, zero_add]

private theorem boxBasis_last (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) :
    boxBasis R θ w hR hw (Fin.last 3) =
      ((-1 : ℝ) / w) • standard (Fin.last 3) := by
  change boxEquiv R θ w hR hw (standard (Fin.last 3)) = _
  apply coords_ext
  · intro i
    change coords (fun k => standard (Fin.last 3) k.castSucc / R k) _ i.castSucc = _
    simp only [coords_castSucc, PiLp.smul_apply, smul_eq_mul, standard_apply,
      Fin.castSucc_ne_last, ite_false, zero_div, mul_zero]
  · change coords _ (((∑ k : Fin 3, standard (Fin.last 3) k.castSucc * θ k) -
      standard (Fin.last 3) (Fin.last 3)) / w) (Fin.last 3) = _
    simp only [coords_last, PiLp.smul_apply, smul_eq_mul, standard_apply,
      Fin.castSucc_ne_last, ite_false, zero_mul, Finset.sum_const_zero, ite_true, zero_sub, mul_one]

private theorem box_point (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) {v : E}
    (hv : v ∈ Submodule.span ℤ (Set.range (boxBasis R θ w hR hw))) :
    ∃ (b : Fin 3 → ℤ) (m : ℤ),
      v = coords (fun i => (b i : ℝ) / R i)
        (((∑ i, (b i : ℝ) * θ i) - (m : ℝ)) / w) := by
  classical
  let g := boxBasis R θ w hR hw
  let e := boxEquiv R θ w hR hw
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  have hstandard : (∑ k, (z k : ℝ) • standard k) = toLp 2 (fun k => (z k : ℝ)) := by
    simpa only [standard, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, PiLp.toLp_apply] using
      standard.sum_repr (toLp 2 (fun k => (z k : ℝ)))
  have hsum : (∑ k, z k • g k) = e (toLp 2 (fun k => (z k : ℝ))) := by
    rw [← hstandard, map_sum]
    simp only [g, boxBasis, e, Basis.map_apply, Int.cast_smul_eq_zsmul, map_zsmul]
  exact ⟨fun i => z i.castSucc, z (Fin.last 3), hz.symm.trans hsum⟩

private theorem dual_coordinates (R θ : Fin 3 → ℝ) (w : ℝ)
    (hR : ∀ i, R i ≠ 0) (hw : w ≠ 0) {y : E}
    (hy : y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E)
      (Submodule.span ℤ (Set.range (boxBasis R θ w hR hw)))) :
    ∃ (h : ℤ) (j : Fin 3 → ℤ),
      (∀ i, y i.castSucc = R i * ((j i : ℝ) - (h : ℝ) * θ i)) ∧
      y (Fin.last 3) = w * (h : ℝ) := by
  classical
  have hpair := (LinearMap.BilinForm.mem_dualSubmodule (innerₗ E)).mp hy
  have hint (k : Fin 4) : ∃ m : ℤ, (m : ℝ) = inner ℝ y (boxBasis R θ w hR hw k) :=
    Submodule.mem_one.mp (hpair _ (Submodule.subset_span ⟨k, rfl⟩))
  obtain ⟨m, hm⟩ := hint (Fin.last 3)
  have hint_axes (i : Fin 3) : ∃ a : ℤ,
      (a : ℝ) = inner ℝ y (boxBasis R θ w hR hw i.castSucc) := hint i.castSucc
  choose j hj using hint_axes
  have hm' : (m : ℝ) * w = -y (Fin.last 3) := by
    apply (eq_div_iff hw).mp
    rw [hm, boxBasis_last, real_inner_smul_right]
    change ((-1 : ℝ) / w) * inner ℝ y (EuclideanSpace.basisFun (Fin 4) ℝ (Fin.last 3)) = _
    rw [EuclideanSpace.inner_basisFun_real]
    ring
  let h : ℤ := -m
  have hyLast : y (Fin.last 3) = w * (h : ℝ) := by
    dsimp only [h]
    rw [Int.cast_neg, mul_neg, mul_comm w, hm', neg_neg]
  refine ⟨h, j, ?_, hyLast⟩
  intro i
  have hji : (j i : ℝ) = y i.castSucc / R i + (h : ℝ) * θ i := by
    calc
      _ = (1 / R i) * y i.castSucc + (θ i / w) * y (Fin.last 3) := by
        simp only [hj i, boxBasis_axis, inner_add_right, real_inner_smul_right, standard,
          OrthonormalBasis.coe_toBasis, EuclideanSpace.inner_basisFun_real]
      _ = _ := by
        rw [hyLast]
        field_simp [hR i, hw]
  have hmul := (eq_div_iff (hR i)).mp
    (show (j i : ℝ) - (h : ℝ) * θ i = y i.castSucc / R i by linarith only [hji])
  exact hmul.symm.trans (mul_comm _ _)

private theorem of_half_close {center value scale : ℝ} (hscale : 0 < scale)
    (hclose : |center / scale - value / scale| < 1 / 2) :
    center - scale / 2 < value ∧ value < center + scale / 2 := by
  rw [div_sub_div_same] at hclose
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hclose
  have hlo' := (lt_div_iff₀ hscale).mp hlo
  have hhi' := (div_lt_iff₀ hscale).mp hhi
  constructor <;> linarith only [hlo', hhi']

public section

/-- A missed strict phase window on the closed three-axis integer box forces a
positive common resonance with the padded joint squared bound `43 / 9`. -/
theorem finite_integer_box_inverse_three
    (N : Fin 3 → ℤ) (hN : ∀ i, 1 ≤ N i)
    (θ : Fin 3 → ℝ) (t w : ℝ) (hw : 0 < w)
    (hmiss : ¬ ∃ (b : Fin 3 → ℤ) (m : ℤ),
      (∀ i, N i ≤ b i ∧ b i ≤ 2 * N i) ∧
      t < (∑ i, (b i : ℝ) * θ i) - (m : ℝ) ∧
      (∑ i, (b i : ℝ) * θ i) - (m : ℝ) < t + w) :
    ∃ (h : ℤ) (j : Fin 3 → ℤ), 1 ≤ h ∧
      (∑ i, ((N i : ℝ) + 2) ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2) +
        w ^ 2 * (h : ℝ) ^ 2 ≤ 43 / 9 := by
  classical
  let R (i : Fin 3) : ℝ := (N i : ℝ) + 2
  have hR3 (i : Fin 3) : 3 ≤ R i := by
    have hNi : (1 : ℝ) ≤ (N i : ℝ) := by exact_mod_cast hN i
    dsimp only [R]
    linarith only [hNi]
  have hRp (i : Fin 3) : 0 < R i := by linarith only [hR3 i]
  have hR (i : Fin 3) : R i ≠ 0 := (hRp i).ne'
  let g := boxBasis R θ w hR hw.ne'
  let L : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  let : DiscreteTopology L := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range g)))
  let : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range g)))
  let x : E := coords (fun i => (3 * (N i : ℝ) / 2) / R i) ((t + w / 2) / w)
  have hfar (v : E) (hvL : v ∈ L) : (1 / 2 : ℝ) ≤ ‖x - v‖ := by
    by_contra! hdist
    have hcoord (k : Fin 4) : |x k - v k| < (1 / 2 : ℝ) :=
      lt_of_le_of_lt (by
        simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - v) k) hdist
    obtain ⟨b, m, hv⟩ := box_point R θ w hR hw.ne' hvL
    have hbox (i : Fin 3) : N i ≤ b i ∧ b i ≤ 2 * N i := by
      have hi : |(3 * (N i : ℝ) / 2) / R i - (b i : ℝ) / R i| < 1 / 2 := by
        simpa only [x, hv, coords_castSucc] using hcoord i.castSucc
      have hb := of_half_close (hRp i) hi
      dsimp only [R] at hb
      have hlo : (N i : ℝ) - 1 < (b i : ℝ) := by linarith only [hb.1]
      have hhi : (b i : ℝ) < 2 * (N i : ℝ) + 1 := by linarith only [hb.2]
      have hlo' : N i - 1 < b i := by exact_mod_cast hlo
      have hhi' : b i < 2 * N i + 1 := by exact_mod_cast hhi
      omega
    have hz : |(t + w / 2) / w - (((∑ i, (b i : ℝ) * θ i) - (m : ℝ)) / w)| <
        1 / 2 := by
      simpa only [x, hv, coords_last] using hcoord (Fin.last 3)
    have hphase := of_half_close hw hz
    exact hmiss ⟨b, m, hbox, by linarith only [hphase.1], by linarith only [hphase.2]⟩
  obtain ⟨y, hy, hy0, hcover⟩ :=
    D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference.exists_dual_covering_four L
  obtain ⟨v, hvL, hvdist⟩ := hcover x
  have hvSq : (1 / 2 : ℝ) ^ 2 ≤ ‖x - v‖ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (hfar v hvL) 2
  have hySq : ‖y‖ ^ 2 ≤ (43 / 9 : ℝ) := by
    have hquarter := mul_le_mul_of_nonneg_right hvSq (sq_nonneg ‖y‖)
    linarith only [hquarter, hvdist]
  have hyshort : ‖y‖ < (3 : ℝ) := by
    by_contra! hlong
    have hlongSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hlong 2
    linarith only [hlongSq, hySq]
  obtain ⟨h, j, hyAxis, hyLast⟩ := dual_coordinates R θ w hR hw.ne' hy
  have hh0 : h ≠ 0 := by
    intro hh
    have hyAxis' (i : Fin 3) : y i.castSucc = R i * (j i : ℝ) := by
      simpa only [hh, Int.cast_zero, zero_mul, sub_zero] using hyAxis i
    have hj0 (i : Fin 3) : j i = 0 := by
      have habs : |R i * (j i : ℝ)| < 3 := lt_of_le_of_lt
        (by simpa only [hyAxis' i, Real.norm_eq_abs] using PiLp.norm_apply_le y i.castSucc)
        hyshort
      rw [abs_mul, abs_of_pos (hRp i)] at habs
      have hjSmall : |(j i : ℝ)| < 1 := by
        by_contra! hjLarge
        have hmul := mul_le_mul_of_nonneg_left hjLarge (hRp i).le
        linarith only [habs, hmul, hR3 i]
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hjSmall)
    apply hy0
    apply coords_ext
    · intro i
      simp [hyAxis' i, hj0 i]
    · simp only [hyLast, hh, Int.cast_zero, mul_zero, PiLp.zero_apply]
  have hnorm : ‖y‖ ^ 2 =
      (∑ i, R i ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2) + w ^ 2 * (h : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_castSucc, hyLast, mul_pow w (h : ℝ) 2]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [hyAxis i]
    ring
  have hjoint := hnorm ▸ hySq
  change ∃ (h : ℤ) (j : Fin 3 → ℤ), 1 ≤ h ∧
    (∑ i, R i ^ 2 * ((h : ℝ) * θ i - (j i : ℝ)) ^ 2) + w ^ 2 * (h : ℝ) ^ 2 ≤ 43 / 9
  by_cases hh : 1 ≤ h
  · exact ⟨h, j, hh, hjoint⟩
  · refine ⟨-h, fun i => -j i, by omega, ?_⟩
    have haxisNeg (i : Fin 3) :
        (((-h : ℤ) : ℝ) * θ i - ((-j i : ℤ) : ℝ)) ^ 2 =
          ((h : ℝ) * θ i - (j i : ℝ)) ^ 2 := by
      push_cast
      ring
    change (∑ i, R i ^ 2 * (((-h : ℤ) : ℝ) * θ i - ((-j i : ℤ) : ℝ)) ^ 2) +
      w ^ 2 * ((-h : ℤ) : ℝ) ^ 2 ≤ 43 / 9
    simp only [haxisNeg]
    simpa only [Int.cast_neg, neg_sq] using hjoint

end

end D5.S3.Arith.DiophantineApproximation.FiniteIntegerBoxThreeCircleCover
