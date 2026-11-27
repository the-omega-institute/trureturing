/- GID: D5/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover
   generality: G
   mirror-B: D5/B/S3/Arith/DiophantineApproximation/FiniteRectangleCircleCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A missed closed integer rectangle forces a joint squared resonance of at most 11/3. -/
module

public import D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference
import Mathlib.Tactic

/-!
Apply the direct three-dimensional dual covering bound to a triangular lattice.
The three scaled resonance coordinates satisfy one squared norm bound.
The phase interval has strict endpoints and the integer rectangle is closed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

public section

open Module Set Matrix WithLp
open scoped RealInnerProductSpace

namespace D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover

private abbrev E := EuclideanSpace ℝ (Fin 3)

private noncomputable abbrev standard : Basis (Fin 3) ℝ E :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis

/-- Coordinates in the domain are ordered `(b,d,a)`. -/
private noncomputable def rectangleEquiv (N M theta phi w : ℝ)
    (hN : N ≠ 0) (hM : M ≠ 0) (hw : w ≠ 0) : E ≃ₗ[ℝ] E where
  toFun z := toLp 2 ![z 0 / N, z 1 / M, (z 0 * theta + z 1 * phi - z 2) / w]
  invFun z := toLp 2 ![N * z 0, M * z 1, N * z 0 * theta + M * z 1 * phi - w * z 2]
  left_inv z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> field_simp [hN, hM, hw] <;> ring
  right_inv z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> field_simp [hN, hM, hw]
  map_add' z u := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp <;> ring
  map_smul' c z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [smul_eq_mul] <;> ring

private noncomputable def rectangleBasis (N M theta phi w : ℝ)
    (hN : N ≠ 0) (hM : M ≠ 0) (hw : w ≠ 0) : Basis (Fin 3) ℝ E :=
  standard.map (rectangleEquiv N M theta phi w hN hM hw)

/-- Reading the actual integral coordinates of a lattice point. -/
private theorem rectangle_point (N M theta phi w : ℝ)
    (hN : N ≠ 0) (hM : M ≠ 0) (hw : w ≠ 0) {v : E}
    (hv : v ∈ Submodule.span ℤ
      (Set.range (rectangleBasis N M theta phi w hN hM hw))) :
    ∃ b d a : ℤ, v = toLp 2 ![(b : ℝ) / N, (d : ℝ) / M,
      ((b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ)) / w] := by
  classical
  let g := rectangleBasis N M theta phi w hN hM hw
  let e := rectangleEquiv N M theta phi w hN hM hw
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hv
  have hstandard : (∑ i, (z i : ℝ) • standard i) = toLp 2 (fun i => (z i : ℝ)) := by
    simpa only [standard, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr, PiLp.toLp_apply] using
      standard.sum_repr (toLp 2 (fun i => (z i : ℝ)))
  have hsum : (∑ i, z i • g i) = e (toLp 2 (fun i => (z i : ℝ))) := by
    rw [← hstandard, map_sum]
    simp only [g, rectangleBasis, e, Basis.map_apply, Int.cast_smul_eq_zsmul, map_zsmul]
  refine ⟨z 0, z 1, z 2, ?_⟩
  exact hz.symm.trans hsum

/-- Each integral-dual vector has the precise triangular integer parametrization.
Only the direction used by the inverse theorem is asserted. -/
private theorem dual_coordinates (N M theta phi w : ℝ)
    (hN : N ≠ 0) (hM : M ≠ 0) (hw : w ≠ 0) {y : E}
    (hy : y ∈ LinearMap.BilinForm.dualSubmodule (innerₗ E)
      (Submodule.span ℤ (Set.range (rectangleBasis N M theta phi w hN hM hw)))) :
    ∃ h j k : ℤ,
      y 0 = N * ((j : ℝ) - (h : ℝ) * theta) ∧
      y 1 = M * ((k : ℝ) - (h : ℝ) * phi) ∧ y 2 = w * (h : ℝ) := by
  classical
  let g := rectangleBasis N M theta phi w hN hM hw
  have hg0 : g 0 = toLp 2 ![1 / N, 0, theta / w] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [g, rectangleBasis, rectangleEquiv, standard,
      EuclideanSpace.basisFun_apply, PiLp.toLp_apply]
  have hg1 : g 1 = toLp 2 ![0, 1 / M, phi / w] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [g, rectangleBasis, rectangleEquiv, standard,
      EuclideanSpace.basisFun_apply, PiLp.toLp_apply]
  have hg2 : g 2 = toLp 2 ![0, 0, -1 / w] := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [g, rectangleBasis, rectangleEquiv, standard,
      EuclideanSpace.basisFun_apply, PiLp.toLp_apply]
  have hip (a b c : ℝ) : inner ℝ y (toLp 2 ![a, b, c]) =
      y 0 * a + y 1 * b + y 2 * c := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_three]
    ring
  have hpair := (LinearMap.BilinForm.mem_dualSubmodule (innerₗ E)).mp hy
  obtain ⟨j, hj⟩ := Submodule.mem_one.mp (hpair (g 0) (Submodule.subset_span ⟨0, rfl⟩))
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hpair (g 1) (Submodule.subset_span ⟨1, rfl⟩))
  obtain ⟨m, hm⟩ := Submodule.mem_one.mp (hpair (g 2) (Submodule.subset_span ⟨2, rfl⟩))
  have hj' : (j : ℝ) = y 0 / N + y 2 * theta / w := by
    calc
      _ = inner ℝ y (g 0) := hj
      _ = _ := by rw [hg0, hip]; ring
  have hk' : (k : ℝ) = y 1 / M + y 2 * phi / w := by
    calc
      _ = inner ℝ y (g 1) := hk
      _ = _ := by rw [hg1, hip]; ring
  have hm' : (m : ℝ) * w = -y 2 := by
    apply (eq_div_iff hw).mp
    calc
      (m : ℝ) = inner ℝ y (g 2) := hm
      _ = -y 2 / w := by rw [hg2, hip]; ring
  let h : ℤ := -m
  have hy2 : y 2 = w * (h : ℝ) := by
    dsimp only [h]
    push_cast
    nlinarith only [hm']
  have hj'' : (j : ℝ) = y 0 / N + (h : ℝ) * theta := by
    rw [hj', hy2]
    field_simp [hN, hw]
  have hk'' : (k : ℝ) = y 1 / M + (h : ℝ) * phi := by
    rw [hk', hy2]
    field_simp [hM, hw]
  refine ⟨h, j, k, ?_, ?_, hy2⟩
  · have hh := (eq_div_iff hN).mp
      (show (j : ℝ) - (h : ℝ) * theta = y 0 / N by linarith only [hj''])
    exact hh.symm.trans (mul_comm _ _)
  · have hh := (eq_div_iff hM).mp
      (show (k : ℝ) - (h : ℝ) * phi = y 1 / M by linarith only [hk''])
    exact hh.symm.trans (mul_comm _ _)

/-- A miss of the closed integer rectangle and strict phase window forces a
positive integer resonance with joint squared bound `11 / 3`. -/
theorem finite_rectangle_inverse (N M : ℕ) (hN : 2 ≤ N) (hM : 2 ≤ M)
    (theta phi t w : ℝ) (hw : 0 < w ∧ w < 1)
    (hmiss : ¬ ∃ b d : ℕ, ∃ a : ℤ,
      N ≤ b ∧ b ≤ 2 * N ∧ M ≤ d ∧ d ≤ 2 * M ∧
      t < (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) ∧
      (b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ) < t + w) :
    ∃ h j k : ℤ, 1 ≤ h ∧
      (N : ℝ) ^ 2 * ((h : ℝ) * theta - (j : ℝ)) ^ 2 +
        (M : ℝ) ^ 2 * ((h : ℝ) * phi - (k : ℝ)) ^ 2 + w ^ 2 * (h : ℝ) ^ 2 ≤ 11 / 3 := by
  classical
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMr : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hNp : 0 < (N : ℝ) := by linarith
  have hMp : 0 < (M : ℝ) := by linarith
  let g := rectangleBasis (N : ℝ) (M : ℝ) theta phi w hNp.ne' hMp.ne' hw.1.ne'
  let L : Submodule ℤ E := Submodule.span ℤ (Set.range g)
  let : DiscreteTopology L := inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range g)))
  let : IsZLattice ℝ L := inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range g)))
  let x : E := toLp 2 ![3 / 2, 3 / 2, (t + w / 2) / w]
  have hfar (v : E) (hvL : v ∈ L) : (1 / 2 : ℝ) ≤ ‖x - v‖ := by
    by_contra! hdist
    have hcoord (i : Fin 3) : |x i - v i| < (1 / 2 : ℝ) := by
      exact lt_of_le_of_lt
        (by simpa only [PiLp.sub_apply, Real.norm_eq_abs] using PiLp.norm_apply_le (x - v) i) hdist
    obtain ⟨b, d, a, hv⟩ :=
      rectangle_point (N : ℝ) (M : ℝ) theta phi w hNp.ne' hMp.ne' hw.1.ne' hvL
    have hbclose : |(3 / 2 : ℝ) - (b : ℝ) / (N : ℝ)| < 1 / 2 := by
      simpa only [x, hv, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hcoord 0
    have hdclose : |(3 / 2 : ℝ) - (d : ℝ) / (M : ℝ)| < 1 / 2 := by
      simpa only [x, hv, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one] using hcoord 1
    have hzclose : |(t + w / 2) / w -
        ((b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ)) / w| < 1 / 2 := by
      simpa only [x, hv, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using hcoord 2
    have hbfrac : 1 < (b : ℝ) / (N : ℝ) ∧ (b : ℝ) / (N : ℝ) < 2 := by
      obtain ⟨hl, hu⟩ := abs_lt.mp hbclose
      constructor <;> linarith
    have hdfrac : 1 < (d : ℝ) / (M : ℝ) ∧ (d : ℝ) / (M : ℝ) < 2 := by
      obtain ⟨hl, hu⟩ := abs_lt.mp hdclose
      constructor <;> linarith
    have hbN : (N : ℝ) < (b : ℝ) := by
      simpa only [one_mul] using (lt_div_iff₀ hNp).mp hbfrac.1
    have hb2N : (b : ℝ) < 2 * (N : ℝ) := (div_lt_iff₀ hNp).mp hbfrac.2
    have hdM : (M : ℝ) < (d : ℝ) := by
      simpa only [one_mul] using (lt_div_iff₀ hMp).mp hdfrac.1
    have hd2M : (d : ℝ) < 2 * (M : ℝ) := (div_lt_iff₀ hMp).mp hdfrac.2
    have hbpos : (0 : ℤ) < b := by exact_mod_cast (lt_trans hNp hbN)
    have hdpos : (0 : ℤ) < d := by exact_mod_cast (lt_trans hMp hdM)
    have hbn : ((b.toNat : ℕ) : ℝ) = (b : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hbpos.le)
    have hdn : ((d.toNat : ℕ) : ℝ) = (d : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg hdpos.le)
    have hmid : (t + w / 2) / w = t / w + 1 / 2 := by field_simp [hw.1.ne']
    have hend : (t + w) / w = t / w + 1 := by field_simp [hw.1.ne']
    obtain ⟨hzlo, hzhi⟩ := abs_lt.mp hzclose
    rw [hmid] at hzlo hzhi
    have hzlo' : t / w < ((b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ)) / w := by linarith
    have hzhi' : ((b : ℝ) * theta + (d : ℝ) * phi - (a : ℝ)) / w < (t + w) / w := by
      rw [hend]
      linarith
    have hzlo'' := (div_lt_div_iff_of_pos_right hw.1).mp hzlo'
    have hzhi'' := (div_lt_div_iff_of_pos_right hw.1).mp hzhi'
    apply hmiss
    refine ⟨b.toNat, d.toNat, a, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hreal : (N : ℝ) ≤ (b.toNat : ℝ) := by rw [hbn]; exact hbN.le
      exact_mod_cast hreal
    · have hreal : (b.toNat : ℝ) ≤ 2 * (N : ℝ) := by rw [hbn]; exact hb2N.le
      exact_mod_cast hreal
    · have hreal : (M : ℝ) ≤ (d.toNat : ℝ) := by rw [hdn]; exact hdM.le
      exact_mod_cast hreal
    · have hreal : (d.toNat : ℝ) ≤ 2 * (M : ℝ) := by rw [hdn]; exact hd2M.le
      exact_mod_cast hreal
    · simpa only [hbn, hdn] using hzlo''
    · simpa only [hbn, hdn] using hzhi''
  obtain ⟨y, hy, hy0, hcover⟩ :=
    D5.S3.Arith.Lattices.EuclideanThreeLatticeTransference.exists_dual_covering L
  obtain ⟨v, hvL, hvdist⟩ := hcover x
  have hvSq : (1 / 2 : ℝ) ^ 2 ≤ ‖x - v‖ ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (hfar v hvL) 2
  have hySq : ‖y‖ ^ 2 ≤ (11 / 3 : ℝ) := by
    have hquarter := mul_le_mul_of_nonneg_right hvSq (sq_nonneg ‖y‖)
    linarith only [hquarter, hvdist]
  have hyshort : ‖y‖ < (2 : ℝ) := by
    by_contra! hlong
    have hlongSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hlong 2
    linarith only [hlongSq, hySq]
  have hycoord (i : Fin 3) : |y i| < (2 : ℝ) :=
    lt_of_le_of_lt (by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i) hyshort
  obtain ⟨h, j, k, hyx, hyy, hyz⟩ :=
    dual_coordinates (N : ℝ) (M : ℝ) theta phi w hNp.ne' hMp.ne' hw.1.ne' hy
  have hzero_int (D : ℝ) (hD : 2 ≤ D) (m : ℤ) (hm : |D * (m : ℝ)| < 2) : m = 0 := by
    have hDp : 0 < D := by linarith only [hD]
    rw [abs_mul, abs_of_pos hDp] at hm
    have hmSmall : |(m : ℝ)| < 1 := by
      by_contra! hmLarge
      have hmul := mul_le_mul_of_nonneg_left hmLarge hDp.le
      linarith only [hm, hmul, hD]
    exact Int.abs_lt_one_iff.mp (by exact_mod_cast hmSmall)
  have hh0 : h ≠ 0 := by
    intro hh
    have hyx' : y 0 = (N : ℝ) * (j : ℝ) := by
      simpa only [hh, Int.cast_zero, zero_mul, sub_zero] using hyx
    have hyy' : y 1 = (M : ℝ) * (k : ℝ) := by
      simpa only [hh, Int.cast_zero, zero_mul, sub_zero] using hyy
    have hj := hzero_int (N : ℝ) hNr j (by simpa only [hyx'] using hycoord 0)
    have hk := hzero_int (M : ℝ) hMr k (by simpa only [hyy'] using hycoord 1)
    apply hy0
    apply PiLp.ext
    intro i
    fin_cases i
    · simp [hyx', hj]
    · simp [hyy', hk]
    · simp [hyz, hh]
  have hnorm : ‖y‖ ^ 2 =
      (N : ℝ) ^ 2 * ((h : ℝ) * theta - (j : ℝ)) ^ 2 +
        (M : ℝ) ^ 2 * ((h : ℝ) * phi - (k : ℝ)) ^ 2 + w ^ 2 * (h : ℝ) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three, hyx, hyy, hyz]
    ring
  have hjoint := hnorm ▸ hySq
  by_cases hh : 1 ≤ h
  · exact ⟨h, j, k, hh, hjoint⟩
  · refine ⟨-h, -j, -k, by omega, ?_⟩
    calc
      _ = (N : ℝ) ^ 2 * ((h : ℝ) * theta - (j : ℝ)) ^ 2 +
          (M : ℝ) ^ 2 * ((h : ℝ) * phi - (k : ℝ)) ^ 2 + w ^ 2 * (h : ℝ) ^ 2 := by
        push_cast
        ring
      _ ≤ _ := hjoint

end D5.S3.Arith.DiophantineApproximation.FiniteRectangleCircleCover
