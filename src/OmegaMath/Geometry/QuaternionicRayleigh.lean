import OmegaMath.Geometry.QuaternionicHermitianRealification
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
Omega original.

Rayleigh estimates for quaternionic Hermitian operators follow from Bessel's
inequality in the realified space.
-/

open scoped BigOperators Quaternion InnerProductSpace

noncomputable section

namespace Omega.Geometry.HolonomySpectrum

open Finset

section FiniteFrame

variable {J I E : Type*} [Fintype J] [Fintype I] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem rayleigh_expand (T : E →ₗ[ℝ] E) (b : OrthonormalBasis J ℝ E) (f : J → ℝ)
    (hb : ∀ j, T (b j) = f j • b j) (x : E) :
    ⟪x, T x⟫_ℝ = ∑ j, f j * ⟪b j, x⟫_ℝ ^ 2 := by
  nth_rw 2 [← b.sum_repr x]
  simp only [map_sum, map_smul, hb, inner_sum, real_inner_smul_right, b.repr_apply_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x (b j)]
  ring

/-- For an orthonormal frame, the Rayleigh sum is bounded by an equal-sized
set of largest eigenvalues. -/
theorem rayleigh_frame_le (T : E →ₗ[ℝ] E) (b : OrthonormalBasis J ℝ E) (f : J → ℝ)
    (hb : ∀ j, T (b j) = f j • b j) (v : I → E) (hv : Orthonormal ℝ v)
    (s : Finset J) (hs : s.card = Fintype.card I)
    (t : ℝ) (hlo : ∀ j ∉ s, f j ≤ t) (hhi : ∀ j ∈ s, t ≤ f j) :
    (∑ i, ⟪v i, T (v i)⟫_ℝ) ≤ ∑ j ∈ s, f j := by
  classical
  let w (j : J) := ∑ i, ⟪b j, v i⟫_ℝ ^ 2
  have hw₀ (j) : 0 ≤ w j := sum_nonneg fun _ _ => sq_nonneg _
  have hw₁ (j) : w j ≤ 1 := by
    have h := hv.sum_inner_products_le (s := univ) (b j)
    simp only [Real.norm_eq_abs, sq_abs, b.orthonormal.norm_eq_one, one_pow] at h
    simpa only [w, real_inner_comm] using h
  have hwSum : ∑ j, w j = (s.card : ℝ) := by
    unfold w
    rw [sum_comm]
    simp only [b.sum_sq_inner_right, hv.norm_eq_one, one_pow, sum_const, card_univ, nsmul_eq_mul,
      mul_one, hs]
  have hterm (j) : (f j - t) * w j ≤ if j ∈ s then f j - t else 0 := by
    split_ifs with hj
    · simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (hw₁ j) (sub_nonneg.mpr (hhi j hj))
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hlo j hj)) (hw₀ j)
  have h := sum_le_sum (s := univ) (fun j _ => hterm j)
  simp only [sub_mul, sum_sub_distrib, ← mul_sum, hwSum, ← sum_filter,
    filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul] at h
  simp only [rayleigh_expand T b f hb]
  rw [sum_comm]
  simp only [← mul_sum]
  change (∑ j, f j * w j) ≤ _
  linarith only [h]

end FiniteFrame

section QuaternionFrame

variable {ι : Type*} [Fintype ι]

/-- Quaternionic inner pairing, conjugate-linear in the first column. -/
def pairing (x y : Columns ι) : ℍ[ℝ] := ∑ i, star (x i) * y i

private theorem re_sum (z : ι → ℍ[ℝ]) : (∑ i, z i).re = ∑ i, (z i).re :=
  map_sum (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) z univ

theorem inner_rightMul_rightMul (x y : Columns ι) (q r : ℍ[ℝ]) :
    ⟪rightMul q x, rightMul r y⟫_ℝ = (pairing y x * (q * star r)).re := by
  simp only [PiLp.inner_apply, rightMul_apply, Quaternion.inner_def, star_mul, pairing,
    sum_mul, re_sum]
  refine sum_congr rfl fun i _ => ?_
  calc
    _ = (x i * q * star r * star (y i)).re := by rw [mul_assoc (x i * q)]
    _ = (star (y i) * (x i * q * star r)).re := re_mul_cycle _ _
    _ = _ := by simp only [mul_assoc]

theorem pairing_self (x : Columns ι) : pairing x x = (‖x‖ ^ 2 : ℝ) := by
  simp only [pairing, Quaternion.star_mul_self, ← Quaternion.algebraMap_def, ← map_sum]
  congr 1
  simpa only [Quaternion.normSq_eq_norm_mul_self, pow_two] using
    (PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℍ[ℝ]) x).symm

private def quaternionAxes : Fin 4 → ℍ[ℝ] :=
  ![1, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

private theorem axes_inner (i j : Fin 4) :
    (quaternionAxes i * star (quaternionAxes j)).re = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> norm_num [quaternionAxes, Quaternion.re_mul]

/-- Quaternionic orthonormal columns generate real orthonormal frames by
right multiplication by the standard four quaternion axes. -/
theorem orthonormal_rightMul_axes {I : Type*} [DecidableEq I] (v : I → Columns ι)
    (hv : ∀ i j, pairing (v i) (v j) = if i = j then 1 else 0) :
    Orthonormal ℝ (fun ij : I × Fin 4 => rightMul (quaternionAxes ij.2) (v ij.1)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_rightMul_rightMul, hv]
  rcases i with ⟨i, k⟩
  rcases j with ⟨j, l⟩
  by_cases hij : i = j
  · subst j
    simp only [ite_true, one_mul, Prod.mk.injEq, true_and]
    exact axes_inner k l
  · simp [hij, Ne.symm hij]

theorem rayleigh_rightMul_axes (M : Matrix ι ι ℍ[ℝ]) (x : Columns ι) (k : Fin 4) :
    ⟪rightMul (quaternionAxes k) x, realAction M (rightMul (quaternionAxes k) x)⟫_ℝ =
      ⟪x, realAction M x⟫_ℝ := by
  rw [realAction_rightMul, inner_rightMul_rightMul]
  have hu : quaternionAxes k * star (quaternionAxes k) = 1 := by
    fin_cases k <;> ext <;> norm_num [quaternionAxes, Quaternion.re_mul]
  rw [hu, mul_one]
  have ho (v : Columns ι) : rightMul (1 : ℍ[ℝ]) v = v := by
    apply PiLp.ext
    intro i
    simp
  simpa only [ho, star_one, mul_one] using (inner_rightMul_rightMul x (realAction M x) 1 1).symm


theorem pairing_add_left (x y z : Columns ι) : pairing (x + y) z = pairing x z + pairing y z := by
  simp [pairing, PiLp.add_apply, star_add, add_mul, sum_add_distrib]

theorem pairing_add_right (x y z : Columns ι) : pairing x (y + z) = pairing x y + pairing x z := by
  simp [pairing, PiLp.add_apply, mul_add, sum_add_distrib]

theorem pairing_smul_left (r : ℝ) (x y : Columns ι) : pairing (r • x) y = r • pairing x y := by
  simp [pairing, PiLp.smul_apply, Finset.smul_sum]

theorem pairing_smul_right (r : ℝ) (x y : Columns ι) : pairing x (r • y) = r • pairing x y := by
  simp [pairing, PiLp.smul_apply, Finset.smul_sum]

theorem pairing_star (x y : Columns ι) : star (pairing x y) = pairing y x := by
  simp [pairing, star_sum, star_mul]

theorem pairing_neg_right (x y : Columns ι) : pairing x (-y) = -pairing x y := by
  simpa only [neg_one_smul] using pairing_smul_right (-1) x y

theorem pairing_neg_left (x y : Columns ι) : pairing (-x) y = -pairing x y := by
  simpa only [neg_one_smul] using pairing_smul_left (-1) x y

theorem pairing_rightMul (x y : Columns ι) (q : ℍ[ℝ]) :
    pairing x (rightMul q y) = pairing x y * q := by
  simp only [pairing, rightMul_apply, sum_mul, mul_assoc]

theorem real_inner_eq_re_pairing (x y : Columns ι) : ⟪x, y⟫_ℝ = (pairing x y).re := by
  simp only [pairing, PiLp.inner_apply, Quaternion.inner_def, re_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [← Quaternion.re_star (x i * star (y i)), star_mul, star_star, re_mul_cycle]

private theorem qpair_rayleigh_sum
    {m : ℕ} (hm : 2 ≤ m) (M : Matrix ι ι ℍ[ℝ]) (μ : Fin m → ℝ) (hμ : Antitone μ)
    (b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι))
    (hb : ∀ i k, realAction M (b (i, k)) = μ i • b (i, k))
    (v : Fin 2 → Columns ι)
    (hv : ∀ i j, pairing (v i) (v j) = if i = j then 1 else 0) :
    (∑ i, ⟪v i, realAction M (v i)⟫_ℝ) ≤ μ ⟨0, by omega⟩ + μ ⟨1, by omega⟩ := by
  classical
  let e : Fin 2 ↪ Fin m := ⟨Fin.castLE hm, Fin.castLE_injective hm⟩
  let s : Finset (Fin m × Fin 4) := (univ.map e) ×ˢ univ
  let R (p : Fin 2 × Fin 4) := rightMul (quaternionAxes p.2) (v p.1)
  have hs (j : Fin m × Fin 4) : j ∈ s ↔ j.1.val < 2 := by
    simp only [s, mem_product, mem_univ, and_true, mem_map, e, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨k, _, he⟩
      rw [← he]
      exact k.isLt
    · intro hj
      exact ⟨⟨j.1.val, hj⟩, trivial, rfl⟩
  have hcard : s.card = Fintype.card (Fin 2 × Fin 4) := by
    simp [s, Fintype.card_prod]
  have hsum := rayleigh_frame_le (realAction M) b (fun j => μ j.1)
    (fun ⟨i,k⟩ => hb i k) R (orthonormal_rightMul_axes v hv) s hcard (μ ⟨1, by omega⟩)
    (fun j hj => hμ (by
      have hj' : ¬j.1.val < 2 := fun h => hj ((hs j).mpr h)
      change 1 ≤ j.1.val
      omega))
    (fun j hj => hμ (by
      have hj' := (hs j).mp hj
      change j.1.val ≤ 1
      omega))
  have hr (p : Fin 2 × Fin 4) :
      ⟪R p, realAction M (R p)⟫_ℝ = ⟪v p.1, realAction M (v p.1)⟫_ℝ :=
    rayleigh_rightMul_axes M _ _
  simp only [hr, Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, ← mul_sum] at hsum
  have he : (∑ j ∈ s, μ j.1) = 4 * (μ ⟨0, by omega⟩ + μ ⟨1, by omega⟩) := by
    simp only [s, sum_product, sum_map, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
      Nat.cast_ofNat, Fin.sum_univ_two]
    change 4 * μ ⟨0, by omega⟩ + 4 * μ ⟨1, by omega⟩ = _
    ring
  rw [he] at hsum
  linarith only [hsum]

private theorem qrayleigh_le_max {m : ℕ} (hm : 0 < m) (M : Matrix ι ι ℍ[ℝ])
    (μ : Fin m → ℝ) (hμ : Antitone μ) (b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι))
    (hb : ∀ i k, realAction M (b (i, k)) = μ i • b (i, k))
    (x : Columns ι) (hx : ‖x‖ = 1) :
    ⟪x, realAction M x⟫_ℝ ≤ μ ⟨0, hm⟩ := by
  rw [rayleigh_expand (realAction M) b (fun j => μ j.1) (fun j => hb j.1 j.2)]
  calc
    _ ≤ ∑ j, μ ⟨0, hm⟩ * ⟪b j, x⟫_ℝ ^ 2 :=
      sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hμ (Nat.zero_le _)) (sq_nonneg _)
    _ = _ := by rw [← mul_sum, b.sum_sq_inner_right, hx, one_pow, mul_one]

/-- The sum of the Rayleigh quotients of two unit columns is bounded by
the largest two quaternionic eigenvalues, weighted by their overlap. -/
theorem rayleigh_two_unit_le {m : ℕ} (hm : 2 ≤ m) (M : Matrix ι ι ℍ[ℝ])
    (μ : Fin m → ℝ) (hμ : Antitone μ) (b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι))
    (hb : ∀ i k, realAction M (b (i, k)) = μ i • b (i, k))
    (x y : Columns ι) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1) (hxy : pairing x y = (a : ℍ[ℝ])) :
    ⟪x, realAction M x⟫_ℝ + ⟪y, realAction M y⟫_ℝ ≤
      (1 + a) * μ ⟨0, by omega⟩ + (1 - a) * μ ⟨1, by omega⟩ := by
  let p := 1 / √(2 * (1 + a))
  let q := 1 / √(2 * (1 - a))
  have hp : 0 < 2 * (1 + a) := by linarith
  have hq : 0 < 2 * (1 - a) := by linarith
  have hp' : p ^ 2 * (2 * (1 + a)) = 1 := by
    dsimp [p]
    rw [div_pow, one_pow, Real.sq_sqrt hp.le, div_mul_cancel₀ _ hp.ne']
  have hq' : q ^ 2 * (2 * (1 - a)) = 1 := by
    dsimp [q]
    rw [div_pow, one_pow, Real.sq_sqrt hq.le, div_mul_cancel₀ _ hq.ne']
  let u := p • (x + y)
  let v := q • (x - y)
  have hyx : pairing y x = (a : ℍ[ℝ]) := by
    rw [← pairing_star, hxy]
    simp
  have hxx : pairing x x = 1 := by rw [pairing_self, hx]; norm_num
  have hyy : pairing y y = 1 := by rw [pairing_self, hy]; norm_num
  have hu : pairing u u = 1 := by
    simp only [u, pairing_smul_left, pairing_smul_right, pairing_add_left,
      pairing_add_right, hxx, hyy, hxy, hyx]
    ext <;> simp [pow_two] at *
    nlinarith only [hp']
  have hv : pairing v v = 1 := by
    simp only [v, sub_eq_add_neg, pairing_smul_left, pairing_smul_right, pairing_add_left,
      pairing_add_right, pairing_neg_left, pairing_neg_right, hxx, hyy, hxy, hyx]
    ext <;> simp [pow_two] at *
    nlinarith only [hq']
  have huv : pairing u v = 0 := by
    simp only [u, v, sub_eq_add_neg, pairing_smul_left, pairing_smul_right, pairing_add_left,
      pairing_add_right, pairing_neg_right, hxx, hyy, hxy, hyx]
    abel_nf
    exact smul_zero _
  have hvu : pairing v u = 0 := by rw [← pairing_star, huv, star_zero]
  let frame : Fin 2 → Columns ι := ![u, v]
  have hframe (i j : Fin 2) : pairing (frame i) (frame j) = if i = j then 1 else 0 := by
    fin_cases i <;> fin_cases j <;> simp [frame, hu, hv, huv, hvu]
  have hpair := qpair_rayleigh_sum hm M μ hμ b hb frame hframe
  simp only [Fin.sum_univ_two] at hpair
  change ⟪u, realAction M u⟫_ℝ + ⟪v, realAction M v⟫_ℝ ≤ _ at hpair
  have hun : ‖u‖ = 1 := by
    have h := congrArg QuaternionAlgebra.re hu
    rw [pairing_self] at h
    change ‖u‖ ^ 2 = 1 at h
    nlinarith [norm_nonneg u]
  have htop := qrayleigh_le_max (by omega) M μ hμ b hb u hun
  have hdecomp : ⟪x, realAction M x⟫_ℝ + ⟪y, realAction M y⟫_ℝ =
      (1 + a) * ⟪u, realAction M u⟫_ℝ + (1 - a) * ⟪v, realAction M v⟫_ℝ := by
    simp only [u, v, map_smul, map_add, map_sub, inner_add_left, inner_add_right,
      inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
    have hp'' : (1 + a) * (p * p) = 1 / 2 := by nlinarith only [hp']
    have hq'' : (1 - a) * (q * q) = 1 / 2 := by nlinarith only [hq']
    calc
      _ = ((1 + a) * (p * p)) * (⟪x, realAction M x⟫_ℝ + ⟪x, realAction M y⟫_ℝ +
          ⟪y, realAction M x⟫_ℝ + ⟪y, realAction M y⟫_ℝ) +
          ((1 - a) * (q * q)) * (⟪x, realAction M x⟫_ℝ - ⟪x, realAction M y⟫_ℝ -
          ⟪y, realAction M x⟫_ℝ + ⟪y, realAction M y⟫_ℝ) := by rw [hp'', hq'']; ring
      _ = _ := by ring
  rw [hdecomp]
  have h₁ := mul_le_mul_of_nonneg_left htop (show 0 ≤ 2 * a by positivity)
  have h₂ := mul_le_mul_of_nonneg_left hpair (sub_nonneg.mpr ha'.le)
  linarith only [h₁, h₂]


theorem norm_rightMul (x : Columns ι) (q : ℍ[ℝ]) :
    ‖rightMul q x‖ = ‖x‖ * ‖q‖ := by
  apply (pow_left_inj₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) two_ne_zero).mp
  rw [PiLp.norm_sq_eq_of_L2, mul_pow, PiLp.norm_sq_eq_of_L2]
  simp only [rightMul_apply, norm_mul, mul_pow, sum_mul]

private theorem exists_orientation (z : ℍ[ℝ]) :
    ∃ r : ℍ[ℝ], ‖r‖ = 1 ∧ z * r = (‖z‖ : ℍ[ℝ]) := by
  by_cases hz : z = 0
  · subst z
    exact ⟨1, by simp, by simp⟩
  let r := ‖z‖⁻¹ • star z
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  refine ⟨r, by simp [r, norm_smul, hn], ?_⟩
  rw [show z * r = ‖z‖⁻¹ • (z * star z) by exact mul_smul_comm _ _ _,
    Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self]
  rw [← Quaternion.algebraMap_def, Algebra.smul_def, ← RingHom.map_mul]
  congr 1
  field_simp

/-- The two-column Rayleigh bound depends on the norm of their quaternionic overlap. -/
theorem rayleigh_two_unit_le_norm {m : ℕ} (hm : 2 ≤ m) (M : Matrix ι ι ℍ[ℝ])
    (μ : Fin m → ℝ) (hμ : Antitone μ) (b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι))
    (hb : ∀ i k, realAction M (b (i, k)) = μ i • b (i, k))
    (x y : Columns ι) (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hxy : ‖pairing x y‖ < 1) :
    ⟪x, realAction M x⟫_ℝ + ⟪y, realAction M y⟫_ℝ ≤
      (1 + ‖pairing x y‖) * μ ⟨0, by omega⟩ + (1 - ‖pairing x y‖) * μ ⟨1, by omega⟩ := by
  obtain ⟨r, hr, hzr⟩ := exists_orientation (pairing x y)
  have hyn : ‖rightMul r y‖ = 1 := by rw [norm_rightMul, hy, hr, one_mul]
  have hpair : pairing x (rightMul r y) = (‖pairing x y‖ : ℍ[ℝ]) :=
    (pairing_rightMul x y r).trans hzr
  have h := rayleigh_two_unit_le hm M μ hμ b hb x (rightMul r y) hx hyn (norm_nonneg _) hxy hpair
  have hr' : r * star r = 1 := by
    rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hr, one_mul, Quaternion.coe_one]
  have hp : ⟪rightMul r y, realAction M (rightMul r y)⟫_ℝ = ⟪y, realAction M y⟫_ℝ := by
    rw [realAction_rightMul, inner_rightMul_rightMul, hr', mul_one, real_inner_eq_re_pairing, ← pairing_star]
    simp
  rwa [hp] at h


theorem quaternion_cauchy {x y : Columns ι} : ‖pairing x y‖ ≤ ‖x‖ * ‖y‖ := by
  obtain ⟨r, hr, he⟩ := exists_orientation (pairing x y)
  have h := real_inner_le_norm x (rightMul r y)
  rw [real_inner_eq_re_pairing, pairing_rightMul, he, norm_rightMul, hr, mul_one] at h
  exact h

/-- Projection onto a unit quaternionic line satisfies Bessel's inequality. -/
theorem pair_orthogonal_bessel {u v d : Columns ι} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (h : pairing u v = 0) :
    ‖pairing u d‖ ^ 2 + ‖pairing v d‖ ^ 2 ≤ ‖d‖ ^ 2 := by
  let proj (x : Columns ι) := rightMul (pairing x d) x
  have hpx (x : Columns ι) (hx : ‖x‖ = 1) : ‖proj x‖ = ‖pairing x d‖ := by
    dsimp only [proj]
    rw [norm_rightMul, hx, one_mul]
  have hpair (x : Columns ι) (hx : ‖x‖ = 1) : ⟪proj x, d⟫_ℝ = ‖pairing x d‖ ^ 2 := by
    have h₀ : rightMul (1 : ℍ[ℝ]) d = d := by
      apply PiLp.ext
      intro i
      simp
    calc
      _ = (pairing d x * pairing x d).re := by
        simpa only [proj, h₀, star_one, mul_one] using
          inner_rightMul_rightMul x d (pairing x d) 1
      _ = _ := by
        rw [← pairing_star, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self]
        exact (pow_two _).symm
  have ho : ⟪proj u, proj v⟫_ℝ = 0 := by
    dsimp only [proj]
    rw [inner_rightMul_rightMul, ← pairing_star, h, star_zero, zero_mul]
    rfl
  have hh : 0 ≤ ‖d - (proj u + proj v)‖ ^ 2 := sq_nonneg _
  rw [← real_inner_self_eq_norm_sq] at hh
  have hu' : ⟪d, proj u⟫_ℝ = ‖pairing u d‖ ^ 2 :=
    (real_inner_comm _ _).trans (hpair u hu)
  have hv' : ⟪d, proj v⟫_ℝ = ‖pairing v d‖ ^ 2 :=
    (real_inner_comm _ _).trans (hpair v hv)
  have ho' : ⟪proj v, proj u⟫_ℝ = 0 := (real_inner_comm _ _).trans ho
  simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
    hu', hv', hpair u hu, hpair v hv, ho, ho', real_inner_self_eq_norm_sq,
    hpx u hu, hpx v hv] at hh
  linarith only [hh]


/-- The top quaternionic eigenline controls every Rayleigh quotient when the
first two eigenvalues differ. With a repeated top eigenvalue the estimate
reduces to the ordinary maximum bound. -/
theorem top_eigenline_bound {m : ℕ} (hm : 2 ≤ m) (M : Matrix ι ι ℍ[ℝ])
    (hM : M.IsHermitian) (μ : Fin m → ℝ) (hμ : Antitone μ)
    (b : OrthonormalBasis (Fin m × Fin 4) ℝ (Columns ι))
    (hb : ∀ i k, realAction M (b (i,k)) = μ i • b (i,k)) :
    ∃ v : Columns ι, ‖v‖ = 1 ∧ ∀ x : Columns ι, ‖x‖ = 1 →
      ⟪x, realAction M x⟫_ℝ ≤ μ ⟨1, by omega⟩ +
        (μ ⟨0, by omega⟩ - μ ⟨1, by omega⟩) * ‖pairing v x‖ ^ 2 := by
  classical
  let i₀ : Fin m := ⟨0, by omega⟩
  let i₁ : Fin m := ⟨1, by omega⟩
  let v := b (i₀, 0)
  have hv : ‖v‖ = 1 := b.orthonormal.norm_eq_one _
  refine ⟨v, hv, fun x hx => ?_⟩
  change _ ≤ μ i₁ + (μ i₀ - μ i₁) * ‖pairing v x‖ ^ 2
  have hm₁ : μ i₁ ≤ μ i₀ := hμ (show i₀ ≤ i₁ by exact Nat.zero_le _)
  by_cases he : μ i₁ = μ i₀
  · rw [he, sub_self, zero_mul, add_zero]
    exact qrayleigh_le_max (by omega) M μ hμ b hb x hx
  let y := x - rightMul (pairing v x) v
  have hp : pairing v y = 0 := by
    simp only [y, sub_eq_add_neg, pairing_add_right, pairing_neg_right, pairing_rightMul,
      pairing_self, hv, one_pow, Quaternion.coe_one, one_mul, add_neg_cancel]
  have h₁ (k : Fin 4) : ⟪rightMul (quaternionAxes k) v, y⟫_ℝ = 0 := by
    have ho : rightMul (1 : ℍ[ℝ]) y = y := by apply PiLp.ext; intro i; simp
    rw [← ho, inner_rightMul_rightMul, ← pairing_star, hp, star_zero, zero_mul]
    rfl
  let W := Module.End.eigenspace (realAction M) (μ i₀)
  have hW (k : Fin 4) : rightMul (quaternionAxes k) v ∈ W :=
    Module.End.mem_eigenspace_iff.mpr (real_eigenvector_rightMul (hb i₀ 0) _)
  let frame (k : Fin 4) : W := ⟨rightMul (quaternionAxes k) v, hW k⟩
  have hf : Orthonormal ℝ frame := by
    rw [orthonormal_iff_ite]
    intro j k
    change ⟪rightMul (quaternionAxes j) v, rightMul (quaternionAxes k) v⟫_ℝ = _
    rw [inner_rightMul_rightMul, pairing_self, hv, one_pow, Quaternion.coe_one, one_mul, axes_inner]
  have hd : Module.finrank ℝ W = 4 := by
    have hWle : W ≤ Submodule.span ℝ (Set.range fun k : Fin 4 => b (i₀, k)) := by
      intro z hz
      have hfz := Module.End.mem_eigenspace_iff.mp hz
      nth_rw 1 [← b.sum_repr z]
      apply Submodule.sum_mem
      intro j hj
      by_cases hj' : j.1 = i₀
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨j.2, congrArg b (Prod.ext hj'.symm rfl)⟩
      · have hlt : μ j.1 < μ i₀ :=
          (hμ (show i₁ ≤ j.1 by
            have hn : j.1.val ≠ 0 := fun he => hj' (Fin.ext he)
            change 1 ≤ j.1.val
            omega)).trans_lt (lt_of_le_of_ne hm₁ he)
        have hsym := (isSymmetric_realAction hM) (b j) z
        rw [show realAction M (b j) = μ j.1 • b j from hb j.1 j.2,
          hfz, real_inner_smul_left, real_inner_smul_right] at hsym
        have hi : ⟪b j, z⟫_ℝ = 0 := by
          exact (mul_eq_zero.mp (show (μ j.1 - μ i₀) * ⟪b j, z⟫_ℝ = 0 by
            linarith only [hsym])).resolve_left (sub_ne_zero.mpr hlt.ne)
        rw [b.repr_apply_apply, hi, zero_smul]
        exact Submodule.zero_mem _
    have hdim := (Submodule.finrank_mono hWle).trans
      (finrank_range_le_card (R := ℝ) (fun k : Fin 4 => b (i₀, k)))
    have hdim' := hf.linearIndependent.fintype_card_le_finrank
    simpa using le_antisymm hdim hdim'
  let bf := Module.Basis.mk hf.linearIndependent
    (by
      apply (hf.linearIndependent.span_eq_top_of_card_eq_finrank' ?_).ge
      simp [hd])
  have hy (k : Fin 4) : ⟪b (i₀, k), y⟫_ℝ = 0 := by
    have hb' : b (i₀, k) ∈ W := Module.End.mem_eigenspace_iff.mpr (hb i₀ k)
    let w : W := ⟨b (i₀, k), hb'⟩
    have he := congrArg (fun z : W => ⟪(z : Columns ι), y⟫_ℝ) (bf.sum_repr w)
    change _ = ⟪b (i₀, k), y⟫_ℝ at he
    rw [Submodule.coe_sum, sum_inner] at he
    dsimp only [bf] at he
    simp only [Submodule.coe_smul, Module.Basis.mk_apply, frame, real_inner_smul_left,
      h₁, mul_zero, sum_const_zero] at he
    exact he.symm
  have hyR : ⟪y, realAction M y⟫_ℝ ≤ μ i₁ * ‖y‖ ^ 2 := by
    rw [rayleigh_expand (realAction M) b (fun j => μ j.1) (fun j => hb j.1 j.2),
      ← b.sum_sq_inner_right y, mul_sum]
    refine sum_le_sum fun j _ => ?_
    by_cases h : j.1 = i₀
    · rcases j with ⟨j,k⟩
      dsimp at h
      subst j
      simp [hy]
    · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact hμ (by
        have hn : j.1.val ≠ 0 := fun he' => h (Fin.ext he')
        change 1 ≤ j.1.val
        omega)
  let z := rightMul (pairing v x) v
  have hz : realAction M z = μ i₀ • z := real_eigenvector_rightMul (hb i₀ 0) _
  have hzN : ‖z‖ = ‖pairing v x‖ := by dsimp only [z]; rw [norm_rightMul, hv, one_mul]
  have heq : x = z + y := by dsimp [z,y]; abel
  have hzy : ⟪z, y⟫_ℝ = 0 := by
    have h₀ : rightMul (1 : ℍ[ℝ]) y = y := by apply PiLp.ext; intro i; simp
    dsimp only [z]
    rw [← h₀, inner_rightMul_rightMul, ← pairing_star, hp, star_zero, zero_mul]
    rfl
  have hyz : ⟪y, z⟫_ℝ = 0 := (real_inner_comm _ _).trans hzy
  have hNorm := congrArg (fun r : Columns ι => ‖r‖ ^ 2) heq
  simp only [hx, one_pow, ← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    hzy, hyz] at hNorm
  have hR : ⟪x, realAction M x⟫_ℝ =
      μ i₀ * ‖z‖ ^ 2 + ⟪y, realAction M y⟫_ℝ := by
    rw [heq, map_add, inner_add_left, inner_add_right, inner_add_right, hz,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      ← (isSymmetric_realAction hM) z y, hz, real_inner_smul_left, hzy, hyz]
    ring
  rw [hR, ← hzN]
  have hEq : ‖z‖ ^ 2 + ‖y‖ ^ 2 = 1 := by
    simpa only [real_inner_self_eq_norm_sq, zero_add, add_zero, hx, one_pow] using hNorm.symm
  have hm := congrArg (fun r : ℝ => μ i₁ * r) hEq
  linarith only [hyR, hm]


theorem pairing_rightMul_left (x y : Columns ι) (q : ℍ[ℝ]) :
    pairing (rightMul q x) y = star q * pairing x y := by
  rw [← pairing_star, pairing_rightMul, star_mul, pairing_star]

theorem pairing_sub_left (x y z : Columns ι) :
    pairing (x - y) z = pairing x z - pairing y z := by
  simp only [sub_eq_add_neg, pairing_add_left, pairing_neg_left]

theorem pairing_sub_right (x y z : Columns ι) :
    pairing x (y - z) = pairing x y - pairing x z := by
  simp only [sub_eq_add_neg, pairing_add_right, pairing_neg_right]

theorem norm_pairing_comm (x y : Columns ι) : ‖pairing x y‖ = ‖pairing y x‖ := by
  rw [← pairing_star x y, Quaternion.norm_star]

private theorem residual_sq (e x : Columns ι) (he : ‖e‖ = 1) :
    ‖x - rightMul (pairing e x) e‖ ^ 2 = ‖x‖ ^ 2 - ‖pairing e x‖ ^ 2 := by
  let z := rightMul (pairing e x) e
  have hz : ‖z‖ = ‖pairing e x‖ := by dsimp [z]; rw [norm_rightMul, he, one_mul]
  have hpair : ⟪z, x⟫_ℝ = ‖pairing e x‖ ^ 2 := by
    rw [real_inner_eq_re_pairing]
    change (pairing (rightMul (pairing e x) e) x).re = _
    rw [pairing_rightMul_left, Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, pow_two]
    rfl
  change ‖x - z‖ ^ 2 = _
  rw [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hz]
  have hp' : ⟪x, z⟫_ℝ = ‖pairing e x‖ ^ 2 := (real_inner_comm _ _).trans hpair
  rw [hpair, hp']
  ring

/-- The component of a quaternionic overlap outside one unit line is bounded
by the product of the two residual norms. -/
theorem overlap_le_projection (e d x : Columns ι) (he : ‖e‖ = 1) (hd : ‖d‖ = 1)
    (hx : ‖x‖ = 1) :
    ‖pairing d x‖ ≤ ‖pairing e d‖ * ‖pairing e x‖ +
      √(1 - ‖pairing e d‖ ^ 2) * √(1 - ‖pairing e x‖ ^ 2) := by
  let D := d - rightMul (pairing e d) e
  let X := x - rightMul (pairing e x) e
  have hD : ‖D‖ = √(1 - ‖pairing e d‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg D)]
    congr 1
    simpa only [D, hd, one_pow] using residual_sq e d he
  have hX : ‖X‖ = √(1 - ‖pairing e x‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg X)]
    congr 1
    simpa only [X, hx, one_pow] using residual_sq e x he
  have hp : pairing d x = star (pairing e d) * pairing e x + pairing D X := by
    dsimp only [D, X]
    rw [pairing_sub_left, pairing_sub_right, pairing_sub_right, pairing_rightMul_left,
      pairing_rightMul_left, pairing_rightMul, pairing_rightMul, pairing_self, he, one_pow,
      Quaternion.coe_one, one_mul, ← pairing_star e d]
    abel
  calc
    _ ≤ ‖star (pairing e d) * pairing e x‖ + ‖pairing D X‖ := by rw [hp]; exact norm_add_le _ _
    _ ≤ _ := by
      rw [norm_mul, Quaternion.norm_star, ← hD, ← hX]
      exact add_le_add_right (quaternion_cauchy (x := D) (y := X)) _

end QuaternionFrame

end Omega.Geometry.HolonomySpectrum
