import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation

open Set
open scoped BigOperators

/-! 
The first two declarations are the analytic part of the box interpolation
argument. The interpolation weights require positive interval width;
`corner_floor` also handles degenerate intervals directly.
-/

theorem corner_interpolation {f : ℝ → ℝ} (C lo hi x : ℝ)
    (hlt : lo < hi)
    (hf : ContinuousOn f (Icc lo hi))
    (hf' : DifferentiableOn ℝ f (Ioo lo hi))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo lo hi))
    (hC : ∀ t ∈ Ioo lo hi, deriv^[2] f t ≤ C)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    ((hi - x) / (hi - lo)) * f lo + ((x - lo) / (hi - lo)) * f hi -
        (C / 2) * (x - lo) * (hi - x) ≤ f x := by
  let q : ℝ → ℝ := fun t => f t - (C / 2) * t ^ 2
  have hpoly_cont : ContinuousOn (fun t : ℝ => (C / 2) * t ^ 2) (Icc lo hi) := by
    exact continuousOn_const.mul (continuousOn_id.pow 2)
  have hq_cont : ContinuousOn q (Icc lo hi) := by
    change ContinuousOn (f - fun t => (C / 2) * t ^ 2) (Icc lo hi)
    exact hf.sub hpoly_cont
  have hq1 : ∀ t ∈ interior (Icc lo hi),
      HasDerivWithinAt q (deriv f t - C * t) (interior (Icc lo hi)) t := by
    intro t ht
    have ht' : t ∈ Ioo lo hi := by
      simpa only [interior_Icc] using ht
    have hft : HasDerivAt f (deriv f t) t :=
      ((hf' t ht').differentiableAt (isOpen_Ioo.mem_nhds ht')).hasDerivAt
    have hpow : HasDerivAt (fun y : ℝ => (C / 2) * y ^ 2) (C * t) t := by
      have hp := (hasDerivAt_pow 2 t).const_mul (C / 2)
      convert hp using 1 <;> norm_num <;> ring
    change HasDerivWithinAt (f - fun y => (C / 2) * y ^ 2)
      (deriv f t - C * t) (interior (Icc lo hi)) t
    exact (hft.sub hpow).hasDerivWithinAt
  have hq2 : ∀ t ∈ interior (Icc lo hi),
      HasDerivWithinAt (fun y : ℝ => deriv f y - C * y)
        (deriv (deriv f) t - C) (interior (Icc lo hi)) t := by
    intro t ht
    have ht' : t ∈ Ioo lo hi := by
      simpa only [interior_Icc] using ht
    have hft : HasDerivAt (deriv f) (deriv (deriv f) t) t :=
      ((hf'' t ht').differentiableAt (isOpen_Ioo.mem_nhds ht')).hasDerivAt
    change HasDerivWithinAt (deriv f - fun y => C * y)
      (deriv (deriv f) t - C) (interior (Icc lo hi)) t
    exact (hft.sub (hasDerivAt_const_mul (x := t) C)).hasDerivWithinAt
  have hq_conc : ConcaveOn ℝ (Icc lo hi) q := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc lo hi) hq_cont hq1 hq2
    intro t ht
    have ht' : t ∈ Ioo lo hi := by
      simpa only [interior_Icc] using ht
    have hct : deriv (deriv f) t ≤ C := by
      simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using hC t ht'
    exact sub_nonpos.mpr hct
  have hw : 0 < hi - lo := sub_pos.mpr hlt
  have hlo_mem : lo ∈ Icc lo hi := ⟨le_rfl, hlt.le⟩
  have hhi_mem : hi ∈ Icc lo hi := ⟨hlt.le, le_rfl⟩
  have ha : 0 ≤ (hi - x) / (hi - lo) :=
    div_nonneg (sub_nonneg.mpr hx1) hw.le
  have hb : 0 ≤ (x - lo) / (hi - lo) :=
    div_nonneg (sub_nonneg.mpr hx0) hw.le
  have hab : (hi - x) / (hi - lo) + (x - lo) / (hi - lo) = 1 := by
    field_simp [ne_of_gt hw] <;> ring
  have harg :
      ((hi - x) / (hi - lo)) * lo + ((x - lo) / (hi - lo)) * hi = x := by
    field_simp [ne_of_gt hw] <;> ring
  have hmix := hq_conc.2 hlo_mem hhi_mem ha hb hab
  simp only [smul_eq_mul] at hmix
  rw [harg] at hmix
  have hquad :
      ((hi - x) / (hi - lo)) * lo ^ 2 +
          ((x - lo) / (hi - lo)) * hi ^ 2 - x ^ 2 =
        (x - lo) * (hi - x) := by
    field_simp [ne_of_gt hw] <;> ring
  have hquadC := congrArg (fun z : ℝ => (C / 2) * z) hquad
  dsimp only [q] at hmix
  nlinarith only [hmix, hquadC]

theorem corner_floor {f : ℝ → ℝ} (C lo hi x L : ℝ)
    (hlohi : lo ≤ hi)
    (hf : ContinuousOn f (Icc lo hi))
    (hf' : DifferentiableOn ℝ f (Ioo lo hi))
    (hf'' : DifferentiableOn ℝ (deriv f) (Ioo lo hi))
    (hC : ∀ t ∈ Ioo lo hi, deriv^[2] f t ≤ C)
    (hC0 : 0 ≤ C)
    (hlo : L ≤ f lo) (hhi : L ≤ f hi)
    (hx0 : lo ≤ x) (hx1 : x ≤ hi) :
    L - C * (hi - lo) ^ 2 / 8 ≤ f x := by
  by_cases hzero : lo = hi
  · subst hi
    have hxe : x = lo := le_antisymm hx1 hx0
    subst x
    simpa using hlo
  · have hlt : lo < hi := lt_of_le_of_ne hlohi hzero
    have hw : 0 < hi - lo := sub_pos.mpr hlt
    have hcorner := corner_interpolation C lo hi x hlt hf hf' hf'' hC hx0 hx1
    have ha : 0 ≤ (hi - x) / (hi - lo) :=
      div_nonneg (sub_nonneg.mpr hx1) hw.le
    have hb : 0 ≤ (x - lo) / (hi - lo) :=
      div_nonneg (sub_nonneg.mpr hx0) hw.le
    have hab : (hi - x) / (hi - lo) + (x - lo) / (hi - lo) = 1 := by
      field_simp [ne_of_gt hw] <;> ring
    have hlin :
        L ≤ ((hi - x) / (hi - lo)) * f lo +
          ((x - lo) / (hi - lo)) * f hi := by
      have h0 := mul_le_mul_of_nonneg_left hlo ha
      have h1 := mul_le_mul_of_nonneg_left hhi hb
      calc
        L = ((hi - x) / (hi - lo)) * L + ((x - lo) / (hi - lo)) * L := by
          rw [← add_mul, hab, one_mul]
        _ ≤ _ := add_le_add h0 h1
    have hprod : (x - lo) * (hi - x) ≤ (hi - lo) ^ 2 / 4 := by
      nlinarith only [sq_nonneg (x - (lo + hi) / 2)]
    have hloss :
        (C / 2) * ((x - lo) * (hi - x)) ≤ C * (hi - lo) ^ 2 / 8 := by
      have hprodC := mul_le_mul_of_nonneg_left hprod
        (div_nonneg hC0 (by norm_num : (0 : ℝ) ≤ 2))
      nlinarith only [hprodC]
    nlinarith only [hcorner, hlin, hloss]

def boxCorner {ι : Type*} [Fintype ι]
    (lo hi : ι → ℝ) (ε : ι → Bool) : ι → ℝ :=
  fun i => if ε i then hi i else lo i

/-- Each fixed coordinate retains its share of the corner margin. -/
theorem finite_box_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (lo hi e x : ι → ℝ) (L : ℝ)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hcorner : ∀ ε, L + (∑ i, e i) ≤ f (boxCorner lo hi ε))
    (haxis : ∀ (y : ι → ℝ), (∀ i, lo i ≤ y i ∧ y i ≤ hi i) → ∀ i,
      min (f (Function.update y i (lo i))) (f (Function.update y i (hi i))) -
        e i ≤ f y) :
    L ≤ f x := by
  classical
  have hface (S : Finset ι) :
      ∀ y : ι → ℝ, (∀ i, lo i ≤ y i ∧ y i ≤ hi i) →
        (∀ i ∉ S, y i = lo i ∨ y i = hi i) →
        L + (∑ i ∈ Sᶜ, e i) ≤ f y := by
    induction S using Finset.induction_on with
    | empty =>
      intro y _ hfixed
      let ε : ι → Bool := fun i => decide (y i = hi i)
      have hycorner : y = boxCorner lo hi ε := by
        funext i
        by_cases hhi : y i = hi i
        · simp [boxCorner, ε, hhi]
        · simpa [boxCorner, ε, hhi] using
            (hfixed i (Finset.notMem_empty i)).resolve_right hhi
      simpa only [Finset.compl_empty, hycorner] using hcorner ε
    | @insert i S hiS ih =>
      intro y hy hfixed
      have hwidth : lo i ≤ hi i := (hy i).1.trans (hy i).2
      have hendpoint (t : ℝ) (ht : t = lo i ∨ t = hi i) :
          L + (∑ j ∈ Sᶜ, e j) ≤ f (Function.update y i t) := by
        apply ih
        · intro j
          by_cases hji : j = i
          · subst j
            rw [Function.update_self]
            rcases ht with rfl | rfl
            · exact ⟨le_rfl, hwidth⟩
            · exact ⟨hwidth, le_rfl⟩
          · rw [Function.update_of_ne hji]
            exact hy j
        · intro j hj
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using ht
          · rw [Function.update_of_ne hji]
            exact hfixed j (fun hj' => (Finset.mem_insert.mp hj').elim hji hj)
      have hsum : (∑ j ∈ Sᶜ, e j) = e i + (∑ j ∈ (insert i S)ᶜ, e j) := by
        calc
          _ = ∑ j ∈ insert i (insert i S)ᶜ, e j := by
            rw [Finset.insert_compl_insert hiS]
          _ = _ := Finset.sum_insert (by simp)
      have hmin := le_min (hendpoint (lo i) (Or.inl rfl)) (hendpoint (hi i) (Or.inr rfl))
      calc
        L + (∑ j ∈ (insert i S)ᶜ, e j) =
            (L + (∑ j ∈ Sᶜ, e j)) - e i := by
          rw [hsum]
          ring
        _ ≤ f y := (sub_le_sub_right hmin (e i)).trans (haxis y hy i)
  simpa only [Finset.compl_univ, Finset.sum_empty, add_zero] using
    hface Finset.univ x hx (fun i hi => (hi (Finset.mem_univ i)).elim)

/-- Coordinate slices with upper second-derivative bounds supply the box losses. -/
theorem finite_box_floor_of_second_deriv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : (ι → ℝ) → ℝ) (lo hi C x : ι → ℝ) (L : ℝ)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hC : ∀ i, 0 ≤ C i)
    (hcorner : ∀ ε, L + (∑ i, C i * (hi i - lo i) ^ 2 / 8) ≤ f (boxCorner lo hi ε))
    (hslice : ∀ (y : ι → ℝ), (∀ i, lo i ≤ y i ∧ y i ≤ hi i) → ∀ i,
      let g : ℝ → ℝ := fun t => f (Function.update y i t)
      ContinuousOn g (Icc (lo i) (hi i)) ∧
        DifferentiableOn ℝ g (Ioo (lo i) (hi i)) ∧
        DifferentiableOn ℝ (deriv g) (Ioo (lo i) (hi i)) ∧
        (∀ t ∈ Ioo (lo i) (hi i), deriv^[2] g t ≤ C i)) :
    L ≤ f x := by
  apply finite_box_floor f lo hi (fun i => C i * (hi i - lo i) ^ 2 / 8) x L hx hcorner
  intro y hy i
  obtain ⟨hg, hg', hg'', hbound⟩ := hslice y hy i
  simpa only [Function.update_eq_self] using
    corner_floor (f := fun t => f (Function.update y i t))
      (C i) (lo i) (hi i) (y i)
      (min (f (Function.update y i (lo i))) (f (Function.update y i (hi i))))
      ((hy i).1.trans (hy i).2) hg hg' hg'' hbound (hC i)
      (min_le_left _ _) (min_le_right _ _) (hy i).1 (hy i).2

/-! A compact consumer-facing form of the multilinear step.  The caller's
separate-affinity induction supplies `haverage`; this theorem then converts
the endpoint certificate into the box-wide floor.  It is written with an
arbitrary finite index type so the same statement covers the 3-variable box.
-/

theorem multilinear_box_floor {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F : (ι → ℝ) → ℝ) (lo hi x : ι → ℝ) (L : ℝ)
    (w : (ι → Bool) → ℝ)
    (hweight : ∀ ε, 0 ≤ w ε)
    (hsum : ∑ ε, w ε = 1)
    (haverage : F x = ∑ ε, w ε * F (boxCorner lo hi ε))
    (hcorner : ∀ ε, L ≤ F (boxCorner lo hi ε)) :
    L ≤ F x := by
  rw [haverage]
  have hsumL : ∑ ε, w ε * L = L := by
    rw [← Finset.sum_mul, hsum, one_mul]
  calc
    L = ∑ ε, w ε * L := hsumL.symm
    _ ≤ ∑ ε, w ε * F (boxCorner lo hi ε) := by
      exact Finset.sum_le_sum (fun ε _ => mul_le_mul_of_nonneg_left (hcorner ε) (hweight ε))

/-! The row-sum correction consumed by each of the two real symmetric 3×3
tests.  An entrywise absolute error `eᵢⱼ` costs at most the sum of the errors
in the two incident rows, by `2 |uv| ≤ u² + v²`.
-/

def quad3 (a00 a01 a02 a11 a12 a22 x0 x1 x2 : ℝ) : ℝ :=
  a00 * x0 ^ 2 + 2 * a01 * x0 * x1 + 2 * a02 * x0 * x2 +
    a11 * x1 ^ 2 + 2 * a12 * x1 * x2 + a22 * x2 ^ 2

private theorem cross_error (d e u v : ℝ) (he : 0 ≤ e) (hd : |d| ≤ e) :
    -e * (u ^ 2 + v ^ 2) ≤ 2 * d * u * v := by
  have hdlo : -e ≤ d := (abs_le.mp hd).1
  have hdhi : d ≤ e := (abs_le.mp hd).2
  by_cases huv : 0 ≤ u * v
  · have hterm : -2 * e * (u * v) ≤ 2 * d * u * v := by
      nlinarith only [mul_le_mul_of_nonneg_right hdlo huv]
    have hquad : -e * (u ^ 2 + v ^ 2) ≤ -2 * e * (u * v) := by
      nlinarith only [mul_le_mul_of_nonneg_left (show 2 * u * v ≤ u ^ 2 + v ^ 2 by
        nlinarith only [sq_nonneg (u - v)]) he]
    exact hquad.trans hterm
  · have huv' : u * v ≤ 0 := le_of_not_ge huv
    have hterm : 2 * e * (u * v) ≤ 2 * d * u * v := by
      nlinarith only [mul_le_mul_of_nonpos_right hdhi huv']
    have hquad : -e * (u ^ 2 + v ^ 2) ≤ 2 * e * (u * v) := by
      nlinarith only [mul_le_mul_of_nonneg_left (show -2 * u * v ≤ u ^ 2 + v ^ 2 by
        nlinarith only [sq_nonneg (u + v)]) he]
    exact hquad.trans hterm

theorem quad3_row_sum_correction
    (a00 a01 a02 a11 a12 a22 : ℝ)
    (b00 b01 b02 b11 b12 b22 : ℝ)
    (e00 e01 e02 e11 e12 e22 : ℝ)
    (he00 : 0 ≤ e00) (he01 : 0 ≤ e01) (he02 : 0 ≤ e02)
    (he11 : 0 ≤ e11) (he12 : 0 ≤ e12) (he22 : 0 ≤ e22)
    (h00 : |a00 - b00| ≤ e00) (h01 : |a01 - b01| ≤ e01)
    (h02 : |a02 - b02| ≤ e02) (h11 : |a11 - b11| ≤ e11)
    (h12 : |a12 - b12| ≤ e12) (h22 : |a22 - b22| ≤ e22)
    (hcorrected : ∀ x0 x1 x2 : ℝ,
      0 ≤ quad3 (b00 - (e00 + e01 + e02)) b01 b02
        (b11 - (e01 + e11 + e12)) b12
        (b22 - (e02 + e12 + e22)) x0 x1 x2) :
    ∀ x0 x1 x2 : ℝ, 0 ≤ quad3 a00 a01 a02 a11 a12 a22 x0 x1 x2 := by
  intro x0 x1 x2
  have hdiag0 : -e00 * x0 ^ 2 ≤ (a00 - b00) * x0 ^ 2 := by
    have h := (abs_le.mp h00).1
    exact mul_le_mul_of_nonneg_right h (sq_nonneg x0)
  have hdiag1 : -e11 * x1 ^ 2 ≤ (a11 - b11) * x1 ^ 2 := by
    have h := (abs_le.mp h11).1
    exact mul_le_mul_of_nonneg_right h (sq_nonneg x1)
  have hdiag2 : -e22 * x2 ^ 2 ≤ (a22 - b22) * x2 ^ 2 := by
    have h := (abs_le.mp h22).1
    exact mul_le_mul_of_nonneg_right h (sq_nonneg x2)
  have h01 := cross_error (a01 - b01) e01 x0 x1 he01 h01
  have h02 := cross_error (a02 - b02) e02 x0 x2 he02 h02
  have h12 := cross_error (a12 - b12) e12 x1 x2 he12 h12
  have hcorr := hcorrected x0 x1 x2
  unfold quad3 at hcorr ⊢
  nlinarith only [hcorr, hdiag0, hdiag1, hdiag2, h01, h02, h12]

/-- Upper-triangular entries in the order used by the Wu cubic matrix tests. -/
def quad3Entries (a : Fin 6 → ℝ) (u v w : ℝ) : ℝ :=
  quad3 (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) u v w

/-- The quadratic form of the diagonal row-sum correction. -/
def quad3RowError (e : Fin 6 → ℝ) (u v w : ℝ) : ℝ :=
  (e 0 + e 1 + e 2) * u ^ 2 + (e 1 + e 3 + e 4) * v ^ 2 + (e 2 + e 4 + e 5) * w ^ 2

private theorem quad3_entries_sub_row_error_le (a b e : Fin 6 → ℝ)
    (h : ∀ k, |a k - b k| ≤ e k) (u v w : ℝ) :
    quad3Entries b u v w - quad3RowError e u v w ≤ quad3Entries a u v w := by
  let r0 := e 0 + e 1 + e 2
  let r1 := e 1 + e 3 + e 4
  let r2 := e 2 + e 4 + e 5
  have he (k : Fin 6) : 0 ≤ e k := (abs_nonneg _).trans (h k)
  -- Compare the shifted perturbation with the diagonal row-sum matrix.
  have hq := quad3_row_sum_correction
    (a 0 - b 0 + r0) (a 1 - b 1) (a 2 - b 2) (a 3 - b 3 + r1) (a 4 - b 4)
      (a 5 - b 5 + r2)
    r0 0 0 r1 0 r2
    (e 0) (e 1) (e 2) (e 3) (e 4) (e 5)
    (he 0) (he 1) (he 2) (he 3) (he 4) (he 5)
    (by simpa only [add_sub_cancel_right] using h 0)
    (by simpa only [sub_zero] using h 1)
    (by simpa only [sub_zero] using h 2)
    (by simpa only [add_sub_cancel_right] using h 3)
    (by simpa only [sub_zero] using h 4)
    (by simpa only [add_sub_cancel_right] using h 5)
    (by intro x y z; simp [quad3, r0, r1, r2])
    u v w
  simp only [quad3Entries, quad3RowError, quad3, r0, r1, r2] at hq ⊢
  nlinarith only [hq]

/-- The four-axis matrix test uses a common chord weight for all six entries.
For a nondegenerate slice this weight is `(y i - lo i) / (hi i - lo i)`.
Applying `corner_interpolation` to an entry and its negation gives the
two-sided chord error with loss `C * (hi i - lo i)^2 / 8`.
For each nonzero test vector, the minimum of the corrected corner values is a
strictly positive floor for the scalar box theorem. -/
theorem quad3_pos_on_fin4_box
    (A : (Fin 4 → ℝ) → Fin 6 → ℝ) (lo hi x : Fin 4 → ℝ) (e : Fin 4 → Fin 6 → ℝ)
    (hx : ∀ i, lo i ≤ x i ∧ x i ≤ hi i)
    (hcorner : ∀ ε (u v w : ℝ), (u, v, w) ≠ (0, 0, 0) →
      0 < quad3Entries (A (boxCorner lo hi ε)) u v w -
        quad3RowError (fun k => ∑ i, e i k) u v w)
    (haxis : ∀ (y : Fin 4 → ℝ), (∀ i, lo i ≤ y i ∧ y i ≤ hi i) → ∀ i,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ k,
        |A y k - ((1 - t) * A (Function.update y i (lo i)) k +
          t * A (Function.update y i (hi i)) k)| ≤ e i k) :
    ∀ u v w : ℝ, (u, v, w) ≠ (0, 0, 0) → 0 < quad3Entries (A x) u v w := by
  intro u v w huv
  let f (y : Fin 4 → ℝ) := quad3Entries (A y) u v w
  let loss (i : Fin 4) := quad3RowError (e i) u v w
  let g (ε : Fin 4 → Bool) := f (boxCorner lo hi ε) - (∑ i, loss i)
  obtain ⟨ε₀, _, hmin⟩ := Finset.exists_min_image Finset.univ g Finset.univ_nonempty
  have hsum : (∑ i, loss i) = quad3RowError (fun k => ∑ i, e i k) u v w := by
    simp only [loss, quad3RowError, Finset.sum_add_distrib]
    simp only [← Finset.sum_mul, Finset.sum_add_distrib]
  have hpos : 0 < g ε₀ := by
    change 0 < f (boxCorner lo hi ε₀) - (∑ i, loss i)
    rw [hsum]
    exact hcorner ε₀ u v w huv
  apply hpos.trans_le
  refine finite_box_floor f lo hi loss x (g ε₀) hx ?_ ?_
  · intro ε
    have h := hmin ε (Finset.mem_univ ε)
    change g ε₀ ≤ f (boxCorner lo hi ε) - (∑ i, loss i) at h
    exact le_sub_iff_add_le.mp h
  · intro y hy i
    obtain ⟨t, ht0, ht1, hentry⟩ := haxis y hy i
    let qlo := f (Function.update y i (lo i))
    let qhi := f (Function.update y i (hi i))
    let m (k : Fin 6) := (1 - t) * A (Function.update y i (lo i)) k +
      t * A (Function.update y i (hi i)) k
    have hmix : quad3Entries m u v w = (1 - t) * qlo + t * qhi := by
      simp only [quad3Entries, quad3, f, m, qlo, qhi]
      ring
    have hq := quad3_entries_sub_row_error_le (A y) m (e i) hentry u v w
    rw [hmix] at hq
    have hlo := mul_le_mul_of_nonneg_left (min_le_left qlo qhi) (sub_nonneg.mpr ht1)
    have hhi := mul_le_mul_of_nonneg_left (min_le_right qlo qhi) ht0
    calc
      min qlo qhi - loss i =
          (1 - t) * min qlo qhi + t * min qlo qhi - loss i := by ring
      _ ≤ (1 - t) * qlo + t * qhi - loss i := sub_le_sub_right (add_le_add hlo hhi) _
      _ ≤ f y := hq

end D5.S3.Quantum.Semigroups.WuCubicCornerInterpolation
