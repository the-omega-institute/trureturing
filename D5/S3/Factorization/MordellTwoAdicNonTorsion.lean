/- GID: D5/S3/Factorization/MordellTwoAdicNonTorsion
   generality: G
   mirror-B: D5/B/S3/Factorization/MordellTwoAdicNonTorsion
   mirror-E: none(waiver:symbolic-elliptic-valuation-theorem)
   anchors: [mathlib/module/Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point]
   utility: none
   digest: Negative binary X-valuation forces infinite order on an integral Mordell model. -/

import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Factorization.MordellTwoAdicNonTorsion

/-- The rational Weierstrass model `Y² = X³ + b`. -/
def mordellCurve (b : ℤ) : WeierstrassCurve.Affine ℚ :=
  ⟨0, 0, 0, 0, (b : ℚ)⟩

/-- A rational point with negative binary `X`-valuation has infinite order. The
strict descent of that valuation along successive doubles is the new content. -/
theorem infinite_add_order_of_negative_two_adic_x (b : ℤ) {x y : ℚ}
    (h : (mordellCurve b).Nonsingular x y) (hx : padicValRat 2 x < 0) :
    ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point) := by
  let W := mordellCurve b
  let P : W.Point := .some x y h
  have add_int (q : ℚ) (hq : padicValRat 2 q < 0) (k : ℤ) :
      q + (k : ℚ) ≠ 0 ∧ padicValRat 2 (q + (k : ℚ)) = padicValRat 2 q := by
    have hq0 : q ≠ 0 := by
      intro hzero
      simp [hzero] at hq
    have hkval : 0 ≤ padicValRat 2 (k : ℚ) := by
      rw [padicValRat.of_int]
      exact Nat.cast_nonneg _
    have hsum : q + (k : ℚ) ≠ 0 := by
      intro hzero
      have heq : q = -(k : ℚ) := by linarith
      rw [heq, padicValRat.neg] at hq
      omega
    refine ⟨hsum, ?_⟩
    by_cases hk : k = 0
    · subst k
      simp
    · have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast hk
      exact padicValRat.add_eq_of_lt hsum hq0 hk0 (lt_of_lt_of_le hq hkval)
  have double_step : ∀ {u v : ℚ} (huv : W.Nonsingular u v),
      padicValRat 2 u < 0 →
      ∃ (u' v' : ℚ) (huv' : W.Nonsingular u' v'),
        (2 : ℕ) • (.some u v huv : W.Point) = (.some u' v' huv' : W.Point) ∧
        padicValRat 2 u' = padicValRat 2 u - 2 := by
    intro u v huv huval
    have hu0 : u ≠ 0 := by
      intro hzero
      simp [hzero] at huval
    have hcubeval : padicValRat 2 (u ^ 3) = 3 * padicValRat 2 u := by
      rw [padicValRat.pow]
      norm_num
    have hcubeNeg : padicValRat 2 (u ^ 3) < 0 := by
      rw [hcubeval]
      omega
    obtain ⟨hden0, hdenval⟩ := add_int (u ^ 3) hcubeNeg b
    have hcurve : v ^ 2 = u ^ 3 + (b : ℚ) := by
      simpa [W, mordellCurve] using (W.equation_iff u v).mp huv.1
    have hv0 : v ≠ 0 := by
      intro hzero
      apply hden0
      rw [← hcurve, hzero]
      norm_num
    have hnegY : v ≠ W.negY u v := by
      intro heq
      have : v = -v := by simpa [W, mordellCurve, WeierstrassCurve.Affine.negY] using heq
      apply hv0
      linarith
    let u' := W.addX u u (W.slope u u v v)
    let v' := W.addY u u v (W.slope u u v v)
    have huv' : W.Nonsingular u' v' :=
      WeierstrassCurve.Affine.nonsingular_add (W := W) huv huv
        (fun hxy => hnegY hxy.right)
    have hslope : W.slope u u v v = 3 * u ^ 2 / (2 * v) := by
      rw [WeierstrassCurve.Affine.slope_of_Y_ne (W := W) rfl hnegY]
      simp [W, mordellCurve, WeierstrassCurve.Affine.negY]
      ring
    have hu'form : u' = (3 * u ^ 2 / (2 * v)) ^ 2 - 2 * u := by
      simp only [u', WeierstrassCurve.Affine.addX, hslope]
      simp [W, mordellCurve]
      ring
    have hu'frac : u' = u * (u ^ 3 - 8 * (b : ℚ)) / (4 * (u ^ 3 + (b : ℚ))) := by
      rw [hu'form, ← hcurve]
      field_simp [hv0]
      have hmul := congrArg (fun z : ℚ => 8 * u * z) hcurve
      nlinarith [hmul]
    have hnumexpr : u ^ 3 - 8 * (b : ℚ) = u ^ 3 + ((-8 * b : ℤ) : ℚ) := by
      push_cast
      ring
    obtain ⟨hnum0, hnumval⟩ := add_int (u ^ 3) hcubeNeg (-8 * b)
    refine ⟨u', v', huv', ?_, ?_⟩
    · simpa only [u', v', two_nsmul] using
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := W) hnegY
    · rw [hu'frac, hnumexpr,
        padicValRat.div (mul_ne_zero hu0 hnum0) (mul_ne_zero (by norm_num) hden0),
        padicValRat.mul hu0 hnum0,
        padicValRat.mul (by norm_num : (4 : ℚ) ≠ 0) hden0,
        hnumval, hdenval, hcubeval]
      have hfour : padicValRat 2 (4 : ℚ) = 2 := by
        have h4 : (4 : ℚ) = (2 : ℚ) ^ 2 := by norm_num
        have htwo : padicValRat 2 (2 : ℚ) = 1 := by
          change padicValRat 2 ((2 : ℕ) : ℚ) = 1
          rw [padicValRat.of_nat]
          exact_mod_cast (padicValNat_self (p := 2))
        rw [h4, padicValRat.pow, htwo]
        norm_num
      rw [hfour]
      ring
  have iterated : ∀ n : ℕ,
      ∃ (u v : ℚ) (huv : W.Nonsingular u v),
        (2 ^ n) • P = (.some u v huv : W.Point) ∧
        padicValRat 2 u = padicValRat 2 x - 2 * (n : ℤ) := by
    intro n
    induction n with
    | zero =>
        refine ⟨x, y, h, ?_, ?_⟩
        · simp [P]
        · norm_num
    | succ n ih =>
        obtain ⟨u, v, huv, hpoint, hval⟩ := ih
        have huneg : padicValRat 2 u < 0 := by
          rw [hval]
          omega
        obtain ⟨u', v', huv', hdouble, hval'⟩ := double_step huv huneg
        refine ⟨u', v', huv', ?_, ?_⟩
        · rw [pow_succ, mul_nsmul, hpoint]
          exact hdouble
        · rw [hval', hval]
          push_cast
          omega
  have distinct_doubles : Function.Injective (fun n : ℕ => (2 ^ n) • P) := by
    intro n m heq
    obtain ⟨u, v, huv, hn, hnv⟩ := iterated n
    obtain ⟨u', v', huv', hm, hmv⟩ := iterated m
    change (2 ^ n) • P = (2 ^ m) • P at heq
    rw [hn, hm] at heq
    simp only [WeierstrassCurve.Affine.Point.some.injEq] at heq
    have hvaleq := congrArg (padicValRat 2) heq.1
    rw [hnv, hmv] at hvaleq
    omega
  intro hfinite
  have hsubset : Set.range (fun n : ℕ => (2 ^ n) • P) ⊆
      (AddSubmonoid.multiples P : Set W.Point) := by
    rintro _ ⟨n, rfl⟩
    exact (AddSubmonoid.mem_multiples_iff _ _).2 ⟨2 ^ n, rfl⟩
  exact (Set.infinite_range_of_injective distinct_doubles)
    (hfinite.finite_multiples.subset hsubset)

/-- A point with a nonzero binary unit abscissa and positive binary ordinate
valuation has a double with negative abscissa valuation, hence infinite order. -/
theorem infinite_add_order_of_unit_x_positive_two_adic_y (b : ℤ) {x y : ℚ}
    (h : (mordellCurve b).Nonsingular x y) (hx0 : x ≠ 0)
    (hx : padicValRat 2 x = 0) (hy : 0 < padicValRat 2 y) :
    ¬ IsOfFinAddOrder (.some x y h : (mordellCurve b).Point) := by
  let W := mordellCurve b
  let P : W.Point := .some x y h
  have hy0 : y ≠ 0 := by
    intro hzero
    simp [hzero] at hy
  have hnegY : y ≠ W.negY x y := by
    intro heq
    have : y = -y := by simpa [W, mordellCurve, WeierstrassCurve.Affine.negY] using heq
    apply hy0
    linarith
  let x' := W.addX x x (W.slope x x y y)
  let y' := W.addY x x y (W.slope x x y y)
  have h' : W.Nonsingular x' y' :=
    WeierstrassCurve.Affine.nonsingular_add (W := W) h h
      (fun hxy => hnegY hxy.right)
  have hdouble : (2 : ℕ) • P = (.some x' y' h' : W.Point) := by
    simpa only [P, x', y', two_nsmul] using
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne (W := W) hnegY
  have hslope : W.slope x x y y = 3 * x ^ 2 / (2 * y) := by
    rw [WeierstrassCurve.Affine.slope_of_Y_ne (W := W) rfl hnegY]
    simp [W, mordellCurve, WeierstrassCurve.Affine.negY]
    ring
  have hx'form : x' = (3 * x ^ 2 / (2 * y)) ^ 2 - 2 * x := by
    simp only [x', WeierstrassCurve.Affine.addX, hslope]
    simp [W, mordellCurve]
    ring
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    change padicValRat 2 ((2 : ℕ) : ℚ) = 1
    rw [padicValRat.of_nat]
    exact_mod_cast (padicValNat_self (p := 2))
  have hthree : padicValRat 2 (3 : ℚ) = 0 := by
    change padicValRat 2 ((3 : ℕ) : ℚ) = 0
    rw [padicValRat.of_nat]
    exact_mod_cast (padicValNat.eq_zero_of_not_dvd (by norm_num : ¬2 ∣ 3))
  have hslope0 : 3 * x ^ 2 / (2 * y) ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hx0))
      (mul_ne_zero (by norm_num) hy0)
  have hslopeval : padicValRat 2 (3 * x ^ 2 / (2 * y)) =
      -(1 + padicValRat 2 y) := by
    rw [padicValRat.div
        (mul_ne_zero (by norm_num) (pow_ne_zero _ hx0))
        (mul_ne_zero (by norm_num) hy0),
      padicValRat.mul (by norm_num : (3 : ℚ) ≠ 0) (pow_ne_zero _ hx0),
      padicValRat.pow,
      padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hy0,
      hthree, htwo, hx]
    ring
  have hleadval : padicValRat 2 ((3 * x ^ 2 / (2 * y)) ^ 2) =
      -2 - 2 * padicValRat 2 y := by
    rw [padicValRat.pow, hslopeval]
    ring
  have htailval : padicValRat 2 (2 * x) = 1 := by
    rw [padicValRat.mul (by norm_num : (2 : ℚ) ≠ 0) hx0, htwo, hx]
    ring
  have hsum0 : (3 * x ^ 2 / (2 * y)) ^ 2 + -(2 * x) ≠ 0 := by
    intro hzero
    have heq : (3 * x ^ 2 / (2 * y)) ^ 2 = 2 * x := by linarith
    have hvaleq := congrArg (padicValRat 2) heq
    rw [hleadval, htailval] at hvaleq
    omega
  have hx' : padicValRat 2 x' < 0 := by
    have hval := padicValRat.add_eq_of_lt hsum0 (pow_ne_zero _ hslope0)
      (neg_ne_zero.mpr (mul_ne_zero (by norm_num) hx0)) (by
        rw [padicValRat.neg, hleadval, htailval]
        omega)
    rw [hx'form, sub_eq_add_neg, hval, hleadval]
    omega
  intro hfinite
  have hdoublefinite : IsOfFinAddOrder ((2 : ℕ) • P) := by
    obtain ⟨n, hn, hnP⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp hfinite
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨n, hn, ?_⟩
    calc
      n • ((2 : ℕ) • P) = (n * 2) • P := (mul_nsmul' P n 2).symm
      _ = (2 : ℕ) • (n • P) := mul_nsmul P n 2
      _ = 0 := by rw [hnP, smul_zero]
  exact (infinite_add_order_of_negative_two_adic_x b h' hx')
    (hdouble ▸ hdoublefinite)

#print axioms infinite_add_order_of_negative_two_adic_x
#print axioms infinite_add_order_of_unit_x_positive_two_adic_y

end D5.S3.Factorization.MordellTwoAdicNonTorsion
