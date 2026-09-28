/- GID: D5/S3/Analytic/PolynomialReflectionNumerator
   generality: G
   mirror-B: D5/B/S3/Analytic/PolynomialReflectionNumerator
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.RingTheory.Polynomial.HilbertPoly]
   utility: none
   digest: Reflection gives an exact-degree palindromic numerator. -/

import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Analytic.PolynomialReflectionNumerator

open Polynomial

private theorem preHilbertPoly_reflect (n j : ℕ) (hj : j ≤ n) :
    (preHilbertPoly ℝ n j).comp (-1 - X) =
      (-1 : ℝ[X]) ^ n * preHilbertPoly ℝ n (n - j) := by
  apply Polynomial.funext
  intro x
  simp only [eval_comp, eval_sub, eval_neg, eval_one, eval_X, eval_mul,
    eval_pow, eval_neg, eval_one]
  simp only [preHilbertPoly, eval_smul, smul_eq_mul, eval_comp, eval_sub,
    eval_add, eval_X, eval_C, eval_one]
  have hleft : -1 - x - (j : ℝ) + 1 = -(x + j) := by ring
  have hright : x - ((n - j : ℕ) : ℝ) + 1 = x + j - n + 1 := by
    rw [Nat.cast_sub hj]
    ring
  rw [hleft, hright]
  rw [ascPochhammer_eval_neg_eq_descPochhammer,
    descPochhammer_eval_eq_ascPochhammer]
  ring

private theorem hilbertPoly_reflect (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    (hilbertPoly p (n + 1)).comp (-1 - X) =
      (-1 : ℝ[X]) ^ n * hilbertPoly (p.reflect n) (n + 1) := by
  rw [hilbertPoly_succ, hilbertPoly_succ, reflect_support]
  simp only [sum_comp, smul_comp]
  rw [Finset.mul_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro j hj
    have hjn : j ≤ n := (le_natDegree_of_mem_supp j hj).trans hp
    rw [preHilbertPoly_reflect n j hjn]
    simp only [coeff_reflect, revAt_invol, smul_eq_C_mul]
    rw [revAt_le hjn]
    ring
  · exact (revAt n).injective.injOn

private def binomialSequence : Polynomial.Sequence ℝ where
  elems' i := preHilbertPoly ℝ i 0
  degree_eq' i := by
    rw [degree_eq_natDegree]
    · exact congrArg (fun j : ℕ => (j : WithBot ℕ))
        (natDegree_preHilbertPoly ℝ i 0)
    · have h : (preHilbertPoly ℝ i 0).leadingCoeff ≠ 0 := by
        rw [leadingCoeff_preHilbertPoly]
        exact inv_ne_zero (by exact_mod_cast Nat.factorial_ne_zero i)
      exact leadingCoeff_ne_zero.mp h

private theorem binomial_expansion (n : ℕ) (p : ℝ[X]) (hp : p.natDegree ≤ n) :
    ∃ a : ℕ → ℝ,
      ∑ i ∈ Finset.range (n + 1), a i • preHilbertPoly ℝ i 0 = p := by
  have hcoeff : ∀ i ≤ n, IsUnit (binomialSequence i).leadingCoeff := by
    intro i _
    change IsUnit (preHilbertPoly ℝ i 0).leadingCoeff
    rw [leadingCoeff_preHilbertPoly]
    exact isUnit_iff_ne_zero.mpr (inv_ne_zero (by positivity))
  have hmem : p ∈ degreeLE ℝ n := by
    apply mem_degreeLE.mpr
    exact degree_le_natDegree.trans (by exact_mod_cast hp)
  rw [← binomialSequence.span_degreeLE hcoeff] at hmem
  change p ∈ Submodule.span ℝ (binomialSequence '' Set.Iic n) at hmem
  have hrange : (Finset.range (n + 1) : Set ℕ) = Set.Iic n := by
    ext i
    simp
  rw [← hrange] at hmem
  obtain ⟨a, ha⟩ := (Submodule.mem_span_image_finset_iff_exists_fun'
    (R := ℝ) (M := ℝ[X]) (v := binomialSequence)
    (s := Finset.range (n + 1))).mp hmem
  exact ⟨a, ha⟩

private def series (p : ℝ[X]) : PowerSeries ℝ :=
  PowerSeries.mk (fun k => p.eval (k : ℝ))

private theorem series_binomial (i : ℕ) :
    series (preHilbertPoly ℝ i 0) *
      (1 - PowerSeries.X) ^ (i + 1) = 1 := by
  have heval (k : ℕ) : (preHilbertPoly ℝ i 0).eval (k : ℝ) =
      ((i + k).choose i : ℝ) := by
    simpa [Nat.add_comm] using
      (preHilbertPoly_eq_choose_sub_add (F := ℝ) i (k := 0) (n := k) (Nat.zero_le k))
  simp only [series, heval]
  exact PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℝ i

private theorem series_binomial_common (n i : ℕ) (hi : i ≤ n) :
    series (preHilbertPoly ℝ i 0) * (1 - PowerSeries.X) ^ (n + 1) =
      (1 - PowerSeries.X) ^ (n - i) := by
  have h := series_binomial i
  have hadd : n + 1 = (i + 1) + (n - i) := by omega
  rw [hadd, pow_add, ← mul_assoc, h, one_mul]

private theorem mk_choose_shift (i : ℕ) :
    (PowerSeries.mk (fun k => (k.choose i : ℝ)) : PowerSeries ℝ) =
      PowerSeries.X ^ i * PowerSeries.mk (fun k => ((i + k).choose i : ℝ)) := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul']
  split_ifs with hik
  · rw [PowerSeries.coeff_mk]
    have hki : i + (k - i) = k := by omega
    rw [hki]
  · simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hik)]

private theorem series_binomial_reflected (i : ℕ) :
    series ((preHilbertPoly ℝ i 0).comp (-1 - X)) *
      (1 - PowerSeries.X) ^ (i + 1) =
        (-1 : ℝ) ^ i • PowerSeries.X ^ i := by
  have heval (k : ℕ) :
      ((preHilbertPoly ℝ i 0).comp (-1 - X)).eval (k : ℝ) =
        (-1 : ℝ) ^ i * (k.choose i : ℝ) := by
    simp only [preHilbertPoly, eval_comp, eval_sub, eval_neg, eval_one, eval_X,
      eval_smul, smul_eq_mul, eval_comp, eval_add, eval_C, Nat.cast_zero, sub_zero]
    have hx : -1 - (k : ℝ) + 1 = -(k : ℝ) := by ring
    rw [hx, ascPochhammer_eval_neg_eq_descPochhammer]
    rw [Nat.cast_choose_eq_descPochhammer_div]
    ring
  have hseries : series ((preHilbertPoly ℝ i 0).comp (-1 - X)) =
      (-1 : ℝ) ^ i •
        (PowerSeries.mk (fun k => (k.choose i : ℝ)) : PowerSeries ℝ) := by
    apply PowerSeries.ext
    intro k
    simp [series, heval, smul_eq_mul]
  rw [hseries, mk_choose_shift]
  rw [smul_mul_assoc, mul_assoc, PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℝ i]
  simp

private theorem series_binomial_reflected_common (n i : ℕ) (hi : i ≤ n) :
    series ((preHilbertPoly ℝ i 0).comp (-1 - X)) *
      (1 - PowerSeries.X) ^ (n + 1) =
        (-1 : ℝ) ^ i •
          (PowerSeries.X ^ i * (1 - PowerSeries.X) ^ (n - i)) := by
  have hadd : n + 1 = (i + 1) + (n - i) := by omega
  rw [hadd, pow_add, ← mul_assoc, series_binomial_reflected]
  rw [smul_mul_assoc]

private theorem series_smul (a : ℝ) (p : ℝ[X]) :
    series (a • p) = a • series p := by
  ext k
  simp [series, eval_smul, smul_eq_mul]

private theorem series_sum {ι : Type*} (s : Finset ι) (p : ι → ℝ[X]) :
    series (∑ i ∈ s, p i) = ∑ i ∈ s, series (p i) := by
  ext k
  simp [series, eval_finsetSum]

private theorem natDegree_one_sub_X_pow_le (d : ℕ) :
    ((1 - X : ℝ[X]) ^ d).natDegree ≤ d := by
  have hbase : (1 - X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp)
  exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left d hbase)

private theorem reflect_one_sub_X_pow (d : ℕ) :
    ((1 - X : ℝ[X]) ^ d).reflect d = (X - 1) ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [pow_succ,
        reflect_mul ((1 - X : ℝ[X]) ^ d) (1 - X)
          (natDegree_one_sub_X_pow_le d)
          (by exact (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp))]
      simp [ih, reflect_sub, pow_succ]

private theorem reflect_one_sub_X_basis (n i : ℕ) (hi : i ≤ n) :
    ((1 - X : ℝ[X]) ^ (n - i)).reflect n =
      (-1 : ℝ[X]) ^ (n - i) * X ^ i * (1 - X) ^ (n - i) := by
  have hni : n - i + i = n := Nat.sub_add_cancel hi
  calc
    ((1 - X : ℝ[X]) ^ (n - i)).reflect n =
        (((1 - X : ℝ[X]) ^ (n - i)) * 1).reflect ((n - i) + i) := by
          rw [hni, mul_one]
    _ = ((1 - X : ℝ[X]) ^ (n - i)).reflect (n - i) * (1 : ℝ[X]).reflect i := by
          exact reflect_mul ((1 - X : ℝ[X]) ^ (n - i)) 1
            (natDegree_one_sub_X_pow_le (n - i)) (by simp)
    _ = _ := by
      rw [reflect_one_sub_X_pow]
      simp only [reflect_one, mul_comm]
      rw [show (X - 1 : ℝ[X]) = -(1 - X) by ring, neg_pow]
      ring

private theorem reflect_sum {ι : Type*} (n : ℕ) (s : Finset ι)
    (p : ι → ℝ[X]) :
    (∑ i ∈ s, p i).reflect n = ∑ i ∈ s, (p i).reflect n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, reflect_add, ih]

private theorem reflect_numerator (n : ℕ) (a : ℕ → ℝ) :
    (-1 : ℝ[X]) ^ n *
      (∑ i ∈ Finset.range (n + 1),
        C (a i) * (1 - X) ^ (n - i)).reflect n =
      ∑ i ∈ Finset.range (n + 1),
        C (a i) * (-1 : ℝ[X]) ^ i * X ^ i * (1 - X) ^ (n - i) := by
  rw [reflect_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := by
    have := Finset.mem_range.mp hi
    omega
  rw [reflect_C_mul, reflect_one_sub_X_basis n i hin]
  have hsign : (-1 : ℝ[X]) ^ n * (-1 : ℝ[X]) ^ (n - i) = (-1 : ℝ[X]) ^ i := by
    have hni : n - i + i = n := Nat.sub_add_cancel hin
    have hs : ((-1 : ℝ[X]) ^ (n - i)) ^ 2 = 1 := by
      simp [← pow_mul]
    calc
      (-1 : ℝ[X]) ^ n * (-1 : ℝ[X]) ^ (n - i) =
          (-1 : ℝ[X]) ^ (n + (n - i)) := by rw [pow_add]
      _ = (-1 : ℝ[X]) ^ ((n - i) + i + (n - i)) := by congr 1; omega
      _ =
          ((-1 : ℝ[X]) ^ (n - i) * (-1 : ℝ[X]) ^ i) *
            (-1 : ℝ[X]) ^ (n - i) := by rw [pow_add, pow_add]
      _ =
        ((-1 : ℝ[X]) ^ (n - i)) ^ 2 * (-1 : ℝ[X]) ^ i := by ring
      _ = _ := by rw [hs]; ring
  calc
    (-1 : ℝ[X]) ^ n *
        (C (a i) * ((-1 : ℝ[X]) ^ (n - i) * X ^ i * (1 - X) ^ (n - i))) =
      C (a i) * ((-1 : ℝ[X]) ^ n * (-1 : ℝ[X]) ^ (n - i)) *
        X ^ i * (1 - X) ^ (n - i) := by ring
    _ = _ := by rw [hsign]

private theorem polynomial_series_numerator (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n) :
    ∃ r : ℝ[X], r.natDegree ≤ n ∧
      series p * (1 - PowerSeries.X) ^ (n + 1) = (r : PowerSeries ℝ) ∧
      series (p.comp (-1 - X)) * (1 - PowerSeries.X) ^ (n + 1) =
        (((-1 : ℝ[X]) ^ n * r.reflect n : ℝ[X]) : PowerSeries ℝ) := by
  obtain ⟨a, ha⟩ := binomial_expansion n p hp
  let r : ℝ[X] := ∑ i ∈ Finset.range (n + 1),
    C (a i) * (1 - X) ^ (n - i)
  have hrdeg : r.natDegree ≤ n := by
    dsimp [r]
    apply natDegree_sum_le_of_forall_le
    intro i hi
    have hin : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    calc
      (C (a i) * (1 - X) ^ (n - i)).natDegree ≤
          (C (a i)).natDegree + ((1 - X : ℝ[X]) ^ (n - i)).natDegree :=
        natDegree_mul_le
      _ ≤ n := by
        calc
          _ ≤ 0 + (n - i) := by
            apply Nat.add_le_add
            · simp
            · have hbase : (1 - X : ℝ[X]).natDegree ≤ 1 := by
                exact (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp)
              have hmul := Nat.mul_le_mul_left (n - i) hbase
              exact natDegree_pow_le.trans (by simpa using hmul)
          _ ≤ n := by omega
  refine ⟨r, hrdeg, ?_, ?_⟩
  · rw [← ha, series_sum, Finset.sum_mul]
    simp only [series_smul]
    calc
      (∑ i ∈ Finset.range (n + 1),
        (a i • series (preHilbertPoly ℝ i 0)) *
          (1 - PowerSeries.X) ^ (n + 1)) =
        ∑ i ∈ Finset.range (n + 1),
          a i • (1 - PowerSeries.X) ^ (n - i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hin : i ≤ n := by
              have := Finset.mem_range.mp hi
              omega
            rw [smul_mul_assoc, series_binomial_common n i hin]
      _ = (r : PowerSeries ℝ) := by
        change _ = (Polynomial.coeToPowerSeries.ringHom (R := ℝ)) r
        simp [r, map_sum, map_mul, map_pow, map_sub, map_one,
          Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
  · have hcomp : p.comp (-1 - X) =
        ∑ i ∈ Finset.range (n + 1),
          a i • (preHilbertPoly ℝ i 0).comp (-1 - X) := by
      rw [← ha, sum_comp]
      simp [smul_comp]
    rw [hcomp, series_sum, Finset.sum_mul]
    simp only [series_smul]
    calc
      (∑ i ∈ Finset.range (n + 1),
        (a i • series ((preHilbertPoly ℝ i 0).comp (-1 - X))) *
          (1 - PowerSeries.X) ^ (n + 1)) =
        ∑ i ∈ Finset.range (n + 1),
          a i • ((-1 : ℝ) ^ i •
            (PowerSeries.X ^ i * (1 - PowerSeries.X) ^ (n - i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hin : i ≤ n := by
              have := Finset.mem_range.mp hi
              omega
            rw [smul_mul_assoc, series_binomial_reflected_common n i hin]
      _ = (((-1 : ℝ[X]) ^ n * r.reflect n : ℝ[X]) : PowerSeries ℝ) := by
        rw [reflect_numerator n a]
        change _ = (Polynomial.coeToPowerSeries.ringHom (R := ℝ))
          (∑ i ∈ Finset.range (n + 1),
            C (a i) * (-1 : ℝ[X]) ^ i * X ^ i * (1 - X) ^ (n - i))
        simp [map_sum, map_mul, map_pow, map_sub, map_one,
          Polynomial.coeToPowerSeries.ringHom_apply, PowerSeries.smul_eq_C_mul]
        apply Finset.sum_congr rfl
        intro i hi
        ring

/-- Reflection of a degree-bounded polynomial about -1/2 reverses its
generating-series numerator; normalization at zero makes the degree exact. -/
theorem palindromic_numerator_of_reflection (n : ℕ) (p : ℝ[X])
    (hp : p.natDegree ≤ n)
    (href : p.comp (-1 - X) = (-1 : ℝ) ^ n • p)
    (hzero : p.eval 0 = 1) :
    ∃ r : ℝ[X], r.natDegree = n ∧
      PowerSeries.mk (fun k => p.eval (k : ℝ)) *
        (1 - PowerSeries.X) ^ (n + 1) = (r : PowerSeries ℝ) ∧
      ∀ j ≤ n, r.coeff j = r.coeff (n - j) := by
  change ∃ r : ℝ[X], r.natDegree = n ∧
    series p * (1 - PowerSeries.X) ^ (n + 1) = (r : PowerSeries ℝ) ∧
    ∀ j ≤ n, r.coeff j = r.coeff (n - j)
  obtain ⟨r, hrdeg, hseries, hrefseries⟩ := polynomial_series_numerator n p hp
  have hreflect : r.reflect n = r := by
    have hmul : (-1 : ℝ[X]) ^ n * r = (-1 : ℝ[X]) ^ n * r.reflect n := by
      apply Polynomial.coe_injective ℝ
      have h := hrefseries
      rw [href, series_smul, smul_mul_assoc, hseries] at h
      simpa [Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_neg,
        Polynomial.coe_one, Polynomial.coe_smul, PowerSeries.smul_eq_C_mul] using h
    have hnz : (-1 : ℝ[X]) ^ n ≠ 0 := by simp
    exact (mul_left_cancel₀ hnz hmul).symm
  have hc0 : r.coeff 0 = 1 := by
    have h := congrArg (fun f : PowerSeries ℝ => f.coeff 0) hseries
    simpa [series, hzero] using h.symm
  have hcn : r.coeff n = 1 := by
    have h := congrArg (fun q : ℝ[X] => q.coeff 0) hreflect
    simpa [coeff_reflect, revAt_zero, hc0] using h
  have hrdeg' : r.natDegree = n := by
    apply le_antisymm hrdeg
    exact le_natDegree_of_ne_zero (by rw [hcn]; norm_num)
  refine ⟨r, hrdeg', hseries, ?_⟩
  intro j hj
  have h := congrArg (fun q : ℝ[X] => q.coeff j) hreflect
  simpa [coeff_reflect, revAt_le hj] using h.symm


end D5.S3.Analytic.PolynomialReflectionNumerator
