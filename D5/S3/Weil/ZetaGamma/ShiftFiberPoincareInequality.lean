/- GID: D5/S3/Weil/ZetaGamma/ShiftFiberPoincareInequality
   generality: I
   mirror-B: D5/B/S3/Weil/ZetaGamma/ShiftFiberPoincareInequality
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Bound one real-line translation by its compact-support fiber gap. -/

import D5.S3.QuantumBounds.ReferenceFrameTaxOptimal
import D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

namespace D5.S3.Weil.ZetaGamma.ShiftFiberPoincareInequality

open MeasureTheory Set
open scoped BigOperators ComplexConjugate
open D5.S3.QuantumBounds.ReferenceFrameTax
open D5.S3.Weil.TestFunctions
open D5.S3.Weil.ZetaGamma.ArchimedeanJumpDecomposition

noncomputable section

/-- The maximum number of nonzero entries in a translation fiber through `[-L, L]`. -/
def shiftFiberCount (L a : ℝ) : ℕ :=
  ⌊2 * L / a⌋₊ + 1

/-- The first Dirichlet eigenvalue of a path with the support-controlled fiber length. -/
def shiftFiberGap (L a : ℝ) : ℝ :=
  4 * Real.sin (Real.pi / (2 * (shiftFiberCount L a + 1 : ℝ))) ^ 2

private theorem finite_complex_path_gap (N : ℕ) (hN : 1 ≤ N) (c : Fin N → ℂ) :
    4 * Real.sin (Real.pi / (2 * (N + 1 : ℝ))) ^ 2 *
        (∑ i : Fin N, Complex.normSq (c i)) ≤
      ∑ j : Fin (N + 1), Complex.normSq
        ((if hj : j.val < N then c ⟨j.val, hj⟩ else 0) -
          (if hj : 0 < j.val then
            c ⟨j.val - 1, lt_of_lt_of_le (Nat.sub_lt (by omega) (by omega)) (by omega)⟩
          else 0)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := N) (by omega : N ≠ 0)
  let average : Fin (k + 1) → ℂ := fun m ↦
    ((if _h : 0 < m.val then
        c ⟨m.val - 1, lt_of_le_of_lt (Nat.sub_le ..) m.isLt⟩ else 0) +
      (if _h : m.val + 1 < k + 1 then c ⟨m.val + 1, _h⟩ else 0)) / 2
  let mass : ℝ := ∑ i : Fin (k + 1), Complex.normSq (c i)
  let averagedMass : ℝ := ∑ i : Fin (k + 1), Complex.normSq (average i)
  let correlation : ℝ := ∑ i : Fin (k + 1), (conj (c i) * average i).re
  have hmass : 0 ≤ mass := Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have havg : 0 ≤ averagedMass := Finset.sum_nonneg fun _ _ ↦ Complex.normSq_nonneg _
  have hreal := nearestNeighborQuadratic_le_cos_sq (k + 1) (fun i ↦ (c i).re)
  have himag := nearestNeighborQuadratic_le_cos_sq (k + 1) (fun i ↦ (c i).im)
  have havg_bound :
      averagedMass ≤ Real.cos (Real.pi / ((k.succ : ℝ) + 1)) ^ 2 * mass := by
    dsimp only [averagedMass, mass, average]
    rw [show (∑ i : Fin (k + 1), Complex.normSq
        (((if _h : 0 < i.val then
            c ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩ else 0) +
          (if _h : i.val + 1 < k + 1 then c ⟨i.val + 1, _h⟩ else 0)) / 2)) =
        nearestNeighborQuadratic (fun i ↦ (c i).re) +
          nearestNeighborQuadratic (fun i ↦ (c i).im) by
      unfold nearestNeighborQuadratic
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hl : 0 < i.val <;> by_cases hr : i.val + 1 < k + 1 <;>
        simp [hl, hr, Complex.normSq_apply] <;> ring]
    rw [show (∑ i : Fin (k + 1), Complex.normSq (c i)) =
        (∑ i : Fin (k + 1), (c i).re ^ 2) + ∑ i : Fin (k + 1), (c i).im ^ 2 by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Complex.normSq_apply]
      ring]
    nlinarith
  have hcs : correlation ^ 2 ≤ mass * averagedMass := by
    let u : Fin (k + 1) × Fin 2 → ℝ :=
      fun p ↦ if p.2 = 0 then (c p.1).re else (c p.1).im
    let v : Fin (k + 1) × Fin 2 → ℝ := fun p ↦
      if p.2 = 0 then (average p.1).re else (average p.1).im
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin (k + 1) × Fin 2)) u v
    change (∑ p : Fin (k + 1) × Fin 2, u p * v p) ^ 2 ≤
      (∑ p : Fin (k + 1) × Fin 2, u p ^ 2) *
        ∑ p : Fin (k + 1) × Fin 2, v p ^ 2 at h
    simp_rw [Fintype.sum_prod_type] at h
    simp only [Fin.sum_univ_two, u, v, if_pos, one_ne_zero, if_false] at h
    simpa only [correlation, mass, averagedMass, Complex.normSq_apply,
      Complex.mul_re, Complex.conj_re, Complex.conj_im, neg_mul, sub_eq_add_neg,
      neg_neg, pow_two] using h
  have hcos : 0 ≤ Real.cos (Real.pi / ((k.succ : ℝ) + 1)) := by
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hangle : 0 ≤ Real.pi / ((k.succ : ℝ) + 1) :=
        div_nonneg Real.pi_pos.le (by positivity)
      linarith [Real.pi_pos]
    · have hN' : 2 ≤ k + 2 := by omega
      have hden : (2 : ℝ) ≤ (k.succ : ℝ) + 1 := by exact_mod_cast hN'
      exact (div_le_div_iff_of_pos_left Real.pi_pos (by positivity) (by positivity)).2 hden
  have hcorr : correlation ≤ Real.cos (Real.pi / ((k.succ : ℝ) + 1)) * mass := by
    by_cases hc : correlation ≤ 0
    · exact hc.trans (mul_nonneg hcos hmass)
    · have hcpos : 0 < correlation := lt_of_not_ge hc
      have hsq : correlation ^ 2 ≤
          (Real.cos (Real.pi / ((k.succ : ℝ) + 1)) * mass) ^ 2 := by
        calc
          correlation ^ 2 ≤ mass * averagedMass := hcs
          _ ≤ mass * (Real.cos (Real.pi / ((k.succ : ℝ) + 1)) ^ 2 * mass) :=
            mul_le_mul_of_nonneg_left havg_bound hmass
          _ = (Real.cos (Real.pi / ((k.succ : ℝ) + 1)) * mass) ^ 2 := by ring
      nlinarith [mul_nonneg hcos hmass]
  have henergy :
      (∑ j : Fin (k + 2), Complex.normSq
        ((if hj : j.val < k + 1 then c ⟨j.val, hj⟩ else 0) -
          (if hj : 0 < j.val then
            c ⟨j.val - 1, lt_of_lt_of_le (Nat.sub_lt (by omega) (by omega)) (by omega)⟩
          else 0))) = 2 * mass - 2 * correlation := by
    let left : Fin (k + 1) → ℂ := fun i ↦
      if hi : 0 < i.val then
        c ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩
      else 0
    let right : Fin (k + 1) → ℂ := fun i ↦
      if hi : i.val + 1 < k + 1 then c ⟨i.val + 1, hi⟩ else 0
    have c_castSucc (i : Fin k) (hi : i.val < k + 1) :
        c ⟨i.val, hi⟩ = c i.castSucc := by
      exact congrArg c (Fin.ext rfl)
    have c_succ (i : Fin k) (hi : i.val + 1 < k + 1) :
        c ⟨i.val + 1, hi⟩ = c i.succ := by
      exact congrArg c (Fin.ext rfl)
    have right_eq (i : Fin (k + 1)) :
        (if hi : i.val < k then c ⟨i.val + 1, by omega⟩ else 0) = right i := by
      by_cases hi : i.val < k
      · rw [dif_pos hi]
        simp only [right, dif_pos (by omega : i.val + 1 < k + 1)]
      · rw [dif_neg hi]
        simp only [right, dif_neg (by omega : ¬i.val + 1 < k + 1)]
    have hleft_right :
        (∑ i : Fin (k + 1), (conj (c i) * left i).re) =
          ∑ i : Fin (k + 1), (conj (c i) * right i).re := by
      calc
        (∑ i : Fin (k + 1), (conj (c i) * left i).re) =
            ∑ i : Fin k, (conj (c i.succ) * c i.castSucc).re := by
          rw [Fin.sum_univ_succ]
          simp [left, c_castSucc]
        _ = ∑ i : Fin k, (conj (c i.castSucc) * c i.succ).re := by
          apply Finset.sum_congr rfl
          intro i _hi
          simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
          ring
        _ = ∑ i : Fin (k + 1), (conj (c i) * right i).re := by
          rw [Fin.sum_univ_castSucc]
          simp [right, c_succ]
    have hcorr_forward :
        correlation = ∑ i : Fin (k + 1), (conj (c i) * right i).re := by
      dsimp only [correlation, average]
      calc
        (∑ i : Fin (k + 1),
          (conj (c i) *
            (((if _h : 0 < i.val then
                c ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le ..) i.isLt⟩ else 0) +
              (if _h : i.val + 1 < k + 1 then c ⟨i.val + 1, _h⟩ else 0)) / 2)).re) =
            ((∑ i : Fin (k + 1), (conj (c i) * left i).re) +
              ∑ i : Fin (k + 1), (conj (c i) * right i).re) / 2 := by
          rw [← Finset.sum_add_distrib, Finset.sum_div]
          apply Finset.sum_congr rfl
          intro i _hi
          simp only [left, right]
          split_ifs <;> simp_all [Complex.mul_re] <;> ring
        _ = ∑ i : Fin (k + 1), (conj (c i) * right i).re := by
          rw [hleft_right]
          ring
    have hright_mass :
        Complex.normSq (c 0) + ∑ i : Fin (k + 1), Complex.normSq (right i) = mass := by
      calc
        Complex.normSq (c 0) + ∑ i : Fin (k + 1), Complex.normSq (right i) =
            Complex.normSq (c 0) + ∑ i : Fin k, Complex.normSq (c i.succ) := by
          congr 1
          rw [Fin.sum_univ_castSucc]
          simp [right, c_succ]
        _ = mass := by
          dsimp only [mass]
          rw [Fin.sum_univ_succ]
    have hcross :
        (∑ i : Fin (k + 1), (right i * conj (c i)).re) = correlation := by
      rw [hcorr_forward]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [mul_comm]
    have hcross_two :
        (∑ i : Fin (k + 1), 2 * (right i * conj (c i)).re) = 2 * correlation := by
      rw [← Finset.mul_sum, hcross]
    have hmass_eq : (∑ i : Fin (k + 1), Complex.normSq (c i)) = mass := rfl
    rw [Fin.sum_univ_succ]
    simp
    simp_rw [right_eq]
    simp_rw [Complex.normSq_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hcross_two, hmass_eq]
    nlinarith [hright_mass]
  rw [henergy]
  rw [show 4 * Real.sin (Real.pi / (2 * ((k.succ : ℝ) + 1))) ^ 2 =
      2 - 2 * Real.cos (Real.pi / ((k.succ : ℝ) + 1)) by
    rw [show Real.pi / ((k.succ : ℝ) + 1) =
        2 * (Real.pi / (2 * ((k.succ : ℝ) + 1))) by
      field_simp]
    rw [Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (Real.pi / (2 * ((k.succ : ℝ) + 1)))]]
  nlinarith

private theorem integral_fin_shifted_intervals (g : ℝ → ℝ) (hg : Continuous g)
    (n : ℕ) (b a : ℝ) :
    (∫ r in 0..a, ∑ j : Fin n, g (r + (b + (j : ℕ) * a))) =
      ∫ x in b..b + n * a, g x := by
  calc
    (∫ r in 0..a, ∑ j : Fin n, g (r + (b + (j : ℕ) * a))) =
        ∑ j : Fin n, ∫ r in 0..a, g (r + (b + (j : ℕ) * a)) := by
      apply intervalIntegral.integral_finsetSum
      intro j _hj
      exact (hg.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    _ = ∑ j ∈ Finset.range n,
        ∫ x in b + (j : ℝ) * a..b + ((j + 1 : ℕ) : ℝ) * a, g x := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Finset.mem_range] at hj
      simp only [hj, ↓reduceDIte]
      rw [intervalIntegral.integral_comp_add_right]
      congr 1 <;> push_cast <;> ring
    _ = ∫ x in b..b + n * a, g x := by
      simpa only [Nat.cast_zero, zero_mul, add_zero] using
        (intervalIntegral.sum_integral_adjacent_intervals
          (a := fun j : ℕ ↦ b + (j : ℝ) * a) (n := n)
          (fun j hj ↦ hg.intervalIntegrable _ _))

/-- A compactly supported Weil test has the sharp Dirichlet gap along every positive shift. -/
theorem shift_fiber_poincare_inequality (f : WeilTestFunction) (L a : ℝ) (ha : 0 < a)
    (hSupport : Function.support (f : ℝ → ℂ) ⊆ Icc (-L) L) :
    translationEnergy f a ≥ shiftFiberGap L a * l2Mass f := by
  by_cases hL : 0 ≤ L
  swap
  · have hfzero : ∀ x : ℝ, f x = 0 := by
      intro x
      by_contra hx
      have hxSupport := hSupport hx
      exact hL (by linarith [hxSupport.1, hxSupport.2])
    simp [translationEnergy, l2Mass, hfzero]
  let N := shiftFiberCount L a
  have hN : 1 ≤ N := by
    simp [N, shiftFiberCount]
  have hcover : 2 * L < (N : ℝ) * a := by
    have hratio : 2 * L / a < ((⌊2 * L / a⌋₊ : ℕ) : ℝ) + 1 :=
      Nat.lt_floor_add_one (2 * L / a)
    calc
      2 * L = (2 * L / a) * a := (div_mul_cancel₀ _ ha.ne').symm
      _ < (((⌊2 * L / a⌋₊ : ℕ) : ℝ) + 1) * a :=
        mul_lt_mul_of_pos_right hratio ha
      _ = (N : ℝ) * a := by simp [N, shiftFiberCount, Nat.cast_add, Nat.cast_one]
  let massIntegrand : ℝ → ℝ := fun x ↦ Complex.normSq (f x)
  let energyIntegrand : ℝ → ℝ := fun x ↦ Complex.normSq (f x - f (x - a))
  have hmassContinuous : Continuous massIntegrand := by
    exact Complex.continuous_normSq.comp f.continuous
  have henergyContinuous : Continuous energyIntegrand := by
    exact Complex.continuous_normSq.comp
      (f.continuous.sub (f.continuous.comp (continuous_id.sub continuous_const)))
  have hmassInterval :
      (∫ x in -L..-L + N * a, massIntegrand x) = l2Mass f := by
    have hlower : -L ≤ -L + (N : ℝ) * a := by
      have : 0 ≤ (N : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha.le
      linarith
    rw [intervalIntegral.integral_of_le hlower]
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · rfl
    filter_upwards [(volume : Measure ℝ).ae_ne (-L)] with x hx hOutside
    have hxBounds : x < -L ∨ L < x := by
      simp only [mem_Ioc, not_and_or, not_lt] at hOutside
      rcases hOutside with hxlow | hxhigh
      · exact Or.inl (lt_of_le_of_ne hxlow hx)
      · exact Or.inr (by
          have hupper : -L + (N : ℝ) * a < x := lt_of_not_ge hxhigh
          linarith [hcover])
    have hfx : f x = 0 := by
      by_contra hne
      have hxmem := hSupport hne
      rcases hxBounds with hxlow | hxhigh
      · exact (not_lt_of_ge hxmem.1) hxlow
      · exact (not_lt_of_ge hxmem.2) hxhigh
    simp [massIntegrand, hfx]
  have henergyInterval :
      (∫ x in -L..-L + ((N + 1 : ℕ) : ℝ) * a, energyIntegrand x) =
        translationEnergy f a := by
    have hlower : -L ≤ -L + ((N + 1 : ℕ) : ℝ) * a := by
      have : 0 ≤ ((N + 1 : ℕ) : ℝ) * a := mul_nonneg (Nat.cast_nonneg _) ha.le
      linarith
    rw [intervalIntegral.integral_of_le hlower]
    rw [setIntegral_eq_integral_of_ae_compl_eq_zero]
    · rfl
    filter_upwards [(volume : Measure ℝ).ae_ne (-L)] with x hx hOutside
    have hxBounds : x < -L ∨ L + a < x := by
      simp only [mem_Ioc, not_and_or, not_lt] at hOutside
      rcases hOutside with hxlow | hxhigh
      · exact Or.inl (lt_of_le_of_ne hxlow hx)
      · exact Or.inr (by
          have hupper : -L + ((N + 1 : ℕ) : ℝ) * a < x := lt_of_not_ge hxhigh
          norm_num [Nat.cast_add, Nat.cast_one] at hupper
          linarith [hcover])
    have hfx : f x = 0 := by
      by_contra hne
      have hxmem := hSupport hne
      rcases hxBounds with hxlow | hxhigh
      · exact (not_lt_of_ge hxmem.1) hxlow
      · exact (not_lt_of_ge hxmem.2) (by linarith)
    have hfxa : f (x - a) = 0 := by
      by_contra hne
      have hxmem := hSupport hne
      rcases hxBounds with hxlow | hxhigh
      · exact (not_lt_of_ge hxmem.1) (by linarith)
      · exact (not_lt_of_ge hxmem.2) (by linarith)
    simp [energyIntegrand, hfx, hfxa]
  have hpoint (r : ℝ) (hr : r ∈ Ioo 0 a) :
      shiftFiberGap L a *
          (∑ j : Fin N, massIntegrand (r + (-L + (j : ℕ) * a))) ≤
        ∑ j : Fin (N + 1), energyIntegrand (r + (-L + (j : ℕ) * a)) := by
    let c : Fin N → ℂ := fun j ↦ f (r + (-L + (j : ℕ) * a))
    have hleftZero : f (r - L - a) = 0 := by
      by_contra hne
      have hmem := hSupport hne
      exact (not_lt_of_ge hmem.1) (by linarith [hr.2])
    have hrightZero : f (r - L + (N : ℝ) * a) = 0 := by
      by_contra hne
      have hmem := hSupport hne
      exact (not_lt_of_ge hmem.2) (by linarith [hr.1, hcover])
    have first_eq (j : Fin (N + 1)) :
        (if hj : j.val < N then c ⟨j.val, hj⟩ else 0) =
          f (r + (-L + (j : ℕ) * a)) := by
      by_cases hj : j.val < N
      · simp [hj, c]
      · rw [dif_neg hj]
        have hjval : j.val = N := by omega
        rw [hjval]
        convert hrightZero.symm using 1 <;> ring
    have second_eq (j : Fin (N + 1)) :
        (if hj : 0 < j.val then
            c ⟨j.val - 1, lt_of_lt_of_le (Nat.sub_lt hj Nat.zero_lt_one)
              (Nat.le_of_lt_succ j.isLt)⟩
          else 0) = f (r + (-L + (j : ℕ) * a) - a) := by
      by_cases hj : 0 < j.val
      · rw [dif_pos hj]
        simp only [c]
        congr 1
        rw [Nat.cast_sub (by omega : 1 ≤ j.val)]
        push_cast
        ring
      · rw [dif_neg hj]
        have hjval : j.val = 0 := by omega
        rw [hjval]
        convert hleftZero.symm using 1 <;> norm_num <;> ring
    calc
      shiftFiberGap L a *
          (∑ j : Fin N, massIntegrand (r + (-L + (j : ℕ) * a))) ≤
          ∑ j : Fin (N + 1), Complex.normSq
            ((if hj : j.val < N then c ⟨j.val, hj⟩ else 0) -
              (if hj : 0 < j.val then
                c ⟨j.val - 1, lt_of_lt_of_le (Nat.sub_lt hj Nat.zero_lt_one)
                  (Nat.le_of_lt_succ j.isLt)⟩
              else 0)) := by
        simpa only [shiftFiberGap, massIntegrand, N, c] using
          finite_complex_path_gap N hN c
      _ = ∑ j : Fin (N + 1),
          energyIntegrand (r + (-L + (j : ℕ) * a)) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [first_eq j, second_eq j]
  have hmassFiberContinuous : Continuous (fun r : ℝ ↦
      ∑ j : Fin N, massIntegrand (r + (-L + (j : ℕ) * a))) := by
    exact continuous_finsetSum _ fun j _ ↦
      hmassContinuous.comp (continuous_id.add continuous_const)
  have henergyFiberContinuous : Continuous (fun r : ℝ ↦
      ∑ j : Fin (N + 1), energyIntegrand (r + (-L + (j : ℕ) * a))) := by
    exact continuous_finsetSum _ fun j _ ↦
      henergyContinuous.comp (continuous_id.add continuous_const)
  have hintegral :
      (∫ r in 0..a, shiftFiberGap L a *
          (∑ j : Fin N, massIntegrand (r + (-L + (j : ℕ) * a)))) ≤
        ∫ r in 0..a,
          ∑ j : Fin (N + 1), energyIntegrand (r + (-L + (j : ℕ) * a)) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo ha.le
    · exact (continuous_const.mul hmassFiberContinuous).intervalIntegrable _ _
    · exact henergyFiberContinuous.intervalIntegrable _ _
    · intro r hr
      exact hpoint r hr
  rw [intervalIntegral.integral_const_mul,
    integral_fin_shifted_intervals massIntegrand hmassContinuous N (-L) a,
    integral_fin_shifted_intervals energyIntegrand henergyContinuous (N + 1) (-L) a,
    hmassInterval, henergyInterval] at hintegral
  exact hintegral

#print axioms shift_fiber_poincare_inequality

end

end D5.S3.Weil.ZetaGamma.ShiftFiberPoincareInequality
