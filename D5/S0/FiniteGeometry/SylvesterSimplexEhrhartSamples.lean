/- GID: D5/S0/FiniteGeometry/SylvesterSimplexEhrhartSamples
   generality: G
   mirror-B: D5/B/S0/FiniteGeometry/SylvesterSimplexEhrhartSamples
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact sampled count polynomials for the source Sylvester simplex. -/

import D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.WellKnown

noncomputable section

namespace D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples

open scoped BigOperators

open D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

open private axisScale_pos baseWeight base_axisScale_dvd_mass naturalWeightedMass
  IsBaseSolution IsInteriorShiftSolution ehrhartCount_base_eq_solution_card
  ehrhartCount_source_decomposition no_interior_shift_solution_zero two_le_sylvester from
  D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity

private def partitionWeight (d : ℕ) : Option (Fin d) → ℕ
  | none => 1
  | some i => baseWeight d i

/-- The geometric series whose nonzero exponents are multiples of `w`. -/
private def geometricFactor (w : ℕ) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if w ∣ n then 1 else 0

private lemma geometricFactor_eq_subst (w : ℕ) (hw : 0 < w) :
    geometricFactor w =
      (PowerSeries.mk 1 : PowerSeries ℚ).subst (PowerSeries.X ^ w) := by
  ext n
  rw [PowerSeries.coeff_subst_X_pow hw.ne']
  simp [geometricFactor]

private lemma geometricFactor_mul_one_sub_X_pow (w : ℕ) (hw : 0 < w) :
    geometricFactor w * (1 - PowerSeries.X ^ w) = 1 := by
  rw [geometricFactor_eq_subst w hw]
  let φ : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ :=
    PowerSeries.substAlgHom (PowerSeries.HasSubst.X_pow hw.ne')
  have hφ (f : PowerSeries ℚ) :
      φ f = f.subst (PowerSeries.X ^ w) := by
    exact congrFun
      (PowerSeries.coe_substAlgHom (PowerSeries.HasSubst.X_pow hw.ne')) f
  have hφX : φ PowerSeries.X = PowerSeries.X ^ w :=
    PowerSeries.substAlgHom_X (PowerSeries.HasSubst.X_pow hw.ne')
  rw [← hφ]
  calc
    φ (PowerSeries.mk 1) * (1 - PowerSeries.X ^ w) =
        φ (PowerSeries.mk 1) * φ (1 - PowerSeries.X) := by
      rw [map_sub, map_one, hφX]
    _ = φ ((PowerSeries.mk 1 : PowerSeries ℚ) * (1 - PowerSeries.X)) :=
      (map_mul φ _ _).symm
    _ = φ 1 := by rw [PowerSeries.mk_one_mul_one_sub_eq_one]
    _ = 1 := map_one φ

/-- The exact source-specific restricted-partition generating series, including slack. -/
private def restrictedPartitionSeries (d : ℕ) : PowerSeries ℚ :=
  ∏ j : Option (Fin d), geometricFactor (partitionWeight d j)

private lemma baseWeight_pos (d : ℕ) (hd : 1 ≤ d) (i : Fin d) :
    0 < baseWeight d i := by
  rw [baseWeight]
  apply Nat.div_pos
  · exact Nat.le_of_dvd (Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd)))
      (base_axisScale_dvd_mass d hd i)
  · exact axisScale_pos d 0 i

private lemma partitionWeight_pos (d : ℕ) (hd : 1 ≤ d) (j : Option (Fin d)) :
    0 < partitionWeight d j := by
  cases j with
  | none => simp [partitionWeight]
  | some i => simpa [partitionWeight] using baseWeight_pos d hd i

private def finiteGeometricPolynomial (w M : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range (M / w), Polynomial.X ^ (j * w)

private def periodNumerator (d : ℕ) : Polynomial ℚ :=
  ∏ j : Option (Fin d), finiteGeometricPolynomial (partitionWeight d j)
    (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)

private lemma partitionWeight_dvd_period (d : ℕ) (hd : 1 ≤ d)
    (j : Option (Fin d)) :
    partitionWeight d j ∣
      D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1 := by
  cases j with
  | none => simp [partitionWeight]
  | some i =>
      refine ⟨axisScale d 0 i, ?_⟩
      rw [partitionWeight, baseWeight]
      exact (Nat.div_mul_cancel (base_axisScale_dvd_mass d hd i)).symm

private lemma finiteGeometricPolynomial_natDegree_le (w M : ℕ)
    (hw : 0 < w) (hdiv : w ∣ M) :
    (finiteGeometricPolynomial w M).natDegree ≤ M - w := by
  rw [finiteGeometricPolynomial]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  simp only [Finset.mem_range] at hj
  rw [Polynomial.natDegree_X_pow]
  have hM : M / w * w = M := Nat.div_mul_cancel hdiv
  apply Nat.le_sub_of_add_le
  rw [← Nat.add_one_mul, ← hM]
  exact Nat.mul_le_mul_right w (by omega)

private lemma periodNumerator_natDegree_le (d : ℕ) (hd : 1 ≤ d) :
    (periodNumerator d).natDegree ≤
      (d + 1) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 2) := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  rw [periodNumerator]
  refine (Polynomial.natDegree_prod_le Finset.univ _).trans ?_
  calc
    ∑ j : Option (Fin d),
        (finiteGeometricPolynomial (partitionWeight d j) M).natDegree ≤
        ∑ _j : Option (Fin d), (M - 1) := by
      apply Finset.sum_le_sum
      intro j _
      have hw := partitionWeight_pos d hd j
      refine (finiteGeometricPolynomial_natDegree_le _ M
        hw (partitionWeight_dvd_period d hd j)).trans ?_
      omega
    _ = (d + 1) * (M - 1) := by simp [Nat.mul_comm]
    _ = (d + 1) *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 2) := by
      simp [M, Nat.sub_sub]

private lemma finiteGeometricPolynomial_mul_one_sub_X_pow (w M : ℕ)
    (hw : 0 < w) (hdiv : w ∣ M) :
    (finiteGeometricPolynomial w M : PowerSeries ℚ) * (1 - PowerSeries.X ^ w) =
      1 - PowerSeries.X ^ M := by
  change Polynomial.coeToPowerSeries.ringHom (finiteGeometricPolynomial w M) *
      (1 - PowerSeries.X ^ w) = 1 - PowerSeries.X ^ M
  rw [finiteGeometricPolynomial, map_sum]
  simp only [map_pow, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [show (∑ x ∈ Finset.range (M / w), PowerSeries.X ^ (x * w)) =
      ∑ x ∈ Finset.range (M / w), (PowerSeries.X ^ w) ^ x by
    apply Finset.sum_congr rfl
    intro x _
    rw [Nat.mul_comm]
    exact pow_mul (PowerSeries.X : PowerSeries ℚ) w x]
  rw [geom_sum_mul_neg, ← pow_mul, Nat.mul_div_cancel' hdiv]

private lemma geometricFactor_eq_finite_mul_period (w M : ℕ)
    (hw : 0 < w) (hM : 0 < M) (hdiv : w ∣ M) :
    geometricFactor w =
      (finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M := by
  have hfinite := finiteGeometricPolynomial_mul_one_sub_X_pow w M hw hdiv
  have hwInv := geometricFactor_mul_one_sub_X_pow w hw
  have hMInv := geometricFactor_mul_one_sub_X_pow M hM
  have hcand :
      ((finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M) *
          (1 - PowerSeries.X ^ w) = 1 := by
    calc
      _ = geometricFactor M *
          ((finiteGeometricPolynomial w M : PowerSeries ℚ) *
            (1 - PowerSeries.X ^ w)) := by ring
      _ = geometricFactor M * (1 - PowerSeries.X ^ M) := by rw [hfinite]
      _ = 1 := hMInv
  calc
    geometricFactor w = geometricFactor w * 1 := by rw [mul_one]
    _ = geometricFactor w *
        (((finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M) *
          (1 - PowerSeries.X ^ w)) := by rw [hcand]
    _ = (finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M := by
      rw [show geometricFactor w *
          (((finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M) *
            (1 - PowerSeries.X ^ w)) =
          (geometricFactor w * (1 - PowerSeries.X ^ w)) *
            ((finiteGeometricPolynomial w M : PowerSeries ℚ) * geometricFactor M) by ring]
      rw [hwInv, one_mul]

private lemma restrictedPartitionSeries_factorization (d : ℕ) (hd : 1 ≤ d) :
    restrictedPartitionSeries d =
      (periodNumerator d : PowerSeries ℚ) *
        geometricFactor
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) ^
            (d + 1) := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  rw [restrictedPartitionSeries]
  simp_rw [geometricFactor_eq_finite_mul_period _ M
    (partitionWeight_pos d hd _) hM
    (partitionWeight_dvd_period d hd _)]
  rw [Finset.prod_mul_distrib]
  have hcoe :
      (∏ j : Option (Fin d),
          (finiteGeometricPolynomial (partitionWeight d j) M : PowerSeries ℚ)) =
        (periodNumerator d : PowerSeries ℚ) := by
    change (∏ j : Option (Fin d), Polynomial.coeToPowerSeries.ringHom
        (finiteGeometricPolynomial (partitionWeight d j) M)) =
      Polynomial.coeToPowerSeries.ringHom (periodNumerator d)
    rw [periodNumerator, map_prod]
  rw [hcoe]
  simp [M]

private lemma coeff_geometricFactor_pow (d M n : ℕ) (hM : 0 < M) :
    PowerSeries.coeff n (geometricFactor M ^ (d + 1)) =
      if M ∣ n then ((n / M + d).choose d : ℚ) else 0 := by
  rw [geometricFactor_eq_subst M hM]
  rw [← PowerSeries.subst_pow (PowerSeries.HasSubst.X_pow hM.ne')]
  rw [PowerSeries.coeff_subst_X_pow hM.ne']
  split_ifs with hdiv
  · rw [PowerSeries.mk_one_pow_eq_mk_choose_add]
    simp [Nat.add_comm]
  · rfl

private def binomialShiftPolynomial (d j : ℕ) : Polynomial ℚ :=
  Polynomial.C (d.factorial : ℚ)⁻¹ *
    (descPochhammer ℚ d).comp
      (Polynomial.X + Polynomial.C ((d : ℚ) - (j : ℚ)))

private lemma binomialShiftPolynomial_eval (d j t : ℕ) (hj : j ≤ d) :
    (binomialShiftPolynomial d j).eval (t : ℚ) =
      if j ≤ t then ((t - j + d).choose d : ℚ) else 0 := by
  rw [binomialShiftPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
  split_ifs with hjt
  · have harg : (t : ℚ) + ((d : ℚ) - (j : ℚ)) = (t - j + d : ℕ) := by
      rw [Nat.cast_add, Nat.cast_sub hjt]
      push_cast
      ring
    rw [harg, Nat.cast_choose_eq_descPochhammer_div]
    simp [div_eq_mul_inv, mul_comm]
  · have htj : t < j := by omega
    have harg : (t : ℚ) + ((d : ℚ) - (j : ℚ)) = (t + d - j : ℕ) := by
      rw [Nat.cast_sub (by omega : j ≤ t + d), Nat.cast_add]
      push_cast
      ring
    rw [harg, descPochhammer_eval_coe_nat_of_lt]
    · simp
    · omega

private def baseSamplePolynomial (d : ℕ) : Polynomial ℚ :=
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  ∑ j ∈ Finset.range (d + 1),
    Polynomial.C ((periodNumerator d).coeff (j * M)) * binomialShiftPolynomial d j

private def interiorSamplePolynomial (d : ℕ) : Polynomial ℚ :=
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  ∑ j ∈ Finset.Icc 1 d,
    Polynomial.C ((periodNumerator d).coeff (j * M - 1)) * binomialShiftPolynomial d j

private lemma baseSamplePolynomial_eval (d t : ℕ) :
    (baseSamplePolynomial d).eval (t : ℚ) =
      ∑ j ∈ Finset.range (d + 1),
        (periodNumerator d).coeff
            (j *
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)) *
          if j ≤ t then ((t - j + d).choose d : ℚ) else 0 := by
  classical
  rw [baseSamplePolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    binomialShiftPolynomial_eval d j t (by simpa using hj)]

private lemma interiorSamplePolynomial_eval (d t : ℕ) :
    (interiorSamplePolynomial d).eval (t : ℚ) =
      ∑ j ∈ Finset.Icc 1 d,
        (periodNumerator d).coeff
            (j *
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1) *
          if j ≤ t then ((t - j + d).choose d : ℚ) else 0 := by
  classical
  rw [interiorSamplePolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  have hjd : j ≤ d := (Finset.mem_Icc.mp hj).2
  rw [Polynomial.eval_mul, Polynomial.eval_C,
    binomialShiftPolynomial_eval d j t hjd]

private lemma coeff_restrictedPartitionSeries_period_eq_eval (d t : ℕ) (hd : 1 ≤ d) :
    PowerSeries.coeff
        (t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))
        (restrictedPartitionSeries d) = (baseSamplePolynomial d).eval (t : ℚ) := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  rw [restrictedPartitionSeries_factorization d hd, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.fst, Prod.snd, Polynomial.coeff_coe]
  simp_rw [coeff_geometricFactor_pow d
    (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) _ hM]
  rw [baseSamplePolynomial_eval]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => j * M) ?_ ?_ ?_ ?_
  · intro a ha hne
    have hat : a ≤ t := by
      by_contra h
      simp [Nat.lt_of_not_ge h] at hne
    simp only [Finset.mem_range]
    change a * M < (t * M).succ
    exact Nat.lt_succ_iff.mpr (Nat.mul_le_mul_right M hat)
  · intro a₁ _ _ a₂ _ _ heq
    exact Nat.eq_of_mul_eq_mul_right hM heq
  · intro b hb hne
    have hcoeff : (periodNumerator d).coeff b ≠ 0 := by
      intro hzero
      simp [hzero] at hne
    have hdivSub : M ∣ t * M - b := by
      by_contra h
      simp [M, h] at hne
    have hb : b ≤ t * M := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hb
    have hdiv : M ∣ b := by
      rcases hdivSub with ⟨q, hq⟩
      have hsum : M * q + b = M * t := by
        rw [← hq, Nat.sub_add_cancel hb, Nat.mul_comm t M]
      have hmq : M * q ≤ M * t := by omega
      have hqle : q ≤ t := le_of_mul_le_mul_left hmq hM
      refine ⟨t - q, ?_⟩
      rw [Nat.mul_sub_left_distrib]
      omega
    let a := b / M
    have hab : a * M = b := Nat.div_mul_cancel hdiv
    have hdeg := periodNumerator_natDegree_le d hd
    have hble : b ≤ (periodNumerator d).natDegree :=
      Polynomial.le_natDegree_of_ne_zero hcoeff
    have ha : a < d + 1 := by
      have hbstrict : b < (d + 1) * M := by
        refine lt_of_le_of_lt (hble.trans hdeg) ?_
        dsimp [M]
        exact Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      by_contra h
      rw [not_lt] at h
      have hamul := Nat.mul_le_mul_right M h
      omega
    have hat : a ≤ t := by
      have hamul : a * M ≤ t * M := by omega
      exact le_of_mul_le_mul_right hamul hM
    refine ⟨a, Finset.mem_range.mpr ha, ?_, hab⟩
    have hcoeffa : (periodNumerator d).coeff (a *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)) ≠ 0 := by
      rw [show a *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) = b by
        exact hab]
      exact hcoeff
    have hchoose : (t - a + d).choose d ≠ 0 :=
      (Nat.choose_pos (by omega)).ne'
    rw [if_pos hat]
    exact mul_ne_zero hcoeffa (Nat.cast_ne_zero.mpr hchoose)
  · intro a _ hne
    have hat : a ≤ t := by
      by_contra h
      simp [Nat.lt_of_not_ge h] at hne
    rw [if_pos hat]
    change (periodNumerator d).coeff (a * M) * ↑((t - a + d).choose d) =
      (periodNumerator d).coeff (a * M) *
        if M ∣ t * M - a * M then
          ↑(((t * M - a * M) / M + d).choose d) else 0
    rw [show t * M - a * M = (t - a) * M by rw [Nat.sub_mul]]
    simp [hM.ne']

private lemma coeff_restrictedPartitionSeries_period_sub_one_eq_eval
    (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    PowerSeries.coeff
        (t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)
        (restrictedPartitionSeries d) = (interiorSamplePolynomial d).eval (t : ℚ) := by
  classical
  let M := D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1
  have hM : 0 < M := Nat.sub_pos_of_lt
    (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd))
  rw [restrictedPartitionSeries_factorization d hd, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Prod.fst, Prod.snd, Polynomial.coeff_coe]
  simp_rw [coeff_geometricFactor_pow d
    (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) _ hM]
  rw [interiorSamplePolynomial_eval]
  symm
  refine Finset.sum_bij_ne_zero (fun j _ _ => j * M - 1) ?_ ?_ ?_ ?_
  · intro a ha hne
    have hat : a ≤ t := by
      by_contra h
      simp [Nat.lt_of_not_ge h] at hne
    simp only [Finset.mem_range]
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    change a * M - 1 < (t * M - 1).succ
    exact Nat.lt_succ_iff.mpr
      (Nat.sub_le_sub_right (Nat.mul_le_mul_right M hat) 1)
  · intro a₁ ha₁ _ a₂ ha₂ _ heq
    have ha₁pos : 0 < a₁ * M := Nat.mul_pos (Finset.mem_Icc.mp ha₁).1 hM
    have ha₂pos : 0 < a₂ * M := Nat.mul_pos (Finset.mem_Icc.mp ha₂).1 hM
    have hmul : a₁ * M = a₂ * M := by omega
    exact Nat.eq_of_mul_eq_mul_right hM hmul
  · intro b hb hne
    have hcoeff : (periodNumerator d).coeff b ≠ 0 := by
      intro hzero
      simp [hzero] at hne
    have hdivSub : M ∣ t * M - 1 - b := by
      by_contra h
      simp [M, h] at hne
    have htM : 0 < t * M := Nat.mul_pos ht hM
    have hb : b < t * M := by
      simp only [Finset.mem_range] at hb
      change b < (t * M - 1).succ at hb
      simpa only [Nat.succ_eq_add_one, Nat.sub_add_cancel htM] using hb
    have hdiv : M ∣ b + 1 := by
      rcases hdivSub with ⟨q, hq⟩
      refine ⟨t - q, ?_⟩
      have hsum : M * q + (b + 1) = M * t := by
        calc
          M * q + (b + 1) = (t * M - 1 - b) + (b + 1) := by rw [hq]
          _ = t * M := by omega
          _ = M * t := Nat.mul_comm t M
      have hmq : M * q ≤ M * t := by omega
      have hqle : q ≤ t := le_of_mul_le_mul_left hmq hM
      rw [Nat.mul_sub_left_distrib]
      omega
    let a := (b + 1) / M
    have hab : a * M = b + 1 := Nat.div_mul_cancel hdiv
    have habsub : a * M - 1 = b := by omega
    have ha1 : 1 ≤ a := by
      apply Nat.one_le_iff_ne_zero.mpr
      intro ha0
      rw [ha0, zero_mul] at hab
      omega
    have hdeg : (periodNumerator d).natDegree ≤ (d + 1) * (M - 1) := by
      simpa [M, Nat.sub_sub] using periodNumerator_natDegree_le d hd
    have hble : b ≤ (periodNumerator d).natDegree :=
      Polynomial.le_natDegree_of_ne_zero hcoeff
    have had : a ≤ d := by
      by_contra h
      have hda : d + 1 ≤ a := by omega
      have hmul := Nat.mul_le_mul_right M hda
      have hleft : (d + 1) * (M - 1) < (d + 1) * M - 1 := by
        rw [Nat.mul_sub_left_distrib]
        have hprod : d + 1 ≤ (d + 1) * M :=
          Nat.le_mul_of_pos_right (d + 1) hM
        omega
      have hright : (d + 1) * M - 1 ≤ a * M - 1 :=
        Nat.sub_le_sub_right hmul 1
      omega
    have hat : a ≤ t := by
      have hamul : a * M ≤ t * M := by omega
      exact le_of_mul_le_mul_right hamul hM
    refine ⟨a, Finset.mem_Icc.mpr ⟨ha1, had⟩, ?_, ?_⟩
    · have hcoeffa : (periodNumerator d).coeff (a *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1) ≠
          0 := by
        change (periodNumerator d).coeff (a * M - 1) ≠ 0
        rw [habsub]
        exact hcoeff
      have hchoose : (t - a + d).choose d ≠ 0 :=
        (Nat.choose_pos (by omega)).ne'
      rw [if_pos hat]
      exact mul_ne_zero hcoeffa (Nat.cast_ne_zero.mpr hchoose)
    · omega
  · intro a ha hne
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have hat : a ≤ t := by
      by_contra h
      simp [Nat.lt_of_not_ge h] at hne
    rw [if_pos hat]
    change (periodNumerator d).coeff (a * M - 1) * ↑((t - a + d).choose d) =
      (periodNumerator d).coeff (a * M - 1) *
        if M ∣ t * M - 1 - (a * M - 1) then
          ↑(((t * M - 1 - (a * M - 1)) / M + d).choose d) else 0
    have hapos : 0 < a * M := Nat.mul_pos ha1 hM
    have hatmul : a * M ≤ t * M := Nat.mul_le_mul_right M hat
    have hasub : a * M - 1 + 1 = a * M := Nat.sub_add_cancel hapos
    have hdiff : t * M - a * M = (t - a) * M := by rw [Nat.sub_mul]
    have hrewrite : t * M - 1 - (a * M - 1) = (t - a) * M := by
      omega
    rw [hrewrite]
    simp [hM.ne']

private def weightedAntidiagonal (d n : ℕ) :=
  (Finset.finsuppAntidiag (Finset.univ : Finset (Option (Fin d))) n).filter
    fun l => ∀ j, partitionWeight d j ∣ l j

private def solutionFinsupp (d : ℕ) (x : (Fin d → ℕ) × ℕ) :
    Option (Fin d) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun
    | none => x.2
    | some i => x.1 i * baseWeight d i

private lemma solutionFinsupp_sum (d : ℕ) (x : (Fin d → ℕ) × ℕ) :
    ∑ j, solutionFinsupp d x j = naturalWeightedMass d x.1 + x.2 := by
  simp [solutionFinsupp, Fintype.sum_option, naturalWeightedMass, Nat.add_comm]

private def solutionToWeightedAntidiagonal (d n : ℕ)
    (x : {x : (Fin d → ℕ) × ℕ // IsBaseSolution d n x}) :
    weightedAntidiagonal d
      (n * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)) := by
  refine ⟨solutionFinsupp d x, ?_⟩
  rw [weightedAntidiagonal, Finset.mem_filter, Finset.mem_finsuppAntidiag]
  refine ⟨⟨?_, by simp⟩, ?_⟩
  · rw [solutionFinsupp_sum]
    exact x.property
  · intro j
    cases j with
    | none => simp [partitionWeight]
    | some i =>
        refine ⟨x.val.1 i, ?_⟩
        simp [partitionWeight, solutionFinsupp, Nat.mul_comm]

private lemma weightedAntidiagonal_spec (d n : ℕ)
    (l : weightedAntidiagonal d n) :
    (∑ j, l.val j = n) ∧ ∀ j, partitionWeight d j ∣ l.val j := by
  simpa only [weightedAntidiagonal, Finset.mem_filter, Finset.mem_finsuppAntidiag,
    Finset.mem_univ, Finset.subset_univ, and_true] using l.property

private def weightedAntidiagonalToSolution (d n : ℕ) (hd : 1 ≤ d)
    (l : weightedAntidiagonal d
      (n * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))) :
    {x : (Fin d → ℕ) × ℕ // IsBaseSolution d n x} := by
  have hl := weightedAntidiagonal_spec d _ l
  refine ⟨((fun i => l.val (some i) / baseWeight d i), l.val none), ?_⟩
  rw [IsBaseSolution, naturalWeightedMass]
  calc
    (∑ i, l.val (some i) / baseWeight d i * baseWeight d i) + l.val none =
        (∑ i, l.val (some i)) + l.val none := by
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact Nat.div_mul_cancel (hl.2 (some i))
    _ = ∑ j, l.val j := by rw [Fintype.sum_option, Nat.add_comm]
    _ = n *
        (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) :=
      hl.1

private def baseSolutionWeightedAntidiagonalEquiv (d n : ℕ) (hd : 1 ≤ d) :
    {x : (Fin d → ℕ) × ℕ // IsBaseSolution d n x} ≃
      weightedAntidiagonal d
        (n * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1)) where
  toFun := solutionToWeightedAntidiagonal d n
  invFun := weightedAntidiagonalToSolution d n hd
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change x.val.1 i * baseWeight d i / baseWeight d i = x.val.1 i
      exact Nat.mul_div_cancel _ (baseWeight_pos d hd i)
    · change x.val.2 = x.val.2
      rfl
  right_inv l := by
    apply Subtype.ext
    apply Finsupp.ext
    intro j
    cases j with
    | none =>
        change l.val none = l.val none
        rfl
    | some i =>
        have hl := weightedAntidiagonal_spec d _ l
        change l.val (some i) / baseWeight d i * baseWeight d i = l.val (some i)
        exact Nat.div_mul_cancel (hl.2 (some i))

private def interiorSolutionToWeightedAntidiagonal (d t : ℕ)
    (x : {x : (Fin d → ℕ) × ℕ // IsInteriorShiftSolution d t x}) :
    weightedAntidiagonal d
      (t * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1) := by
  refine ⟨solutionFinsupp d x, ?_⟩
  rw [weightedAntidiagonal, Finset.mem_filter, Finset.mem_finsuppAntidiag]
  refine ⟨⟨?_, by simp⟩, ?_⟩
  · rw [solutionFinsupp_sum]
    have hx := x.property
    rw [IsInteriorShiftSolution] at hx
    omega
  · intro j
    cases j with
    | none => simp [partitionWeight]
    | some i =>
        refine ⟨x.val.1 i, ?_⟩
        simp [partitionWeight, solutionFinsupp, Nat.mul_comm]

private def weightedAntidiagonalToInteriorSolution (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t)
    (l : weightedAntidiagonal d
      (t * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)) :
    {x : (Fin d → ℕ) × ℕ // IsInteriorShiftSolution d t x} := by
  have hl := weightedAntidiagonal_spec d _ l
  refine ⟨((fun i => l.val (some i) / baseWeight d i), l.val none), ?_⟩
  rw [IsInteriorShiftSolution, naturalWeightedMass]
  have hperiod : 0 <
      t * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) :=
    Nat.mul_pos (by omega) (Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two (two_le_sylvester d hd)))
  calc
    (∑ i, l.val (some i) / baseWeight d i * baseWeight d i) + l.val none + 1 =
        (∑ i, l.val (some i)) + l.val none + 1 := by
          congr 2
          apply Finset.sum_congr rfl
          intro i _
          exact Nat.div_mul_cancel (hl.2 (some i))
    _ = (∑ j, l.val j) + 1 := by
      rw [Fintype.sum_option]
      omega
    _ = t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1 + 1 :=
      congrArg (· + 1) hl.1
    _ = t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) :=
      Nat.sub_add_cancel (by omega)

private def interiorSolutionWeightedAntidiagonalEquiv (d t : ℕ) (hd : 1 ≤ d) (ht : 1 ≤ t) :
    {x : (Fin d → ℕ) × ℕ // IsInteriorShiftSolution d t x} ≃
      weightedAntidiagonal d
        (t * (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1) where
  toFun := interiorSolutionToWeightedAntidiagonal d t
  invFun := weightedAntidiagonalToInteriorSolution d t hd ht
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change x.val.1 i * baseWeight d i / baseWeight d i = x.val.1 i
      exact Nat.mul_div_cancel _ (baseWeight_pos d hd i)
    · change x.val.2 = x.val.2
      rfl
  right_inv l := by
    apply Subtype.ext
    apply Finsupp.ext
    intro j
    cases j with
    | none =>
        change l.val none = l.val none
        rfl
    | some i =>
        have hl := weightedAntidiagonal_spec d _ l
        change l.val (some i) / baseWeight d i * baseWeight d i = l.val (some i)
        exact Nat.div_mul_cancel (hl.2 (some i))

/-- Expanding the finite product gives precisely the weighted antidiagonal.
This is the coefficient-level identity needed before any root decomposition. -/
private lemma coeff_restrictedPartitionSeries (d n : ℕ) :
    PowerSeries.coeff n (restrictedPartitionSeries d) =
      (weightedAntidiagonal d n).card := by
  classical
  rw [restrictedPartitionSeries, PowerSeries.coeff_prod]
  simp only [geometricFactor, PowerSeries.coeff_mk, Finset.mem_univ, Finset.prod_boole,
    forall_const]
  rw [Finset.sum_boole]
  rfl

/-- The coefficient at the source period multiple is the actual lattice-point
count of the undilated-last-axis Sylvester simplex. -/
private lemma coeff_restrictedPartitionSeries_base_count (d t : ℕ) (hd : 1 ≤ d) :
    PowerSeries.coeff
        (t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))
        (restrictedPartitionSeries d) = (ehrhartCount d 0 t : ℚ) := by
  rw [coeff_restrictedPartitionSeries, ehrhartCount_base_eq_solution_card d t hd]
  norm_cast
  calc
    (weightedAntidiagonal d
        (t *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))).card =
        Fintype.card
          (weightedAntidiagonal d
            (t *
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))) :=
      (Fintype.card_coe _).symm
    _ = Nat.card
          (weightedAntidiagonal d
            (t *
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1))) :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card {x : (Fin d → ℕ) × ℕ // IsBaseSolution d t x} :=
      (Nat.card_congr (baseSolutionWeightedAntidiagonalEquiv d t hd)).symm

private lemma baseSamplePolynomial_eq_count (d t : ℕ) (hd : 1 ≤ d) :
    (baseSamplePolynomial d).eval (t : ℚ) = (ehrhartCount d 0 t : ℚ) := by
  rw [← coeff_restrictedPartitionSeries_period_eq_eval d t hd,
    coeff_restrictedPartitionSeries_base_count d t hd]

/-- Integer-indexed `Mt-1` sampling.  The zero input is the coefficient at
formal index `-1`, hence zero rather than the constant coefficient. -/
private def interiorRestrictedPartitionSample (d : ℕ) : ℕ → ℚ
  | 0 => 0
  | t + 1 =>
      PowerSeries.coeff
        ((t + 1) *
          (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)
        (restrictedPartitionSeries d)

private lemma interiorSamplePolynomial_eq_sample (d t : ℕ) (hd : 1 ≤ d) :
    (interiorSamplePolynomial d).eval (t : ℚ) =
      interiorRestrictedPartitionSample d t := by
  cases t with
  | zero =>
      rw [interiorSamplePolynomial_eval]
      simp [interiorRestrictedPartitionSample]
  | succ t =>
      rw [interiorRestrictedPartitionSample,
        coeff_restrictedPartitionSeries_period_sub_one_eq_eval d (t + 1) hd (by omega)]

private lemma interiorRestrictedPartitionSample_eq_count (d t : ℕ) (hd : 1 ≤ d) :
    interiorRestrictedPartitionSample d t =
      (Nat.card {x : (Fin d → ℕ) × ℕ // IsInteriorShiftSolution d t x} : ℚ) := by
  cases t with
  | zero =>
      letI := no_interior_shift_solution_zero d
      simp [interiorRestrictedPartitionSample, Nat.card_of_isEmpty]
  | succ t =>
      rw [interiorRestrictedPartitionSample, coeff_restrictedPartitionSeries]
      norm_cast
      calc
        (weightedAntidiagonal d
            ((t + 1) *
              (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)).card =
            Fintype.card
              (weightedAntidiagonal d
                ((t + 1) *
                  (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)) :=
          (Fintype.card_coe _).symm
        _ = Nat.card
              (weightedAntidiagonal d
                ((t + 1) *
                  (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester d - 1) - 1)) :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card {x : (Fin d → ℕ) × ℕ // IsInteriorShiftSolution d (t + 1) x} :=
          (Nat.card_congr
            (interiorSolutionWeightedAntidiagonalEquiv d (t + 1) hd (by omega))).symm

/-- The actual all-`k` source count is the sum of its exact `Mt` and `Mt-1`
restricted-partition samples. -/
private lemma ehrhartCount_eq_restrictedPartition_samples (n k t : ℕ) :
    (ehrhartCount (n + 1) k t : ℚ) =
      PowerSeries.coeff
          (t *
            (D5.S0.FiniteGeometry.SylvesterSimplexEhrhartNonpositivity.sylvester
              (n + 1) - 1))
          (restrictedPartitionSeries (n + 1)) +
        (k : ℚ) * interiorRestrictedPartitionSample (n + 1) t := by
  rw [ehrhartCount_source_decomposition, Nat.cast_add, Nat.cast_mul,
    ← coeff_restrictedPartitionSeries_base_count (n + 1) t (by omega),
    ← interiorRestrictedPartitionSample_eq_count (n + 1) t (by omega)]

private def sourceEhrhartPolynomial (n k : ℕ) : Polynomial ℚ :=
  baseSamplePolynomial (n + 1) +
    Polynomial.C (k : ℚ) * interiorSamplePolynomial (n + 1)

private lemma sourceEhrhartPolynomial_eval (n k t : ℕ) :
    (sourceEhrhartPolynomial n k).eval (t : ℚ) =
      (ehrhartCount (n + 1) k t : ℚ) := by
  rw [sourceEhrhartPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, baseSamplePolynomial_eq_count (n + 1) t (by omega),
    interiorSamplePolynomial_eq_sample (n + 1) t (by omega),
    interiorRestrictedPartitionSample_eq_count (n + 1) t (by omega)]
  exact_mod_cast (ehrhartCount_source_decomposition n k t).symm

end D5.S0.FiniteGeometry.SylvesterSimplexEhrhartSamples
